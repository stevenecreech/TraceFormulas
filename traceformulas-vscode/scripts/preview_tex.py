"""Build manuscripts in their volume; preview lecture fragments separately."""

from pathlib import Path
import argparse
import shutil
import sys

from tex import TexError, run

ROOT = Path(__file__).resolve().parents[1]


def manuscript_volume(source: Path) -> str | None:
    """Find the volume only for sources actually included in its manuscript."""
    if source.name not in {'text.tex', 'intro.tex'}:
        return None
    from build import catalog, load_json, source_directory, validate_outline
    for volume in catalog(ROOT)['volumes']:
        book = ROOT / volume['path']
        if not source.is_relative_to(book.resolve()):
            continue
        outline_path = book / 'outline.json'
        records, _ = validate_outline(load_json(outline_path), str(outline_path))
        for record in records:
            base = source_directory(book, record)
            included = [base / 'intro.tex'] + [
                base / 'sections' / f'Section{index:02d}' / 'text.tex'
                for index, _ in enumerate(record['sections'], 1)
            ]
            if any(source == path.resolve() for path in included):
                return volume['id']
    return None


def preview_volume(volume_id: str) -> Path:
    from build import build
    print(f'Building volume {volume_id} and the website so manuscript references '
          'and numbering resolve correctly.', flush=True)
    result = build(ROOT, ROOT / 'dist', pdf=True, selected_volume=volume_id)
    if not result['pdfs']:
        raise TexError(f'{volume_id} has no manuscript chapters to compile.')
    return ROOT / '.build' / volume_id / 'main.pdf'


def preview(source: Path) -> Path:
    source = source.resolve()
    if source.name == 'main.tex' and source.parent.parent == ROOT / '.build':
        # A generated volume root is a useful editor entry point, but regenerate
        # it from the manuscript rather than treating it as a section fragment.
        return preview_volume(source.parent.name)
    if source.suffix != '.tex' or not source.is_file() or not source.is_relative_to(ROOT / 'volumes'):
        raise TexError('Open a .tex source inside volumes/ before running this task.')
    volume_id = manuscript_volume(source)
    if volume_id is not None:
        return preview_volume(volume_id)
    engine = shutil.which('pdflatex')
    # GUI-launched VS Code on macOS may not inherit the shell's TeX PATH.
    if not engine and Path('/Library/TeX/texbin/pdflatex').is_file():
        engine = '/Library/TeX/texbin/pdflatex'
    if not engine:
        raise TexError('pdflatex was not found. Install a TeX distribution or add it to PATH.')
    relative = source.relative_to(ROOT / 'volumes')
    output = ROOT / '.build/previews' / relative.parent / source.stem
    output.mkdir(parents=True, exist_ok=True)
    wrapper = output / 'preview.tex'
    wrapper.write_text('\n'.join([
        r'\documentclass[11pt,oneside]{book}',
        r'\input{tex/preamble.tex}',
        r'\setcounter{secnumdepth}{-1}',
        r'\setlength{\emergencystretch}{3em}',
        r'\begin{document}',
        r'\input{' + source.relative_to(ROOT).as_posix() + '}',
        r'\end{document}', '',
    ]), encoding='utf-8')
    command = [engine, '-no-shell-escape', '-halt-on-error', '-file-line-error',
               '-interaction=nonstopmode', '-synctex=1',
               '-output-directory=' + str(output), str(wrapper)]
    for _ in range(2):
        run(command, cwd=ROOT)
    log = (output / 'preview.log').read_text(errors='replace')
    if 'There were undefined references' in log or 'There were undefined citations' in log:
        raise TexError(f'{output}/preview.log: unresolved references; use the full-volume build for cross-section references.')
    return output / 'preview.pdf'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path, help='Active .tex file supplied by VS Code')
    args = parser.parse_args()
    try:
        pdf = preview(args.source)
    except (ValueError, OSError) as exc:
        print(f'Preview failed: {exc}', file=sys.stderr)
        return 1
    print(f'Compiled successfully. PDF: {pdf}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
