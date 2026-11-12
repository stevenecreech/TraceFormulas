"""Render the shared LaTeX manuscript with Pandoc; compile print editions with TeX."""

from __future__ import annotations

import os
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import html
from html.parser import HTMLParser
import re
from urllib.parse import quote, unquote, urlsplit


def publish_file(source: Path, destination: Path) -> None:
    """Replace a published artifact only once the complete new file is ready."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=destination.parent, prefix='.publish-', delete=False) as stream:
        temporary = Path(stream.name)
    try:
        shutil.copyfile(source, temporary)
        os.replace(temporary, destination)
    finally:
        temporary.unlink(missing_ok=True)


class TexError(ValueError):
    pass


def manuscript_images(source: str, root: Path) -> str:
    """Use a paired SVG for each print PDF; publish both under sources/volumes.

    Manuscripts specify package-relative paths, as required by the TeX build.
    Check both assets before emitting an image URL, including during --check.
    """
    changes = []
    offsets = [0]
    for line in source.splitlines(keepends=True):
        offsets.append(offsets[-1] + len(line))
    volume_root = (root / 'volumes').resolve()

    class Images(HTMLParser):
        def handle_starttag(self, tag, attrs):
            if tag not in {'img', 'embed'}:
                return
            src = dict(attrs).get('src', '')
            url = urlsplit(src)
            if url.scheme or url.netloc or url.query or url.fragment:
                raise TexError('Manuscript figures must use local paths under volumes/.')
            path = (root / unquote(url.path)).resolve()
            if not path.is_relative_to(volume_root) or not path.is_file():
                raise TexError(f'Missing or out-of-tree manuscript figure: {src}')
            if path.suffix.lower() == '.pdf':
                web = path.with_suffix('.svg').resolve()
                if not web.is_relative_to(volume_root) or not web.is_file():
                    raise TexError(f'Manuscript PDF figure requires a paired SVG: {src}')
            elif path.suffix.lower() in {'.png', '.jpg', '.jpeg'}:
                web = path
            else:
                raise TexError('Use PDF with a paired SVG, or PNG/JPEG, for manuscript figures.')
            target = 'sources/' + quote(web.relative_to(root.resolve()).as_posix())
            old = self.get_starttag_text()
            new = re.sub(r'''\bsrc\s*=\s*(["']).*?\1''',
                         lambda _: 'src="' + html.escape(target, quote=True) + '"', old, count=1)
            if tag == 'embed':
                # Pandoc emits PDF images as <embed>; browsers need the paired
                # vector image. The adjacent figure caption describes it.
                new = re.sub(r'^<embed\b', '<img alt=""', new)
            line, col = self.getpos()
            start = offsets[line - 1] + col
            changes.append((start, start + len(old), new))

        handle_startendtag = handle_starttag

    Images(convert_charrefs=True).feed(source)
    for start, end, replacement in reversed(changes):
        source = source[:start] + replacement + source[end:]
    return source


def pandoc_path(root: Path) -> str:
    local = sorted(root.glob('.venv/lib/*/site-packages/pypandoc/files/pandoc'))
    candidates = [os.environ.get('PANDOC'), *(str(p) for p in local)]
    # CI installs pypandoc_binary in the active interpreter, without a project
    # .venv. Its bundled executable is not necessarily on PATH.
    package = importlib.util.find_spec('pypandoc')
    if package and package.submodule_search_locations:
        candidates.extend(str(Path(directory) / 'files/pandoc')
                          for directory in package.submodule_search_locations)
    candidates.append(shutil.which('pandoc'))
    for candidate in candidates:
        if candidate and Path(candidate).is_file():
            return candidate
    raise TexError('Pandoc is required. Run python3 -m venv .venv, then '
                   '.venv/bin/python -m pip install -r requirements.txt (or set PANDOC).')


def run(command: list[str], *, cwd: Path, source: str | None = None) -> str:
    try:
        result = subprocess.run(command, cwd=cwd, input=source, text=True,
                                capture_output=True, timeout=120)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise TexError(f'{command[0]} could not finish: {exc}') from exc
    if result.returncode:
        raise TexError(f'{" ".join(command)}\n{result.stderr or result.stdout}')
    return result.stdout


class Renderer:
    def __init__(self, root: Path):
        self.root = root
        self.pandoc = pandoc_path(root)
        self.macros = (root / 'tex/macros.tex').read_text(encoding='utf-8')
        self.cache: dict[tuple[Path, str, str | None], str] = {}

    def render(self, path: Path, *, optional: bool = False,
               number_prefix: str | None = None) -> str:
        if optional and not path.exists():
            return ''
        if path.suffix != '.tex':
            raise TexError(f'{path}: prose sources must be .tex files')
        source = path.read_text(encoding='utf-8').strip()
        if not source:
            return ''
        key = (path.resolve(), source, number_prefix)
        if key not in self.cache:
            # Fail on unsupported raw TeX instead of silently dropping mathematical text.
            command = [
                self.pandoc, '--from=latex+raw_tex', '--to=html5', '--mathjax', '--wrap=none',
                '--fail-if-warnings', '--lua-filter=' + str(self.root / 'scripts/strict-tex.lua'),
            ]
            if number_prefix is not None:
                command.append('--metadata=theorem-prefix:' + number_prefix)
            rendered = run(command, cwd=path.parent, source=self.macros + '\n' + source)
            self.cache[key] = manuscript_images(rendered, self.root)
        return self.cache[key]


def escape(value: str) -> str:
    replacements = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
                    '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
                    '~': r'\textasciitilde{}', '^': r'\textasciicircum{}',
                    '₂': r'\ensuremath{_2}', 'ℤ': r'\ensuremath{\mathbb Z}'}
    return ''.join(replacements.get(c, c) for c in value)


def print_source(root: Path, outline: dict, records: list[dict], directories: dict[str, Path]) -> str:
    lines = [r'\documentclass[11pt,oneside]{book}', r'\input{tex/preamble.tex}',
             r'\title{' + escape(outline['title']) + r'\\[1ex]\large Volume ' + escape(outline['volume'])
             + r'\\' + escape(outline['subtitle']) + '}',
             r'\author{' + escape(outline['author']) + '}', r'\date{Draft edition}',
             r'\begin{document}', r'\frontmatter',
             # book.cls resets the page number after its title page. Suppress
             # that page's anchor so the first front-matter page owns page.i.
             r'\hypersetup{pageanchor=false}', r'\maketitle',
             r'\hypersetup{pageanchor=true}']
    acknowledgments = root / 'volumes/acknowledgments.tex'
    if acknowledgments.is_file() and acknowledgments.read_text(encoding='utf-8').strip():
        lines.extend([r'\chapter*{Acknowledgments}', r'\label{series-acknowledgments}',
                      r'\addcontentsline{toc}{chapter}{Acknowledgments}',
                      r'\input{volumes/acknowledgments.tex}'])
    lines.extend([r'\tableofcontents', r'\mainmatter'])
    division = None
    appendix = False
    for record in records:
        base = directories[record['id']]
        if 'letter' in record and not appendix:
            lines.append(r'\appendix')
            appendix = True
        if not appendix:
            if record['division'] != division:
                division = record['division']
                title = next(d['title'] for d in outline['divisions'] if d['id'] == division)
                lines.append(r'\part{' + escape(title) + '}')
            lines.append(r'\setcounter{chapter}{' + str(record['number'] - 1) + '}')
        else:
            lines.append(r'\setcounter{chapter}{' + str(ord(record['letter'].upper()) - ord('A')) + '}')
        lines.extend([r'\chapter{' + escape(record['title']) + '}',
                      r'\label{' + record['id'] + '}'])
        intro = base / 'intro.tex'
        if intro.read_text().strip():
            lines.append(r'\input{' + intro.relative_to(root).as_posix() + '}')
        elif not record['sections']:
            lines.append(r'\emph{This appendix is in preparation.}')
        for index, section in enumerate(record['sections'], 1):
            path = base / 'sections' / f'Section{index:02d}' / 'text.tex'
            lines.extend([r'\section{' + escape(section['title']) + '}',
                          r'\label{' + section['id'] + '}'])
            if path.read_text().strip():
                lines.append(r'\input{' + path.relative_to(root).as_posix() + '}')
            else:
                lines.append(r'\emph{This section is in preparation.}')
    lines.append(r'\end{document}')
    return '\n'.join(lines) + '\n'


def build_pdf(root: Path, volume_id: str, source: str) -> Path:
    engine = shutil.which('pdflatex')
    if not engine and Path('/Library/TeX/texbin/pdflatex').is_file():
        engine = '/Library/TeX/texbin/pdflatex'
    if not engine:
        raise TexError('PDF requested, but pdflatex is unavailable. Install a TeX distribution.')
    target = root / '.build' / volume_id
    target.mkdir(parents=True, exist_ok=True)
    main = target / 'main.tex'
    if not main.exists() or main.read_text(encoding='utf-8') != source:
        main.write_text(source, encoding='utf-8')
    # Never let the compiler truncate the PDF currently open in the editor.
    staging = target / '.compile'
    staging.mkdir(exist_ok=True)
    command = [engine, '-no-shell-escape', '-halt-on-error', '-interaction=nonstopmode',
               '-file-line-error', '-synctex=1',
               '-output-directory=' + str(staging), str(main)]
    # Two passes resolve the table of contents and ordinary LaTeX references.
    for _ in range(2):
        run(command, cwd=root)
    log = (staging / 'main.log').read_text(errors='replace')
    shutil.copyfile(staging / 'main.log', target / 'main.log')
    if 'There were undefined references' in log or 'There were undefined citations' in log:
        raise TexError(f'{target}/main.log: unresolved references or citations in PDF')
    for suffix in ('synctex.gz', 'aux', 'toc', 'out'):
        artifact = staging / ('main.' + suffix)
        if artifact.exists():
            publish_file(artifact, target / artifact.name)
    publish_file(staging / 'main.pdf', target / 'main.pdf')
    return target / 'main.pdf'
