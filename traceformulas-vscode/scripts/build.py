#!/usr/bin/env python3
"""Build every volume from LaTeX, adjacent Lean sources, and media metadata."""

from __future__ import annotations

import argparse
import json
import html
from html.parser import HTMLParser
import re
import shutil
import sys
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

from tex import Renderer, TexError, build_pdf, print_source, publish_file

ROOT = Path(__file__).resolve().parent.parent


class BuildError(ValueError):
    """An actionable authoring error."""


def fail(where: str, message: str) -> None:
    raise BuildError(f"{where}: {message}")


def object_value(value, where: str) -> dict:
    if not isinstance(value, dict):
        fail(where, "expected a JSON object")
    return value


def text(value, where: str) -> str:
    if not isinstance(value, str):
        fail(where, "expected text")
    return value


def array(value, where: str) -> list:
    if not isinstance(value, list):
        fail(where, "expected a JSON array")
    return value


def keys(value: dict, allowed: set[str], where: str) -> None:
    unexpected = set(value) - allowed
    if unexpected:
        fail(where, "unknown field(s): " + ", ".join(sorted(unexpected)))


def load_json(path: Path) -> dict:
    try:
        return object_value(json.loads(path.read_text(encoding="utf-8")), str(path))
    except OSError as exc:
        raise BuildError(f"{path}: {exc.strerror or exc}") from exc
    except json.JSONDecodeError as exc:
        raise BuildError(f"{path}:{exc.lineno}:{exc.colno}: {exc.msg}") from exc


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError as exc:
        raise BuildError(f"{path}: {exc.strerror or exc}") from exc


def local_file(base: Path, name: str, where: str) -> Path:
    name = text(name, where)
    if not name:
        fail(where, "file path cannot be empty")
    path = (base / name).resolve()
    if not path.is_relative_to(base.resolve()):
        fail(where, "referenced files must stay inside this chapter directory")
    if not path.is_file():
        fail(where, f"referenced file does not exist: {name}")
    return path


def from_text_or_file(row: dict, field: str, base: Path, where: str, renderer: Renderer) -> str:
    inline = text(row.get(field, ""), f"{where}.{field}")
    file_key = field + "File"
    if file_key not in row:
        return "<p>" + html.escape(inline) + "</p>" if inline else ""
    if inline.strip():
        fail(where, f"use either {field} or {file_key}, not both")
    return renderer.render(local_file(base, row[file_key], f"{where}.{file_key}"))


def url(value, where: str) -> str:
    value = text(value, where).strip()
    if not value:
        return ""
    try:
        parsed = urlsplit(value)
        parsed.port
    except ValueError as exc:
        raise BuildError(f"{where}: invalid URL") from exc
    if parsed.scheme not in {"http", "https"} or not parsed.hostname:
        fail(where, "use a complete http:// or https:// URL")
    if parsed.username or parsed.password or any(c.isspace() for c in value):
        fail(where, "URL cannot contain embedded credentials or whitespace")
    return value


def declarations(value, where: str) -> str:
    if isinstance(value, str):
        names = value.splitlines()
    elif isinstance(value, list):
        names = [text(name, where) for name in value]
    else:
        fail(where, "expected an array of declaration names or newline-separated text")
    return "\n".join(name.strip() for name in names if name.strip())


def prerequisites(value, target: str, node_ids: set[str], where: str) -> list[str]:
    result = []
    for item in array(value, where):
        item = text(item, where)
        if item not in node_ids:
            fail(where, f"unknown prerequisite ID: {item}")
        if item == target:
            fail(where, "an item cannot be its own prerequisite")
        if item not in result:
            result.append(item)
    return result


ROW_FIELDS = {
    "videos": {"title", "kind", "url", "transcript", "transcriptFile"},
    "exercises": {"title", "question", "questionFile", "hint", "hintFile", "solution", "solutionFile"},
    "explorations": {"title", "url", "description", "descriptionFile"},
    "resources": {"title", "url"},
}
PROSE_FIELDS = {
    "videos": ("transcript",),
    "exercises": ("question", "hint", "solution"),
    "explorations": ("description",),
    "resources": (),
}


def rows(metadata: dict, name: str, base: Path, renderer: Renderer) -> list[dict]:
    result = []
    for index, entry in enumerate(array(metadata.get(name, []), f"{base}/chapter.json:{name}")):
        where = f"{base}/chapter.json:{name}[{index}]"
        entry = object_value(entry, where)
        keys(entry, ROW_FIELDS[name], where)
        row = {"title": text(entry.get("title", ""), where + ".title")}
        if "url" in ROW_FIELDS[name]:
            row["url"] = url(entry.get("url", ""), where + ".url")
        for field in PROSE_FIELDS[name]:
            row[field] = from_text_or_file(entry, field, base, where, renderer)
        if name == "videos":
            kind = text(entry.get("kind", "concept"), where + ".kind")
            if kind not in {"concept", "proof", "formalization"}:
                fail(where + ".kind", "choose concept, proof, or formalization")
            row["kind"] = kind
        if any(value.strip() for field, value in row.items() if field != "kind"):
            result.append(row)
    return result


def source_directory(book: Path, record: dict) -> Path:
    if "number" in record:
        return book / "chapters" / f"Chapter{record['number']:02d}"
    return book / "appendices" / record["letter"].upper()


def validate_outline(outline: dict, where: str) -> tuple[list[dict], set[str]]:
    if outline.get("schemaVersion") != 1:
        fail(where, "schemaVersion must be 1")
    for field in ("title", "subtitle", "volume", "author", "source"):
        text(outline.get(field), f"{where}.{field}")
    divisions = array(outline.get("divisions"), where + ".divisions")
    division_ids = set()
    for division in divisions:
        object_value(division, where + ".divisions")
        division_id = text(division.get("id"), where + ".divisions.id")
        if division_id in division_ids:
            fail(where, f"duplicate division ID: {division_id}")
        division_ids.add(division_id)
        text(division.get("title"), where + ".divisions.title")
    chapters = array(outline.get("chapters"), where + ".chapters")
    appendices = array(outline.get("appendices"), where + ".appendices")
    records, node_ids, chapter_numbers, letters = [], set(), set(), set()
    for is_appendix, group in ((False, chapters), (True, appendices)):
        for record in group:
            object_value(record, where)
            if is_appendix:
                letter = text(record.get("letter"), where + ".letter")
                if len(letter) != 1 or not letter.isascii() or not letter.isalpha():
                    fail(where, "appendix letter must be a single ASCII letter")
                if letter.lower() in letters:
                    fail(where, f"duplicate appendix letter: {letter}")
                letters.add(letter.lower())
            else:
                number = record.get("number")
                if type(number) is not int or number < 0:
                    fail(where, "chapter number must be a nonnegative integer")
                if number in chapter_numbers:
                    fail(where, f"duplicate chapter number: {number}")
                chapter_numbers.add(number)
                if record.get("division") not in division_ids:
                    fail(where, f"unknown division for chapter {number}")
            record_id = text(record.get("id"), where + ".id")
            if not record_id or record_id in node_ids:
                fail(where, f"empty or duplicate outline ID: {record_id}")
            node_ids.add(record_id)
            text(record.get("title"), where + ".title")
            text(record.get("description"), where + ".description")
            for section in array(record.get("sections"), where + ".sections"):
                object_value(section, where + ".sections")
                section_id = text(section.get("id"), where + ".sections.id")
                if not section_id or section_id in node_ids:
                    fail(where, f"empty or duplicate outline ID: {section_id}")
                node_ids.add(section_id)
                text(section.get("title"), where + ".sections.title")
            records.append(record)
    for route in array(outline.get("routes"), where + ".routes"):
        object_value(route, where + ".routes")
        route_numbers = array(route.get("chapters"), where + ".routes.chapters")
        if not route_numbers:
            fail(where, "reading routes must contain at least one chapter")
        if any(type(number) is not int or number not in chapter_numbers for number in route_numbers):
            fail(where, "reading route contains an unknown chapter number")
    return records, node_ids


def formal_metadata(value: dict, where: str) -> dict:
    formal = object_value(value, where)
    keys(formal, {"status", "url", "declarations"}, where)
    status = text(formal.get("status", "not-started"), where + ".status")
    if status not in {"not-started", "in-progress", "linked", "autoformalized-awaiting-review"}:
        fail(where, "formal.status must be not-started, in-progress, linked, or autoformalized-awaiting-review")
    return {"status": status, "url": url(formal.get("url", ""), where + ".url"),
            "declarations": declarations(formal.get("declarations", []), where + ".declarations")}


def chapter_content(root: Path, book: Path, record: dict, node_ids: set[str], renderer: Renderer) -> dict:
    base = source_directory(book, record)
    chapter_number = str(record['number']) if 'number' in record else record['letter'].upper()
    metadata = load_json(base / "chapter.json")
    keys(metadata, set(ROW_FIELDS) | {"formal", "prerequisites", "sectionPrerequisites"}, str(base))
    formal = formal_metadata(metadata.get("formal", {}), str(base / "chapter.json"))
    section_ids = {section["id"] for section in record["sections"]}
    section_prerequisites = object_value(metadata.get("sectionPrerequisites", {}), str(base))
    for target in section_prerequisites:
        if target not in section_ids:
            fail(str(base), f"unknown section target: {target}")
    content = {
        "intro": renderer.render(base / "intro.tex", number_prefix=chapter_number + '.0'), "sections": {},
        **{name: rows(metadata, name, base, renderer) for name in ROW_FIELDS},
        "formal": {**formal, "summary": renderer.render(base / "formalization.tex"), "sources": []},
        "comparisons": [],
        "prerequisites": prerequisites(metadata.get("prerequisites", []), record["id"], node_ids, str(base)),
        "sectionPrerequisites": {
            target: prerequisites(value, target, node_ids, str(base))
            for target, value in section_prerequisites.items()
        },
    }
    for index, section in enumerate(record["sections"], 1):
        directory = base / "sections" / f"Section{index:02d}"
        section_path = directory / "section.json"
        data = load_json(section_path) if section_path.exists() else {}
        keys(data, {"formal", "videos"}, str(section_path))
        section_formal = formal_metadata(data.get("formal", {}), str(section_path))
        tex_file = local_file(directory, "text.tex", str(directory))
        prose = renderer.render(tex_file, number_prefix=f'{chapter_number}.{index}')
        content["sections"][section["id"]] = prose
        lean_file = directory / "Formalization.lean"
        lean = local_file(directory, "Formalization.lean", str(directory)).read_text(encoding="utf-8") if lean_file.exists() else ""
        if not lean.strip() and (section_formal["status"] != "not-started" or section_formal["declarations"]):
            fail(str(section_path), "a formalization status or declarations requires Formalization.lean")
        # The comparison always reads the same text.tex and actual Lean file; no copied snippets.
        if prose or lean.strip():
            content["comparisons"].append({
                "title": section["title"], "sectionId": section["id"],
                "book": prose, "lean": lean, "status": section_formal["status"],
                "notes": renderer.render(directory / "compare.tex", optional=True),
                "texSource": "sources/" + tex_file.relative_to(root).as_posix(),
                "leanSource": "sources/" + lean_file.relative_to(root).as_posix() if lean_file.exists() else "",
            })
        if lean.strip():
            content["formal"]["sources"].append({
                "title": section["title"], "sectionId": section["id"],
                "code": lean, **section_formal,
                "source": "sources/" + lean_file.relative_to(root).as_posix(),
            })
        content["videos"].extend(rows(data, "videos", directory, renderer))
    return content


def has_content(content: dict) -> bool:
    formal = content["formal"]
    return bool(
        content["intro"]
        or any(content["sections"].values())
        or any(content[name] for name in ROW_FIELDS)
        or content["prerequisites"]
        or any(content["sectionPrerequisites"].values())
        or formal["status"] != "not-started"
        or formal["summary"]
        or formal["url"]
        or formal["declarations"]
    )


class ManuscriptHTML(HTMLParser):
    """Locate anchors and link tags without reserializing mathematics or prose."""

    def __init__(self, source: str):
        super().__init__(convert_charrefs=False)
        self.ids = []
        self.links = []
        self.equations = {}
        self.equation_refs = []
        self.pending_equation_ref = None
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        if attributes.get('id'):
            self.ids.append(attributes['id'])
        if 'numbered-equation' in attributes.get('class', '').split():
            self.equations[attributes['id']] = attributes['data-equation-number']
        if tag == 'a' and attributes.get('href'):
            self.links.append((self.getpos(), self.get_starttag_text(), attributes['href']))
            if 'equation-reference' in attributes.get('class', '').split():
                self.pending_equation_ref = (self.getpos(), self.get_starttag_text(), attributes['href'])

    def handle_endtag(self, tag):
        if tag == 'a' and self.pending_equation_ref:
            self.equation_refs.append((*self.pending_equation_ref, self.getpos()))
            self.pending_equation_ref = None

    handle_startendtag = handle_starttag


def prose_fields(chapter: dict):
    """Yield only rendered HTML fields; Lean code and source paths stay verbatim."""
    yield chapter, 'intro', 'intro'
    for section_id in chapter['sections']:
        yield chapter['sections'], section_id, section_id
    yield chapter['formal'], 'summary', 'formal.summary'
    for name, fields in {**PROSE_FIELDS, 'comparisons': ('book', 'notes')}.items():
        for index, row in enumerate(chapter[name]):
            for field in fields:
                yield row, field, f'{name}[{index}].{field}'


def resolve_manuscript_links(records: list[dict], chapters: dict) -> None:
    """Resolve named links and equation numbers against this volume's manuscript."""
    targets = {}
    equation_numbers = {}

    def add(label, route, where):
        targets.setdefault(label, []).append((route, where))

    for record in records:
        chapter_id = record['id']
        route = '#/chapter/' + quote(chapter_id, safe='') + '/read'
        add(chapter_id, route, chapter_id)
        for section in record['sections']:
            section_id = section['id']
            add(section_id, route + '/' + quote(section_id, safe=''), section_id)
        chapter = chapters.get(chapter_id)
        if not chapter:
            continue
        for section_id, source in [('', chapter['intro']), *chapter['sections'].items()]:
            parsed = ManuscriptHTML(source)
            equation_numbers.update(parsed.equations)
            for label in parsed.ids:
                add(label, route + '/' + quote(section_id, safe='') + '/' + quote(label, safe=''),
                    (section_id or chapter_id + '.intro') + ':' + label)

    for label in equation_numbers:
        if len(targets[label]) != 1:
            fail(label, 'ambiguous equation label; give every manuscript target a unique label')

    href_attribute = re.compile(r'''(?<![-\w:])href\s*=\s*(?:"[^"]*"|'[^']*'|[^\s>]+)''', re.I)
    for chapter_id, chapter in chapters.items():
        for owner, field, location in prose_fields(chapter):
            source = owner[field]
            replacements = []
            line_offsets = [0]
            for match in re.finditer('\n', source):
                line_offsets.append(match.end())
            parsed = ManuscriptHTML(source)
            for (line, column), tag, href, (end_line, end_column) in parsed.equation_refs:
                label = unquote(href[1:])
                if label not in equation_numbers:
                    fail(chapter_id + '.' + location, f"unknown equation reference '{label}'; "
                         "use a label in a manuscript equation environment")
                start = line_offsets[line - 1] + column + len(tag)
                end = line_offsets[end_line - 1] + end_column
                replacements.append((start, end, '(' + equation_numbers[label] + ')'))
            for (line, column), tag, href in parsed.links:
                if not href.startswith('#') or href.startswith('#/') or href == '#':
                    continue
                label = unquote(href[1:])
                candidates = targets.get(label, [])
                where = chapter_id + '.' + location
                if not candidates:
                    fail(where, f"unknown manuscript hyperlink target '{label}'; use an existing "
                         "chapter/section ID or a label on a manuscript heading, theorem, or equation in this volume")
                if len(candidates) != 1:
                    fail(where, f"ambiguous manuscript hyperlink target '{label}' in "
                         + ', '.join(place for _, place in candidates)
                         + '; give the target a unique label')
                destination = html.escape(candidates[0][0], quote=True)
                updated = href_attribute.sub(lambda _: 'href="' + destination + '"', tag, count=1)
                offset = line_offsets[line - 1] + column
                replacements.append((offset, offset + len(tag), updated))
            for start, end, replacement in sorted(replacements, reverse=True):
                source = source[:start] + replacement + source[end:]
            owner[field] = source


def catalog(root: Path) -> dict:
    series = load_json(root / "series.json")
    keys(series, {"schemaVersion", "title", "defaultVolume", "volumes"}, str(root / "series.json"))
    if series.get("schemaVersion") != 1:
        fail("series.json", "schemaVersion must be 1")
    text(series.get("title"), "series.title")
    seen, locations = set(), set()
    for volume in array(series.get("volumes"), "series.volumes"):
        object_value(volume, "series.volume")
        keys(volume, {"id", "number", "part", "label", "topic", "perspective", "description", "path", "status"}, "series.volume")
        for field in ("id", "part", "label", "topic", "perspective", "description", "path", "status"):
            text(volume.get(field), "volume." + field)
        if type(volume.get("number")) is not int or volume["number"] < 1 or volume["part"] not in {"a", "b", "c"}:
            fail("series.json", "volume numbers must be positive integers and parts a, b, c")
        if volume["id"] != f"v{volume['number']}{volume['part']}" or volume["label"] != f"{volume['number']}{volume['part']}":
            fail("series.json", "volume IDs and labels must agree with number and part")
        if volume["id"] in seen or volume["path"] in locations:
            fail("series.json", "duplicate volume ID or path")
        if volume["status"] not in {"planned", "draft", "published"}:
            fail("series.json", "volume status must be planned, draft, or published")
        seen.add(volume["id"])
        locations.add(volume["path"])
        local_file(root / "volumes", str(Path(volume["path"]).relative_to("volumes") / "outline.json"), "volume.path")
    if series.get("defaultVolume") not in seen:
        fail("series.json", "unknown default volume")
    return series


def compile_book(root: Path, volume: dict, renderer: Renderer) -> tuple[dict, dict, list[dict]]:
    root = root.resolve()
    book = root / volume["path"]
    outline = load_json(book / "outline.json")
    if outline.get("volume") != volume["label"]:
        fail(str(book), "outline volume must match series catalog")
    records, node_ids = validate_outline(outline, str(book / "outline.json"))
    if any(not node.startswith(volume["id"] + "-") for node in node_ids):
        fail(str(book), "outline IDs must begin with the volume ID followed by a hyphen")
    settings = load_json(root / "site.json")
    keys(settings, {"features", "repositoryUrl"}, "site.json")
    features = object_value(settings.get("features", {}), "site.features")
    keys(features, {"exercises", "explore"}, "site.features")
    for name, value in features.items():
        if type(value) is not bool:
            fail("site.json", f"features.{name} must be true or false")
    content = {
        "schemaVersion": 2, "bookId": "traceformulas-" + volume["id"], "format": "html",
        "features": {"exercises": False, "explore": False, **features},
        "repositoryUrl": url(settings.get("repositoryUrl", ""), "site.repositoryUrl"),
        "acknowledgments": renderer.render(root / "volumes/acknowledgments.tex", optional=True),
        "chapters": {},
    }
    for record in records:
        chapter = chapter_content(root, book, record, node_ids, renderer)
        if has_content(chapter):
            content["chapters"][record["id"]] = chapter
    resolve_manuscript_links(records, content['chapters'])
    return outline, content, records


def build(root: Path, output: Path, check_only: bool = False, pdf: bool = False,
          selected_volume: str | None = None) -> dict:
    root, output = root.resolve(), output.resolve()
    # Generated output must never overlap authoring files or ancestors of the checkout.
    if output == root or output in root.parents or any(
        output == source or output.is_relative_to(source) or source.is_relative_to(output)
        for source in [root / name for name in ("volumes", "web", "scripts", "tex", "docs", "archive", ".git", ".venv", ".build")]
    ):
        fail(str(output), "output must be separate from the source directories")
    if check_only and pdf:
        fail("build", "--check and --pdf cannot be combined")
    series = catalog(root)
    if selected_volume and selected_volume not in {v["id"] for v in series["volumes"]}:
        fail("--volume", "unknown volume ID")
    renderer = Renderer(root)
    built = []
    for volume in series["volumes"]:
        outline, content, records = compile_book(root, volume, renderer)
        entry = {**volume, "dataPath": "data/" + volume["id"], "pdfUrl": ""}
        if pdf and records and (not selected_volume or volume["id"] == selected_volume):
            source = print_source(root, outline, records, {r["id"]: source_directory(root / volume["path"], r) for r in records})
            pdf_file = build_pdf(root, volume["id"], source)
            pdf_path = output / "pdf" / (volume["id"] + ".pdf")
            pdf_path.parent.mkdir(parents=True, exist_ok=True)
            publish_file(pdf_file, pdf_path)
            entry["pdfUrl"] = "pdf/" + volume["id"] + ".pdf"
        if not check_only:
            directory = output / entry["dataPath"]
            directory.mkdir(parents=True, exist_ok=True)
            for name, value in (("outline", outline), ("content", content)):
                (directory / (name + ".json")).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        built.append((entry, outline, content))
    if not (root / "web/index.html").is_file():
        fail("web", "missing index.html")
    if not check_only:
        # Ship manuscript/Lean downloads in their original layout, along with web assets.
        for source_root, destination_root in ((root / "web", output), (root / "volumes", output / "sources/volumes")):
            for source in sorted(source_root.rglob("*")):
                if not source.is_file():
                    continue
                if not source.resolve().is_relative_to(source_root.resolve()):
                    fail(str(source), "asset resolves outside its source directory")
                target = destination_root / source.relative_to(source_root)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
        data = output / "data"
        data.mkdir(parents=True, exist_ok=True)
        (data / "series.json").write_text(json.dumps({**series, "volumes": [x[0] for x in built]}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        (output / ".nojekyll").write_text("")
    return {
        "volumes": len(built), "chapters": sum(len(o["chapters"]) for _, o, _ in built),
        "sections": sum(len(r["sections"]) for _, o, _ in built for r in o["chapters"] + o["appendices"]),
        "appendices": sum(len(o["appendices"]) for _, o, _ in built),
        "entries_with_content": sum(len(c["chapters"]) for _, _, c in built),
        "pdfs": sum(bool(v["pdfUrl"]) for v, _, _ in built), "output": str(output),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate and render without writing output")
    parser.add_argument("--pdf", action="store_true", help="also compile the natural-language PDF editions")
    parser.add_argument("--volume", help="limit PDF compilation to a volume ID, e.g. v1a; the site includes all volumes")
    parser.add_argument("--output", type=Path, default=ROOT / "dist")
    args = parser.parse_args()
    try:
        result = build(ROOT, args.output, args.check, args.pdf, args.volume)
    except (BuildError, TexError, OSError, ValueError) as exc:
        print(f"Build failed: {exc}", file=sys.stderr)
        return 1
    print(f"{'Validated' if args.check else 'Built'} {result['volumes']} volume parts, "
          f"{result['chapters']} chapters, {result['sections']} sections, "
          f"{result['appendices']} appendices; {result['entries_with_content']} entries have content.")
    if not args.check:
        print(f"Website: {result['output']}; PDFs: {result['pdfs']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
