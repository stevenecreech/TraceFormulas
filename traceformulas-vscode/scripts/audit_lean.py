#!/usr/bin/env python3
"""Build the Lean project and record a selected chapter's axiom audit.

This records machine evidence only. It cannot approve the correspondence with
the manuscript on Steven's behalf and never changes the manuscript or sources.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
CHAPTER_SECTIONS = {0: (1, 2, 3), 1: (1, 2, 3, 4, 5, 6, 7, 8)}
CHAPTER_APPENDIX_SECTIONS = {0: (), 1: (("A", 1), ("A", 2))}


def audited_sections(chapter: int):
    for number in CHAPTER_SECTIONS[chapter]:
        yield f"Section {number}", ROOT / f"volumes/Volume01/A/chapters/Chapter{chapter:02}/sections/Section{number:02}"
    for letter, number in CHAPTER_APPENDIX_SECTIONS[chapter]:
        yield f"Appendix {letter}.{number}", ROOT / f"volumes/Volume01/A/appendices/{letter}/sections/Section{number:02}"


def audit_file(chapter: int) -> str:
    return "Audit.lean" if chapter == 0 else "AuditChapter01.lean"


def source_hashes(chapter: int = 0) -> dict[str, str]:
    sources = list((LEAN / "TraceFormulas").rglob("*.lean"))
    sources += [LEAN / name for name in ("TraceFormulas.lean", audit_file(chapter))]
    sources += [ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    )]
    for _, section in audited_sections(chapter):
        sources += [section / name for name in (
            "text.tex", "Formalization.lean", "compare.tex", "section.json",
        )]
    sources.append(Path(__file__).resolve())
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(sources)
    }


def output(args: list[str], cwd: Path = ROOT) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def verify_lean_version(pin: str, actual: str) -> str:
    expected = re.fullmatch(r"(?:[^:\s]+:)?v(\d+\.\d+\.\d+(?:-[\w.-]+)?)", pin)
    observed = re.match(r"Lean \(version ([^,\s)]+)[,\s)]", actual)
    if not expected or not observed or expected[1] != observed[1]:
        raise RuntimeError(f"Lean version does not match {pin!r}: {actual!r}")
    return observed[1]


def verify_dependencies(manifest: dict) -> list[dict]:
    dependencies = []
    for package in manifest["packages"]:
        directory = ROOT / manifest["packagesDir"] / package["name"]
        revision = output(["git", "rev-parse", "HEAD"], directory)
        changes = output(["git", "status", "--porcelain", "--untracked-files=no"], directory)
        if revision != package["rev"] or changes:
            raise RuntimeError(f"Dependency {package['name']} differs from its locked source")
        dependencies.append({"name": package["name"], "url": package["url"],
                             "revision": revision, "tracked_source_clean": True})
    return dependencies


def forbidden_lean_modifier(source: str) -> str | None:
    """Find unsafe/partial keyword tokens outside comments and literal contents.

    This conservative source policy also rejects quoted occurrences of those
    keywords in syntax-producing code. It is independent of declaration layout
    and attribute prefixes; the Lean environment supplies the actual axiom gate.
    """
    i = 0
    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i + 2)
            i = len(source) if end < 0 else end + 1
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while depth and i < len(source):
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise RuntimeError("Unterminated Lean block comment")
        elif source[i] == "«":
            end = source.find("»", i + 1)
            if end < 0:
                raise RuntimeError("Unterminated Lean quoted identifier")
            i = end + 1
        elif (raw := re.match(r'r(#+)?"', source[i:])):
            terminator = '"' + (raw[1] or "")
            end = source.find(terminator, i + len(raw[0]))
            if end < 0:
                raise RuntimeError("Unterminated Lean raw string")
            i = end + len(terminator)
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= len(source):
                raise RuntimeError("Unterminated Lean string")
            i += 1
        elif source[i] == "'" and (char := re.match(r"'(?:\\.|[^'\\])'", source[i:])):
            i += len(char[0])
        elif source[i].isalpha() or source[i] == "_":
            end = i + 1
            while end < len(source) and (source[end].isalnum() or source[end] in "_'!?"):
                end += 1
            token = source[i:end]
            if token in {"unsafe", "partial"}:
                return token
            i = end
        else:
            i += 1
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable for the pinned toolchain")
    parser.add_argument("--chapter", type=int, choices=CHAPTER_SECTIONS, default=0,
                        help="0: all three sections; 1: implemented portions of sections 1–8 and Appendices A.1–A.2")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    destination = (args.output or LEAN / f"audits/chapter{args.chapter:02}-current").resolve()
    destination.mkdir(parents=True, exist_ok=True)
    record: dict = {
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "in-progress",
        "human_correspondence_review": "not-reviewed",
        "scope": ("Chapter 0 shared library and all three section companions" if args.chapter == 0
                  else "Implemented portions of Chapter 1 Sections 1.1–1.8, Appendices A.1–A.2 and their shared library; incomplete chapter coverage"),
        "allowed_foundational_axioms": sorted(FOUNDATIONS),
        "commands": [],
    }
    try:
        record["source_sha256"] = source_hashes(args.chapter)
        for relative in record["source_sha256"]:
            if relative.endswith(".lean"):
                modifier = forbidden_lean_modifier((ROOT / relative).read_text())
                if modifier:
                    raise RuntimeError(f"Forbidden {modifier} keyword in {relative}")
        record["toolchain_pin"] = (ROOT / "lean-toolchain").read_text().strip()
        record["lean_version"] = output([args.lake, "env", "lean", "--version"])
        record["verified_lean_version"] = verify_lean_version(
            record["toolchain_pin"], record["lean_version"])
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        record["dependencies"] = verify_dependencies(manifest)
        record["dependency_verification_stages"] = ["before-build"]
        for stage, command in (
            ("build", [args.lake, "build"]),
            ("axioms", [args.lake, "env", "lean", "lean/" + audit_file(args.chapter)]),
        ):
            print(f"Running {stage}; log: {destination / (stage + '.log')}", flush=True)
            with (destination / (stage + ".log")).open("w") as log:
                result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            record["commands"].append({"stage": stage, "argv": command,
                                       "cwd": ".", "exit_code": result.returncode})
            if result.returncode:
                raise RuntimeError(f"{stage} failed; inspect {stage}.log")
            if verify_dependencies(manifest) != record["dependencies"]:
                raise RuntimeError(f"Dependencies changed during {stage}")
            record["dependency_verification_stages"].append(f"after-{stage}")
        log_text = (destination / "axioms.log").read_text()
        reports = [json.loads(line.split("AXIOM_AUDIT_JSON ", 1)[1])
                   for line in log_text.splitlines() if "AXIOM_AUDIT_JSON " in line]
        counts = re.findall(r"AXIOM_AUDIT_CHECKED (\d+)", log_text)
        if len(counts) != 1 or int(counts[0]) != len(reports) or not reports:
            raise RuntimeError("Missing or inconsistent axiom-audit output")
        for report in reports:
            if set(report["axioms"]) - FOUNDATIONS:
                raise RuntimeError(f"Unexpected axiom in {report['declaration']}")
        audited_names = {report["declaration"] for report in reports}
        for label, section in audited_sections(args.chapter):
            metadata = json.loads((section / "section.json").read_text())
            declared = metadata["formal"]["declarations"]
            if not declared or set(declared) - audited_names:
                raise RuntimeError(f"{label} metadata has empty or unaudited declarations")
        record["declarations"] = sorted(reports, key=lambda item: item["declaration"])
        record["audited_declaration_count"] = len(reports)
        if source_hashes(args.chapter) != record["source_sha256"]:
            raise RuntimeError("A source changed during the audit; rerun against the final snapshot")
        record["status"] = "passed"
        print(f"Build and axiom checks passed for {len(reports)} declarations, including generated helpers.")
        print("Steven's mathematical correspondence review remains pending.")
    except (OSError, RuntimeError, subprocess.CalledProcessError, ValueError) as error:
        record["status"] = "failed"
        record["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        record["finished_at_utc"] = datetime.now(timezone.utc).isoformat()
        for name in ("build.log", "axioms.log"):
            path = destination / name
            if path.exists():
                record.setdefault("log_sha256", {})[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        (destination / "record.json").write_text(json.dumps(record, indent=2) + "\n")
    return 0 if record["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
