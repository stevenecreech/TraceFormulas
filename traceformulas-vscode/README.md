# Trace Formulas

A multimedia book series authored in **LaTeX and Lean**, with a natural-language PDF edition and a website containing Read, Watch, Formalization, Compare, and Map.

The collaboration process is recorded in [Steven's chapter workflow](docs/WORKFLOW.md): draft the chapter, edit its prose while formalizing, review the correspondence with Steven, then create the visual script and video.

| Volume | Setting | a | b | c |
|---|---|---|---|---|
| 1 | SL₂(ℤ) | Automorphic forms | Automorphic representations | Dictionary |
| 2 | Congruence subgroups of SL₂(ℤ), including nebentypus | Automorphic forms | Automorphic representations | Dictionary |
| 3 | Half-integral weight | Automorphic forms | Automorphic representations | Dictionary |
| 4 | Quaternionic forms | Automorphic forms | Automorphic representations | Dictionary |

Volume 1a has **31 chapters (0–30), 153 sections, and nine appendices (A–I)**, including a [notational index](volumes/Volume01/A/appendices/I/intro.tex) with links to definitions. Chapter 0 is a compact reference introduction; individual trace formulas are developed in their own chapters. The series has no exercises. The other eleven parts have registered destinations and empty outlines, clearly marked as planned.

## Work on one section

Chapter 0 now has a revised prose draft in `intro.tex` and three section `text.tex` files. A section's companions live beside its manuscript; for example:

```text
volumes/Volume01/A/chapters/Chapter00/sections/Section01/
  text.tex             # Natural-language manuscript: PDF + website
  Formalization.lean   # Actual companion Lean source: Formalization + Compare
  compare.tex          # Explanation of correspondence and remaining obligations
  lecture.tex          # Pointer to the current chapter-level script
  section.json         # Formalization status, declaration names, video metadata
```

Edit `text.tex` and `Formalization.lean` together. Compare reads those exact files; there are no separately maintained theorem excerpts. Other sections already have `text.tex`; add the optional companions when work begins. All three Chapter 0 companions and their shared mathematics have compiled in the [pinned Lean project](lean/README.md): matrix and endomorphism traces, finite-rank L² kernel identities, and relative and weighted kernel identities, including the chapter's examples. They reuse Mathlib's linear algebra and measure theory. The chapter-wide build and axiom audit passed on 2026-11-04; its evidence record is [chapter00-2026-11-04/record.json](lean/audits/chapter00-2026-11-04/record.json). Steven's review of the prose–Lean correspondence remains pending, and no new video has been approved.

Videos cover a whole chapter by default, with multiple videos when length warrants it. The [Chapter 0 script](volumes/Volume01/A/chapters/Chapter00/lecture.tex), **What does a trace measure?**, contains fifteen scenes with narration, equations, and animation directions. Its provisional running time is 35–40 minutes, with optional breaks into three parts. The chapter's Watch tab displays this unrecorded draft; `chapter.json` points to the script. The earlier Section 0.1 script is preserved in `archive/2026-11-05-chapter00-lecture/`. Use **Preview active LaTeX file** to compile the script separately; it is not included in the manuscript PDF.

## Install build dependencies

For Lean editing, open a section's `Formalization.lean` in VS Code with the Lean 4 extension. The project configuration (`lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`) is at `traceformulas-vscode/`, above both `lean/` and `volumes/`. An import such as `TraceFormulas.LinearAlgebra.MatrixTrace` loads [the shared matrix-trace module](lean/TraceFormulas/LinearAlgebra/MatrixTrace.lean). Run `lake build` from `traceformulas-vscode/` to build all current formalizations. After the project-root fix, use **Cmd+Shift+P → Developer: Reload Window** once so VS Code discovers the new root.

From `traceformulas-vscode/`:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
```

The pinned package supplies Pandoc 3.9. The builder finds the project-local binary automatically. An external Pandoc can be selected with `PANDOC`; use the pinned version for reproducible output. For PDF compilation, also install a TeX distribution providing `pdflatex`, Latin Modern, AMS packages, geometry, microtype, and hyperref (for example MacTeX or TeX Live).

## Build and preview

In VS Code, keep the book PDF open beside `text.tex` and press **Cmd+Shift+B** after editing. The default **Build book** task saves your files and rebuilds Volume 1a and the website, regardless of the active tab. You do not need to switch to `main.tex` or run a section preview first.

Open `.build/v1a/main.pdf` once with **LaTeX Workshop Internal PDF Viewer** and keep it beside the source. Workspace settings select that viewer, whose file watcher refreshes the open PDF. The build compiles into a staging directory and replaces the PDF only after success; an unsuccessful build retains the last good PDF. Automatic LaTeX Workshop builds are disabled here to avoid a second compiler writing the same files alongside the task.

For a lecture preview, select its `lecture.tex` tab, save, and use **Terminal → Run Task → Preview active LaTeX file**. The script PDF is written under `.build/previews/`. When the active file is a manuscript `text.tex` or `intro.tex` included in an outline, the same task builds its containing volume and website, preserving cross-section hyperlinks and theorem numbering; open `.build/<volume-id>/main.pdf`. The terminal reports the resulting PDF path. Both task sets are available whether you open the enclosing repository or the package folder.

```bash
python3 scripts/build.py --check
python3 scripts/build.py --pdf --volume v1a
python3 -m http.server 8000 --directory dist --bind 127.0.0.1
```

Open <http://127.0.0.1:8000/> for the series, or <http://127.0.0.1:8000/?volume=v1a#/chapter/v1a-ch00/compare/v1a-ch00-s1> for the first comparison. The PDF is `dist/pdf/v1a.pdf` and appears as a download on the volume overview.

Without `--pdf`, the command builds the website only and does not advertise a PDF download. `--volume` limits PDF compilation; the website always includes the whole catalog. `--check` renders and validates without writing generated output. Rebuild after editing, then refresh the browser.

## Source and output

| Path | Purpose |
|---|---|
| `series.json` | Volume settings, a/b/c perspectives, paths, and draft/planned statuses |
| `site.json` | Optional features and repository URL |
| `volumes/Volume01/A/outline.json` | Volume 1a chapter titles, stable IDs, ordering, and reading routes |
| `volumes/VolumeNN/A`, `B`, `C` | Each volume part's own outline and manuscript |
| `volumes/acknowledgments.tex` | Shared NSF acknowledgment for the PDF front matter and website About page |
| `lean/TraceFormulas/` | Shared reusable Lean mathematics; see its layout notes |
| `tex/macros.tex` | Semantic macros shared by PDF and web rendering |
| `tex/preamble.tex` | Print packages and layout |
| `web/` | Browser interface and assets |
| `scripts/` | Source validation, LaTeX rendering, PDF assembly |
| `.build/v1a/` | Generated `main.tex`, TeX logs, and intermediate PDF |
| `dist/` | Generated website, downloadable sources, and requested PDFs |
| `archive/2026-10-30-markdown/` | Preserved original manuscript; archival, not an authoring source |

Run `python3 -m unittest discover -s tests -v` for source-pipeline regression tests. For optional browser QA, install `requirements-dev.txt`, then run `.venv/bin/python scripts/check_browser.py --chrome /path/to/chrome`; this uses a temporary profile and local server, and closes both afterward. See [AUTHORING.md](AUTHORING.md), the [project plan](docs/PROJECT.md), [quality criteria](docs/QUALITY.md), and [status record](docs/STATUS.md).

## Publishing

The supplied `.github/workflows/pages.yml` installs the converter and TeX packages, runs the pipeline tests, builds the website and PDF, and uploads `dist/`. For a standalone repository, keep this package at its root. For the current enclosing TraceFormulas repository, GitHub discovers workflows only in the repository-root `.github/workflows/`: move/integrate the workflow there, run its Python steps with `working-directory: traceformulas-vscode`, point its dependency install at that directory, and upload `traceformulas-vscode/dist`. No remote publication is configured by this migration.

All site assets and generated data use relative paths, so the site can be hosted under a subdirectory. Mathematical display currently loads MathJax from the configured CDN. The website displays Lean source; it does not execute Lean or certify proof correctness. The supported LaTeX scope and current rendering limitations are documented in [AUTHORING.md](AUTHORING.md).
