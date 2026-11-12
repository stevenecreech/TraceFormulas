# Trace Formulas

A multimedia reference book series by **Steven Creech**, bringing together mathematical exposition, Lean formalizations, and visual explanations of trace formulas.

The project aims to develop a comprehensive treatment through three connected perspectives: classical automorphic forms, automorphic representations, and the dictionary between them. The natural-language book is written in LaTeX and builds as a PDF. A companion website presents the same manuscript alongside its Lean sources, correspondence notes, and chapter video scripts or recordings as they become available.

## The series

| Volume | Setting |
|---|---|
| 1 | The modular group SL₂(ℤ) |
| 2 | Congruence subgroups of SL₂(ℤ), including nebentypus |
| 3 | Half-integral weight |
| 4 | Quaternionic forms |

Each volume has three parts: **A — Automorphic forms**, **B — Automorphic representations**, and **C — The dictionary**. This is a reference work with definitions, complete arguments, worked examples, supporting appendices, and a notational index. It has no exercise sets.

## Current state

The series is under development. Volume 1a has an outline of 31 chapters and nine appendices; most chapters remain unwritten. The other eleven volume parts have planned destinations.

Chapter 0 develops matrix traces, finite-rank integral kernels, relative pairings, and weighted diagonal traces across three sections. Its manuscript and Lean companions are available, together with a full chapter video script. The script is a draft; no recording has been produced.

All three Chapter 0 companions and their shared Lean mathematics passed the recorded build and axiom audit on November 5, 2026. Formalization reuses Mathlib's linear algebra and measure theory. **Machine verification and Steven's review of the prose–Lean correspondence are separate:** that human correspondence review remains pending. See the [audit evidence](traceformulas-vscode/lean/audits/chapter00-2026-11-05-editor/record.json), [quality criteria](traceformulas-vscode/docs/QUALITY.md), and [project status](traceformulas-vscode/docs/STATUS.md).

Chapter 1 has an edited prose draft covering the upper half-plane, Iwasawa decomposition, hyperbolic geometry, and the modular arithmetic lattice, with explicit SL₂/PSL₂ measure conventions. Partial Lean companions for Sections 1.1–1.8 and Appendices A.1–A.2 accompany that work, with explicit coverage gaps in Compare. The measure-theory refresher and general Haar proofs are collected in Appendix A.

Useful starting points:

- [Chapter 0 introduction](traceformulas-vscode/volumes/Volume01/A/chapters/Chapter00/intro.tex) and [first section](traceformulas-vscode/volumes/Volume01/A/chapters/Chapter00/sections/Section01/text.tex).
- [Chapter 1 introduction](traceformulas-vscode/volumes/Volume01/A/chapters/Chapter01/intro.tex) and [first section](traceformulas-vscode/volumes/Volume01/A/chapters/Chapter01/sections/Section01/text.tex).
- [Chapter 0 visual lecture script](traceformulas-vscode/volumes/Volume01/A/chapters/Chapter00/lecture.tex).
- [Shared Lean library and build instructions](traceformulas-vscode/lean/README.md).
- [Detailed setup guide](traceformulas-vscode/README.md) and [authoring guide](traceformulas-vscode/AUTHORING.md).

## Build the book and website

Run these commands from the repository root. You need Python 3.10 or newer. Building the PDF also requires a TeX distribution providing `pdflatex` and the packages listed in the [setup guide](traceformulas-vscode/README.md).

```sh
cd traceformulas-vscode
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
python3 scripts/build.py --pdf --volume v1a
python3 -m http.server 8000 --directory dist --bind 127.0.0.1
```

Open <http://127.0.0.1:8000/> to browse the local website. The generated PDF is `traceformulas-vscode/dist/pdf/v1a.pdf`, also available from the volume overview. The website has **Read**, **Watch**, **Formalization**, **Compare**, and **Map** views. It displays Lean source; Lean checking runs separately.

To build only the website, omit `--pdf --volume v1a`. Generated files live in `dist/` and `.build/`; edit the sources under `volumes/` instead. The website publishes to GitHub Pages at <https://stevenecreech.github.io/TraceFormulas/> on every push to `main` via [`.github/workflows/pages.yml`](.github/workflows/pages.yml); see [Publishing](traceformulas-vscode/README.md#publishing).

In VS Code, **Cmd+Shift+B** builds Volume 1a and the website. Keep `.build/v1a/main.pdf` open in LaTeX Workshop's PDF viewer. For the video script, select the chapter's `lecture.tex` and run **Tasks: Run Task → Preview active LaTeX file**. Selecting a manuscript file with that task builds its containing volume so hyperlinks and numbering resolve.

## Check the Lean formalizations

Install Lean's `elan` toolchain manager and use the pinned toolchain and dependency versions in the project. From `traceformulas-vscode/`:

```sh
lake build
python3 scripts/audit_lean.py
```

The [Lean guide](traceformulas-vscode/lean/README.md) explains dependencies, the axiom audit, and mathematical conventions. The project aims for faithful, reusable formalizations with no admitted proofs or unproved project axioms. A successful build does not establish that a formal statement expresses the intended prose; that correspondence is reviewed explicitly.

## Source organization and collaboration

All implementation and book sources live under `traceformulas-vscode/`:

| Path | Contents |
|---|---|
| `volumes/VolumeNN/A`, `B`, `C` | Part outlines, chapter introductions, and section manuscripts |
| `…/sections/SectionNN/text.tex` | Natural-language section, shared by the PDF and website |
| `…/sections/SectionNN/Formalization.lean` | Corresponding Lean source |
| `…/sections/SectionNN/compare.tex` | Correspondence notes and differences to review |
| `…/chapters/ChapterNN/lecture.tex` | Chapter video narration and storyboard |
| `lean/TraceFormulas/` | Reusable mathematical library |
| `web/`, `scripts/`, `tex/` | Website interface, build tools, and shared LaTeX support |
| `docs/` | Workflow, quality criteria, plans, and status records |

The [chapter workflow](traceformulas-vscode/docs/WORKFLOW.md) proceeds from a complete prose draft through collaborative editing and formalization, then human correspondence review and video production. Mathematical corrections and proposed contributions should identify the affected volume, section, and statement. Preserve semantic labels and explain any changes to hypotheses, definitions, or proof routes. Repository collaboration instructions are in [AGENTS.md](AGENTS.md).

## Acknowledgments

This material is based upon work supported by the National Science Foundation under Award No. DMS-2602321.

Any opinions, findings and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.

The [shared acknowledgment source](traceformulas-vscode/volumes/acknowledgments.tex) supplies the PDF front matter and the website's About page.
