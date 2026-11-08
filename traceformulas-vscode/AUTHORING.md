# Authoring the series

The manuscript has one editable source: LaTeX. The website renders that source with Pandoc and MathJax; the print build includes it directly with `pdflatex`. Lean companions are ordinary source files, displayed verbatim by the website.

## Volumes and outlines

`series.json` registers each volume part. Volume 1 concerns SL₂(ℤ), Volume 2 congruence subgroups with nebentypus, Volume 3 half-integral weight, and Volume 4 quaternionic forms. Parts A, B, and C respectively develop automorphic forms, automorphic representations, and their dictionary.

Each part has a separate directory, such as `volumes/Volume02/B/`, with its own `outline.json`. Only Volume 1a currently has a chapter outline. Populate a planned volume's outline when its mathematical scope is ready; the website already knows how to open it.

An outline retains the original schema: title, subtitle, volume label, author, source, divisions, chapters, appendices, and reading routes. Every chapter, appendix, and section ID must start with its volume ID, such as `v2b-ch00` or `v1a-ch00-s1`. Preserve IDs when renaming titles. Directory numbers follow chapter numbers and section positions, so move the entire section directory when reordering it.

IDs are stable keys, not printed numbers: after removal of the introductory survey and finite Fourier section, the final section keeps `v1a-ch00-s5`, lives in `Section03`, and displays as Section 0.3. The retired IDs `v1a-ch00-s3` and `v1a-ch00-s4` are not reused.

## A chapter and its sections

```text
volumes/Volume01/A/
  outline.json
  chapters/Chapter00/
    chapter.json
    intro.tex
    formalization.tex
    lecture.tex          # Chapter video narration and storyboard
    sections/Section01/
      text.tex
      Formalization.lean   # Optional until formalization work starts
      section.json         # Optional; defaults to no media and not-started
      compare.tex          # Optional; commentary, not a second theorem statement
      lecture.tex          # Optional focused section video, when explicitly planned
  appendices/A/
    chapter.json
    intro.tex
    formalization.tex
```

Appendices may acquire `sections/Section01/` etc. by adding sections to their outline records. Empty manuscript files render as material in preparation. Do not fill every section with empty Lean theorem stubs.

Volume 1a's notational index is maintained in `volumes/Volume01/A/appendices/I/intro.tex`. Add entries as notation is introduced, with a symbol, its meaning and relevant conventions, and a named hyperlink to the defining heading. Group entries by mathematical context and distinguish reused symbols. This is an authored index of the manuscript, not automatic symbol extraction. Its `longtable` tables can break across PDF pages and render as ordinary tables on the website.

Use heading labels of the form `v1a-notation-topic` (with the appropriate volume prefix) for index groups. The website keeps the final reference column of the following table on one line, so section numbers remain readable on narrow screens.

The source paths are valid Lean module components. See [lean/TraceFormulas/README.md](lean/TraceFormulas/README.md) for the intended shared-library and section-module roots. No generated copy of a Lean file is needed for imports or website display.

## LaTeX writing

Write fragments without `\documentclass` or `\begin{document}`. The outline supplies chapter and section headings. Use `$...$` for inline mathematics and `\[...\]` for displays. Chapter 0 has continuous exposition within its three sections, with examples woven in and no subsection headings. Elsewhere, use `\subsection{...}` only when a broader topic needs a heading within a section.

```tex
\subsection{The upper half-plane}
Write $z=x+iy$, with $y>0$.
\[
  \HH=\{x+iy:y>0\}.
\]
The condition $y>0$ puts $z$ above the real axis.
```

Put shared semantic commands in `tex/macros.tex`, which both builds read. Put print-only package and page-layout choices in `tex/preamble.tex`. Ordinary prose, emphasis, lists, mathematical expressions, AMS-style theorem/proof environments, and semantic macros have a Pandoc rendering path. The converter rejects unhandled raw TeX or conversion warnings rather than silently dropping content.

Write transpose as `$A^{\mathsf{T}}$`, with an upright sans-serif `T`. Use the same form for row vectors, for example `$(1,1)^{\mathsf{T}}$`. It means ordinary transpose, without complex conjugation. Keep this convention consistent in manuscripts, comparison notes, and lecture scripts; it is recorded in Volume 1a's notational index.

Give every inner product and norm an ambient-space subscript. For example, write `$\langle f,g\rangle_{L^2(X,\mu)}$` and `$\|f\|_{L^2(X,\mu)}$`. Define the measure and scalar field at first use. Preserve the book's convention that complex inner products are linear in their first argument, and update notation-index entries when a space or measure changes.

Pandoc does not execute arbitrary TeX packages. Bibliography processing, automatic numbered reference commands, TikZ, and custom environments need explicit tested integration before relying on them for a release. The supported theorem environments below have matching numbering in the full PDF and manuscript views on the website. Use stable result IDs for correspondence. LaTeX PDF compilation checks ordinary unresolved references and citations.

### Definitions, statements, and proofs

Use AMS environments for mathematical statements and proofs. The shared macros provide `definition`, `proposition`, `theorem`, `lemma`, `corollary`, `example`, and `remark`, together with the standard `proof` environment.

```tex
\begin{proposition}[Cyclicity for two factors]\label{linear-algebra.trace-cyclic}
For compatible rectangular complex matrices $A$ and $B$,
\[
  \operatorname{tr}(AB)=\operatorname{tr}(BA).
\]
\end{proposition}

\begin{proof}
Expand the two traces and interchange the finite sums.
\end{proof}
```

Place each statement's label immediately after `\begin{...}[Title]`, before any displayed mathematics. Existing semantic labels stay with their statements when formatting changes. The website preserves these labels as link destinations, including in Compare and from the notational index.

Numbered environments share one counter within each section: for example, Definition 0.1.1 followed by Proposition 0.1.2. The print build supplies chapter and section numbering; the website uses the corresponding outline position, including appendix letters. Definitions and examples use upright text, theorem statements use the plain italic style, remarks use the remark style, and proofs are unnumbered with a closing square. Avoid manual counter changes in manuscript fragments.

Short names `defn`, `prop`, `thm`, `lem`, `cor`, and `rem` are also available and share the same counter. Use `defn` rather than `def`, which conflicts with TeX's primitive `\def`. Chapter 0 uses the full names for readability.

### Hyperlinks between chapters

Separate source files do not prevent links. The full-volume PDF includes all chapters in one LaTeX document, with `hyperref` loaded. The website resolves named manuscript links across chapters in the same volume.

Chapter and section labels come from the outline automatically. For example, this can appear in Chapter 10:

```tex
See \hyperref[v1a-ch08]{Chapter 8}, especially
\hyperref[v1a-ch08-s4]{the construction of Hecke kernels}.
```

For a specific result, attach a unique semantic label to its theorem environment and use a descriptive link:

```tex
\begin{proposition}[A kernel identity]\label{v1a-hecke-kernel-identity}
% Statement goes here.
\end{proposition}
\begin{proof}
% Proof goes here.
\end{proof}

% Elsewhere in the same volume:
By \hyperref[v1a-hecke-kernel-identity]{the kernel identity}, ...
```

For a passage without a heading or theorem environment, place an invisible anchor just before it:

```tex
\phantomsection\label{finite-kernel-model}

Let $(X,\mu)$ be a sigma-finite measure space.
```

Use the complete `\phantomsection\label{...}` pair. A bare label in prose is unsupported by the website; inside a numbered theorem environment, use the ordinary opening label instead. These anchors preserve links when removing a subsection heading without introducing a visible replacement.

These named links are clickable in both the full PDF and Read/Compare on the website; the website opens the destination chapter and scrolls to the section, heading, theorem block, or prose anchor. Missing or ambiguous manuscript targets fail the build. Keep labels unique within a volume. The link text is authored text, so update it if a chapter is renumbered, or use a descriptive name.

Automatic numbered `\ref`/`\eqref` references work in the PDF engine but are not yet supported by the shared website converter; use the named form above for now. Equation labels still need further converter integration. Manuscript previews build the containing volume so that cross-section and cross-chapter links resolve. Standalone companion previews do not import manuscript references, and links across separately compiled volume PDFs need additional support.

Documentation remains Markdown; the preserved archive remains Markdown. Neither is read as the live book manuscript.

### Shared acknowledgments

`volumes/acknowledgments.tex` contains the series-wide support statement and disclaimer, including NSF Award DMS-2602321. The PDF assembler includes this fragment on an unnumbered Acknowledgments page after the title page, with a contents entry. The website renders the same source on each volume's About page; its footer links directly to that section. This file is also included among the downloadable sources. Keep the repository-root README's acknowledgment synchronized when revising it. The source is optional for other uses of the build tools; when absent or empty, both editions omit the acknowledgment.

## How the website is populated

| Reader view | Source |
|---|---|
| Read | Chapter `intro.tex` and each section's `text.tex` |
| Watch | Chapter/section video metadata, with a `.tex` script or transcript |
| Formalization | Chapter `formalization.tex` plus each actual `Formalization.lean` |
| Compare | The same `text.tex` used by Read, beside the exact adjacent `Formalization.lean`; optional `compare.tex` notes |
| Map | Chapter and section prerequisites in `chapter.json` |

A comparison appears when a section has prose or Lean source. Missing Lean source is explicitly indicated. Download links serve the original `.tex` and `.lean` files. The chapter metadata no longer accepts a manually copied `comparisons` array.

`chapter.json` supports `videos`, `resources`, `exercises`, `explorations`, `formal`, `prerequisites`, and `sectionPrerequisites`. Section metadata supports `videos` and `formal`:

```json
{
  "formal": {
    "status": "not-started",
    "declarations": []
  },
  "videos": [
    {
      "title": "Two ways to see a trace (unrecorded script)",
      "kind": "proof",
      "url": "",
      "transcriptFile": "lecture.tex"
    }
  ]
}
```

Video kinds are `concept`, `proof`, and `formalization`. By default, plan one video per chapter and keep its narration and storyboard in the chapter's `lecture.tex`, referenced by `chapter.json`. Split a longer chapter into several videos when the pacing warrants it; each may have its own script file and chapter-level video entry. Use section-level video entries only for separately planned section recordings. When a recording exists, add its complete HTTP(S) URL. The script/transcript file path is relative to the JSON file's directory and must stay inside it. Chapter-level videos and section-level videos are combined in Watch.

Chapter 0's current script is `volumes/Volume01/A/chapters/Chapter00/lecture.tex`. It has fifteen scenes, with spoken narration, visual directions, and estimated durations; it is available in Watch as an unrecorded draft. Its estimates are not measured video timestamps. The former Section 0.1 draft is preserved in `archive/2026-11-05-chapter00-lecture/`.

The formal statuses are `not-started`, `in-progress`, and `linked`. A file's existence or a linked source does not certify a proof. Use the separate evidence ledger described in [QUALITY.md](docs/QUALITY.md). A section cannot list declarations or claim progress without its Lean source file.

Resources have `title` and `url`; exploration fields are `title`, `url`, and `description`. Inline metadata strings are plain text, not Markdown or TeX; use files for mathematical prose. Prose fields support `.tex` alternatives such as `descriptionFile`. Exercise metadata (`title`, `question`, `hint`, `solution`, and corresponding file fields) remains supported for compatibility, but this series is a reference book without exercises: leave exercise lists empty and the `exercises` flag in `site.json` false. Use complete proofs and selected explanatory examples in the manuscript.

Prerequisite arrays contain IDs from that volume's outline. `sectionPrerequisites` maps a section ID to prerequisite IDs. These are authored reading relationships, not dependency edges extracted from Lean. Cross-volume dependency links are not implemented yet.

## PDF and validation

For the normal writing loop, open `.build/v1a/main.pdf` with **LaTeX Workshop Internal PDF Viewer**, arrange it beside `text.tex`, and press **Cmd+Shift+B** after editing. The default **Build book** task saves files and rebuilds the full Volume 1a PDF and website from any active tab. The PDF viewer watches the stable output path and refreshes it. No preliminary section build or tab switch to `main.tex` is required.

PDF compilation happens in `.build/v1a/.compile/`. The last complete PDF stays available until a successful build replaces it; failed compilation leaves it intact. The published PDF under `dist/pdf/` is also replaced only when complete. Native automatic LaTeX Workshop builds are disabled to avoid competing compiler processes.

Select a `.tex` file and run **Terminal → Run Task → Preview active LaTeX file**. For a manuscript introduction or section registered in an outline, this builds the containing volume and website, reporting `.build/<volume-id>/main.pdf`; the full context preserves hyperlinks and numbering. For `lecture.tex` and other companions, it compiles that selected fragment separately, with the wrapper and PDF beneath `.build/previews/`. Select the chapter-level `lecture.tex` tab when compiling its video script. Save changes before running the task.

Run these commands from the package directory:

```bash
python3 scripts/build.py --check
python3 -m unittest discover -s tests -v
python3 scripts/build.py --pdf --volume v1a
```

The PDF build generates `.build/v1a/main.tex` in outline order and includes only chapter introductions and section manuscript files. Lean source, correspondence notes, and lecture scripts remain website material. Chapter 0 and appendices retain their numbering; unwritten sections are visibly labeled. The PDF runs twice for contents and references. Do not edit `.build/` or `dist/`.

The `--volume` flag selects the PDF part, while all parts remain available on the website. A website-only build does not advertise an old PDF as current; rebuild with `--pdf` when preparing a complete artifact. Open the printed edition and representative website sections as part of editorial review. Neither converter checks the mathematics.
