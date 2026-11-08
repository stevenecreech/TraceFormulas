# Trace Formulas: series, library, and lectures

The aim is a definitive, graduate-accessible reference on trace formulas, accompanied by a reusable Lean library and chapter lectures. The website presents the natural-language argument, formal source, correspondence, videos, and dependencies. A PDF presents the natural-language book from the same LaTeX sources.

## Series architecture

| Volume | Setting | Part a | Part b | Part c |
|---|---|---|---|---|
| 1 | SL₂(ℤ) | Automorphic forms | Automorphic representations | Dictionary |
| 2 | Congruence subgroups of SL₂(ℤ), including nebentypus | Automorphic forms | Automorphic representations | Dictionary |
| 3 | Half-integral weight | Automorphic forms | Automorphic representations | Dictionary |
| 4 | Quaternionic forms | Automorphic forms | Automorphic representations | Dictionary |

This structure follows the author's clarified request of 2026-10-30. `series.json` is the catalog; each part has its own outline in `volumes/VolumeNN/A`, `B`, or `C`. Volume 1a's outline reflects the author's revisions: Chapter 0 has three reference sections, and Appendix H contains supplementary proofs rather than exercise solutions. Other parts are planned, without invented chapters.

Volume 1a's first substantial mathematical milestone remains Chapters 0–7, ending with Petersson. Its advanced endpoints still require precise formulations and source audits. This is a reference book without exercises. Chapter 0 establishes elementary trace and kernel identities; the named automorphic formulas belong in their own chapters. The handoff is background planning material; its embedded prompts were not installed as repository instructions.

## Sources and correspondence

Each section has `text.tex` next to its optional `Formalization.lean`, `compare.tex`, `lecture.tex`, and `section.json`. Read and the PDF use the manuscript; Compare uses that same manuscript and the actual Lean source, rather than duplicated theorem strings. `compare.tex` explains hypotheses, objects, normalizations, and proof differences.

Lean section modules follow the book's volume/chapter/section organization. Shared mathematical infrastructure belongs under `lean/TraceFormulas/` by subject. A book-facing module imports reusable definitions and proves or exposes the exact specialization used in the prose. The Lake configuration is at the common parent `traceformulas-vscode/`, so VS Code discovers it from both source trees. It pins Lean `4.21.0-rc3`, Mathlib `39d8416ae1e1083477f7546f1fd10e460ad37936`, and the transitive revisions in `lake-manifest.json`.

All three Chapter 0 companions and their shared mathematics have compiled. Section 0.1 covers rectangular cyclicity, similarity, basis independence, the trace as a sum of characteristic roots with algebraic multiplicity, and the concrete matrix examples. Section 0.2 covers finite orthonormal decompositions, actual finite-rank operator traces, integrable L² kernels, representative changes and their diagonal limitation, spectral kernels, counting measure, and the interval rank-one example. Section 0.3 covers relative kernel integrability and period identities, bounded multiplication and weighted compressed traces, both diagonal specializations, and the two-point example. These constructions reuse Mathlib's established matrices, characteristic polynomials, linear maps, L²/L∞ spaces, and integration theory.

The chapter-wide build and axiom audit passed on 2026-11-04. The [dated evidence record](../lean/audits/chapter00-2026-11-04/record.json) records the outcome, audited declarations, and source hashes; it is separate from Steven's pending mathematical correspondence review. See the [Lean README](../lean/README.md) for build and audit commands. No new video is approved by this compilation milestone.

The original Markdown manuscript is preserved under `archive/2026-10-30-markdown/`. Live manuscript authoring now happens only under `volumes/`. Documentation can remain Markdown.

## Supporting appendices

Develop appendices as supporting subjects arise during chapter work. Special integrals, special-function identities, transform calculations, and analytic prerequisites are natural candidates. Extend an existing appendix when its scope fits; add a focused appendix when a distinct subject needs its own treatment. The current outline already provides Analytic Foundations, Special Functions, Integral Transforms, and Supplementary Proofs.

The main chapter states the result it needs, including the relevant hypotheses and normalization, and links to the appendix derivation. For an integral identity, record the parameter domain, convergence conditions, branch conventions where relevant, and a complete proof. Keep appendix dependencies independent of the later formulas that use them. Appendix sections follow the same LaTeX/Lean layout, formalization standards, and Steven correspondence-review process as chapter sections, with shared lemmas available for reuse.

Each volume part also maintains a notational index as its manuscript grows. Volume 1a's Appendix I lists the symbols currently used in Chapter 0, their meanings and conventions, and links to the defining passages. The same LaTeX supplies the printed and website index. Update entries with the prose, including scope distinctions for overloaded symbols; the normalization dictionary remains the place for derivations comparing conventions.

## A completed mathematical unit

Follow [Steven's chapter workflow](WORKFLOW.md): full AI prose draft, collaborative human editing with concurrent formalization, Steven's explicit correspondence review, then visual scripting and video creation. The human-edited prose is the formalization roadmap. The review and production stages must remain distinct.

Each result needs an exact statement, a complete prose proof, explicit conventions, meaningful examples where useful, a stable result ID, a source record, and reviewed correspondence to its Lean declaration. Compilation and statement review are distinct requirements. Essential arguments belong in the exposition or a linked proof supplement.

After Steven's correspondence review, each chapter should ultimately have a conceptual lecture and proof walkthrough, with formalization tours where useful. Scripts, recordings, captions, and reviewed timestamps have separate statuses. A planned video never receives a fabricated URL or claimed recording.

## Immediate sequence

1. Review the full Chapter 0 prose draft with Steven, using the modular LaTeX/Lean/PDF/website pipeline.
2. During subsequent editing rounds, update affected formalizations and comparisons and rerun the build and axiom audit against the exact saved prose and Lean sources. Keep the dated evidence for earlier snapshots.
3. Present the compiled declarations, audit evidence, and correspondence notes for Steven's review; develop the chapter video after that review.
4. Develop Chapters 1–7 by the same workflow and mathematical dependency, reviewing analytic justifications and constants before release.

See [QUALITY.md](QUALITY.md) for acceptance criteria and [STATUS.md](STATUS.md) for observed evidence. The infrastructure supports the series; it does not imply the volumes or formalizations are complete.
