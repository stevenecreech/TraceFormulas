# Shared Lean mathematics

Reusable definitions and lemmas live here by subject. The Chapter 0 library has compiled with the toolchain and dependency revisions recorded in the [Lean project README](../README.md). The chapter-wide build and axiom audit passed on 2026-11-04; Steven's correspondence review remains pending independently.

`LinearAlgebra/` contains matrix and endomorphism trace results, finite orthonormal operators and coefficient identities, and finite matrix measurements. `Analysis/` connects those results to actual L² operators and integrable kernels: finite-rank traces, spectral kernels, projection, representative changes, relative pairings, weighted compressed traces, counting measure, and the interval rank-one example. These modules reuse Mathlib's existing mathematical objects and standard theorems.

Book-facing modules live next to the corresponding LaTeX, for example:

```text
volumes/Volume01/A/chapters/Chapter00/sections/Section01/Formalization.lean
```

All directory components are valid Lean module identifiers. The Lake project at `traceformulas-vscode/` exposes the shared `TraceFormulas` library with `srcDir = "lean"` and `TraceFormulasBook` with `srcDir = "volumes"`; its roots include all three Chapter 0 companions. This common project root lets VS Code find the dependencies of both libraries. The layout requires no generated Lean-source copies.

A section module imports shared mathematical results and expresses the specialization used by its companion `text.tex`. It may import an earlier section module when appropriate; avoid circular imports, especially between the forms, representation, and dictionary volumes. Record changes of convention or proof route in the adjacent `compare.tex` rather than silently weakening the manuscript's target.

Run `lake build` from `traceformulas-vscode/`, or `python3 scripts/audit_lean.py` from that same directory for recorded build and axiom evidence. The dated evidence record is [chapter00-2026-11-04/record.json](../audits/chapter00-2026-11-04/record.json). File presence and website rendering do not establish proof correctness, and machine checks do not approve mathematical correspondence or video production.
