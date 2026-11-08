# Lean formalization

This pinned Lake project contains reusable mathematics and adjacent book companions. All three Chapter 0 companions and the shared modules they use have compiled. The chapter-wide build and axiom audit passed on 2026-11-04 for 297 logical declarations, including generated helpers; the evidence record is [audits/chapter00-2026-11-04/record.json](audits/chapter00-2026-11-04/record.json). Compilation and axiom evidence are separate from **Steven's pending review of mathematical correspondence**.

- Toolchain: `leanprover/lean4:v4.21.0-rc3`.
- Mathlib: `39d8416ae1e1083477f7546f1fd10e460ad37936`.
- Transitive dependency revisions: [lake-manifest.json](../lake-manifest.json).
- Shared library: [TraceFormulas/](TraceFormulas/README.md).
- Book companions: `../volumes/Volume01/A/chapters/Chapter00/sections/Section01/Formalization.lean` and the corresponding files in `Section02` and `Section03`.

The dependency environment is now populated locally at the exact locked revisions. Earlier failed import checks remain historical evidence in `audits/`; they do not describe the current working environment. No machine-specific dependency paths or package symlinks are required by the project configuration. A separate fresh-checkout reproduction has not yet been demonstrated.

The project-root fix was rebuilt and audited on 2026-11-05, again passing all 297 declarations. See the [current configuration audit](audits/chapter00-2026-11-05-editor/record.json) and [three-section editor check](audits/chapter00-2026-11-05-editor/editor-check.json). The earlier dated audit remains a record of the previous configuration.

## Building and auditing

The Lake project configuration and `lean-toolchain` live in `traceformulas-vscode/`, the common parent of `lean/` and `volumes/`. VS Code can therefore discover the same project when you open either a shared module or a section's `Formalization.lean`. After the configuration relocation, use **Cmd+Shift+P → Developer: Reload Window** once to clear the previous editor session.

With the pinned dependencies available, run from `traceformulas-vscode/`:

```sh
lake build
lake env lean lean/Audit.lean
```

`lake build` builds both `TraceFormulas` and `TraceFormulasBook`. Their source directories are `lean/` and `volumes/`, respectively. All three companions compile directly, without generated copies. Both libraries disable automatic implicit variables. Dependency checkouts and compiled files remain under `lean/.lake/`; moving the configuration does not require another copy of Mathlib.

An import such as `TraceFormulas.LinearAlgebra.MatrixTrace` names the module at `lean/TraceFormulas/LinearAlgebra/MatrixTrace.lean`. The adjacent section file imports its reusable results and states the book's specializations. Use Go to Definition on a theorem name to inspect the shared proof.

For a recorded build and audit, run from `traceformulas-vscode/`:

```sh
python3 scripts/audit_lean.py
```

Future runs write to `lean/audits/chapter00-current` by default, preserving the dated evidence above. The runner records the toolchain, locked dependency revisions, source hashes, build and audit output, and each audited declaration's axiom dependencies. `Audit.lean` inspects the actual kernel dependency closure of logical project declarations, including private proof helpers. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; an admitted proof or additional mathematical axiom fails the gate. The runner also checks that the declarations listed in section metadata were audited. Its record explicitly leaves human correspondence review unapproved. Read the recorded outcome before describing a particular source snapshot as audited.

The runner accepts `--lake /path/to/lake` when a direct executable is needed. Use the pinned toolchain, and ensure its `lean` executable is on `PATH`. A new dependency environment needs sufficient disk space and the appropriate Mathlib cache or a dependency build; keep the exact pins when preparing it. Downloading the entire Mathlib cache is not required by these commands.

## Mathematical scope and conventions

- **Section 0.1:** rectangular cyclicity, similarity invariance, basis independence of endomorphism trace, characteristic roots with algebraic multiplicity, and the concrete examples. The eigenvalue-sum theorem includes empty matrices and does not assume diagonalizability; the Jordan example proves the absence of an eigenbasis.
- **Section 0.2:** finite orthonormal coefficients and orthogonal remainders; finite-rank operators and a trace independent of the supporting subspace; kernel integrability, operator action, and diagonal trace identities; spectral specialization; representative changes and the diagonal-indicator counterexample; counting-measure kernels; and the normalized interval rank-one example.
- **Section 0.3:** integrable relative kernels and period formulas; L∞ multiplication on L², projection and compressed traces; weighted diagonal integrals; the diagonal-matrix corollaries; representative invariance; and the two-point example with its actual counting-measure interpretation.

Mathlib supplies established matrices, characteristic polynomials, finite-dimensional traces, bases, inner-product spaces, L²/L∞ spaces, measure theory, and integration theorems. Project modules supply the constructions and connecting lemmas specific to the book. Standard linear algebra is reused on the same basis as standard analysis; the project does not reprove these foundations from scratch.

Mathlib's complex inner product is linear in the second argument. `bookInner f g := inner ℂ g f` implements the manuscript's linear-first convention. L² elements are equivalence classes; pointwise integral representations of their operators are therefore stated almost everywhere. Diagonal identities use the specified finite-sum kernel representatives, and the counterexample explains why arbitrary product-null kernel changes cannot preserve diagonal integrals. Finite index types may be empty unless a concrete example fixes their size.

Each section's `compare.tex` records the exact convention changes and proof-route differences for Steven to review. In particular, the finite-rank trace comparison uses trace of compositions, and complex polynomial splitting comes from proved Mathlib results. The website displays these Lean sources but does not run Lean or certify their correspondence to the prose. No new video script or production approval follows from a successful proof build.
