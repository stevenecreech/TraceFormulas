## First target: finite-dimensional trace

Section 0.1 has prose drafts for `linear-algebra.trace-cyclic`, `linear-algebra.trace-similarity`, and `linear-algebra.trace-eigenvalue-sum`. None has a checked Lean counterpart in this repository yet.

Lean and Lake launchers are installed on the author's machine, but this project has no `lean-toolchain`, Lake configuration, dependency lock, or Lean source files. Mathlib declaration availability has not been audited against a project pin.

Start with cyclicity for compatible rectangular complex matrices, including empty index sets. Search the selected Mathlib revision for an existing result before writing a proof. A library theorem over more general scalars is appropriate if its specialization to the book is recorded explicitly.

Similarity invariance should then reuse cyclicity or an existing compatible theorem. The eigenvalue-sum statement needs a separate audit of characteristic polynomials and algebraic multiplicities; proving only the diagonalizable case would not cover the book theorem.

The Compare tab records this first target and the correspondence obligations. There are no invented declaration names or admitted proof snippets. A completed record will include the exact declaration, source revision, pinned build, axiom audit, and statement review. The website itself does not perform those checks.
