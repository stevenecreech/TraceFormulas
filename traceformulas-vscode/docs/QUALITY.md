# Formalization and editorial quality

The author identified [Tau Ceti](https://taucetiproject.org/) as the formalization benchmark. Its public approach combines human-owned mathematical roadmaps with machine-checked proofs and open review. Its [review project](https://github.com/TauCetiProject/TauCetiReview) separates mechanical checks from review of mathematical meaning and library design. These sources were consulted on 2026-10-30. The criteria below are a proposed TraceFormulas adaptation, not a claim of Tau Ceti certification or an installed copy of its review system.

## Acceptance evidence for a formal result

1. **Faithful statement.** Compare every quantifier, object, hypothesis, normalization, and conclusion with the book. Expand project definitions far enough to rule out a disguised assumption of the conclusion, an empty domain, or an unintentionally trivial object. Check representative and degenerate examples.
2. **Kernel-checked proof.** Build the actual declaration in a pinned Lean version and exact dependency revisions. No `sorry`, `admit`, `sorryAx`, or unproved project axioms may occur in its dependency closure. Inspect the reported axioms; distinguish ordinary foundational axioms from added mathematical assumptions. Text searches alone do not constitute an axiom audit.
3. **Reusable mathematics.** Audit Mathlib and any proposed dependency before introducing definitions. Use compatible abstractions, useful generality, small supporting lemmas, and documented conventions. Demonstrate at least one meaningful use of new definitions or interfaces beyond restating their construction.
4. **Reproducibility.** Record source revision, toolchain, dependency lock, build command, and the actual output or durable build evidence. Website excerpts must eventually be extracted from that revision or checked against it; hand-copied code is not build evidence.
5. **Separate review.** Record statement-correspondence review separately from proof compilation, and editorial/source review separately from both. Review must actively look for missing hypotheses, circular dependencies, misleading claims of coverage, and gratuitous redefinitions. An author's self-check is not independent review.

Chapter 0's three sections now have a successful pinned build and an axiom audit of 297 logical project declarations, including generated helpers. The [dated evidence](../lean/audits/chapter00-2026-11-05-editor/record.json) identifies the exact sources and all nine locked dependencies; the [coverage inventory](../lean/audits/chapter00-2026-11-04/coverage.json) maps manuscript claims to formal declarations and records AI cross-checks separately. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited dependency closures. Steven's mathematical correspondence review remains pending. These machine checks do not constitute Tau Ceti certification or approval of video production.

## Mathlib reuse

Use the pinned Mathlib library for standard linear algebra as well as measure theory. Matrices, characteristic polynomials, algebraic multiplicities, bases, traces, L²/L∞ spaces, Lebesgue integration, and Tonelli/Fubini should retain their established mathematical meanings. Prefer targeted module imports and reuse existing theorems when their full hypotheses and conclusions match the manuscript. A specialization of a proved Mathlib theorem is legitimate formalization; redefining the desired conclusion into a project object is not.

Book-specific constructions and connecting lemmas belong in the shared project library. Record convention changes, representative choices, and any different proof route in Compare. Library reuse does not remove the obligation to inspect the actual formal statement, prove the connecting lemmas, and audit the final declaration's axiom dependencies.

## Book-specific review

Every canonical formula needs all constants, measures, summation sets, spectral terms, convergence assumptions, and regularization conventions. Alternate normalizations are derived from it. This is a reference book without exercises: give complete arguments in the exposition or in an explicitly linked proof supplement. Selected examples should illuminate a statement or convention, not stand in for a problem set.

Keep SL₂ and PSL₂ distinct, and distinguish Hecke normalization from orthonormality. Track ordinary traces, relative pairings, and weighted traces separately. A comparison between formulas must say whether it is a specialization, a derivation from a common kernel, or a theorem requiring additional information.

The Compare view is a mathematical explanation of correspondence. In particular, the Lean proof may have a different dependency order from the prose, and a tactic name is not an explanation of why the statements agree.

## Coverage vocabulary

| Track | Status sequence | Evidence required at the end |
|---|---|---|
| Prose | planned → statement-draft → proof-draft → author-reviewed | Exact text and review record |
| Sources | unchecked → checked | Source, precise location, and what was checked |
| Lean | not-audited → dependency-audited → in-progress → checked | Declaration, pinned build, dependency/axiom audit |
| Correspondence | not-reviewed → reviewed | Hypothesis and conclusion comparison at matching revisions |
| Lecture | planned → script-draft → recorded → reviewed | Recording, captions, result IDs, verified timestamps |
| Build | not-run / passed / failed / unavailable | Command, environment, outcome |

The website's existing chapter labels (`not-started`, `in-progress`, `linked`) remain navigation metadata. A source link or a successful website build cannot promote a theorem to `checked`.
