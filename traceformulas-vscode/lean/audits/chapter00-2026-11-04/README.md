Chapter 0's build and axiom audit **passed** on 2026-11-04 at 17:54:31 UTC. The audit checked **297 project declarations**, including generated and private helpers. Their transitive axiom dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`.

The coverage inventory contains **229 public declarations** across 17 shared-library and section-companion modules, with **29 entries covering all 26 labels** in the three section manuscripts. Every inventory and coverage declaration was verified to occur in the audited environment. After the audit, all **32 recorded source hashes** and both log hashes were independently recomputed and matched.

- [record.json](record.json) records the commands, exit codes, dependency revisions, source hashes, and declaration-level axiom results.
- [build.log](build.log) records the successful project build; [axioms.log](axioms.log) records the environment-wide axiom check.
- [coverage.json](coverage.json) maps manuscript claims, definitions, examples, and narrative anchors to source declarations. It records proof-route differences and identifies intermediate prose estimates that are not separately exported as project theorems.
- [negative-control.json](negative-control.json) records the gate's rejection of a deliberately added axiom in a separate scratch environment; the saved source and failure log accompany it. That axiom was never part of the project build or positive audit.

The pinned toolchain is `leanprover/lean4:v4.21.0-rc3`; Mathlib is commit `39d8416ae1e1083477f7546f1fd10e460ad37936`. All nine dependency checkouts matched their locked revisions with clean tracked sources. The exact prose, Lean, comparison, metadata, configuration, and audit-script versions are the SHA-256 snapshots in `record.json`.

Both recorded commands ran from `traceformulas-vscode/lean/` and returned exit code 0:

```sh
/Users/stevencreech/.elan/toolchains/leanprover--lean4---v4.21.0-rc3/bin/lake build
/Users/stevencreech/.elan/toolchains/leanprover--lean4---v4.21.0-rc3/bin/lake env lean Audit.lean
```

This was a build and audit in the repaired local checkout. A separate clean-checkout reproduction has **not** been performed.

**Steven's mathematical correspondence review remains pending.** The AI source cross-checks recorded in `coverage.json` are separate from that review. Machine checking does not approve the prose-to-Lean correspondence or authorize video production.
