The project configuration now lives at `traceformulas-vscode/`, above both the shared Lean library and the manuscript companions. This fixes VS Code's upward project discovery for `volumes/.../Formalization.lean`.

The build and axiom audit passed for **297 logical declarations**, with only `propext`, `Classical.choice`, and `Quot.sound`. All mathematical source files match the November 4 snapshot. All nine dependency pins are unchanged, and the existing dependency checkouts and build cache were reused.

- [record.json](record.json) records the new configuration, exact source hashes, pinned dependencies, and successful commands. Commands now run from `traceformulas-vscode/`.
- [build.log](build.log) and [axioms.log](axioms.log) retain the actual build and axiom output.
- [editor-check.json](editor-check.json) records finished language-server elaboration with no error diagnostics for all three section companions, plus resolved theorem hover responses. The editor client used `lake serve` at the new root; it did not control Steven's running VS Code window.
- [lsp-client.py.txt](lsp-client.py.txt) preserves the probe source. It originally ran at `.build/lean-editor-fix/check_lsp.py` under the project root; its path computation assumes that location. The server's stderr is in [lsp-stderr.log](lsp-stderr.log).
- The unchanged mathematics uses the previous [coverage inventory](../chapter00-2026-11-04/coverage.json).

Nine audit-runner tests and the combined website/PDF build also passed. Reload the VS Code window once after the configuration move. Steven's mathematical correspondence review remains pending.
