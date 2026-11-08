# Steven's chapter workflow

Established by Steven on 2026-11-01. This is the default collaboration process for each chapter in every volume. The manuscript, formalization, and video share mathematics but have different completion criteria.

## 1. Full chapter draft

The AI writes the complete natural-language draft in the chapter's `intro.tex` and section `text.tex` files. This is a reference book without exercises or exercise solutions. Include concise motivation, definitions, exact theorem hypotheses, full proofs, and selected worked examples or normalization checks as exposition. Do not replace removed exercise lists with relabeled problem lists. Keep Chapter 0 focused on elementary trace and kernel identities, and develop each automorphic trace formula in its own chapter. Prefer a brief cross-reference to duplicating later material.

The chapter is a **draft for Steven to edit**. AI generation, self-checking, and another AI's review do not constitute Steven's approval. Do not start video production at this stage.

## 2. Collaborative prose editing

Steven reads and edits the chapter with the AI. His edited statements and arguments become the human-authored formalization roadmap. Preserve his text and intent. Surface missing hypotheses, ambiguous definitions, circular arguments, and normalization issues rather than quietly choosing a different theorem.

Each editing round should identify the changed sections and mathematical claims. Use stable result labels, such as `linear-algebra.trace-cyclic`, without printing those internal names in the book. Ordinary theorem names and numbering remain the reader-facing presentation.

Use `$...$` for inline mathematics and `\[...\]` for displays. Present definitions and results in AMS theorem environments, with `proof` environments for their proofs. In Chapter 0, retain the three main sections but omit subsection headings: weave examples and transitions into the exposition. Elsewhere, subsection headings may organize broader topics. When moving a result from a heading into an environment, keep its semantic label and update notation links to the most precise defining passage; a change in typography alone does not change its formalization status.

Keep the volume's notational index synchronized during the same editing round. For new or changed notation, record its meaning, scope, relevant normalization, and a link to the defining passage. Distinguish local uses of the same symbol. The index is authored from the actual manuscript; it does not infer definitions automatically from TeX or certify a Lean correspondence.

Specify the ambient space in each inner-product and norm subscript, including the domain and measure for $L^2$ spaces. Define the measure, scalar field, and inner-product convention at first use; track these conventions in the corresponding formalization and index.

## 3. Formalization alongside editing

Work on the corresponding `Formalization.lean` during prose-editing rounds. This can proceed in parallel on settled portions while Steven edits other sections, with explicit file ownership to avoid overwriting his changes. Use saved source snapshots; unsaved editor buffers are not reliable inputs to the build. There is no unattended autoformalization watcher configured.

Before the first implementation, pin a compatible Lean/Mathlib environment and audit the existing library. Reusable definitions and lemmas belong under `lean/TraceFormulas/`; section companions express the book's exact specialization. Formal proof structure need not mimic every sentence, but a material change of argument must be explained in `compare.tex` and reviewed with Steven.

The quality target is the project's [Tau Ceti-inspired acceptance criteria](QUALITY.md): faithful and nonvacuous statements, reusable definitions, kernel-checked proofs, explicit hypotheses, dependency/axiom audits, reproducible builds, and substantive review. No admitted proof or unproved project axiom counts as finished work. A difficult dependency is a recorded obligation, not permission to weaken the target.

Track the actual source version used for each result. A result record should contain its semantic ID; prose path and source revision or hash; Lean module/declaration and revision or hash; dependencies and source checks; exact build command and outcome; axiom-audit evidence; correspondence notes; and review status. These are independent fields, not a single 'done' flag. Repository commits can provide provenance once the project is committed; do not invent commit IDs for the current untracked tree.

## 4. Steven's correspondence review

Present the edited prose and checked Lean source together in Compare. Steven verifies that the formal definitions, domains, quantifiers, hypotheses, conventions, and conclusions express the intended mathematics. Proof compilation proves only the formal statement, so it does not replace this check.

Record Steven's explicit review against the versions he reviewed. Until then, status remains **awaiting Steven's review**, even when machine checks pass. Editing a statement or underlying definition reopens affected correspondence reviews; editing only proof implementation requires a fresh build and an impact assessment. Track dependencies so downstream claims do not silently retain stale approvals.

## 5. Visual explanation and video

After the human correspondence review, use the reviewed prose as the basis for an original visual script in `lecture.tex`. Aim for the requested 3Blue1Brown style of explanation: a motivating question, intuitive visual models, carefully paced transformations, narration that explains what changes and why, and explicit transitions into the rigorous argument.

Develop the script and storyboard before rendering the video. By Steven's direction of 2026-11-05, plan one video per chapter by default, with multiple videos when length warrants it. Put the full chapter script in its `lecture.tex` and register it in `chapter.json`; keep section video entries for separately planned recordings. Specify scenes, mathematical objects, animation actions, narration, and the statement each scene teaches. Review visuals and spoken claims against the approved mathematics. Then render, edit, caption, and verify the recording before adding its real URL and timestamps. No claimed recording or invented timestamps substitute for the artifact.

The original Section 0.1 script predates this workflow and is preserved in `archive/2026-11-05-chapter00-lecture/`. Steven explicitly requested a full Chapter 0 script on 2026-11-05; that request authorizes preparing the draft before the still-pending formal correspondence review. The new chapter-level `lecture.tex` supersedes the section draft. This request is not approval of the script, recording, or mathematical correspondence. Other new scripts wait for the review gate unless Steven explicitly requests an exception.

## Practical editing loop

Edit `text.tex` and save. Cmd+Shift+B rebuilds the full book and website from any active tab. Keep `.build/v1a/main.pdf` open in LaTeX Workshop's PDF viewer. The staged build retains the last complete PDF until the replacement is ready. Use the website's Compare tab for the prose/Lean comparison and `compare.tex` for explanations of correspondence.

The revised Chapter 0 reference draft incorporates Steven's direction to omit exercises, the introductory survey, and the standalone finite Fourier section. All three section companions and their shared mathematics have now compiled with pinned Lean and Mathlib: Section 0.1 covers matrix and endomorphism traces, Section 0.2 covers finite-rank L² operators and kernels, and Section 0.3 covers relative pairings and weighted compressed traces. The chapter-wide build and axiom audit passed on 2026-11-04 and again after the editor configuration fix on 2026-11-05; run `python3 scripts/audit_lean.py` from the project directory to produce fresh machine evidence. The latest dated evidence record is [chapter00-2026-11-05-editor/record.json](../lean/audits/chapter00-2026-11-05-editor/record.json). The section comparisons describe conventions and proof-route differences for Steven's review. The requested chapter-level video script is a draft; correspondence review and recording approval remain pending.
