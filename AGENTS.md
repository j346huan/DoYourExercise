# Publication repository

This repository displays mathematical solutions and finished Lean proofs. It is not a Lean development project.

For Lean work, read `D:/lean/DoYourExercise/AGENTS.md` and `D:/lean/README.md`. Keep the compiler, Lake files, Mathlib, draft proofs, generated import modules, compiled files, logs, and test examples under `D:/lean`.

Only finished `content/<BookID>/<exercise>/proof.lean` files, their externally generated `verification.json` records, and necessary exercise metadata belong here. Never create a Lean toolchain, Lake project, `.lake` directory, or generated `LeanExercises` source tree here. Never invent verification records or mark a proof formalized without an actual successful external check and a review of its mathematical statement.

Use the existing exercise format in `AUTHORING.md`. Preserve the user's concise mathematical style and textbook-only exercise titles. Question statements and source books remain private. Do not force-add ignored files. Preserve unrelated working changes.

## Storage boundary

Do not install software or write configuration, caches, logs, drafts, or temporary files on C:. All Lean setup and development files belong under D:/lean. Set process-local TEMP, TMP and TMPDIR to D:/lean/tmp. Do not alter Windows user environment settings or global editor/Codex configuration. Existing applications and runtimes on C: may be read or invoked, but do not update them.
