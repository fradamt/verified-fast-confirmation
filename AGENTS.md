# Agent instructions

Read `docs/CONVENTIONS.md` for names, module structure, and file placement, and
`docs/ARCHITECTURE.md` for the five libraries and the checks. These rules are in addition:

- Imports go from Witnesses to Proofs to Internal to Statements to Model, or stay within
  one library. Use `scripts/check_imports.py` to check the library graph.
- Keep Model and Statements free of authored theorems except
  `SuccessfulScheduledBlockImport.processedCount_lt`, which supports the successor-prefix
  definition in Model.
- Do not change a proof statement to fix a module visibility error. Definitions that
  public statements or exposed definitions use must be public. Keep other helpers private
  where valid.
- Keep `scripts/Audit.lean` a non-module script, so that its ordinary imports load proof
  bodies. A module-based audit would need `import all`.
- Run `scripts/validate.sh --fast` before a commit. Run the full `scripts/validate.sh` for
  a library or import change.
- The reachability and trust audit counts in the documents come from their scripts.
  Update them when the scripts change.
