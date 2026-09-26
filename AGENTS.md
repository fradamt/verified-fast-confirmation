# Lean file conventions

- The six library roots are `FastConfirmationModel`,
  `FastConfirmationStatements`, `FastConfirmationInternal`,
  `FastConfirmationProofs`, `FastConfirmationWitnesses`, and
  `FastConfirmationPaper`. `FastConfirmation.lean` imports all six.
- Spec-side imports go from Witnesses to Proofs to Internal to Statements to
  Model, or stay within one library. Paper and the Spec side do not import
  each other. Keep Model and Statements free of authored theorems except
  `SuccessfulScheduledBlockImport.processedCount_lt`, which supports the
  successor-prefix definition in Model.
- Model files under `Spec/` follow the Python consensus specification's
  sections. `Execution/` holds scheduled runs, stake reads, and external
  functions. Statements holds premises and claims; Internal holds proof
  vocabulary; Proofs is grouped by subject; Witnesses holds concrete runs and
  counterexamples.
- The two public executable claims are in `ReviewClaims` in `FastConfirmationStatements/Review.lean`; `review_claims` is proved in `FastConfirmationProofs/ReviewTheorem.lean`.
- Start each new library `.lean` file with `module`.
- Use `public import` to preserve the library's transitive imports.
- Every library module needs a module docstring. Its first sentence states the
  protocol function family, premise, invariant, or theorem in the file.
  Model docstrings cite the Python document and section.
- After the import header, put declarations in an `@[expose] public section`.
  Close all inner namespaces and sections, then close the public section
  with `end`. Use the scope name when closing a named scope.
- An import-only file does not need a public section.
- Keep proof helpers private. The module system also keeps public theorem
  proof bodies private. Definitions used by public statements or exposed
  definitions must be public; keep other local helpers private where valid.
- Do not put public-section commands inside comments. Check scope closures
  when a file has nested sections or namespaces.
- Keep `scripts/Audit.lean` as a non-module script so its ordinary imports
  load proof bodies. A module-based audit would need `import all`.
- Run `scripts/validate.sh --fast` before a commit. Run
  `scripts/validate.sh` for library or import changes; it includes the build,
  import check, and trust audit. Do not change proof statements to fix a
  module visibility error. Use `scripts/check_imports.py` to check the
  library graph.

# Current review documents

- `README.md` states the two public claims and the premise ledger.
- `docs/ARCHITECTURE.md` gives the six-library layout and checks.
- `docs/CONVENTIONS.md` gives naming, module, and import rules.
- `docs/SPEC_MAP.md` maps Python sections and functions to Model.
- `docs/PAPER_MAP.md` maps the paper to the independent Paper library.
- `docs/MODELING_CHOICES.md` records choices and limits.
- `docs/REVIEW_GUIDE.md` gives the cold review reading order, audit dimensions, and current limits.
- `docs/conformance.md` describes the trace comparison.
- Earlier notes are in `docs/history/`.

The reachability check has 64 claim-reachable source declarations and one
approved public exception, `Synchrony`. The trust audit checks 49 public
theorem witnesses. Check these counts against the scripts when they change.
