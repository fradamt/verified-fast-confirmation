# Architecture

Six Lean libraries separate the trusted definitions from proof terms. An arrow means that the library on the right may import the one on the left: Model → Statements → Internal → Proofs → Witnesses. Paper is independent and has no imports in either direction with the executable side. `FastConfirmation.lean` imports all six.

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Library                    │ Contents                                                                                     │
├────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ FastConfirmationModel      │ Python function translation in Spec/; scheduled runs, stake reads, external calls, and state │
│                            │ folds in Execution/.                                                                         │
│ FastConfirmationStatements │ Premise records in Premises/; propositions in Claims.lean and the two-field Review.lean      │
│                            │ bundle.                                                                                      │
│ FastConfirmationInternal   │ Proof vocabulary and compatibility records. Subject folders hold FFG and synchrony facts;    │
│                            │ Legacy/ holds compatibility records.                                                         │
│ FastConfirmationProofs     │ Kernel checked proofs grouped by subject; ReviewTheorem.lean proves review_claims.           │
│ FastConfirmationWitnesses  │ Finite runs in NonVacuity/, negative results in Counterexamples/, and an inventory in        │
│                            │ Index.lean.                                                                                  │
│ FastConfirmationPaper      │ Independent paper definitions, claims, proofs, and witnesses in Core/, LMDGhost/, and HFC/.  │
└────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

`FastConfirmationModel` and `FastConfirmationStatements` are the trusted review surface. They contain definitions and premise propositions, with only proof terms needed by `AcceptedBlockTransition.successorPrefix` and `getLatestConfirmedTrace`. The Lean kernel checks the proof bodies in Internal, Proofs, Witnesses, and Paper. The audit in `scripts/Audit.lean` checks public theorem dependencies and permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Review checks

```text
┌────────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Check                      │ What it enforces                                                                            │
├────────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ check_consensus_source.py  │ The Python tag and the pinned source objects match the recorded hashes.                     │
│ check_review_boundary.py   │ Lean parser import closure of Statements contains only Model and Statements modules; every  │
│                            │ Statements source is included.                                                              │
│ StatementReachability.lean │ Every authored Statements declaration is reachable from ReviewClaims, except two documented │
│                            │ public witness dependencies.                                                                │
│ ReviewSurfaceShape.lean    │ The two review fields and selected premise record shapes remain exact.                      │
│ check_imports.py           │ The six-library import direction and Paper separation hold.                                 │
│ check_doc_names.py         │ Backticked Lean names in current documents resolve to declarations or files.                │
│ Audit.lean                 │ The public witness set has only standard axiom dependencies and no forbidden declarations.  │
│ validate.sh                │ Fast checks above; full mode also builds every library and runs Lean checks.                │
└────────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```
