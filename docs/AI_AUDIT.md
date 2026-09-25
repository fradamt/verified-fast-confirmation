# Brief for a cold auditor

Read the source without assuming that this guide is correct. Cite each finding by declaration, file, and line. Check the meanings of definitions and premises; Lean checks proof scripts separately.

## Reading order

1. `README.md` and `FastConfirmationStatements/Review.lean`: identify the three exact claims.
2. `FastConfirmationModel/Spec/` with `docs/SPEC_MAP.md` and the Python fork `fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`): compare every Python function used by FCR.
3. `FastConfirmationModel/Execution/`: inspect schedules, event folds, handler-successful prefix states, stake reads, and opaque externals.
4. `FastConfirmationStatements/Premises/`, `FastConfirmationStatements/Claims.lean`, and `FastConfirmationStatements/Review.lean`: expand every nested premise and check quantifiers.
5. `FastConfirmationWitnesses/Index.lean` and its cited finite runs: check which premises have joint witnesses and which implications hold only vacuously.
6. `FastConfirmationPaper/` with `docs/PAPER_MAP.md`: compare paper claims and assumptions independently.
7. `docs/MODELING_CHOICES.md`, `docs/REVIEW_GUIDE.md`, `docs/ARCHITECTURE.md`, and `docs/conformance.md`: test document claims against source and `scripts/Audit.lean`.

## Audit dimensions

- **Python fidelity.** Check section by section for faithful control flow, changed branches, totalized maps, loop fuel, integer arithmetic, and the public Gloas empty-slot discount. Identify each simplification or divergence.
- **Execution model.** Check event scheduling, successful handler returns, store state at boundary seconds, payload validation before import, static registry, finite horizon, and all `Externals` contracts. Look for events that the model can create or omit without an implementation justification.
- **Statements.** Expand `ReviewClaims`, `ConfirmedRootSafeFromNextSlot`, and `LiveConfirmedRootMonotonicity`. Check observer, time, and horizon quantifiers. `Execution.NextSlotSafetyPremises.selected_result_safe_from_next_slot_of_scheduled_call` is a spec-correspondence lemma for the `find_latest_confirmed_descendant` note, not a review claim. Distinguish a stored output from an optional in-slot query.
- **Premises.** For every field in `Execution.NextSlotSafetyPremises` and `LiveMonotonicityPremises`, ask whether it is realistic, stronger than the paper or Python prose, and satisfiable with the other fields. Check whether it assumes an FCR output or the claimed ancestry. Check global FFG and finalization conditions beyond the endpoint.
- **Non-vacuity.** Check the 14 names in `scripts/Audit.lean`; locate their concrete runs. The next-slot witness has no payload envelope. There is no joint live-premise witness. Do not infer a production instance from a finite witness.
- **Paper relation.** The executable and paper libraries have no refinement theorem. Check the Section 3.1 Theorem 1 and Section 4 Algorithm 1 statements separately. `SafeConfirmedAlg1Inputs` is stronger than Assumption 6.

Proof script style and local tactic choices are outside this audit. Report errors in definitions, statements, premises, witnesses, and document descriptions even when every proof checks.
