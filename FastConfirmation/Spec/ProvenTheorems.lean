import FastConfirmation.Spec.Proof.AcceptedActualFCRNextSlotSafetyFacade
import FastConfirmation.Spec.Proof.AcceptedActualFCRJointNonVacuityFinal

/-!
# Consensus-spec proved theorems

Public theorem facade for the executable consensus-spec development.

The primary result is `acceptedSpec_safety_next_slot`: if an honest node stores
a confirmed root at a completed execution boundary, then from the following
slot onward that root is an ancestor of every in-horizon honest node's
fork-choice head.

`Execution.AcceptedActualFCRNextSlotSafetyAssumptions.
findLatestConfirmedDescendant_safeFrom_of_actualCall` proves the corresponding
property for the literal descendant-helper result at an actual scheduled
boundary call, including an unchanged return.

`AcceptedActualFCRJointNonVacuityFinal.
acceptedActualFCRNextSlotSafetyAssumptions_nonvacuous` supplies a concrete
finite execution satisfying the complete accepted assumption bundle.
-/
