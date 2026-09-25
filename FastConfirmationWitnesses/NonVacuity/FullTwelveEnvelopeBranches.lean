module
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopePremises

@[expose] public section

namespace FastConfirmation.Spec.FullTwelveEnvelopeWitness

open AcceptedActualFCRJointNonVacuityBase

def q23 := run.fcrStoreAtCall cfg ext 0 23
def q95 := run.fcrStoreAtCall cfg ext 0 95
def q179 := run.fcrStoreAtCall cfg ext 0 179

/-- The call at second 23 selects the child. The call at second 95 resets
the cached child to the finalized anchor. The late call skips selection. -/
theorem fcr_branch_samples :
    getLatestAfterFinalized cfg ext q23 = anchorRoot ∧
    getLatestAfterObserved cfg ext q23 = anchorRoot ∧
    get_latest_confirmed cfg ext q23 = childRoot ∧
    q95.confirmed_root = childRoot ∧
    getLatestAfterFinalized cfg ext q95 = anchorRoot ∧
    get_latest_confirmed cfg ext q95 = anchorRoot ∧
    get_latest_confirmed cfg ext q179 = anchorRoot := by
  set_option maxRecDepth 50000 in decide

/-- Exact guards for the selected, reset, and skipped sample calls. -/
theorem fcr_guard_samples :
    ¬ getLatestFinalizedRevertGuard cfg ext q23 ∧
    getLatestFinalizedRevertGuard cfg ext q95 ∧
    getLatestSelectorGuard cfg q23 (getLatestAfterObserved cfg ext q23) ∧
    ¬ getLatestSelectorGuard cfg q179 (getLatestAfterObserved cfg ext q179) ∧
    getLatestObservedRestartGuard cfg q23
      (getLatestAfterFinalized cfg ext q23) = false ∧
    getLatestObservedRestartGuard cfg q95
      (getLatestAfterFinalized cfg ext q95) = false := by
  simp only [getLatestFinalizedRevertGuard, getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide

/-- The verified child has a FULL fork-choice candidate. The carrier still
selects the EMPTY parent status, and its empty-slot support discount is zero. -/
theorem gloas_discount_sample :
    get_parent_payload_status (run.store cfg ext 0 168)
      ((run.store cfg ext 0 168).blocks carrierRoot) = .empty ∧
    get_parent_payload_support_between_slots cfg ext
      (run.store cfg ext 0 168)
      ((run.store cfg ext 0 168).block_states carrierRoot)
      childRoot .full 2 6 = 0 ∧
    get_support_discount cfg ext (run.store cfg ext 0 168)
      ((run.store cfg ext 0 168).block_states carrierRoot) carrierRoot = 0 := by
  set_option maxRecDepth 50000 in decide

end FastConfirmation.Spec.FullTwelveEnvelopeWitness

end
