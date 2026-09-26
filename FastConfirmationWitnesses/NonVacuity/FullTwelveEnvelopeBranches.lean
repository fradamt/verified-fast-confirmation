module
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopePremises

@[expose] public section

namespace FastConfirmation.Spec.FullTwelveEnvelopeWitness

open ConcreteFFG
open FullTwelveEnvelopeBridgeRun

def q23 := witnessExecution.fcrStoreAtCall witnessConfig witnessExternals 0 23
def q95 := witnessExecution.fcrStoreAtCall witnessConfig witnessExternals 0 95
def q179 := witnessExecution.fcrStoreAtCall witnessConfig witnessExternals 0 179

/-- The call at second 23 selects the child. The call at second 95 resets
the cached child to the finalized anchor. The late call skips selection. -/
theorem fcr_branch_samples :
    getLatestAfterFinalized witnessConfig witnessExternals q23 = anchorRoot ∧
    getLatestAfterObserved witnessConfig witnessExternals q23 = anchorRoot ∧
    get_latest_confirmed witnessConfig witnessExternals q23 = childRoot ∧
    q95.confirmed_root = childRoot ∧
    getLatestAfterFinalized witnessConfig witnessExternals q95 = anchorRoot ∧
    get_latest_confirmed witnessConfig witnessExternals q95 = anchorRoot ∧
    get_latest_confirmed witnessConfig witnessExternals q179 = anchorRoot := by
  set_option maxRecDepth 100000 in decide +kernel

/-- Exact guards for the selected, reset, and skipped sample calls. -/
theorem fcr_guard_samples :
    ¬ getLatestFinalizedRevertGuard witnessConfig witnessExternals q23 ∧
    getLatestFinalizedRevertGuard witnessConfig witnessExternals q95 ∧
    getLatestSelectorGuard witnessConfig q23 (getLatestAfterObserved witnessConfig witnessExternals q23) ∧
    ¬ getLatestSelectorGuard witnessConfig q179 (getLatestAfterObserved witnessConfig witnessExternals q179) ∧
    getLatestObservedRestartGuard witnessConfig q23
      (getLatestAfterFinalized witnessConfig witnessExternals q23) = false ∧
    getLatestObservedRestartGuard witnessConfig q95
      (getLatestAfterFinalized witnessConfig witnessExternals q95) = false := by
  simp only [getLatestFinalizedRevertGuard, getLatestSelectorGuard]
  set_option maxRecDepth 100000 in decide +kernel

/-- The verified child has a FULL fork-choice candidate. The carrier still
selects the EMPTY parent status, and its empty-slot support discount is zero. -/
theorem gloas_discount_sample :
    get_parent_payload_status (witnessExecution.store witnessConfig witnessExternals 0 168)
      ((witnessExecution.store witnessConfig witnessExternals 0 168).blocks carrierRoot) = .empty ∧
    get_parent_payload_support_between_slots witnessConfig witnessExternals
      (witnessExecution.store witnessConfig witnessExternals 0 168)
      ((witnessExecution.store witnessConfig witnessExternals 0 168).block_states carrierRoot)
      childRoot .full 2 6 = 0 ∧
    get_support_discount witnessConfig witnessExternals (witnessExecution.store witnessConfig witnessExternals 0 168)
      ((witnessExecution.store witnessConfig witnessExternals 0 168).block_states carrierRoot) carrierRoot = 0 := by
  set_option maxRecDepth 100000 in decide +kernel

end FastConfirmation.Spec.FullTwelveEnvelopeWitness

end
