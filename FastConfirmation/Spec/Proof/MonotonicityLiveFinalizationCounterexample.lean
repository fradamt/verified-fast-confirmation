module
public import FastConfirmation.Spec.Proof.AcceptedActualFCRJointNonVacuityFinal

@[expose] public section

/-!
# First-boundary finalization counterexample

The accepted finalization delay has an anchor exception. At the first epoch
boundary, the finalized checkpoint can still be the anchor at the start of
the previous epoch. Thus the strict inequality proposed as L3 in the live
monotonicity plan is false. This witness uses an actual accepted execution
and an actual boundary FCR call.
-/

namespace FastConfirmation.Spec
namespace MonotonicityLiveFinalizationCounterexample

open AcceptedActualFCRJointNonVacuityBase
open AcceptedActualFCRJointNonVacuityFinal

-- Reduction of the finite execution needs a deeper recursion limit.
set_option maxRecDepth 30000 in
/-- The accepted execution reaches its first epoch boundary with the anchor
still finalized. The anchor is also the epoch-zero checkpoint on the head.
The proposed strict L3 inequality fails at this actual FCR call. -/
theorem first_boundary_strict_finalized_age_false :
    Nonempty (witnessExecution.AcceptedActualFCRNextSlotSafetyAssumptions
      witnessConfig witnessExternals) ∧
    witnessExecution.IsFCRCallAt witnessConfig witnessExternals 0 3 ∧
    witnessExecution.WithinHorizon witnessConfig 4 ∧
    let last := witnessExecution.store witnessConfig witnessExternals 0 3
    let next := witnessExecution.store witnessConfig witnessExternals 0 4
    get_current_store_epoch witnessConfig next = 1 ∧
    last.unrealized_justified_checkpoint = anchorCheckpoint ∧
    get_checkpoint_for_block witnessConfig next
      (get_head witnessConfig next).root 0 = anchorCheckpoint ∧
    next.unrealized_justifications
      (get_head witnessConfig next).root = anchorCheckpoint ∧
    (get_voting_source witnessConfig next
      (get_head witnessConfig last).root).epoch + 2 ≥ 1 ∧
    (witnessExecution.fcrStep witnessConfig witnessExternals 0 3
      ).current_epoch_observed_justified_checkpoint = anchorCheckpoint ∧
    is_ancestor next (get_head witnessConfig next)
      (get_node_for_root anchorRoot) = true ∧
    next.finalized_checkpoint = anchorCheckpoint ∧
    get_block_slot next next.finalized_checkpoint.root =
      compute_start_slot_at_epoch witnessConfig 0 ∧
    ¬ get_block_slot next next.finalized_checkpoint.root <
      compute_start_slot_at_epoch witnessConfig (1 - 1) := by
  refine ⟨⟨witnessAcceptedActualFCRNextSlotSafetyAssumptions⟩, ?_⟩
  constructor
  · unfold Execution.IsFCRCallAt
    decide
  constructor
  · unfold Execution.WithinHorizon
    decide
  dsimp only
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  decide

end MonotonicityLiveFinalizationCounterexample
end FastConfirmation.Spec

end
