import FastConfirmation.Spec.Proof.SelectedTraceFilterPipeline
import FastConfirmation.Spec.Proof.Delivery

/-!
# Selected current-target support: the exact executable consequence

An accepted tentative edge which crosses a block-epoch boundary really did
pass `will_current_target_be_justified`.  Its call-site proviso also says that
every honest vote from the query slot onward, in the current target's epoch,
targets that checkpoint.

This file records the strongest direct temporal consequence of those two
facts.  Every honest committee member assigned at or after the query casts an
actual recorded vote for the current target, and that vote is strictly before
the start of the next epoch.  The source of the vote is deliberately left
unconstrained: `HonestBehavior.votes_head` computes it from the voter's own
pulled-up head state, while `HonestVotesSupportTarget` constrains only the
target.

Consequently these hypotheses do **not** by themselves construct
`HonestTargetQuorumBefore`.  That structure requires one common source for the
whole two-thirds signer set.  Neither the executable helper nor its normative
proviso states cross-validator source agreement, and the helper arithmetic
counts target support without grouping it by source.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Once a concrete child is known to be on the query head's chain and to
belong to the query's current epoch, the helper target is exactly that child's
epoch checkpoint.  These geometric hypotheses are separate from
`CurrentTargetAcceptedEdge`: that predicate records trace membership and a
strict epoch increase, but does not by itself state that the child has reached
the query's current epoch. -/
theorem current_target_eq_checkpoint_of_current_epoch_ancestor
    {store : Store Root} {c : Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hheadC : is_ancestor store (get_head cfg store)
      (get_node_for_root c) = true)
    (hcEpoch : get_block_epoch cfg store c =
      get_current_store_epoch cfg store)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
      (get_head cfg store).root) :
    get_current_target cfg store =
      get_checkpoint_for_block cfg store c (get_block_epoch cfg store c) := by
  have hslot : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg store) ≤ (store.blocks c).slot := by
    rw [← hcEpoch]
    exact start_slot_at_block_epoch_le cfg store c
  have hroot := get_checkpoint_block_of_ancestor cfg hwf hheadC hslot hwalk
  simp only [get_current_target, get_checkpoint_for_block]
  rw [hcEpoch]
  exact congrArg (Checkpoint.mk (get_current_store_epoch cfg store)) hroot

end Execution

end FastConfirmation.Spec
