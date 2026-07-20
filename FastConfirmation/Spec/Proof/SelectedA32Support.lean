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

/-- A retained tentative epoch-crossing exposes exactly the executable gate
and the normative target-support proviso attached to that gate. -/
theorem currentTargetAcceptedEdge_gate_and_support
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query
      latestConfirmedRoot)
    (hedge : CurrentTargetAcceptedEdge cfg ext query latestConfirmedRoot a c) :
    will_current_target_be_justified cfg ext query.store = true ∧
      HonestVotesSupportTarget cfg E
        (get_current_target cfg query.store) q := by
  exact ⟨hedge.current_target_gate cfg ext,
    hprovisos.current_target a c hedge⟩

/-- A strict selected previous-epoch result away from epoch start exposes both
the wrapper's actual no-conflict boolean and the matching call-site support
proviso.  This result-level form covers tentative-loop outputs which are not
themselves `PreviousAcceptedEdge`s. -/
theorem selectedPreviousResult_noConflict_gate_and_support
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root} {latestConfirmedRoot result : Root}
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query
      latestConfirmedRoot)
    (hout : find_latest_confirmed_descendant cfg ext query
      latestConfirmedRoot = result)
    (hstrict : result ≠ latestConfirmedRoot)
    (hprevious : get_block_epoch cfg query.store result ≠
      get_current_store_epoch cfg query.store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true) :
    will_no_conflicting_checkpoint_be_justified cfg ext query.store = true ∧
      HonestVotesSupportTarget cfg E
        (get_current_target cfg query.store) q := by
  exact ⟨selected_previous_result_no_conflict_gate cfg ext query
      latestConfirmedRoot result hout hstrict hprevious hnotStart,
    hprovisos.selected_previous_result_no_conflict result hout hstrict
      hprevious hnotStart⟩

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

/-- The exact per-seat temporal consequence of
`HonestVotesSupportTarget`: an honest validator assigned at or after the query
casts a concrete vote for `target`, strictly before the next target-epoch
boundary.

The conclusion intentionally says nothing about `a.data.source`.  Fixing that
field uniformly across a quorum is the additional FFG/source-coherence fact
needed by `HonestTargetQuorumBefore`. -/
theorem honest_target_vote_before_next_epoch
    (hhb : HonestBehavior cfg ext E)
    {target : Checkpoint Root} {q : ℕ}
    (hsupport : HonestVotesSupportTarget cfg E target q)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hcommittee : i ∈ E.committee s)
    (hsH : E.SlotWithinHorizon cfg s)
    (hsEpoch : compute_epoch_at_slot cfg s = target.epoch)
    (hqS : E.slot_at cfg q ≤ s)
    (hs0 : E.slot_at cfg 0 ≤ s) :
    ∃ (k : ℕ) (a : Attestation Root),
      E.WithinHorizon cfg k ∧
      E.slot_at cfg k = s ∧
      E.vote i s = some (k, a) ∧
      a.data.slot = s ∧
      a.data.slot < compute_start_slot_at_epoch cfg (target.epoch + 1) ∧
      a.data.target = target := by
  obtain ⟨k, index, hkH, hkSlot, hvote⟩ :=
    hhb.votes_head i hi s hcommittee hsH hs0
  let a := honest_attestation cfg ext (E.store cfg ext i k) s index i
  have haTarget : a.data.target = target :=
    hsupport.2 i hi s hsH hsEpoch hqS k a (by simpa only [a] using hvote)
  have hsBefore : s < compute_start_slot_at_epoch cfg (target.epoch + 1) := by
    rw [← hsEpoch]
    simp only [compute_start_slot_at_epoch, compute_epoch_at_slot]
    simpa only [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (b := cfg.slots_per_epoch) s cfg.slots_per_epoch_pos)
  refine ⟨k, a, hkH, hkSlot, ?_, ?_, ?_, haTarget⟩
  · simpa only [a] using hvote
  · rfl
  · simpa only [a, honest_attestation_data_eq,
      honest_attestation_data_slot] using hsBefore

/-- Specialization of `honest_target_vote_before_next_epoch` to an actual
selected tentative crossing.  This is the complete vote-level fact supplied
by the executable gate plus `SelectedHelperProvisosAt.current_target`. -/
theorem currentTargetAcceptedEdge_honest_vote_before_next_epoch
    (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query
      latestConfirmedRoot)
    (hedge : CurrentTargetAcceptedEdge cfg ext query latestConfirmedRoot a c)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hcommittee : i ∈ E.committee s)
    (hsH : E.SlotWithinHorizon cfg s)
    (hsEpoch : compute_epoch_at_slot cfg s =
      (get_current_target cfg query.store).epoch)
    (hqS : E.slot_at cfg q ≤ s)
    (hs0 : E.slot_at cfg 0 ≤ s) :
    ∃ (k : ℕ) (vote : Attestation Root),
      E.WithinHorizon cfg k ∧
      E.slot_at cfg k = s ∧
      E.vote i s = some (k, vote) ∧
      vote.data.slot = s ∧
      vote.data.slot < compute_start_slot_at_epoch cfg
        ((get_current_target cfg query.store).epoch + 1) ∧
      vote.data.target = get_current_target cfg query.store := by
  exact E.honest_target_vote_before_next_epoch cfg ext hhb
    (hprovisos.current_target a c hedge) hi hcommittee hsH hsEpoch hqS hs0

end Execution

end FastConfirmation.Spec
