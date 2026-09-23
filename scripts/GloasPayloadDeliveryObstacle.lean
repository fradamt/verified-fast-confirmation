import FastConfirmationModel.Execution.Run

/-!
# Gloas payload delivery obstacle

This file uses only the executable Model modules. It exhibits the missing
payload-delivery premise in the former `Delivery.validate_at_extension` lemma.
The two stores have the same blocks. The receiver has no verified payload for
the voted block, so the Gloas index-1 check rejects the vote.

This refutes that private transport step with its former premises. It does not
by itself refute a public safety theorem or construct a full accepted execution.
The `NextSlotSynchronyPremises.envelope_delivery` premise excludes this
missing-envelope delivery pattern within its synchrony horizon. Together
with data-availability relay and deterministic verification, it yields
`Execution.payload_envelope_relay_of_parts`, the verified-payload relay used
by the safety proof.
No Python specification change, extra axiom, or proof-layer import is used.
-/

namespace GloasPayloadDeliveryObstacle

open FastConfirmation.Spec

/-- Minimal values read by this fixture: 8 slots, 6 seconds, PTC size 16. -/
def cfg : Config :=
  { mainnet_config with
    slots_per_epoch := 8
    slots_per_epoch_pos := by decide
    slot_duration_ms := 6000
    slot_duration_ms_pos := by decide
    ptc_size := 16 }

def checkpoint : Checkpoint Nat := ⟨0, 1⟩

def anchorBlock : SignedBeaconBlock Nat :=
  { root := 1
    message :=
      { slot := 0
        parent_root := 0
        proposer_index := 0
        parent_block_hash := 0
        block_hash := 10 } }

def anchorState : BeaconState Nat :=
  { genesis_time := 0
    slot := 0
    validators :=
      [{ effective_balance := 32000000000
         slashed := false
         activation_epoch := 0
         exit_epoch := FAR_FUTURE_EPOCH }]
    current_justified_checkpoint := checkpoint
    finalized_checkpoint := checkpoint }

/-- B follows the anchor's EMPTY node; its own payload has execution hash 20. -/
def blockB : BeaconBlock Nat :=
  { slot := 1
    parent_root := 1
    proposer_index := 0
    parent_block_hash := 0
    block_hash := 20 }

def envelopeB : ExecutionPayloadEnvelope Nat :=
  { beacon_block_root := 2
    parent_beacon_block_root := 1
    identity := 20 }

/-- Both stores have the same known blocks, block states, checkpoints, and PTC maps. -/
def sharedStore : Store Nat :=
  let anchor := get_forkchoice_store cfg anchorState anchorBlock
  { anchor with
    time := 12
    block_roots := [1, 2]
    blocks := Function.update anchor.blocks 2 blockB
    block_states := Function.update anchor.block_states 2 { anchorState with slot := 1 }
    block_timeliness := Function.update anchor.block_timeliness 2 (some (true, true))
    unrealized_justifications := Function.update anchor.unrealized_justifications 2 checkpoint
    payload_timeliness_vote := Function.update anchor.payload_timeliness_vote 2
      (some (List.replicate cfg.ptc_size none))
    payload_data_availability_vote := Function.update anchor.payload_data_availability_vote 2
      (some (List.replicate cfg.ptc_size none)) }

/-- The source is at slot 2 and has received B's verified envelope. -/
def S : Store Nat :=
  { sharedStore with payloads := Function.update sharedStore.payloads 2 (some envelopeB) }

/-- The receiver is at delivery slot 3 and has not received B's envelope. -/
def P : Store Nat := { sharedStore with time := 18 }

/-- A later-slot vote for B's FULL node. -/
def a : Attestation Nat :=
  { attesting_indices := [0]
    data :=
      { slot := 2
        index := 1
        beacon_block_root := 2
        source := checkpoint
        target := checkpoint } }

/-- Whole-map block agreement, stronger than agreement at source-known roots. -/
theorem blocks_equal : S.blocks = P.blocks := rfl

theorem blocks_agree : ∀ root ∈ S.block_roots, S.blocks root = P.blocks root := by
  intro root _
  rfl

theorem block_domain_equal : S.block_roots = P.block_roots := rfl

theorem block_domain_subset : S.block_roots ⊆ P.block_roots := List.Subset.refl _

theorem source_current_slot : get_current_slot cfg S = a.data.slot := by decide

theorem delivery_current_slot : get_current_slot cfg P = a.data.slot + 1 := by decide

theorem target_epoch_matches : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot := by
  decide

theorem voted_root_known : a.data.beacon_block_root ∈ S.block_roots := by decide

theorem target_root_known : a.data.target.root ∈ S.block_roots := by decide

theorem voted_block_is_older : (S.blocks a.data.beacon_block_root).slot < a.data.slot := by
  decide

theorem voted_block_not_future : (S.blocks a.data.beacon_block_root).slot ≤ a.data.slot := by
  decide

theorem target_consistency : a.data.target.root =
    get_checkpoint_block cfg S a.data.beacon_block_root a.data.target.epoch := by decide

/-- These are the two constructors' premises for the old `WalkKnown` argument:
B is known above target slot 0, its parent is known, and its parent stops there.
The script states the elementary facts to avoid importing the proof layer. -/
theorem known_checkpoint_walk :
    a.data.beacon_block_root ∈ S.block_roots ∧
    compute_start_slot_at_epoch cfg a.data.target.epoch <
      (S.blocks a.data.beacon_block_root).slot ∧
    (S.blocks a.data.beacon_block_root).parent_root ∈ S.block_roots ∧
    (S.blocks (S.blocks a.data.beacon_block_root).parent_root).slot ≤
      compute_start_slot_at_epoch cfg a.data.target.epoch := by decide

/-- The parent walk also respects the source model's strict slot decrease. -/
theorem parent_slot_decreases :
    (S.blocks (S.blocks 2).parent_root).slot < (S.blocks 2).slot := by decide

theorem source_payload_verified : is_payload_verified S a.data.beacon_block_root = true := by
  decide

theorem receiver_payload_missing : is_payload_verified P a.data.beacon_block_root = false := by
  decide

/-- Both extra index-shape checks hold. Only receiver payload presence fails. -/
theorem valid_payload_index_shape :
    (a.data.index = 0 ∨ a.data.index = 1) ∧
    ((P.blocks a.data.beacon_block_root).slot = a.data.slot → a.data.index = 0) := by
  decide

/-- The old transport conclusion is false under Gloas. -/
theorem receiver_rejects : validate_on_attestation cfg P a false = false := by decide

theorem old_transport_conclusion_false : ¬ validate_on_attestation cfg P a false = true := by
  rw [receiver_rejects]
  decide

/-- The exact old validation-facts interface is false. All of its premises
hold for P and a, including the epoch window and the checkpoint walk. -/
theorem old_validation_facts_interface_false :
    ¬ (∀ (store : Store Nat) (vote : Attestation Nat),
      validate_target_epoch_against_current_time cfg store vote = true →
      vote.data.target.epoch = compute_epoch_at_slot cfg vote.data.slot →
      vote.data.target.root ∈ store.block_roots →
      vote.data.beacon_block_root ∈ store.block_roots →
      (store.blocks vote.data.beacon_block_root).slot ≤ vote.data.slot →
      vote.data.target.root =
        get_checkpoint_block cfg store vote.data.beacon_block_root vote.data.target.epoch →
      vote.data.slot + 1 ≤ get_current_slot cfg store →
      validate_on_attestation cfg store vote false = true) := by
  intro claimed
  exact old_transport_conclusion_false
    (claimed P a (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))

/-- At the same delivery clock, retaining the source payload makes validation pass. -/
theorem same_clock_with_payload_accepts :
    validate_on_attestation cfg { S with time := P.time } a false = true := by decide

/-- The source's canonical head is B's FULL node at the voting slot. -/
theorem source_head_full : get_head cfg S = ForkChoiceNode.mk 2 .full := by decide

/-- The receiver has the same canonical beacon root, but its EMPTY node. -/
theorem receiver_head_empty : get_head cfg P = ForkChoiceNode.mk 2 .empty := by decide

/-- The Gloas honest data-index rule for this source head selects index 1. -/
theorem honest_data_index_rule :
    (if (S.blocks (get_head cfg S).root).slot = a.data.slot then 0
      else if (get_head cfg S).payload_status = .full then 1 else 0) = a.data.index := by
  rw [source_head_full]
  decide

#eval ("GLOAS_PAYLOAD_DELIVERY_OBSTACLE",
  get_current_slot cfg S,
  get_current_slot cfg P,
  (get_head cfg S).root,
  (get_head cfg P).root,
  is_payload_verified S 2,
  is_payload_verified P 2,
  validate_on_attestation cfg P a false)

#print axioms receiver_rejects
#print axioms old_transport_conclusion_false
#print axioms old_validation_facts_interface_false
#print axioms same_clock_with_payload_accepts
#print axioms source_head_full
#print axioms receiver_head_empty

end GloasPayloadDeliveryObstacle
