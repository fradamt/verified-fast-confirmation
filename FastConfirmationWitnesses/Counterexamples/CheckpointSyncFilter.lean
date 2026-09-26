module
public import FastConfirmationModel
public import Mathlib.Tactic

@[expose] public section

/-!
Checkpoint-sync anchors can lose a confirmed descendant at the raw source-age filter.
The anchor is at the start of epoch 3. Its state still has justification at
epoch 2 and finalization at epoch 0. A child at slot 13 receives all scheduled
votes. The unchanged FCR confirms it at slot 14. At slot 20 the source epoch
is still 2, so the filter rejects the child and the head returns to the anchor.

This is a four-slot, one-second handler regression with a static registry,
zero proposer boost, and no included attestations after the anchor. It does
not assert the complete safety premise bundle or eventual inclusion. The
opaque state functions preserve the old checkpoints along this short trace.
The companion Python probe checks reachable states and the pinned functions.
Normalizing the source to epoch 3 would hide the failed filter comparison.
-/

namespace FastConfirmation.Spec.CheckpointSyncFilterWitness

abbrev R := Fin 4
def anchorRoot : R := 1
def childRoot : R := 2
def oldRoot : R := 3
def cfg : Config where
  slots_per_epoch := 4
  slots_per_epoch_pos := by decide
  slot_duration_ms := 1000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 0
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 0
  min_seed_lookahead := 0

def oldCheckpoint : Checkpoint R := ⟨2, oldRoot⟩
def anchorCheckpoint : Checkpoint R := ⟨3, anchorRoot⟩
def validator : Validator :=
  { effective_balance := 100, slashed := false, activation_epoch := 0,
    exit_epoch := FAR_FUTURE_EPOCH }
def anchorState : BeaconState R :=
  { genesis_time := 0, slot := 12,
    validators := [validator, validator, validator, validator],
    current_justified_checkpoint := oldCheckpoint,
    finalized_checkpoint := ⟨0, 0⟩ }
def anchorBlock : SignedBeaconBlock R :=
  { root := anchorRoot, message := { slot := 12, parent_root := 0 } }
def childBlock : SignedBeaconBlock R :=
  { root := childRoot,
    message := { slot := 13, parent_root := anchorRoot, parent_block_hash := 1 } }
def ext : BeaconFunctionInterface R where
  AnchorCommitsToState := fun _ _ => True
  get_beacon_committee := fun _ slot _ => [slot % 4]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st slot => { st with slot := slot }
  state_transition := fun st sb => some { st with slot := sb.message.slot }
  process_justification_and_finalization := id
  is_valid_indexed_attestation := fun _ _ => true

def vote (slot : Slot) : Attestation R :=
  { attesting_indices := [slot % 4],
    data :=
      { slot := slot
        index := 0
        beacon_block_root := if slot = 12 ∨ 20 ≤ slot then anchorRoot else childRoot
        source := oldCheckpoint
        target := if slot < 16 then anchorCheckpoint
          else if slot < 20 then ⟨4, childRoot⟩ else ⟨5, anchorRoot⟩ } }

def run : Execution R where
  verification_horizon := 6
  genesis_store := get_forkchoice_store cfg anchorState anchorBlock
  schedule := fun _ n =>
    if n = 1 then [.block childBlock, .attestation (vote 12) false]
    else if 2 ≤ n ∧ n ≤ 12 then [.attestation (vote (n + 11)) false]
    else []
  honest := {0, 1, 2, 3}
  committee := fun slot => {slot % 4}
  vote := fun v slot =>
    if 12 ≤ slot ∧ slot < 24 ∧ v = slot % 4 then
      some (slot - 12, vote slot)
    else none

set_option maxRecDepth 50000

/-- Every in-horizon scheduled vote uses the actual head
and the raw old checkpoint as its source. -/
theorem votes_match_honest_data :
    ∀ n : Fin 12, vote (12 + n.val) =
      honest_attestation cfg ext (run.store cfg ext 0 n.val)
        (12 + n.val) 0 ((12 + n.val) % 4) := by
  decide

/-- The block handler accepts the child of the raw checkpoint-sync state. -/
theorem child_import_accepted :
    (on_block cfg ext (on_tick cfg run.genesis_store 13) childBlock).isSome = true := by
  decide

/-- A strict confirmation is later absent from the honest head. This tests
executable behavior, and does not claim satisfaction of the safety bundle. -/
theorem checkpoint_sync_filter_counterexample :
    anchorState.slot = anchorCheckpoint.epoch * cfg.slots_per_epoch ∧
    anchorState.current_justified_checkpoint.epoch < anchorCheckpoint.epoch ∧
    anchorState.finalized_checkpoint.epoch < anchorCheckpoint.epoch ∧
    run.confirmed cfg ext 0 0 = anchorRoot ∧
    run.confirmed cfg ext 0 2 = childRoot ∧
    childRoot ≠ anchorRoot ∧
    run.slot_at cfg 2 + 1 ≤ run.slot_at cfg 8 ∧
    run.WithinHorizon cfg 8 ∧
    (get_head cfg (run.store cfg ext 0 8)).root = anchorRoot ∧
    get_filtered_block_tree cfg (run.store cfg ext 0 8) = [] ∧
    is_ancestor (run.store cfg ext 0 8)
      (get_head cfg (run.store cfg ext 0 8))
      (get_node_for_root (run.confirmed cfg ext 0 2)) = false := by
  simp only [Execution.WithinHorizon]
  decide

/-- The age comparison changes at the boundary; the global checkpoint and
raw unrealized source do not change. -/
theorem raw_source_filter_boundary :
    (run.store cfg ext 0 7).justified_checkpoint = anchorCheckpoint ∧
    (run.store cfg ext 0 8).justified_checkpoint = anchorCheckpoint ∧
    get_voting_source cfg (run.store cfg ext 0 7) childRoot = oldCheckpoint ∧
    get_voting_source cfg (run.store cfg ext 0 8) childRoot = oldCheckpoint ∧
    oldCheckpoint.epoch + 2 ≥ get_current_store_epoch cfg (run.store cfg ext 0 7) ∧
    oldCheckpoint.epoch + 2 < get_current_store_epoch cfg (run.store cfg ext 0 8) ∧
    anchorCheckpoint.epoch + 2 ≥ get_current_store_epoch cfg (run.store cfg ext 0 8) := by
  decide

/-- Raising the old source to the anchor epoch changes the actual head.
This transformation is not applied to the run or to any executable function. -/
theorem normalized_source_changes_head :
    (get_head cfg
      { run.store cfg ext 0 8 with
        unrealized_justifications := fun r =>
          let c := (run.store cfg ext 0 8).unrealized_justifications r
          if c.epoch ≤ anchorCheckpoint.epoch then anchorCheckpoint else c }).root = childRoot := by
  decide

end FastConfirmation.Spec.CheckpointSyncFilterWitness

end
