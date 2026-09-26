module
public import FastConfirmationProofs.Checkpoints.VotePathCheckpointCompatibility

@[expose] public section

/-! A finite execution tests vote-path delivery at a skipped checkpoint boundary.
This execution violates the refined deadline relay: Y is absent at 144,
but the finalized guard accepts its parent checkpoint at 143. It is therefore
not a counterexample under that relay. The full public premise bundle is not
certified in this module. -/

open FastConfirmation.Spec

namespace FastConfirmation.Spec.DeadlineVotePathCandidate

abbrev R := Fin 6
abbrev G : R := 1
abbrev X : R := 2
abbrev C : R := 3
abbrev D : R := 4
abbrev Y : R := 5

def cfg : Config :=
  { mainnet_config with
    slots_per_epoch := 4
    slots_per_epoch_pos := by decide
    proposer_score_boost := 400
    committee_weight_estimation_adjustment_factor := 1000
    effective_balance_increment := 100
    effective_balance_increment_pos := by decide
    hundred_dvd_effective_balance_increment := by decide }

def checkpoint (e : ℕ) (r : R) : Checkpoint R := ⟨e, r⟩
def g0 : Checkpoint R := checkpoint 0 G
def g1 : Checkpoint R := checkpoint 1 G
def c2 : Checkpoint R := checkpoint 2 C

def validator : Validator :=
  { effective_balance := 100, slashed := false, activation_epoch := 0,
    exit_epoch := FAR_FUTURE_EPOCH }

def initial : BeaconState R :=
  { genesis_time := 0, slot := 0, validators := List.replicate 16 validator,
    current_justified_checkpoint := g0, finalized_checkpoint := g0 }

def anchor : SignedBeaconBlock R :=
  { root := G, message := { slot := 0, parent_root := 0 } }

def committee (s : ℕ) : List ValidatorIndex :=
  (List.range 4).map (fun j => 4 * (s % 4) + j)

def data (s : ℕ) (head : R) (source target : Checkpoint R) : AttestationData R :=
  { slot := s, index := 0, beacon_block_root := head, source := source, target := target }

def signed (s i : ℕ) (head : R) (source target : Checkpoint R) : Attestation R :=
  { attesting_indices := [i], data := data s head source target }

def genesisVotes (s : ℕ) : List (Attestation R) :=
  (committee s).map (fun i => signed s i G g0 (checkpoint (s / 4) G))

def carrierVotes (s : ℕ) : List (Attestation R) :=
  (committee s).map (fun i => signed s i C g1 c2)

def xBlock : SignedBeaconBlock R :=
  { root := X
    message :=
      { slot := 4
        parent_root := G
        block_hash := 0
        parent_block_hash := 1 } }

def cBlock : SignedBeaconBlock R :=
  { root := C
    message :=
      { slot := 7
        parent_root := G
        block_hash := 0
        parent_block_hash := 1
        attestations := genesisVotes 4 ++ genesisVotes 5 ++ genesisVotes 6 } }

def dBlock : SignedBeaconBlock R :=
  { root := D
    message :=
      { slot := 11
        parent_root := C
        block_hash := 0
        parent_block_hash := 1
        attestations := carrierVotes 8 ++ carrierVotes 9 ++ carrierVotes 10 } }

def yBlock : SignedBeaconBlock R :=
  { root := Y
    message :=
      { slot := 11
        parent_root := X
        block_hash := 0
        parent_block_hash := 1 } }

def pull (st : BeaconState R) : BeaconState R :=
  if st.slot = 7 then {st with current_justified_checkpoint := g1}
  else if st.slot = 11 ∧ st.current_justified_checkpoint = g1 then
    {st with current_justified_checkpoint := c2, finalized_checkpoint := g1}
  else if st.current_justified_checkpoint.epoch ≤ st.slot / 4 then st
  else {st with current_justified_checkpoint := g0}

def process (st : BeaconState R) (s : ℕ) : BeaconState R :=
  { (if st.slot / 4 < s / 4 then pull st else st) with slot := s }

-- The schedule starts from the genuine genesis constructor.
def votes (s : ℕ) : List (Attestation R) :=
  if s < 8 then genesisVotes s
  else if s < 11 then carrierVotes s
  else if s = 11 then
    (committee s).map (fun i => if i = 12 then signed s i Y g0 (checkpoint 2 X)
      else signed s i D g1 c2)
  else (committee s).map (fun i => signed s i D c2 (checkpoint (s / 4) D))

def ext : BeaconFunctionInterface R :=
  { get_beacon_committee := fun _ s index => if index = 0 then committee s else []
    get_committee_count_per_slot := fun _ _ => 1
    process_slots := process
    state_transition := fun st b =>
      let post := process st b.message.slot
      if st.slot < b.message.slot ∧ b ∈ [xBlock, cBlock, dBlock, yBlock] ∧
          post.current_justified_checkpoint.epoch ≤ b.message.slot / 4 ∧
          post.finalized_checkpoint.epoch ≤ b.message.slot / 4 then some post else none
    process_justification_and_finalization := pull
    is_valid_indexed_attestation := fun st a =>
      decide (st.validators = initial.validators ∧ a.data.slot < 16 ∧
        a ∈ votes a.data.slot)
    AnchorCommitsToState := fun b st => b = anchor.message ∧ st = initial }

def schedule (v n : ℕ) : List (Event R) :=
  let blocks : List (Event R) :=
    if n = 96 then [.block cBlock, .block xBlock]
    else if n = 132 then (if v = 12 then [.block yBlock] else [.block dBlock])
    else if n = 144 then (if v = 12 then [.block dBlock] else [.block yBlock])
    else []
  let attestations := if n % 12 = 0 ∧ 0 < n ∧ n ≤ 192 then
    (votes (n / 12 - 1)).map (fun a => Event.attestation a false) else []
  let included := if n = 96 then
      (genesisVotes 4 ++ genesisVotes 5 ++ genesisVotes 6).map
        (fun a => Event.attestation a true)
    else if n = 132 ∧ v ≠ 12 then
      (carrierVotes 8 ++ carrierVotes 9 ++ carrierVotes 10).map
        (fun a => Event.attestation a true)
    else []
  blocks ++ attestations ++ included

def execution : Execution R :=
  { verification_horizon := 4,
    genesis_store := get_forkchoice_store cfg initial anchor,
    schedule := schedule,
    honest := Finset.range 16,
    committee := fun s => (committee s).toFinset,
    vote := fun i s => if i ∈ committee s ∧ s < 16 then
      some (12 * s, if s < 8 then signed s i G g0 (checkpoint (s / 4) G)
        else if s < 11 then signed s i C g1 c2
        else if s = 11 then if i = 12 then signed s i Y g0 (checkpoint 2 X)
          else signed s i D g1 c2
        else signed s i D c2 (checkpoint (s / 4) D))
      else none }

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Evaluate the finite scheduled prefix in the Lean kernel.
/-- The source head at the final slot of epoch two is the new fork block. -/
theorem source_head :
    (get_head cfg (execution.store cfg ext 12 132)).root = Y := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Check every committee assignment in the four-epoch finite prefix.
/-- Every recorded honest vote uses the actual head and validator construction. -/
theorem honest_votes_match :
    ∀ (s i : Fin 16), i.val ∈ committee s.val →
      execution.vote i.val s.val = some (12 * s.val,
        honest_attestation cfg ext (execution.store cfg ext i.val (12 * s.val))
          s.val 0 i.val) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Check every in-horizon pair of committee endpoints.
/-- The concrete committee estimate bounds every in-horizon span. -/
theorem committee_estimates :
    ∀ (a b : Fin 16), execution.weight (execution.span_committee a.val b.val) ≤
      estimate_committee_weight_between_slots cfg (execution.total_active cfg) a.val b.val := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- The remaining horizon has only 48 seconds after the delivery boundary.
/-- The receiver's finalized guard rejects the source block for the rest of the horizon. -/
theorem later_guard :
    ∀ (k : Fin 192), 144 ≤ k.val →
      (execution.store cfg ext 0 k.val).finalized_checkpoint.root ≠
        get_checkpoint_block cfg (execution.store cfg ext 0 k.val)
          ((execution.store cfg ext 12 132).blocks Y).parent_root
          (execution.store cfg ext 0 k.val).finalized_checkpoint.epoch := by
  decide

private theorem finite_horizon_bound (k : ℕ)
    (h : k * 1000 / 12000 / 4 < 4) : k < 192 := by omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Evaluate only the two finite endpoint stores; the later guard is proved above.
/-- The rejected head satisfies exactly the finalized-only permanent exclusion. -/
theorem permanently_excluded :
    PermanentBlockExclusion cfg ext execution 12 132 Y 0 144 := by
  refine ⟨by decide, by decide, ?_⟩
  intro k h144 hH
  have hk : k < 192 := by
    apply finite_horizon_bound k
    simpa only [compute_epoch_at_slot, Execution.slot_at, Execution.time_at,
      execution, cfg, initial, anchor, get_forkchoice_store, GENESIS_SLOT,
      mainnet_config, Nat.zero_mul, Nat.mul_zero, Nat.zero_div, Nat.add_zero,
      Nat.zero_add, Nat.sub_zero] using hH.2.2
  exact Or.inr (later_guard ⟨k, hk⟩ h144)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- The source walk has one parent step, from slot 11 to slot 4.
/-- The honest vote has the required known source walk to its target epoch. -/
theorem source_walk : WalkKnown (execution.store cfg ext 12 132) 8 Y := by
  apply WalkKnown.step (by decide) (by decide)
  exact WalkKnown.stop (by decide) (by decide)

/-- The old boundary-store version of G4 fails on this execution.
The refined G4 uses second 143 and holds here, as proved below. This theorem
does not assert that the full public premise record is inhabited. -/
theorem vote_path_not_admissible :
    ¬ VotePathAdmissible cfg ext execution 12 132 0 144 8 Y := by
  intro h
  cases h with
  | stop _ hnot _ => exact hnot permanently_excluded
  | step _ hnot _ _ => exact hnot permanently_excluded

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- The finalized guard still permits Y at the last second of its source slot. -/
theorem not_excluded_before_tick :
    ¬ PermanentBlockExclusion cfg ext execution 12 132 Y 0 143 := by
  apply execution.permanentBlockExclusion_false_of_finalized_guards cfg ext
  · unfold Execution.WithinHorizon; decide
  · decide
  · decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- The candidate's path passes the refined G4 exclusion point. -/
theorem vote_path_admissible_before_tick :
    VotePathAdmissible cfg ext execution 12 132 0 143 8 Y := by
  apply VotePathAdmissible.step (by decide) not_excluded_before_tick (by decide)
  apply VotePathAdmissible.stop (by decide) ?_ (by decide)
  intro hexcluded
  exact hexcluded.1 (by decide)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- The refined block relay rules out the skipped-boundary execution. -/
theorem violates_refined_deadline_block_relay :
    ¬ DeadlineBlockRelay cfg ext execution := by
  intro h
  have outcome := h 12 (by decide) 132 Y (by unfold Execution.WithinHorizon; decide) (by decide)
    (by decide) 0 (by decide) 144 (by unfold Execution.WithinHorizon; decide) (by decide) (by decide)
  rcases outcome with hknown | hexcluded
  · exact (by decide : Y ∉ (execution.store cfg ext 0 144).block_roots) hknown
  · exact not_excluded_before_tick hexcluded

end FastConfirmation.Spec.DeadlineVotePathCandidate

end
