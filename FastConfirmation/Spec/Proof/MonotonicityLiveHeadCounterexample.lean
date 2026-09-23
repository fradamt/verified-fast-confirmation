module
public import FastConfirmation.Spec.Proof.AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample

@[expose] public section

/-!
# A one-slot head ancestry obstruction

The live economic bounds are total-stake bounds. They do not force one slot's
honest committee weight to exceed the proposer boost. This executable store
has a delivered honest vote for a slot-two block, but a newly boosted sibling
is the head at slot three. The configuration retains the accepted 25 percent
confirmation threshold and meets both live arithmetic margins with zero
non-honest stake.
-/

namespace FastConfirmation.Spec
namespace MonotonicityLiveHeadCounterexample

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

open AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample

def boostedConfig : Config :=
  { witnessConfig with proposer_score_boost := 140 }

def deliveredStore : Store WitnessRoot :=
  actorPrefix.store witnessConfig witnessExternals

/-- At slot three the assigned honest validator votes for its boosted head.
This changes only the suffix after the head-divergence call. -/
def boostedVote3 : Attestation WitnessRoot :=
  { vote3 with data := { vote3.data with beacon_block_root := siblingRoot } }

def boostedSchedule (w : ValidatorIndex) (n : ℕ) : List (Event WitnessRoot) :=
  if n = 4 then [.attestation boostedVote3 false]
  else witnessSchedule w n

def boostedVote (v : ValidatorIndex) (s : Slot) :
    Option (ℕ × Attestation WitnessRoot) :=
  if v = 3 ∧ s = 3 then some (3, boostedVote3)
  else witnessVote v s

def boostedExecution : Execution WitnessRoot :=
  { witnessExecution with schedule := boostedSchedule, vote := boostedVote }

/-- The accepted trajectory needs the trusted anchor's explicit state
commitment. This field is erased by the executable fork-choice projection. -/
def boostedExternals : Externals WitnessRoot :=
  { witnessExternals with
    AnchorCommitsToState :=
      fun block state => block = anchorSignedBlock.message ∧ state = anchorState
    is_valid_indexed_attestation := fun state a =>
      decide (state.validators ≠ [] ∧
        (a = vote0 ∨ a = vote1 ∨ a = vote2 ∨ a = boostedVote3)) }

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
/-- The actual fork-choice computation can choose a current-slot sibling
despite the completed delivery of the earlier slot's honest vote. -/
theorem delivered_honest_slot_block_off_head :
    candidateRoot ∈ deliveredStore.block_roots ∧
    (deliveredStore.blocks candidateRoot).slot = 2 ∧
    candidateSignedBlock.message.proposer_index ∈ witnessExecution.honest ∧
    deliveredStore.latest_messages 2 =
      some ⟨2, candidateRoot, false⟩ ∧
    deliveredStore.proposer_boost_root = siblingRoot ∧
    get_current_slot boostedConfig deliveredStore = 3 ∧
    get_total_active_balance boostedConfig
      (deliveredStore.checkpoint_states deliveredStore.justified_checkpoint) = 400 ∧
    get_attestation_score boostedConfig deliveredStore
      (get_node_for_root candidateRoot)
      (deliveredStore.checkpoint_states deliveredStore.justified_checkpoint) = 100 ∧
    compute_proposer_score boostedConfig
      (deliveredStore.checkpoint_states deliveredStore.justified_checkpoint) = 140 ∧
    (get_head boostedConfig deliveredStore).root = siblingRoot ∧
    is_ancestor deliveredStore (get_head boostedConfig deliveredStore)
      (get_node_for_root candidateRoot) = false ∧
    4 * 0 + 140 < 400 ∧
    2 * 0 + 2 * (400 / 100 * 25) + 140 < 400 := by
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
/-- The same failure occurs in the completed whole-second execution store,
after the slot-two vote has been delivered and processed. -/
theorem completed_boundary_head_off_live_block :
    witnessExecution.IsFCRCallAt boostedConfig witnessExternals 0 2 ∧
    candidateRoot ∈
      (witnessExecution.store boostedConfig witnessExternals 0 3).block_roots ∧
    (get_head boostedConfig
      (witnessExecution.store boostedConfig witnessExternals 0 3)).root =
        siblingRoot ∧
    is_ancestor
      (witnessExecution.store boostedConfig witnessExternals 0 3)
      (get_head boostedConfig
        (witnessExecution.store boostedConfig witnessExternals 0 3))
      (get_node_for_root candidateRoot) = false := by
  constructor
  · change get_current_slot boostedConfig
        (witnessExecution.store boostedConfig witnessExternals 0 2) <
      get_current_slot boostedConfig
        (witnessExecution.store boostedConfig witnessExternals 0 3)
    decide
  · decide

/-- The corrected slot-three vote changes no scheduled event through the
completed call where the counterexample occurs. -/
theorem boosted_completed_store_eq :
    boostedExecution.store boostedConfig witnessExternals 0 3 =
      witnessExecution.store boostedConfig witnessExternals 0 3 := by
  rfl

/-- The vote after the divergent call follows the actual fork-choice head. -/
theorem boosted_slot_three_vote_is_head :
    boostedExecution.vote 3 3 =
      some (3, honest_attestation boostedConfig witnessExternals
        (boostedExecution.store boostedConfig witnessExternals 3 3) 3 0 3) := by
  decide

theorem boosted_completed_boundary_head_off_live_block :
    boostedExecution.IsFCRCallAt boostedConfig witnessExternals 0 2 ∧
    candidateRoot ∈
      (boostedExecution.store boostedConfig witnessExternals 0 3).block_roots ∧
    is_ancestor
      (boostedExecution.store boostedConfig witnessExternals 0 3)
      (get_head boostedConfig
        (boostedExecution.store boostedConfig witnessExternals 0 3))
      (get_node_for_root candidateRoot) = false := by
  constructor
  · simpa only [Execution.IsFCRCallAt, boosted_completed_store_eq] using
      completed_boundary_head_off_live_block.1
  constructor
  · simpa only [boosted_completed_store_eq] using
      completed_boundary_head_off_live_block.2.1
  · simpa only [boosted_completed_store_eq] using
      completed_boundary_head_off_live_block.2.2.2

private theorem boosted_store_eq_before_four (w : ValidatorIndex)
    (k : ℕ) (hk : k < 4) :
    boostedExecution.store boostedConfig witnessExternals w k =
      witnessExecution.store boostedConfig witnessExternals w k := by
  interval_cases k <;> rfl

private theorem boosted_vote_eq_before_three (i : ValidatorIndex)
    (t : Slot) (ht : t < 3) :
    boostedExecution.vote i t = witnessExecution.vote i t := by
  have htne : t ≠ 3 := Nat.ne_of_lt ht
  simp [boostedExecution, boostedVote, witnessExecution, htne]

private theorem old_vote_time_eq_slot {i t k a}
    (hvote : witnessExecution.vote i t = some (k, a)) : k = t := by
  simp only [witnessExecution, witnessVote] at hvote
  split_ifs at hvote <;> simp_all

private theorem old_blockAt_to_boosted {r : WitnessRoot}
    {b : BeaconBlock WitnessRoot}
    (h : witnessExecution.BlockAt r b) : boostedExecution.BlockAt r b := by
  rcases h with hgen | ⟨w, k, sb, hev, hr, hb⟩
  · exact Or.inl hgen
  · right
    refine ⟨w, k, sb, ?_, hr, hb⟩
    have hk : k ≠ 4 := by
      intro heq
      subst k
      simp [witnessExecution, witnessSchedule] at hev
    simpa [boostedExecution, boostedSchedule, hk] using hev

private theorem hot_slot_at_eq (n : ℕ) :
    witnessExecution.slot_at boostedConfig n = n := by
  norm_num [Execution.slot_at, Execution.time_at, witnessExecution,
    boostedConfig, witnessConfig, anchorState, stateAt,
    anchorSignedBlock, get_forkchoice_store, GENESIS_SLOT]

private theorem boosted_slot_at_eq (n : ℕ) :
    boostedExecution.slot_at boostedConfig n = n :=
  hot_slot_at_eq n

private theorem hot_slot_start_eq (s : Slot) :
    witnessExecution.slot_start boostedConfig s = s := by
  norm_num [Execution.slot_start, witnessExecution, anchorState, stateAt,
    anchorSignedBlock, boostedConfig, witnessConfig, get_forkchoice_store]

private theorem hot_store_node_independent (w w' : ValidatorIndex) (n : ℕ) :
    witnessExecution.store boostedConfig witnessExternals w n =
      witnessExecution.store boostedConfig witnessExternals w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Execution.store]
      rw [ih]
      rfl

/-- All live fields hold through the call at second three. The FFG timing
field has no completed epoch in this short interval. -/
theorem live_prefix :
    MonotonicityLiveAssumptions boostedConfig witnessExternals
      witnessExecution 0 1 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs0 hsm
    have hs : s < 3 := by
      simpa only [hot_slot_at_eq] using hsm
    interval_cases s
    · refine ⟨anchorRoot, anchorSignedBlock.message, ?_, rfl, by decide, ?_, ?_⟩
      · left
        decide
      · intro w hw
        rw [hot_slot_start_eq, hot_store_node_independent w 0]
        decide
      · intro i hi t k a hst htm hvote
        have ht : t < 3 := by
          simpa only [hot_slot_at_eq] using htm
        interval_cases t <;>
          simp [witnessExecution, witnessVote] at hvote <;>
          rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
    · refine ⟨parentRoot, parentSignedBlock.message, ?_, rfl, by decide, ?_, ?_⟩
      · right
        exact ⟨0, 1, parentSignedBlock,
          by simp [witnessExecution, witnessSchedule], rfl, rfl⟩
      · intro w hw
        rw [hot_slot_start_eq, hot_store_node_independent w 0]
        decide
      · intro i hi t k a hst htm hvote
        have ht : t < 3 := by
          simpa only [hot_slot_at_eq] using htm
        interval_cases t <;>
          simp [witnessExecution, witnessVote] at hvote <;>
          rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
    · refine ⟨candidateRoot, candidateSignedBlock.message, ?_, rfl, by decide, ?_, ?_⟩
      · right
        exact ⟨0, 2, candidateSignedBlock,
          by simp [witnessExecution, witnessSchedule], rfl, rfl⟩
      · intro w hw
        rw [hot_slot_start_eq, hot_store_node_independent w 0]
        decide
      · intro i hi t k a hst htm hvote
        have ht : t < 3 := by
          simpa only [hot_slot_at_eq] using htm
        interval_cases t <;>
          simp [witnessExecution, witnessVote] at hvote <;>
          rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
  · intro i hi s k a hstart hend hvote
    have hs : s < 3 := by
      simpa only [hot_slot_at_eq] using hend
    have hs1 : 1 ≤ s := by
      simpa only [hot_slot_at_eq] using hstart
    interval_cases s <;>
      simp [witnessExecution, witnessVote] at hvote <;>
      rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
  · decide
  · decide
  · intro e he0 heDone
    have : 4 ≤ 3 := by
      calc
        4 ≤ compute_start_slot_at_epoch boostedConfig (e + 1) := by
          simp [compute_start_slot_at_epoch, boostedConfig, witnessConfig]
        _ ≤ witnessExecution.slot_at boostedConfig 3 := heDone
        _ = 3 := by decide
    omega

/-- Correcting the following slot's honest vote preserves the five live
fields and the completed counterexample call. -/
theorem boosted_live_prefix :
    MonotonicityLiveAssumptions boostedConfig witnessExternals
      boostedExecution 0 1 3 := by
  obtain ⟨hblocks, hvotes, hpaper, hmargin, _⟩ := live_prefix
  refine ⟨?_, ?_, hpaper, hmargin, ?_⟩
  · intro s hs0 hsm
    obtain ⟨r, b, hblock, hslot, hprop, hdelivery, hsupport⟩ :=
      hblocks s hs0 hsm
    refine ⟨r, b, old_blockAt_to_boosted hblock, hslot, hprop, ?_, ?_⟩
    · intro w hw
      have hs : s < 3 := by simpa only [boosted_slot_at_eq] using hsm
      change r ∈ (boostedExecution.store boostedConfig witnessExternals w
        (witnessExecution.slot_start boostedConfig (s + 1))).block_roots
      rw [hot_slot_start_eq,
        boosted_store_eq_before_four w (s + 1)
          (Nat.add_lt_add_right hs 1)]
      simpa only [hot_slot_start_eq] using hdelivery w hw
    · intro i hi t k a hst htm hvote
      have ht : t < 3 := by simpa only [boosted_slot_at_eq] using htm
      have hvoteOld : witnessExecution.vote i t = some (k, a) := by
        rw [← boosted_vote_eq_before_three i t ht]
        exact hvote
      have hk : k < 4 := by
        rw [old_vote_time_eq_slot hvoteOld]
        exact ht.trans (by decide)
      have h := hsupport i hi t k a hst htm hvoteOld
      simpa only [boosted_store_eq_before_four i k hk] using h
  · intro i hi s k a hstart hend hvote
    have hs : s < 3 := by simpa only [boosted_slot_at_eq] using hend
    have hvoteOld : witnessExecution.vote i s = some (k, a) := by
      rw [← boosted_vote_eq_before_three i s hs]
      exact hvote
    have hk : k < 4 := by
      rw [old_vote_time_eq_slot hvoteOld]
      exact hs.trans (by decide)
    have h := hvotes i hi s k a hstart hend hvoteOld
    simpa only [boosted_store_eq_before_four i k hk,
      boosted_store_eq_before_four 0 1 (by decide)] using h
  · intro e he0 heDone
    have : 4 ≤ 3 := by
      calc
        4 ≤ compute_start_slot_at_epoch boostedConfig (e + 1) := by
          simp [compute_start_slot_at_epoch, boostedConfig, witnessConfig]
        _ ≤ boostedExecution.slot_at boostedConfig 3 := heDone
        _ = 3 := by decide
    omega

/-- The accepted anchor commitment is true, and validation recognizes the
revised honest vote while rejecting its superseded version. -/
theorem committed_anchor_and_vote_validation :
    boostedExternals.AnchorCommitsToState
      anchorSignedBlock.message anchorState ∧
    boostedExternals.is_valid_indexed_attestation anchorState vote0 = true ∧
    boostedExternals.is_valid_indexed_attestation anchorState vote1 = true ∧
    boostedExternals.is_valid_indexed_attestation anchorState vote2 = true ∧
    boostedExternals.is_valid_indexed_attestation anchorState boostedVote3 = true ∧
    boostedExternals.is_valid_indexed_attestation anchorState vote3 = false := by
  constructor
  · exact ⟨rfl, rfl⟩
  · decide

/-- The accepted-compatible validation choice retains the same completed
call failure. -/
theorem committed_actual_head_off_live_block :
    boostedExecution.IsFCRCallAt boostedConfig boostedExternals 0 2 ∧
    candidateRoot ∈
      (boostedExecution.store boostedConfig boostedExternals 0 3).block_roots ∧
    is_ancestor
      (boostedExecution.store boostedConfig boostedExternals 0 3)
      (get_head boostedConfig
        (boostedExecution.store boostedConfig boostedExternals 0 3))
      (get_node_for_root candidateRoot) = false := by
  constructor
  · change get_current_slot boostedConfig
        (boostedExecution.store boostedConfig boostedExternals 0 2) <
      get_current_slot boostedConfig
        (boostedExecution.store boostedConfig boostedExternals 0 3)
    decide
  · decide

private theorem committed_slot_start_eq (s : Slot) :
    boostedExecution.slot_start boostedConfig s = s :=
  hot_slot_start_eq s

private theorem committed_store_node_independent
    (w w' : ValidatorIndex) (n : ℕ) :
    boostedExecution.store boostedConfig boostedExternals w n =
      boostedExecution.store boostedConfig boostedExternals w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Execution.store]
      rw [ih]
      rfl

/-- The complete five-field live premise holds with the anchor commitment
and revised attestation validator used by the accepted-compatible execution. -/
theorem committed_live_prefix :
    MonotonicityLiveAssumptions boostedConfig boostedExternals
      boostedExecution 0 1 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs0 hsm
    have hs : s < 3 := by simpa only [boosted_slot_at_eq] using hsm
    interval_cases s
    · refine ⟨anchorRoot, anchorSignedBlock.message, ?_, rfl, by decide, ?_, ?_⟩
      · left; decide
      · intro w hw
        rw [committed_slot_start_eq, committed_store_node_independent w 0]
        decide
      · intro i hi t k a hst htm hvote
        have ht : t < 3 := by simpa only [boosted_slot_at_eq] using htm
        interval_cases t <;>
          simp [boostedExecution, boostedVote, witnessVote] at hvote <;>
          rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
    · refine ⟨parentRoot, parentSignedBlock.message, ?_, rfl, by decide, ?_, ?_⟩
      · right
        exact ⟨0, 1, parentSignedBlock,
          by simp [boostedExecution, boostedSchedule, witnessSchedule], rfl, rfl⟩
      · intro w hw
        rw [committed_slot_start_eq, committed_store_node_independent w 0]
        decide
      · intro i hi t k a hst htm hvote
        have ht : t < 3 := by simpa only [boosted_slot_at_eq] using htm
        interval_cases t <;>
          simp [boostedExecution, boostedVote, witnessVote] at hvote <;>
          rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
    · refine ⟨candidateRoot, candidateSignedBlock.message, ?_, rfl, by decide, ?_, ?_⟩
      · right
        exact ⟨0, 2, candidateSignedBlock,
          by simp [boostedExecution, boostedSchedule, witnessSchedule], rfl, rfl⟩
      · intro w hw
        rw [committed_slot_start_eq, committed_store_node_independent w 0]
        decide
      · intro i hi t k a hst htm hvote
        have ht : t < 3 := by simpa only [boosted_slot_at_eq] using htm
        interval_cases t <;>
          simp [boostedExecution, boostedVote, witnessVote] at hvote <;>
          rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
  · intro i hi s k a hstart hend hvote
    have hs : s < 3 := by simpa only [boosted_slot_at_eq] using hend
    have hs1 : 1 ≤ s := by simpa only [boosted_slot_at_eq] using hstart
    interval_cases s <;>
      simp [boostedExecution, boostedVote, witnessVote] at hvote <;>
      rcases hvote with ⟨rfl, rfl, rfl⟩ <;> decide
  · decide
  · decide
  · intro e he0 heDone
    have : 4 ≤ 3 := by
      calc
        4 ≤ compute_start_slot_at_epoch boostedConfig (e + 1) := by
          simp [compute_start_slot_at_epoch, boostedConfig, witnessConfig]
        _ ≤ boostedExecution.slot_at boostedConfig 3 := heDone
        _ = 3 := by decide
    omega

/-- Kernel-checked live-field and actual-call obstruction to the proposed
head-extends-every-honest-block link. -/
theorem live_head_link_false :
    MonotonicityLiveAssumptions boostedConfig boostedExternals
      boostedExecution 0 1 3 ∧
    boostedExecution.IsFCRCallAt boostedConfig boostedExternals 0 2 ∧
    candidateRoot ∈
      (boostedExecution.store boostedConfig boostedExternals 0 3).block_roots ∧
    is_ancestor
      (boostedExecution.store boostedConfig boostedExternals 0 3)
      (get_head boostedConfig
        (boostedExecution.store boostedConfig boostedExternals 0 3))
      (get_node_for_root candidateRoot) = false := by
  exact ⟨committed_live_prefix,
    committed_actual_head_off_live_block.1,
    committed_actual_head_off_live_block.2.1,
    committed_actual_head_off_live_block.2.2⟩

end MonotonicityLiveHeadCounterexample
end FastConfirmation.Spec

end
