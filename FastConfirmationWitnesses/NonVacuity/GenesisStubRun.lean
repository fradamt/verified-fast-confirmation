module
public import Mathlib.Tactic
public import FastConfirmationProofs.Execution.Trajectory.PayloadPersistence
public import FastConfirmationProofs.Safety.ConfirmedCacheSafety

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Base execution for the genesis-stub non-vacuity witness

This file is the horizon-four execution of `ScheduledRun` with one change: the
anchor state is a real Phase0 genesis state.  Its current justified and
finalized checkpoints are the stub `stubCheckpoint = (GENESIS_EPOCH, junkRoot)`,
whose root is not the anchor root.  Descendant states and eager processing
before the first justification keep the stub, and honest votes before slot
eight carry it as their source.  The trusted store anchor is still
`anchorCheckpoint = (0, anchorRoot)`.

This file proves the operational laws of a finite, horizon-four execution.
The accepted FFG semantics and Paper A3.2 witness are kept in
a follow-on module; all declarations here are intentionally public so that
the semantic layer can reuse the exact executable trace.

The construction has four honest validators of equal weight, four slots per
epoch, and four roots: a dangling parent, the trusted anchor, a slot-one
child, and a slot-seven carrier.  The last in-horizon vote (slot fifteen) is
delivered at second sixteen, positively exercising the one-slot delivery
lookahead without pretending that second sixteen is itself in the horizon.
-/

namespace FastConfirmation.Spec
namespace GenesisStubBase

abbrev WitnessRoot := Fin 4

def junkRoot : WitnessRoot := 0
def anchorRoot : WitnessRoot := 1
def childRoot : WitnessRoot := 2
def carrierRoot : WitnessRoot := 3

def witnessConfig : Config where
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

def anchorCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 0, root := anchorRoot }

/-- The Phase0 genesis stub: `Checkpoint(GENESIS_EPOCH, ZERO_HASH)` in the
genesis state.  Its root is the anchor block's dangling parent root. -/
def stubCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 0, root := junkRoot }

def childEpochOneCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 1, root := childRoot }

def carrierEpochTwoCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 2, root := carrierRoot }

def carrierEpochThreeCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 3, root := carrierRoot }

def witnessValidator : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH }

def stateAt (slot : Slot) (justified : Checkpoint WitnessRoot) :
    BeaconState WitnessRoot :=
  { genesis_time := 0
    slot := slot
    validators :=
      [witnessValidator, witnessValidator, witnessValidator, witnessValidator]
    current_justified_checkpoint := justified
    finalized_checkpoint := stubCheckpoint }

def anchorState : BeaconState WitnessRoot := stateAt 0 stubCheckpoint
def childState : BeaconState WitnessRoot := stateAt 1 stubCheckpoint
def carrierState : BeaconState WitnessRoot := stateAt 7 stubCheckpoint

def anchorSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 0, parent_root := junkRoot }
    root := anchorRoot }

def childSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 1, parent_root := anchorRoot }
    root := childRoot }

/-! ## Ground honest votes -/

def voteData (slot : Slot) : AttestationData WitnessRoot :=
  if slot = 0 then
    { slot := slot, index := 0, beacon_block_root := anchorRoot
      source := stubCheckpoint, target := anchorCheckpoint }
  else if slot < 4 then
    { slot := slot, index := 0, beacon_block_root := childRoot
      source := stubCheckpoint, target := anchorCheckpoint }
  else if slot < 7 then
    { slot := slot, index := 0, beacon_block_root := childRoot
      source := stubCheckpoint, target := childEpochOneCheckpoint }
  else if slot = 7 then
    { slot := slot, index := 0, beacon_block_root := carrierRoot
      source := stubCheckpoint, target := childEpochOneCheckpoint }
  else if slot < 12 then
    { slot := slot, index := 0, beacon_block_root := carrierRoot
      source := childEpochOneCheckpoint, target := carrierEpochTwoCheckpoint }
  else
    { slot := slot, index := 0, beacon_block_root := carrierRoot
      source := childEpochOneCheckpoint, target := carrierEpochThreeCheckpoint }

def vote (slot : Slot) : Attestation WitnessRoot :=
  { attesting_indices := [slot % 4], data := voteData slot }

def vote0 := vote 0
def vote1 := vote 1
def vote2 := vote 2
def vote3 := vote 3
def vote4 := vote 4
def vote5 := vote 5
def vote6 := vote 6

/-- The carrier contains the three ordered Phase0 FFG votes. -/
def carrierSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 7, parent_root := childRoot, attestations := [vote4, vote5, vote6] }
    root := carrierRoot }
def vote7 := vote 7
def vote8 := vote 8
def vote9 := vote 9
def vote10 := vote 10
def vote11 := vote 11
def vote12 := vote 12
def vote13 := vote 13
def vote14 := vote 14
def vote15 := vote 15

def groundVotes : List (Attestation WitnessRoot) :=
  [vote0, vote1, vote2, vote3, vote4, vote5,
    vote6, vote7, vote8, vote9, vote10, vote11,
    vote12, vote13, vote14, vote15]

/-! ## Phase0-coherent external functions -/

/-- Eager epoch processing at the carrier slot exposes the child
checkpoint.  Every other abstract input clamps to the genesis stub; this
keeps the external total while making the two phase0 laws transparent. -/
def witnessPJF (st : BeaconState WitnessRoot) : BeaconState WitnessRoot :=
  if st.slot = 7 then
    { st with current_justified_checkpoint := childEpochOneCheckpoint }
  else { st with current_justified_checkpoint := stubCheckpoint }

/-- Empty-slot processing changes the realized source precisely when crossing
an epoch boundary, and then reads the eager PJF value of the input state. -/
def witnessProcessSlots (st : BeaconState WitnessRoot) (target : Slot) :
    BeaconState WitnessRoot :=
  if compute_epoch_at_slot witnessConfig st.slot <
      compute_epoch_at_slot witnessConfig target then
    { witnessPJF st with slot := target }
  else
    { st with slot := target }

/-- Decidable extensional equality for the deliberately non-`DecidableEq`
projected beacon-state container. -/
def SameProjectedState (a b : BeaconState WitnessRoot) : Prop :=
  a.genesis_time = b.genesis_time ∧
    a.slot = b.slot ∧
    a.validators = b.validators ∧
    a.current_justified_checkpoint = b.current_justified_checkpoint ∧
    a.finalized_checkpoint = b.finalized_checkpoint ∧
    a.beacon_committee_reads = b.beacon_committee_reads ∧
    a.committee_count_reads = b.committee_count_reads ∧
    a.source_identity = b.source_identity

instance (a b : BeaconState WitnessRoot) : Decidable (SameProjectedState a b) :=
  by
    unfold SameProjectedState
    infer_instance

theorem sameProjectedState_iff_eq {a b : BeaconState WitnessRoot} :
    SameProjectedState a b ↔ a = b := by
  constructor
  · rintro ⟨hgen, hslot, hvalidators, hj, hf, hcommittees, hcounts, hidentity⟩
    cases a
    cases b
    simp_all
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def witnessTransition (st : BeaconState WitnessRoot)
    (block : SignedBeaconBlock WitnessRoot) : Option (BeaconState WitnessRoot) :=
  if SameProjectedState st anchorState ∧ block = childSignedBlock then
    some childState
  else if SameProjectedState st childState ∧ block = carrierSignedBlock then
    some carrierState
  else none

def witnessExternals : BeaconFunctionInterface WitnessRoot where
  AnchorCommitsToState := fun block state =>
    block = anchorSignedBlock.message ∧ state = anchorState
  get_beacon_committee := fun _ slot _ => [slot % 4]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := witnessProcessSlots
  state_transition := witnessTransition
  process_justification_and_finalization := witnessPJF
  is_valid_indexed_attestation := fun state a =>
    decide (state.validators ≠ [] ∧ a ∈ groundVotes)

/-! ## Schedule and execution -/

/-- Symmetric schedule.  False copies implement ordinary gossip.  At second
seven the slot-six receipt precedes the carrier; the true copies after it are
the three attestations projected as carried by that block. -/
def witnessSchedule (_w : ValidatorIndex) (n : ℕ) :
    List (Event WitnessRoot) :=
  if n = 1 then [Event.block childSignedBlock, Event.attestation vote0 false]
  else if n = 7 then
    [Event.attestation vote6 false, Event.block carrierSignedBlock,
      Event.attestation vote4 true, Event.attestation vote5 true,
      Event.attestation vote6 true]
  else if 2 ≤ n ∧ n ≤ 16 then
    [Event.attestation (vote (n - 1)) false]
  else []

def witnessCommittee (slot : Slot) : Finset ValidatorIndex := {slot % 4}

def witnessVote (v : ValidatorIndex) (slot : Slot) :
    Option (ℕ × Attestation WitnessRoot) :=
  if slot < 16 ∧ v = slot % 4 then some (slot, vote slot) else none

def witnessExecution : Execution WitnessRoot where
  verification_horizon := 4
  genesis_store :=
    get_forkchoice_store witnessConfig anchorState anchorSignedBlock
  schedule := witnessSchedule
  honest := {0, 1, 2, 3}
  committee := witnessCommittee
  vote := witnessVote

def confirmingFcr : FastConfirmationStore WitnessRoot :=
  witnessExecution.fcrStoreAtCall witnessConfig witnessExternals 0 1

/-! ## Basic clock and finite classifiers -/

theorem time_at_eq (n : ℕ) : witnessExecution.time_at n = n := by
  norm_num [Execution.time_at, witnessExecution, anchorState, stateAt,
    anchorSignedBlock, witnessConfig, get_forkchoice_store]

theorem slot_at_eq (n : ℕ) :
    witnessExecution.slot_at witnessConfig n = n := by
  norm_num [Execution.slot_at, Execution.time_at, witnessExecution, anchorState,
    stateAt, anchorSignedBlock, witnessConfig, get_forkchoice_store,
    GENESIS_SLOT]

theorem slot_start_eq (s : Slot) :
    witnessExecution.slot_start witnessConfig s = s := by
  norm_num [Execution.slot_start, witnessExecution, anchorState, stateAt,
    anchorSignedBlock, witnessConfig, get_forkchoice_store]

theorem slot_lt_sixteen {s : Slot}
    (hs : witnessExecution.SlotWithinHorizon witnessConfig s) : s < 16 := by
  have hepoch := hs.2
  change s / 4 < 4 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)] at hepoch

theorem time_lt_sixteen {n : ℕ}
    (hn : witnessExecution.WithinHorizon witnessConfig n) : n < 16 := by
  have hepoch := hn.2.2
  rw [slot_at_eq] at hepoch
  change n / 4 < 4 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)] at hepoch

theorem time_within_of_lt_sixteen {n : ℕ} (hn : n < 16) :
    witnessExecution.WithinHorizon witnessConfig n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [time_at_eq]
    exact (Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    exact (Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    change n / 4 < 4
    rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)]

theorem slot_within_of_lt_sixteen {s : Slot} (hs : s < 16) :
    witnessExecution.SlotWithinHorizon witnessConfig s := by
  refine ⟨(Nat.le_of_lt hs).trans (by norm_num [UINT64_MAX]), ?_⟩
  change s / 4 < 4
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)]

theorem honest_eq_zero_or_one_or_two_or_three {v : ValidatorIndex}
    (hv : v ∈ witnessExecution.honest) :
      v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  simpa [witnessExecution] using hv

theorem witness_vote_some_iff {v : ValidatorIndex} {s : Slot}
    {n : ℕ} {a : Attestation WitnessRoot} :
    witnessExecution.vote v s = some (n, a) ↔
      s < 16 ∧ v = s % 4 ∧ n = s ∧ a = vote s := by
  change (if s < 16 ∧ v = s % 4 then some (s, vote s) else none) =
      some (n, a) ↔ _
  by_cases h : s < 16 ∧ v = s % 4
  · rw [if_pos h]
    constructor
    · intro heq
      have hp : (s, vote s) = (n, a) := Option.some.inj heq
      exact ⟨h.1, h.2, (congrArg Prod.fst hp).symm,
        (congrArg Prod.snd hp).symm⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rw [if_neg h]
    constructor
    · intro himpossible
      contradiction
    · rintro ⟨hs, hv, -, -⟩
      exact (h ⟨hs, hv⟩).elim

theorem witness_valid_iff (state : BeaconState WitnessRoot)
    (a : Attestation WitnessRoot) :
    witnessExternals.is_valid_indexed_attestation state a = true ↔
      state.validators ≠ [] ∧ a ∈ groundVotes := by
  simp [witnessExternals]

/-! ## Direct executable regression checks -/





theorem find_latest_confirmed_descendant_strict_advance :
    find_latest_confirmed_descendant witnessConfig witnessExternals confirmingFcr
      anchorRoot = childRoot := by
  set_option maxRecDepth 20000 in
    decide

theorem actual_fcr_transition_strict_advance :
    witnessExecution.confirmed witnessConfig witnessExternals 0 2 = childRoot := by
  set_option maxRecDepth 20000 in
    decide




/-! ## Operational classifiers and execution assumptions -/

theorem block_mem_schedule_iff {w n}
    {b : SignedBeaconBlock WitnessRoot} :
    Event.block b ∈ witnessExecution.schedule w n ↔
      (n = 1 ∧ b = childSignedBlock) ∨
      (n = 7 ∧ b = carrierSignedBlock) := by
  change Event.block b ∈ witnessSchedule w n ↔ _
  by_cases h1 : n = 1
  · subst n
    simp [witnessSchedule]
  · by_cases h7 : n = 7
    · subst n
      simp [witnessSchedule]
    · simp [witnessSchedule, h1, h7]

theorem vote_mem_ground {s : Slot} (hs : s < 16) : vote s ∈ groundVotes := by
  interval_cases s <;>
    simp [groundVotes, vote0, vote1, vote2, vote3, vote4, vote5, vote6,
      vote7, vote8, vote9, vote10, vote11, vote12, vote13, vote14,
      vote15]

theorem attestation_mem_schedule_ground {w n a ifb}
    (h : Event.attestation a ifb ∈ witnessExecution.schedule w n) :
    a ∈ groundVotes := by
  change Event.attestation a ifb ∈ witnessSchedule w n at h
  by_cases h1 : n = 1
  · subst n
    simp [witnessSchedule] at h
    rcases h with ⟨rfl, rfl⟩
    exact vote_mem_ground (s := 0) (by decide)
  · by_cases h7 : n = 7
    · subst n
      simp [witnessSchedule] at h
      rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
        exact vote_mem_ground (by decide)
    · by_cases hb : 2 ≤ n ∧ n ≤ 16
      · simp [witnessSchedule, h1, h7, hb] at h
        rcases h with ⟨rfl, rfl⟩
        have hpred : n - 1 < n := Nat.sub_lt (by omega) (by decide)
        exact vote_mem_ground (s := n - 1) (hpred.trans_le hb.2)
      · simp [witnessSchedule, h1, h7, hb] at h

theorem groundVote_exists {a : Attestation WitnessRoot}
    (ha : a ∈ groundVotes) :
    ∃ s : Slot, s < 16 ∧ a = vote s := by
  simp [groundVotes, vote0, vote1, vote2, vote3, vote4, vote5, vote6,
    vote7, vote8, vote9, vote10, vote11, vote12, vote13, vote14,
    vote15] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, by decide, rfl⟩

theorem vote_data_slot (s : Slot) : (vote s).data.slot = s := by
  simp only [vote, voteData]
  split_ifs <;> simp_all

/-- Every scheduled copy of a ground vote is received after that vote's
recorded send second. -/
theorem scheduled_vote_sent_before {w n s ifb}
    (h : Event.attestation (vote s) ifb ∈ witnessExecution.schedule w n) :
    s ≤ n := by
  have vote_slot_eq {t : Slot} (heq : vote s = vote t) : s = t := by
    have hslot := congrArg (fun a : Attestation WitnessRoot => a.data.slot) heq
    simpa only [vote_data_slot] using hslot
  change Event.attestation (vote s) ifb ∈ witnessSchedule w n at h
  by_cases h1 : n = 1
  · subst n
    simp [witnessSchedule] at h
    have hs := vote_slot_eq h.1
    rw [hs]
    decide
  · by_cases h7 : n = 7
    · subst n
      simp [witnessSchedule, h1] at h
      rcases h with h | h | h | h
      all_goals
        have hs := vote_slot_eq h.1
        rw [hs]
        decide
    · by_cases hb : 2 ≤ n ∧ n ≤ 16
      · simp [witnessSchedule, h1, h7, hb] at h
        have hs := vote_slot_eq h.1
        rw [hs]
        exact Nat.sub_le n 1
      · simp [witnessSchedule, h1, h7, hb] at h

theorem recorded_vote_of_attester {s : Slot} (hs : s < 16)
    {v : ValidatorIndex} (hvin : v ∈ (vote s).attesting_indices) :
    ∃ m a', witnessExecution.vote v (vote s).data.slot = some (m, a') ∧
      (vote s).data = a'.data := by
  have hv : v = s % 4 := by simpa [vote] using hvin
  refine ⟨s, vote s, ?_, rfl⟩
  rw [vote_data_slot]
  simp [witnessExecution, witnessVote, hs, hv]

theorem witness_store_symmetric (v w : ValidatorIndex) (n : ℕ) :
    witnessExecution.store witnessConfig witnessExternals v n =
      witnessExecution.store witnessConfig witnessExternals w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Execution.store]
      rw [ih]
      rfl

theorem witnessWellFormedExecution :
    WellFormedExecution witnessExecution := by
  constructor
  · intro w n b hb w' n' b' hb' hroot
    rcases block_mem_schedule_iff.mp hb with hchild | hcarrier <;>
      rcases block_mem_schedule_iff.mp hb' with hchild' | hcarrier'
    · rcases hchild with ⟨rfl, rfl⟩
      rcases hchild' with ⟨rfl, rfl⟩
      rfl
    · rcases hchild with ⟨rfl, rfl⟩
      rcases hcarrier' with ⟨rfl, rfl⟩
      exact False.elim ((by decide : childRoot ≠ carrierRoot) hroot)
    · rcases hcarrier with ⟨rfl, rfl⟩
      rcases hchild' with ⟨rfl, rfl⟩
      exact False.elim ((by decide : carrierRoot ≠ childRoot) hroot)
    · rcases hcarrier with ⟨rfl, rfl⟩
      rcases hcarrier' with ⟨rfl, rfl⟩
      rfl
  · intro w n b hb hgen
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp [witnessExecution, anchorState, stateAt, anchorSignedBlock,
        childSignedBlock, carrierSignedBlock, get_forkchoice_store,
        anchorRoot, childRoot, carrierRoot] at hgen
  · intro r hr w n b hb
    have hr' : r = anchorRoot := by
      simpa [witnessExecution, anchorState, stateAt, anchorSignedBlock,
        get_forkchoice_store] using hr
    subst r
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide

theorem honest_vote_recorded {s : Slot} (hs : s < 16) :
    witnessExecution.vote (s % 4) s =
      some (s, honest_attestation witnessConfig witnessExternals
        (witnessExecution.store witnessConfig witnessExternals (s % 4) s)
        s 0 (s % 4)) := by
  interval_cases s <;>
    set_option maxRecDepth 50000 in rfl

theorem witnessHonestBehavior :
    HonestBehavior witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := slot_lt_sixteen hs
    have hvmod : v = s % 4 := by
      simpa [witnessExecution, witnessCommittee] using hcommittee
    subst v
    exact ⟨s, 0, time_within_of_lt_sixteen hslt, slot_at_eq s,
      honest_vote_recorded hslt⟩
  · intro v hv s n a hvote
    obtain ⟨_, _, rfl, _⟩ := witness_vote_some_iff.mp hvote
    rw [slot_start_eq]
    simp
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨na, hna⟩
    rcases na with ⟨n, a⟩
    obtain ⟨hs, hvmod, _hn, _ha⟩ := witness_vote_some_iff.mp hna
    simpa [witnessExecution, witnessCommittee, hvmod]
  · intro w n a ifb hschedule v hv hvin
    obtain ⟨s, hs, rfl⟩ :=
      groundVote_exists (attestation_mem_schedule_ground hschedule)
    have hv : v = s % 4 := by simpa [vote] using hvin
    refine ⟨s, vote s, scheduled_vote_sent_before hschedule, ?_, rfl⟩
    rw [vote_data_slot]
    simp [witnessExecution, witnessVote, hs, hv]
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hs, hvmod, hn, ha⟩ := witness_vote_some_iff.mp hvote
    obtain ⟨hs', hvmod', hn', ha'⟩ := witness_vote_some_iff.mp hvote'
    subst n
    subst a
    subst n'
    subst a'
    interval_cases s <;> interval_cases s' <;>
      simp_all [vote, voteData, is_slashable_attestation_data,
        anchorCheckpoint, stubCheckpoint, childEpochOneCheckpoint,
        carrierEpochTwoCheckpoint, carrierEpochThreeCheckpoint]
  · intro v hv
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide

theorem witnessPJF_current_epoch_le (st : BeaconState WitnessRoot) :
    (witnessPJF st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot witnessConfig st.slot := by
  by_cases h : st.slot = 7
  · simp [witnessPJF, h, childEpochOneCheckpoint, witnessConfig,
      compute_epoch_at_slot]
  · simp [witnessPJF, h, stubCheckpoint]

theorem active_index_lt_four {i : ValidatorIndex} {e : Epoch}
    (hactive : is_active_validator
      (witnessExecution.registry.getD i default) e = true) : i < 4 := by
  cases i with
  | zero => decide
  | succ i =>
      cases i with
      | zero => decide
      | succ i =>
          cases i with
          | zero => decide
          | succ i =>
              cases i with
              | zero => decide
              | succ i =>
                  simp [Execution.registry, Execution.anchor_state,
                    witnessExecution, anchorState, stateAt,
                    anchorSignedBlock, witnessValidator,
                    get_forkchoice_store, is_active_validator] at hactive
                  have hexit : (default : Validator).exit_epoch = 0 := rfl
                  rw [hexit] at hactive
                  exact (Nat.not_lt_zero e hactive.2).elim

theorem witness_committee_coverage_at {i : ValidatorIndex} {e : Epoch}
    (hi : i < 4) (he : e < 4) :
    ∃ s : Slot, witnessExecution.SlotWithinHorizon witnessConfig s ∧
      compute_epoch_at_slot witnessConfig s = e ∧
      i ∈ witnessExecution.committee s := by
  have he3 : e ≤ 3 := Nat.le_of_lt_succ he
  have hi3 : i ≤ 3 := Nat.le_of_lt_succ hi
  have hslt : e * 4 + i < 16 := by
    calc
      e * 4 + i ≤ 3 * 4 + 3 :=
        Nat.add_le_add (Nat.mul_le_mul_right 4 he3) hi3
      _ < 16 := by decide
  refine ⟨e * 4 + i, slot_within_of_lt_sixteen hslt, ?_, ?_⟩
  all_goals interval_cases e <;> interval_cases i <;> decide

/-- Raw state-processing facts seed registry constancy before the coherence
record is constructed. -/
theorem witnessProcessSlots_registry (st : BeaconState WitnessRoot) (s : Slot) :
    (witnessExternals.process_slots st s).validators = st.validators := by
  simp only [witnessExternals, witnessProcessSlots]
  split
  · simp only [witnessPJF]
    split <;> rfl
  · rfl

theorem witnessTransition_registry (st : BeaconState WitnessRoot)
    (b : SignedBeaconBlock WitnessRoot) (st' : BeaconState WitnessRoot)
    (h : witnessExternals.state_transition st b = some st') :
    st'.validators = st.validators := by
  simp only [witnessExternals, witnessTransition] at h
  split at h
  · next hguard =>
      simp only [Option.some.injEq] at h
      subst st'
      have hst : st = anchorState := sameProjectedState_iff_eq.mp hguard.1
      subst st
      rfl
  · split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        have hst : st = childState := sameProjectedState_iff_eq.mp hguard.1
        subst st
        rfl
    · contradiction

theorem witnessStore_registryConstant (v : ValidatorIndex) (n : ℕ) :
    RegistryConstant witnessExecution.registry
      (witnessExecution.store witnessConfig witnessExternals v n) := by
  induction n with
  | zero =>
      exact witnessExecution.genesis_registryConstant witnessConfig
        ⟨anchorState, anchorSignedBlock, rfl⟩
  | succ n ih =>
      change RegistryConstant witnessExecution.registry
        ((witnessExecution.schedule v (n + 1)).foldl
          (fun store event =>
            (apply_event witnessConfig witnessExternals store event).getD store)
          (on_tick witnessConfig
            (witnessExecution.store witnessConfig witnessExternals v n)
            (witnessExecution.time_at (n + 1))))
      refine registryConstant_foldl
        (fun store event hstore => apply_event_getD_registryConstant
          witnessConfig witnessExternals witnessTransition_registry
          witnessProcessSlots_registry store event hstore) _ _ ?_
      exact on_tick_registryConstant witnessConfig _ _ ih

theorem witnessCausalStore_registryConstant {store : Store WitnessRoot}
    (hstore : witnessExecution.ScheduledPrefixStore witnessConfig witnessExternals store) :
    RegistryConstant witnessExecution.registry store := by
  cases hstore with
  | genesis =>
      exact witnessExecution.genesis_registryConstant witnessConfig
        ⟨anchorState, anchorSignedBlock, rfl⟩
  | scheduledPrefix p =>
      unfold Execution.ScheduledEventPrefix.store
      refine registryConstant_foldl
        (fun store event hstore => apply_event_getD_registryConstant
          witnessConfig witnessExternals witnessTransition_registry
          witnessProcessSlots_registry store event hstore) _ _ ?_
      exact on_tick_registryConstant witnessConfig _ _
        (witnessStore_registryConstant p.node p.previousSecond)

theorem witnessReachableValidationState_nonempty {state : BeaconState WitnessRoot}
    (hstate : witnessExecution.ReachableValidationState
      witnessConfig witnessExternals state) : state.validators ≠ [] := by
  obtain ⟨store, hstore, hstate⟩ := hstate
  have hreg := witnessCausalStore_registryConstant
    (hstore.causal witnessConfig witnessExternals)
  have heq : state.validators = witnessExecution.registry := by
    rcases hstate with ⟨root, hroot, rfl⟩ | ⟨checkpoint, hcheckpoint, rfl⟩
    · exact hreg.1 root hroot
    · exact hreg.2 checkpoint hcheckpoint
  rw [heq]
  decide

theorem witnessExternalsCoherence :
    BeaconExternalsPremises witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro st s hlt
    simp only [witnessExternals, witnessProcessSlots]
    split <;> rfl
  · intro st s
    simp only [witnessExternals, witnessProcessSlots]
    split
    · simp only [witnessPJF]
      split <;> rfl
    · rfl
  · intro st b st' h
    simp only [witnessExternals, witnessTransition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        rw [hguard.2]
        rfl
    · split at h
      · next hguard =>
          simp only [Option.some.injEq] at h
          subst st'
          rw [hguard.2]
          rfl
      · contradiction
  · intro st b st' h
    simp only [witnessExternals, witnessTransition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        have hst : st = anchorState := sameProjectedState_iff_eq.mp hguard.1
        subst st
        rfl
    · split at h
      · next hguard =>
          simp only [Option.some.injEq] at h
          subst st'
          have hst : st = childState := sameProjectedState_iff_eq.mp hguard.1
          subst st
          rfl
      · contradiction
  · intro st b st' h
    simp only [witnessExternals, witnessTransition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        have hst : st = anchorState := sameProjectedState_iff_eq.mp hguard.1
        subst st
        rw [hguard.2]
        decide
    · split at h
      · next hguard =>
          simp only [Option.some.injEq] at h
          subst st'
          have hst : st = childState := sameProjectedState_iff_eq.mp hguard.1
          subst st
          rw [hguard.2]
          decide
      · contradiction
  · intro st b st' h
    simp only [witnessExternals, witnessTransition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        rw [hguard.2]
        decide
    · split at h
      · next hguard =>
          simp only [Option.some.injEq] at h
          subst st'
          rw [hguard.2]
          decide
      · contradiction
  · intro st
    exact witnessPJF_current_epoch_le st
  · intro v hv n s hn hs
    simp [get_slot_committee, witnessExternals, witnessExecution,
      witnessCommittee]
  · intro state a hreachable v hv hsingle hcommittee hvote
    rcases hvote with ⟨m, a', hvote, hdata⟩
    let s := a.data.slot
    have hvoteS : witnessExecution.vote v s = some (m, a') := by
      simpa [s] using hvote
    obtain ⟨hs, hvmod, hm, ha'⟩ := witness_vote_some_iff.mp hvoteS
    subst m
    subst a'
    have ha : a = vote s := by
      cases a
      simp_all [vote]
    have hmem : a ∈ groundVotes := by
      rw [ha]
      exact vote_mem_ground hs
    exact (witness_valid_iff state a).2
      ⟨witnessReachableValidationState_nonempty hreachable, hmem⟩
  · intro state a _hreachable hvalid v hv hvin
    have haGround := ((witness_valid_iff state a).mp hvalid).2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    exact recorded_vote_of_attester hs hvin
  · intro state a _hreachable hvalid i hi
    have haGround := ((witness_valid_iff state a).mp hvalid).2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    have hi' : i = s % 4 := by simpa [vote] using hi
    rw [vote_data_slot]
    simpa [witnessExecution, witnessCommittee, hi']
  · intro i s s' hs hs' hepoch
    have his : i = s % 4 := by
      simpa [witnessExecution, witnessCommittee] using hs
    have his' : i = s' % 4 := by
      simpa [witnessExecution, witnessCommittee] using hs'
    have hmod : s % 4 = s' % 4 := his.symm.trans his'
    have hdiv : s / 4 = s' / 4 := by
      simpa [witnessConfig, compute_epoch_at_slot] using hepoch
    calc
      s = s % 4 + 4 * (s / 4) := (Nat.mod_add_div s 4).symm
      _ = s' % 4 + 4 * (s' / 4) := by rw [hmod, hdiv]
      _ = s' := Nat.mod_add_div s' 4
  · intro i e he hactive
    have helt : e < 4 := by simpa [witnessExecution] using he
    exact witness_committee_coverage_at (active_index_lt_four hactive) helt
  · intro i s hs hi
    have hslt := slot_lt_sixteen hs
    interval_cases s <;>
      simp [witnessExecution, witnessCommittee] at hi <;>
      subst i <;> decide

  · intro a
    have hdefault : (default : BeaconState WitnessRoot).validators = [] := rfl
    simp [witnessExternals, hdefault]
  · intro state slot a _hreachable _hlt
    change decide ((witnessExternals.process_slots state slot).validators ≠ [] ∧
      a ∈ groundVotes) = decide (state.validators ≠ [] ∧ a ∈ groundVotes)
    rw [witnessProcessSlots_registry]
  · intro state signed o o'
    rfl

theorem witnessStaticValidatorSet :
    StaticValidatorSet witnessConfig witnessExecution := by
  constructor
  · exact time_within_of_lt_sixteen (by decide)
  · intro i e e' he he'
    have helt : e < 4 := by simpa [witnessExecution] using he
    have helt' : e' < 4 := by simpa [witnessExecution] using he'
    interval_cases e <;> interval_cases e'
    all_goals
      cases i with
      | zero => decide
      | succ i =>
          cases i with
          | zero => decide
          | succ i =>
              cases i with
              | zero => decide
              | succ i =>
                  cases i with
                  | zero => decide
                  | succ i => rfl

set_option maxRecDepth 20000 in
theorem witnessByzantineBound :
    ByzantineWeightPremises witnessConfig witnessExecution := by
  constructor
  · intro i
    cases i with
    | zero => decide
    | succ i =>
        cases i with
        | zero => decide
        | succ i =>
            cases i with
            | zero => decide
            | succ i =>
                cases i with
                | zero => decide
                | succ i =>
                    simp [Execution.weight_of, Execution.registry,
                      Execution.anchor_state, witnessExecution, anchorState,
                      stateAt, anchorSignedBlock, witnessValidator,
                      witnessConfig, get_forkchoice_store]
                    exact dvd_zero 100
  · intro a b ha hb
    have halt := slot_lt_sixteen ha
    have hblt := slot_lt_sixteen hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 50000 in decide
  · intro a b ha hb
    have halt := slot_lt_sixteen ha
    have hblt := slot_lt_sixteen hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 50000 in decide

theorem witness_vote_false_delivery {s : Slot} (hs : s < 16)
    (w : ValidatorIndex) :
    Event.attestation (vote s) false ∈
      witnessExecution.schedule w (witnessExecution.slot_start witnessConfig (s + 1)) := by
  rw [slot_start_eq]
  interval_cases s <;>
    simp [witnessExecution, witnessSchedule, vote0, vote1, vote2, vote3,
      vote4, vote5, vote6, vote7, vote8, vote9, vote10, vote11,
      vote12, vote13, vote14, vote15]

theorem witness_slot15_delivery_at_second16 (w : ValidatorIndex) :
    Event.attestation vote15 false ∈ witnessExecution.schedule w 16 := by
  simp [witnessExecution, witnessSchedule, vote15]

theorem witnessSynchrony :
    Synchrony witnessConfig witnessExternals witnessExecution := by
  refine {
    delta := ⟨500, by decide, by decide⟩
    attestation_delivery := ?_
    deadline_block_relay := ?_
    boundary_block_prefix := ?_
    attester_slashing_relay := ?_
  }
  · intro v hv s n a hs hn hvote _hdeadline hdelivery w hw
    obtain ⟨hslt, hvmod, hn', ha⟩ := witness_vote_some_iff.mp hvote
    subst n
    subst a
    exact witness_vote_false_delivery hslt w
  · intro v hv n r hn hr _hdeadline w hw m hm _hnext hlt
    left
    rw [← witness_store_symmetric v w m]
    exact
      (witnessExecution.store_storeLE witnessConfig witnessExternals v hlt.le).1 hr
  · intro v hv n r hn hr _hdeadline w hw boundary hHboundary hlt
      a before after _hschedule _hnotExcluded
    have hnpred : n ≤ boundary - 1 := by omega
    have hrootPred : r ∈
        (witnessExecution.store witnessConfig witnessExternals w
          (boundary - 1)).block_roots := by
      rw [← witness_store_symmetric v w (boundary - 1)]
      exact (witnessExecution.store_storeLE witnessConfig witnessExternals
        v hnpred).1 hr
    have hrootTick : r ∈
        (on_tick witnessConfig
          (witnessExecution.store witnessConfig witnessExternals w
            (boundary - 1))
          (witnessExecution.time_at boundary)).block_roots :=
      (on_tick_storeLE witnessConfig _ _).1 hrootPred
    exact (foldl_storeLE witnessConfig witnessExternals before _).1 hrootTick
  · intro v hv n i hn hi _hdue w hw m hm _hnext hlt
    have hnm : n ≤ m := hlt.le
    rw [← witness_store_symmetric v w m]
    exact
      (witnessExecution.store_storeLE witnessConfig witnessExternals v hnm).2.2.1 hi

/-- No event in this finite witness carries an execution envelope. -/
private theorem witnessSchedule_no_envelope (v n : ℕ) (event : Event WitnessRoot)
    (hmem : event ∈ witnessSchedule v n) :
    ∀ signed observation,
      event ≠ Event.execution_payload_envelope signed observation := by
  intro signed observation heq
  subst event
  simp [witnessSchedule] at hmem
  split_ifs at hmem <;> simp_all

private theorem witness_other_event_payloads (store : Store WitnessRoot)
    (event : Event WitnessRoot)
    (hne : ∀ signed observation,
      event ≠ Event.execution_payload_envelope signed observation) :
    ((apply_event witnessConfig witnessExternals store event).getD store).payloads =
      store.payloads := by
  cases event with
  | block block =>
      cases h : on_block witnessConfig witnessExternals store block with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using on_block_payloads witnessConfig witnessExternals h
  | attestation attestation fromBlock =>
      cases h : on_attestation witnessConfig witnessExternals store attestation fromBlock with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using on_attestation_payloads witnessConfig witnessExternals h
  | attester_slashing slashing =>
      cases h : on_attester_slashing witnessExternals store slashing with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using on_attester_slashing_payloads witnessExternals h
  | execution_payload_envelope signed observation => exact (hne signed observation rfl).elim
  | payload_attestation_message message fromBlock =>
      cases h : on_payload_attestation_message witnessConfig witnessExternals store message fromBlock with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using
            on_payload_attestation_message_payloads witnessConfig witnessExternals h

private theorem witness_fold_no_envelope (events : List (Event WitnessRoot))
    (store : Store WitnessRoot)
    (hno : ∀ event ∈ events, ∀ signed observation,
      event ≠ Event.execution_payload_envelope signed observation) :
    (events.foldl
      (fun s event => (apply_event witnessConfig witnessExternals s event).getD s)
      store).payloads = store.payloads := by
  induction events generalizing store with
  | nil => rfl
  | cons event tail ih =>
      simp only [List.foldl_cons]
      have he := hno event (List.mem_cons_self)
      have ht : ∀ e ∈ tail, ∀ signed observation,
          e ≠ Event.execution_payload_envelope signed observation := by
        intro e he'; exact hno e (List.mem_cons_of_mem event he')
      exact (ih _ ht).trans (witness_other_event_payloads store event he)

private theorem witness_schedule_fold_payloads (v n : ℕ) (store : Store WitnessRoot) :
    ((witnessSchedule v n).foldl
      (fun s event => (apply_event witnessConfig witnessExternals s event).getD s)
      store).payloads = store.payloads := by
  apply witness_fold_no_envelope
  intro event hmem
  exact witnessSchedule_no_envelope v n event hmem

private theorem witness_payloads_empty (v n : ℕ) :
    (witnessExecution.store witnessConfig witnessExternals v n).payloads =
      witnessExecution.genesis_store.payloads := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [Execution.store] using
        (witness_schedule_fold_payloads v (n + 1)
          (on_tick witnessConfig
            (witnessExecution.store witnessConfig witnessExternals v n)
            (witnessExecution.time_at (n + 1)))).trans
          ((on_tick_payloads witnessConfig _ _).trans ih)

theorem witnessHorizonVoteDeliveryLookahead :
    HorizonVoteDeliveryLookahead witnessConfig witnessExecution := by
  constructor
  intro v hv s n a hs hn hvote _hdeadline w hw
  obtain ⟨hslt, hvmod, hn', ha⟩ := witness_vote_some_iff.mp hvote
  subst n
  subst a
  exact witness_vote_false_delivery hslt w

/-- The Gloas envelope and data premises hold for this finite witness. -/
theorem witnessPaperSafetySynchrony :
    NextSlotSynchronyPremises witnessConfig witnessExternals witnessExecution := by
  apply witnessSynchrony.toPaperSafetySynchrony witnessConfig witnessExternals
    witnessHorizonVoteDeliveryLookahead
  · intro v hv n r hn hr
    have hempty := witness_payloads_empty v n
    have hnone : witnessExecution.genesis_store.payloads r = none := rfl
    have hfalse : is_payload_verified
        (witnessExecution.store witnessConfig witnessExternals v n) r = false := by
      simp only [is_payload_verified, hempty, hnone, Option.isSome_none]
    rw [hfalse] at hr
    cases hr
  · intro v hv k n signed sourceObservation hk hn hevent havailable
    have hno := witnessSchedule_no_envelope v k _ hevent signed sourceObservation
    exact (hno rfl).elim

theorem witnessScheduledPrefixTrajectoryAssumptions :
    witnessExecution.ScheduledExecutionPremises
      witnessConfig witnessExternals := by
  exact
    { whole_seconds := by decide
      wellFormed := witnessWellFormedExecution
      externals_coherence := witnessExternalsCoherence
      honest_behavior := witnessHonestBehavior
      genesis := ⟨anchorState, anchorSignedBlock, rfl, rfl, ⟨rfl, rfl⟩, by decide⟩ }

theorem witnessPhase0SourceCoherence :
    Phase0SourceCoherence witnessConfig witnessExternals := by
  constructor
  · intro st target hlt hepoch
    simp only [witnessExternals, witnessProcessSlots]
    have hnot : ¬ compute_epoch_at_slot witnessConfig st.slot <
        compute_epoch_at_slot witnessConfig target := by
      intro hstrict
      exact (Nat.ne_of_lt hstrict) hepoch
    rw [if_neg hnot]
  · intro pre sb post htransition hepoch
    simp only [witnessExternals, witnessTransition] at htransition
    split at htransition
    · next hguard =>
        simp only [Option.some.injEq] at htransition
        subst post
        have hpre : pre = anchorState := sameProjectedState_iff_eq.mp hguard.1
        subst pre
        rfl
    · split at htransition
      · next hguard =>
          simp only [Option.some.injEq] at htransition
          subst post
          have hpre : pre = childState := sameProjectedState_iff_eq.mp hguard.1
          subst pre
          rfl
      · contradiction

theorem witnessPhase0BoundarySourceCoherence :
    Phase0BoundarySourceCoherence witnessConfig witnessExternals := by
  refine Phase0BoundarySourceCoherence.of_eager ?_ ?_ witnessExternalsCoherence.pjf_checkpoint_epoch
  · intro st target hlt hcross
    simp only [witnessExternals, witnessProcessSlots]
    rw [if_pos hcross]
  · intro pre sb post htransition hcross
    simp only [witnessExternals, witnessTransition] at htransition
    split at htransition
    · next hguard =>
        simp only [Option.some.injEq] at htransition
        subst post
        have hpre : pre = anchorState := sameProjectedState_iff_eq.mp hguard.1
        subst pre
        rw [hguard.2] at hcross
        norm_num [anchorState, stateAt, anchorSignedBlock, childSignedBlock,
          witnessConfig, compute_epoch_at_slot] at hcross
    · split at htransition
      · next hguard =>
          simp only [Option.some.injEq] at htransition
          subst post
          have hpre : pre = childState := sameProjectedState_iff_eq.mp hguard.1
          subst pre
          rfl
      · contradiction



theorem witnessBalanceFloor :
    2 * witnessConfig.effective_balance_increment ≤
      witnessExecution.weight
        (witnessExecution.currentTargetAnchorActive witnessConfig) := by
  decide

theorem witnessEpochEndsFitUint64 : EpochEndsFitUint64 witnessConfig := by
  refine ⟨2 ^ 62, ?_⟩
  norm_num [EpochEndsFitUint64, UINT64_MAX, witnessConfig]

theorem witnessAnchorEquality :
    witnessExecution.genesis_store.justified_checkpoint = anchorCheckpoint := by
  decide

theorem witnessTrustedAnchorBoundaryAligned :
    Execution.InitialAnchorAtEpochBoundary (cfg := witnessConfig)
      (E := witnessExecution) (anchor := anchorCheckpoint) := by
  unfold Execution.InitialAnchorAtEpochBoundary
  decide

end GenesisStubBase
end FastConfirmation.Spec

end
