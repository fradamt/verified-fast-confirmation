module
public import Mathlib.Tactic
public import FastConfirmationProofs.Execution.History.CausalQueryTraceAdapter
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Pinned-economic-constants strict-prefix extra-query counterexample

This finite regression uses the executable FCR economic constants from the
pinned configuration: proposer-score boost `40` and confirmation Byzantine
threshold `25`.  It deliberately keeps a four-slot, one-second-per-slot toy
preset so that the complete action-prefix calculation remains small; it is
therefore a pinned-*economics* witness, not an instantiation of
`mainnet_config`.

The trusted anchor has a slot-one child `parent`.  At slot two a competing
child `candidate` is received and the slot-two honest committee votes for it.
At the first second of slot three every node's schedule contains the sibling
block first and the synchronized slot-two vote second.  Between those two
events, the endpoint head is the proposer-boosted sibling.  After the vote,
the actor head is the candidate and an allowed pre-update extra query strictly
confirms it.

For the candidate the exact numbers are:

* support and maximum support: `100`;
* proposer score: `40`;
* adversarial allowance: `25`;
* safety threshold: `(100 + 40 + 2 * 25) / 2 = 95`.

Thus the race is not an artifact of the earlier `100`/`0` toy economics.  The
completed execution boundary processes the vote at every node, so this is a
counterexample only to exact-current safety over every legal in-second query
position, not to the stored-boundary `Execution.confirmed` theorem.
-/

namespace FastConfirmation.Spec
namespace PinnedEconomicsExtraQuery

open AllowedFCRCalls

abbrev WitnessRoot := Fin 5

def junkRoot : WitnessRoot := 0
def anchorRoot : WitnessRoot := 1
def parentRoot : WitnessRoot := 2
def candidateRoot : WitnessRoot := 3
def siblingRoot : WitnessRoot := 4

def witnessConfig : Config where
  slots_per_epoch := 4
  slots_per_epoch_pos := by decide
  slot_duration_ms := 1000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 3333
  min_seed_lookahead := 0

def anchorCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 0, root := anchorRoot }

def witnessValidator : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := 1 }

def stateAt (slot : Slot) : BeaconState WitnessRoot :=
  { genesis_time := 0
    slot := slot
    validators :=
      [witnessValidator, witnessValidator, witnessValidator, witnessValidator]
    current_justified_checkpoint := anchorCheckpoint
    finalized_checkpoint := anchorCheckpoint
    beacon_committee_reads :=
      (List.range 4).map (fun s => (s, 0, [s % 4]))
    committee_count_reads := [(0, 1)] }

def anchorState : BeaconState WitnessRoot := stateAt 0

def anchorSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 0, parent_root := junkRoot }
    root := anchorRoot }

def parentSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 1, parent_root := anchorRoot }
    root := parentRoot }

def candidateSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 2, parent_root := parentRoot }
    root := candidateRoot }

def siblingSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 3, parent_root := parentRoot }
    root := siblingRoot }

def voteData0 : AttestationData WitnessRoot :=
  { slot := 0
    index := 0
    beacon_block_root := anchorRoot
    source := anchorCheckpoint
    target := anchorCheckpoint }

def voteData1 : AttestationData WitnessRoot :=
  { slot := 1
    index := 0
    beacon_block_root := parentRoot
    source := anchorCheckpoint
    target := anchorCheckpoint }

def voteData2 : AttestationData WitnessRoot :=
  { slot := 2
    index := 0
    beacon_block_root := candidateRoot
    source := anchorCheckpoint
    target := anchorCheckpoint }

def voteData3 : AttestationData WitnessRoot :=
  { slot := 3
    index := 0
    beacon_block_root := candidateRoot
    source := anchorCheckpoint
    target := anchorCheckpoint }

def vote0 : Attestation WitnessRoot :=
  { attesting_indices := [0], data := voteData0 }

def vote1 : Attestation WitnessRoot :=
  { attesting_indices := [1], data := voteData1 }

def vote2 : Attestation WitnessRoot :=
  { attesting_indices := [2], data := voteData2 }

def vote3 : Attestation WitnessRoot :=
  { attesting_indices := [3], data := voteData3 }

/-! The abstract state functions preserve realized checkpoints everywhere.
This makes both phase0 source-coherence laws true, not merely true on the
reachable states used below. -/
def witnessExternals : Externals WitnessRoot where
  get_beacon_committee := fun _ slot _ => [slot % 4]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st slot => { st with slot := slot }
  state_transition := fun st block =>
    if st.slot < block.message.slot ∧
        st.current_justified_checkpoint.epoch ≤
          compute_epoch_at_slot witnessConfig block.message.slot ∧
        st.finalized_checkpoint.epoch ≤
          compute_epoch_at_slot witnessConfig block.message.slot ∧
        (block = parentSignedBlock ∨ block = candidateSignedBlock ∨
          block = siblingSignedBlock) then
      some { st with slot := block.message.slot }
    else none
  -- This is definitionally the identity on all reachable witness states, whose
  -- justified epoch is zero, while satisfying the coherence law on arbitrary
  -- off-trajectory abstract states as well.
  process_justification_and_finalization := fun st =>
    { st with
      current_justified_checkpoint :=
        { st.current_justified_checkpoint with epoch := 0 } }
  is_valid_indexed_attestation := fun state a =>
    decide (state.validators ≠ [] ∧ (a = vote0 ∨ a = vote1 ∨ a = vote2 ∨ a = vote3))

def witnessSchedule (_w : ValidatorIndex) (n : ℕ) :
    List (Event WitnessRoot) :=
  if n = 1 then
    [.block parentSignedBlock, .attestation vote0 false]
  else if n = 2 then
    [.block candidateSignedBlock, .attestation vote1 false]
  else if n = 3 then
    [.block siblingSignedBlock, .attestation vote2 false]
  else if n = 4 then
    [.attestation vote3 false]
  else
    []

def witnessCommittee (slot : Slot) : Finset ValidatorIndex :=
  {slot % 4}

def witnessVote (v : ValidatorIndex) (slot : Slot) :
    Option (ℕ × Attestation WitnessRoot) :=
  if v = 0 ∧ slot = 0 then some (0, vote0)
  else if v = 1 ∧ slot = 1 then some (1, vote1)
  else if v = 2 ∧ slot = 2 then some (2, vote2)
  else if v = 3 ∧ slot = 3 then some (3, vote3)
  else none

def witnessExecution : Execution WitnessRoot where
  verification_horizon := 1
  genesis_store :=
    get_forkchoice_store witnessConfig anchorState anchorSignedBlock
  schedule := witnessSchedule
  honest := {0, 1, 2, 3}
  committee := witnessCommittee
  vote := witnessVote

private lemma time_at_eq (n : ℕ) : witnessExecution.time_at n = n := by
  norm_num [Execution.time_at, witnessExecution, anchorState, stateAt,
    anchorSignedBlock, witnessConfig, get_forkchoice_store]

private lemma slot_at_eq (n : ℕ) :
    witnessExecution.slot_at witnessConfig n = n := by
  norm_num [Execution.slot_at, Execution.time_at, witnessExecution,
    anchorState, stateAt, anchorSignedBlock, witnessConfig,
    get_forkchoice_store, GENESIS_SLOT]

private lemma slot_start_eq (s : Slot) :
    witnessExecution.slot_start witnessConfig s = s := by
  norm_num [Execution.slot_start, witnessExecution, anchorState, stateAt,
    anchorSignedBlock, witnessConfig, get_forkchoice_store]

private lemma within_of_lt_four {n : ℕ} (h : n < 4) :
    witnessExecution.WithinHorizon witnessConfig n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [time_at_eq]
    exact (Nat.le_of_lt h).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    exact (Nat.le_of_lt h).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    change n / 4 < 1
    omega

private lemma slot_within_of_lt_four {s : Slot} (h : s < 4) :
    witnessExecution.SlotWithinHorizon witnessConfig s := by
  refine ⟨(Nat.le_of_lt h).trans (by norm_num [UINT64_MAX]), ?_⟩
  change s / 4 < 1
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)]

private lemma slot_within_implies_lt_four {s : Slot}
    (h : witnessExecution.SlotWithinHorizon witnessConfig s) : s < 4 := by
  have hepoch := h.2
  change s / 4 < 1 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)] at hepoch

private lemma within_implies_lt_four {n : ℕ}
    (h : witnessExecution.WithinHorizon witnessConfig n) : n < 4 := by
  have hepoch := h.2.2
  rw [slot_at_eq] at hepoch
  change n / 4 < 1 at hepoch
  omega

private lemma honest_eq {v : ValidatorIndex}
    (h : v ∈ witnessExecution.honest) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  simpa [witnessExecution] using h

private lemma vote_some_cases {v s n a} :
    witnessExecution.vote v s = some (n, a) ↔
      (v = 0 ∧ s = 0 ∧ n = 0 ∧ a = vote0) ∨
      (v = 1 ∧ s = 1 ∧ n = 1 ∧ a = vote1) ∨
      (v = 2 ∧ s = 2 ∧ n = 2 ∧ a = vote2) ∨
      (v = 3 ∧ s = 3 ∧ n = 3 ∧ a = vote3) := by
  simp only [witnessExecution, witnessVote]
  split_ifs with h0 h1 h2 h3 <;> simp_all [eq_comm]

private lemma schedule_node_independent (w w' : ValidatorIndex) (n : ℕ) :
    witnessExecution.schedule w n = witnessExecution.schedule w' n := by
  rfl

private lemma store_node_independent (w w' : ValidatorIndex) (n : ℕ) :
    witnessExecution.store witnessConfig witnessExternals w n =
      witnessExecution.store witnessConfig witnessExternals w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Execution.store]
      rw [ih, schedule_node_independent w w' (n + 1)]

/-! ## Concrete environment properties -/

private lemma scheduled_block_root_not_genesis {w n b}
    (hb : Event.block b ∈ witnessExecution.schedule w n) :
    b.root ∉ witnessExecution.genesis_store.block_roots := by
  simp only [witnessExecution, witnessSchedule] at hb
  split_ifs at hb with hn1 hn2 hn3 hn4 <;> simp_all
  · subst b
    set_option maxRecDepth 20000 in decide
  · subst b
    set_option maxRecDepth 20000 in decide
  · subst b
    set_option maxRecDepth 20000 in decide

private theorem witnessWellFormedExecution :
    WellFormedExecution witnessExecution := by
  constructor
  · intro w n b hb w' n' b' hb' hroot
    simp only [witnessExecution, witnessSchedule] at hb hb'
    split_ifs at hb with hn1 hn2 hn3 hn4 <;>
      split_ifs at hb' with hn1' hn2' hn3' hn4' <;>
      simp_all <;>
      norm_num [parentSignedBlock, candidateSignedBlock, siblingSignedBlock,
        parentRoot, candidateRoot, siblingRoot] at hroot <;> contradiction
  · intro w n b hb hgen
    exact (scheduled_block_root_not_genesis hb hgen).elim
  · intro r hr w n b hb
    have hr' : r = anchorRoot := by
      set_option maxRecDepth 20000 in
        simpa [witnessExecution, anchorState, stateAt, anchorSignedBlock,
          get_forkchoice_store] using hr
    subst r
    simp only [witnessExecution, witnessSchedule] at hb
    split_ifs at hb with hn1 hn2 hn3 hn4 <;> simp_all <;>
      norm_num [witnessExecution, anchorState, stateAt, anchorSignedBlock,
        parentSignedBlock, candidateSignedBlock, siblingSignedBlock,
        get_forkchoice_store, anchorRoot, junkRoot, parentRoot, candidateRoot,
        siblingRoot] <;> decide

private theorem witnessHonestBehavior :
    HonestBehavior witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt : s < 4 := slot_within_implies_lt_four hs
    interval_cases s <;>
      simp only [witnessExecution, witnessCommittee, Finset.mem_singleton] at hcommittee <;>
      subst v
    · refine ⟨0, 0, within_of_lt_four (by omega), slot_at_eq 0, ?_⟩
      set_option maxRecDepth 20000 in decide
    · refine ⟨1, 0, within_of_lt_four (by omega), slot_at_eq 1, ?_⟩
      set_option maxRecDepth 20000 in decide
    · refine ⟨2, 0, within_of_lt_four (by omega), slot_at_eq 2, ?_⟩
      set_option maxRecDepth 20000 in decide
    · refine ⟨3, 0, within_of_lt_four (by omega), slot_at_eq 3, ?_⟩
      set_option maxRecDepth 20000 in decide
  · intro v hv s hvote
    simp [witnessExecution, witnessVote, witnessCommittee] at hvote ⊢
    aesop
  · intro w n a ifb hschedule v hv hvin
    simp only [witnessExecution, witnessSchedule] at hschedule
    split_ifs at hschedule with hn1 hn2 hn3 hn4 <;>
      simp_all [vote0, vote1, vote2, vote3]
    · exact ⟨0, vote0, by decide, rfl⟩
    · exact ⟨1, vote1, by decide, rfl⟩
    · exact ⟨2, vote2, by decide, rfl⟩
    · exact ⟨3, vote3, by decide, rfl⟩
  · intro v hv s s' n n' a a' hvote hvote'
    rw [vote_some_cases] at hvote hvote'
    rcases hvote with h0 | h1 | h2 | h3 <;>
      rcases hvote' with h0' | h1' | h2' | h3' <;>
      simp_all <;> decide
  · intro v hv
    rcases honest_eq hv with rfl | rfl | rfl | rfl <;> decide

def anchorMessage : LatestMessage WitnessRoot :=
  { slot := 0, root := anchorRoot, payload_present := false }

def parentMessage : LatestMessage WitnessRoot :=
  { slot := 1, root := parentRoot, payload_present := false }

def candidateMessage : LatestMessage WitnessRoot :=
  { slot := 2, root := candidateRoot, payload_present := false }

private lemma block_roots_at_zero :
    (witnessExecution.store witnessConfig witnessExternals 0 0).block_roots =
      [anchorRoot] := by decide

private lemma block_roots_at_one :
    (witnessExecution.store witnessConfig witnessExternals 0 1).block_roots =
      [anchorRoot, parentRoot] := by
  set_option maxRecDepth 20000 in decide

private lemma block_roots_at_two :
    (witnessExecution.store witnessConfig witnessExternals 0 2).block_roots =
      [anchorRoot, parentRoot, candidateRoot] := by
  set_option maxRecDepth 20000 in decide

private lemma block_roots_at_three :
    (witnessExecution.store witnessConfig witnessExternals 0 3).block_roots =
      [anchorRoot, parentRoot, candidateRoot, siblingRoot] := by
  set_option maxRecDepth 20000 in decide

private lemma latest_message_at_zero (i : ValidatorIndex) :
    (witnessExecution.store witnessConfig witnessExternals 0 0).latest_messages i =
      none := by rfl

private lemma latest_message_at_one (i : ValidatorIndex) :
    (witnessExecution.store witnessConfig witnessExternals 0 1).latest_messages i =
      if i = 0 then some anchorMessage else none := by
  change (Function.update (fun _ => none) 0 (some anchorMessage)) i = _
  by_cases h0 : i = 0
  · subst i; simp
  · simp [Function.update, h0]

private lemma latest_message_at_two (i : ValidatorIndex) :
    (witnessExecution.store witnessConfig witnessExternals 0 2).latest_messages i =
      if i = 1 then some parentMessage
      else if i = 0 then some anchorMessage else none := by
  change (Function.update
      (Function.update (fun _ => none) 0 (some anchorMessage))
      1 (some parentMessage)) i = _
  by_cases h1 : i = 1
  · subst i; simp
  · by_cases h0 : i = 0
    · subst i; simp
    · simp [Function.update, h0, h1]

private lemma latest_message_at_three (i : ValidatorIndex) :
    (witnessExecution.store witnessConfig witnessExternals 0 3).latest_messages i =
      if i = 2 then some candidateMessage
      else if i = 1 then some parentMessage
      else if i = 0 then some anchorMessage else none := by
  set_option maxRecDepth 30000 in
    change (Function.update
        (Function.update
          (Function.update (fun _ => none) 0 (some anchorMessage))
          1 (some parentMessage))
        2 (some candidateMessage)) i = _
  by_cases h2 : i = 2
  · subst i; simp
  · by_cases h1 : i = 1
    · subst i; simp
    · by_cases h0 : i = 0
      · subst i; simp
      · simp [Function.update, h0, h1, h2]

private lemma equivocating_indices_at_zero :
    (witnessExecution.store witnessConfig witnessExternals 0 0).equivocating_indices =
      ∅ := by decide

private lemma equivocating_indices_at_one :
    (witnessExecution.store witnessConfig witnessExternals 0 1).equivocating_indices =
      ∅ := by
  set_option maxRecDepth 20000 in decide

private lemma equivocating_indices_at_two :
    (witnessExecution.store witnessConfig witnessExternals 0 2).equivocating_indices =
      ∅ := by
  set_option maxRecDepth 20000 in decide

private lemma equivocating_indices_at_three :
    (witnessExecution.store witnessConfig witnessExternals 0 3).equivocating_indices =
      ∅ := by
  set_option maxRecDepth 20000 in decide

private theorem witnessSynchrony :
    Synchrony witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro v hv s n a hs hn hvote w hw
    rw [vote_some_cases] at hvote
    rcases hvote with h0 | h1 | h2 | h3
    · rcases h0 with ⟨rfl, rfl, rfl, rfl⟩
      rw [slot_start_eq]
      simp [witnessExecution, witnessSchedule]
    · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
      rw [slot_start_eq]
      simp [witnessExecution, witnessSchedule]
    · rcases h2 with ⟨rfl, rfl, rfl, rfl⟩
      rw [slot_start_eq]
      simp [witnessExecution, witnessSchedule]
    · rcases h3 with ⟨rfl, rfl, rfl, rfl⟩
      rw [slot_start_eq]
      simp [witnessExecution, witnessSchedule]
  · intro v hv n r hn hr w hw m hm hslot
    have hnlt : n < 4 := within_implies_lt_four hn
    have hmlt : m < 4 := within_implies_lt_four hm
    rw [store_node_independent v 0 n] at hr
    rw [store_node_independent w 0 m]
    interval_cases n <;> interval_cases m <;>
      simp_all [slot_at_eq, block_roots_at_zero, block_roots_at_one,
        block_roots_at_two, block_roots_at_three] <;> aesop
  · intro v hv n i msg hn hmsg w hw m hm hslot
    have hnlt : n < 4 := within_implies_lt_four hn
    have hmlt : m < 4 := within_implies_lt_four hm
    rw [store_node_independent v 0 n] at hmsg
    rw [store_node_independent w 0 m]
    interval_cases n <;> interval_cases m <;>
      simp_all [slot_at_eq, latest_message_at_zero,
        latest_message_at_one, latest_message_at_two,
        latest_message_at_three]
    all_goals aesop
  · intro v hv n i hn hi w hw m hm hslot
    have hnlt : n < 4 := within_implies_lt_four hn
    rw [store_node_independent v 0 n] at hi
    interval_cases n <;>
      simp_all [equivocating_indices_at_zero, equivocating_indices_at_one,
        equivocating_indices_at_two, equivocating_indices_at_three]

private lemma witness_valid_iff (state : BeaconState WitnessRoot)
    (a : Attestation WitnessRoot) (hstate : state.validators ≠ []) :
    witnessExternals.is_valid_indexed_attestation state a = true ↔
      a = vote0 ∨ a = vote1 ∨ a = vote2 ∨ a = vote3 := by
  simp [witnessExternals, hstate]

private theorem witnessProcessSlots_registry (st : BeaconState WitnessRoot) (s : Slot) :
    (witnessExternals.process_slots st s).validators = st.validators := rfl

private theorem witnessTransition_registry (st : BeaconState WitnessRoot)
    (b : SignedBeaconBlock WitnessRoot) (st' : BeaconState WitnessRoot)
    (h : witnessExternals.state_transition st b = some st') :
    st'.validators = st.validators := by
  simp [witnessExternals] at h
  rcases h with ⟨_hguard, rfl⟩
  rfl

private theorem witnessStore_registryConstant (v : ValidatorIndex) (n : ℕ) :
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

private theorem witnessCausalStore_registryConstant {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store) :
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

private theorem witnessReachableValidationState_nonempty {state : BeaconState WitnessRoot}
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

private theorem witnessExternalsCoherence :
    BeaconExternalsPremises witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro st s hlt
    rfl
  · intro st s
    rfl
  · intro st b st' h
    simp [witnessExternals] at h
    rcases h with ⟨_hguard, rfl⟩
    rfl
  · intro st b st' h
    simp [witnessExternals] at h
    rcases h with ⟨_hguard, rfl⟩
    rfl
  · intro st b st' h
    simp [witnessExternals] at h
    exact h.1.1
  · intro st b st' h
    simp [witnessExternals] at h
    rcases h with ⟨_hguard, rfl⟩
    exact ⟨_hguard.2.1, _hguard.2.2.1⟩
  · intro st
    simp [witnessExternals, witnessConfig, compute_epoch_at_slot]
  · intro v hv n s hn hs
    simp [get_slot_committee, witnessExternals, witnessExecution,
      witnessCommittee]
  · intro state a hreachable v hv hsingle hcommittee hvote
    have hstate := witnessReachableValidationState_nonempty hreachable
    rcases hvote with ⟨m, a', hvote, hdata⟩
    rw [vote_some_cases] at hvote
    rcases hvote with h0 | h1 | h2 | h3
    · rcases h0 with ⟨hv0, hs0, hm0, ha'⟩
      subst v
      subst m
      subst a'
      have ha : a = vote0 := by cases a; simp_all [vote0]
      rw [ha]
      exact (witness_valid_iff state vote0 hstate).2 (Or.inl rfl)
    · rcases h1 with ⟨hv1, hs1, hm1, ha'⟩
      subst v
      subst m
      subst a'
      have ha : a = vote1 := by cases a; simp_all [vote1]
      rw [ha]
      exact (witness_valid_iff state vote1 hstate).2 (Or.inr (Or.inl rfl))
    · rcases h2 with ⟨hv2, hs2, hm2, ha'⟩
      subst v
      subst m
      subst a'
      have ha : a = vote2 := by cases a; simp_all [vote2]
      rw [ha]
      exact (witness_valid_iff state vote2 hstate).2 (Or.inr (Or.inr (Or.inl rfl)))
    · rcases h3 with ⟨hv3, hs3, hm3, ha'⟩
      subst v
      subst m
      subst a'
      have ha : a = vote3 := by cases a; simp_all [vote3]
      rw [ha]
      exact (witness_valid_iff state vote3 hstate).2 (Or.inr (Or.inr (Or.inr rfl)))
  · intro state a hreachable hvalid v hv hvin
    have hstate := witnessReachableValidationState_nonempty hreachable
    rcases (witness_valid_iff state a hstate).1 hvalid with rfl | rfl | rfl | rfl
    · have : v = 0 := by simpa [vote0] using hvin
      subst v
      exact ⟨0, vote0, by decide, rfl⟩
    · have : v = 1 := by simpa [vote1] using hvin
      subst v
      exact ⟨1, vote1, by decide, rfl⟩
    · have : v = 2 := by simpa [vote2] using hvin
      subst v
      exact ⟨2, vote2, by decide, rfl⟩
    · have : v = 3 := by simpa [vote3] using hvin
      subst v
      exact ⟨3, vote3, by decide, rfl⟩
  · intro state a hreachable hvalid i hi
    have hstate := witnessReachableValidationState_nonempty hreachable
    rcases (witness_valid_iff state a hstate).1 hvalid with rfl | rfl | rfl | rfl
    · have : i = 0 := by simpa [vote0] using hi
      subst i
      decide
    · have : i = 1 := by simpa [vote1] using hi
      subst i
      decide
    · have : i = 2 := by simpa [vote2] using hi
      subst i
      decide
    · have : i = 3 := by simpa [vote3] using hi
      subst i
      decide
  · intro i s s' hs hs' hepoch
    simp [witnessExecution, witnessCommittee] at hs hs'
    subst i
    change s / 4 = s' / 4 at hepoch
    calc
      s = s % 4 + 4 * (s / 4) := (Nat.mod_add_div s 4).symm
      _ = s' % 4 + 4 * (s' / 4) := by rw [hs', hepoch]
      _ = s' := Nat.mod_add_div s' 4
  · intro i e he hactive
    change e < 1 at he
    have he0 : e = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ he)
    subst e
    rcases i with _ | i
    · exact ⟨0, slot_within_of_lt_four (by decide), by decide, by decide⟩
    · rcases i with _ | i
      · exact ⟨1, slot_within_of_lt_four (by decide), by decide, by decide⟩
      · rcases i with _ | i
        · exact ⟨2, slot_within_of_lt_four (by decide), by decide, by decide⟩
        · rcases i with _ | i
          · exact ⟨3, slot_within_of_lt_four (by decide), by decide, by decide⟩
          · simp [Execution.registry, Execution.anchor_state, witnessExecution,
              anchorState, stateAt, anchorSignedBlock, witnessValidator,
              get_forkchoice_store, is_active_validator] at hactive
            have hdefault : (default : Validator).exit_epoch = 0 := rfl
            rw [hdefault] at hactive
            exact (Nat.lt_irrefl 0 hactive.2).elim
  · intro i s hs hi
    have hslt : s < 4 := slot_within_implies_lt_four hs
    interval_cases s <;>
      simp [witnessExecution, witnessCommittee] at hi <;>
      subst i <;> decide

  · intro a
    have hdefault : (default : BeaconState WitnessRoot).validators = [] := rfl
    simp [witnessExternals, hdefault]
  · intro state slot a _hreachable _hlt
    rfl
  · intro state signed o o'
    rfl

private theorem witnessStaticValidatorSet :
    StaticValidatorSet witnessConfig witnessExecution := by
  constructor
  · exact within_of_lt_four (by decide)
  · intro i e e' he he'
    change e < 1 at he
    change e' < 1 at he'
    have : e = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ he)
    have : e' = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ he')
    subst e
    subst e'
    rfl

private theorem witnessByzantineBound :
    ByzantineWeightPremises witnessConfig witnessExecution := by
  constructor
  · intro i
    rcases i with _ | i
    · decide
    · rcases i with _ | i
      · decide
      · rcases i with _ | i
        · decide
        · rcases i with _ | i
          · decide
          · set_option maxRecDepth 20000 in
            simp [Execution.weight_of, Execution.registry,
              Execution.anchor_state, witnessExecution, anchorState, stateAt,
              anchorSignedBlock, witnessValidator, witnessConfig,
              get_forkchoice_store]
            have hdefault : (default : Validator).effective_balance = 0 := rfl
            rw [hdefault]
            exact dvd_zero 100
  · intro a b ha hb
    have halt : a < 4 := slot_within_implies_lt_four ha
    have hblt : b < 4 := slot_within_implies_lt_four hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 20000 in decide
  · intro a b ha hb
    have halt : a < 4 := slot_within_implies_lt_four ha
    have hblt : b < 4 := slot_within_implies_lt_four hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 20000 in decide

/-! ## Exact strict prefixes and executable query -/

def endpointPrefix : witnessExecution.ScheduledEventPrefix where
  node := 1
  previousSecond := 2
  processedCount := 1
  count_le := by simp [witnessExecution, witnessSchedule]

def actorPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 2
  processedCount := 2
  count_le := by simp [witnessExecution, witnessSchedule]

def queryFcr : FastConfirmationStore WitnessRoot :=
  { witnessExecution.fcr witnessConfig witnessExternals 0 2 with
    store := actorPrefix.store witnessConfig witnessExternals }


/-- The synchronized vote flips the head between two prefixes of one second. -/
theorem strict_prefix_heads_diverge :
    (get_head witnessConfig
        (actorPrefix.store witnessConfig witnessExternals)).root =
        candidateRoot ∧
      (get_head witnessConfig
        (endpointPrefix.store witnessConfig witnessExternals)).root =
        siblingRoot ∧
      is_ancestor (endpointPrefix.store witnessConfig witnessExternals)
        (get_head witnessConfig
          (endpointPrefix.store witnessConfig witnessExternals))
        (get_node_for_root candidateRoot) = false := by
  set_option maxRecDepth 30000 in
    decide

/-- Exact pinned-economic calculation for the strict candidate. -/
theorem candidate_pinned_economic_calculation :
    get_attestation_score witnessConfig queryFcr.store
        (get_node_for_root candidateRoot)
        (get_current_balance_source queryFcr) = 100 ∧
      compute_proposer_score witnessConfig
        (get_current_balance_source queryFcr) = 40 ∧
      get_adversarial_weight witnessConfig witnessExternals queryFcr.store
        (get_current_balance_source queryFcr) candidateRoot = 25 ∧
      compute_safety_threshold witnessConfig witnessExternals queryFcr.store
        candidateRoot (get_current_balance_source queryFcr) = 95 ∧
      is_one_confirmed witnessConfig witnessExternals queryFcr.store
        (get_current_balance_source queryFcr) candidateRoot = true := by
  set_option maxRecDepth 30000 in
    decide

/-- The actual boundary cache is the parent; the pure extra query strictly
advances it to the candidate in the actor prefix. -/
theorem strict_extra_query_result :
    queryFcr.confirmed_root = parentRoot ∧
      find_latest_confirmed_descendant witnessConfig witnessExternals
        queryFcr parentRoot = candidateRoot ∧
      get_latest_confirmed witnessConfig witnessExternals queryFcr =
        candidateRoot ∧
      candidateRoot ≠ parentRoot := by
  set_option maxRecDepth 30000 in
    decide

def directQueryRuntime : Runtime WitnessRoot :=
  initRuntime witnessConfig queryFcr .updateInitialSlot

set_option maxRecDepth 50000 in
/-- The query is legal before this slot's update; it is not inserted into the
forbidden update/mandatory-writeback gap. -/
theorem direct_extra_query_is_legal_preUpdate :
    queryFcr.store = actorPrefix.store witnessConfig witnessExternals ∧
      directQueryRuntime.awaitingMandatoryQuery = false ∧
      wallSlot witnessConfig directQueryRuntime.elapsedMs ∉
        directQueryRuntime.updatedSlots ∧
      ∃ after,
        step? witnessConfig witnessExternals directQueryRuntime
          (.query .extra) = some after ∧
        after.observations.getLast?.map QueryObservation.result =
          some candidateRoot ∧
        after.observations.getLast?.map QueryObservation.writeBack =
          some .exposeOnly := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change wallSlot witnessConfig directQueryRuntime.elapsedMs ∉
      (∅ : Finset Slot)
    simp
  have hready : directQueryRuntime.awaitingMandatoryQuery = false := rfl
  have hexists : ∃ after,
      step? witnessConfig witnessExternals directQueryRuntime
        (.query .extra) = some after := by
    simp only [step?, hready, Bool.false_eq_true, if_false]
    exact ⟨_, rfl⟩
  obtain ⟨after, hstep⟩ := hexists
  have hexact : ∃ observation,
      after.observations = directQueryRuntime.observations ++ [observation] ∧
        observation.result = get_latest_confirmed witnessConfig witnessExternals
          directQueryRuntime.fcrStore ∧
        observation.writeBack = .exposeOnly := by
    set_option maxRecDepth 30000 in
      simp only [step?] at hstep
      split at hstep
      · contradiction
      · cases hstep
        exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨observation, hobservations, hresult, hwriteBack⟩ := hexact
  refine ⟨after, hstep, ?_, ?_⟩
  · rw [hobservations]
    simp only [directQueryRuntime, initRuntime, List.nil_append,
      List.getLast?_singleton, Option.map_some]
    exact congrArg some (hresult.trans strict_extra_query_result.2.2.1)
  · rw [hobservations]
    simp only [directQueryRuntime, initRuntime, List.nil_append,
      List.getLast?_singleton, Option.map_some]
    exact congrArg some hwriteBack

/-! ## Same-position global query witness -/

def endpointFcr : FastConfirmationStore WitnessRoot :=
  { witnessExecution.fcr witnessConfig witnessExternals 1 2 with
    store := endpointPrefix.store witnessConfig witnessExternals }

def endpointRuntime : Runtime WitnessRoot :=
  initRuntime witnessConfig endpointFcr .updateInitialSlot

def globalInitial : GlobalRuntime WitnessRoot where
  nodeState := fun node =>
    if node = 0 then directQueryRuntime
    else if node = 1 then endpointRuntime
    else endpointRuntime
  voteCasts := []
  nextGlobalActionPosition := 0

def globalActions : List (GlobalAction WitnessRoot) :=
  [.nodeAction 0 (.query .extra)]

def directQueryAfter : Runtime WitnessRoot :=
  (step? witnessConfig witnessExternals directQueryRuntime
    (.query .extra)).getD directQueryRuntime

def globalAfter : GlobalRuntime WitnessRoot where
  nodeState := Function.update globalInitial.nodeState 0 directQueryAfter
  voteCasts := []
  nextGlobalActionPosition := 1

private theorem directQueryStep :
    step? witnessConfig witnessExternals directQueryRuntime
      (.query .extra) = some directQueryAfter := by
  rcases direct_extra_query_is_legal_preUpdate with
    ⟨_hstore, _hmandatory, _hslot, after, hstep, _hresult, _hwriteback⟩
  simp [directQueryAfter, hstep]

private theorem directQueryAfter_result :
    directQueryAfter.observations.getLast?.map QueryObservation.result =
      some candidateRoot := by
  rcases direct_extra_query_is_legal_preUpdate with
    ⟨_hstore, _hmandatory, _hslot, after, hstep, hresult, _hwriteback⟩
  have hafter : directQueryAfter = after := by
    simp [directQueryAfter, hstep]
  rwa [hafter]

private theorem globalQueryStep :
    globalStep? witnessConfig witnessExternals globalInitial
      (.nodeAction 0 (.query .extra)) = some globalAfter := by
  have hreseated :
      step? witnessConfig witnessExternals
        { directQueryRuntime with nextActionPosition := 0 }
        (.query .extra) = some directQueryAfter := by
    simpa [directQueryRuntime, initRuntime] using directQueryStep
  set_option maxRecDepth 30000 in
    simp [globalStep?, globalInitial, globalAfter, hreseated]

/-- The global interpreter reaches the query at an exact action position.  In
the pre-query global state, node zero has processed the synchronized vote while
node one has processed only the preceding sibling block from the same schedule
and second. -/
def GlobalPinnedEconomicsStrictPrefixQuerySnapshot : Prop :=
    GlobalQuerySnapshot witnessConfig witnessExternals globalInitial
        globalActions 0 globalInitial globalAfter ∧
      (globalInitial.nodeState 0).fcrStore.store =
        actorPrefix.store witnessConfig witnessExternals ∧
      (globalInitial.nodeState 1).fcrStore.store =
        endpointPrefix.store witnessConfig witnessExternals ∧
      (globalAfter.nodeState 0).observations.getLast?.map
          QueryObservation.result = some candidateRoot

theorem global_pinned_economics_strict_prefix_query_snapshot :
    GlobalPinnedEconomicsStrictPrefixQuerySnapshot := by
  set_option maxRecDepth 30000 in
    refine ⟨?_, rfl, rfl, ?_⟩
  · exact
      { prefixRun := rfl
        action := ⟨0, .extra, by decide, rfl⟩
        accepted := globalQueryStep }
  · simpa [globalAfter] using directQueryAfter_result

/-! ## Public bundled regression -/

/-- Every non-FFG execution and environment assumption used by this regression
is a proved property of the finite model.  The final equations expose the
pinned economic constants and the exact parent/candidate/sibling topology.

The `Synchrony` conjunct is the single synchrony assumption: its delivery
clause now carries the boundary case that used to appear here as a separate
`HorizonVoteDeliveryLookahead` conjunct, so the environment asserted is the
same one as before the merge. -/
def PinnedEconomicsStrictPrefixWitnessEnvironment : Prop :=
    (∃ st block,
        witnessExecution.genesis_store =
          get_forkchoice_store witnessConfig st block ∧
        st.slot = block.message.slot ∧
        block.message.parent_root ≠ block.root) ∧
      WellFormedExecution witnessExecution ∧
      1000 ∣ witnessConfig.slot_duration_ms ∧
      HonestBehavior witnessConfig witnessExternals witnessExecution ∧
      Synchrony witnessConfig witnessExternals witnessExecution ∧
      BeaconExternalsPremises witnessConfig witnessExternals witnessExecution ∧
      StaticValidatorSet witnessConfig witnessExecution ∧
      ByzantineWeightPremises witnessConfig witnessExecution ∧
      witnessConfig.proposer_score_boost = 40 ∧
      witnessConfig.confirmation_byzantine_threshold = 25 ∧
      (∀ n, witnessExecution.time_at n = n) ∧
      (∀ n, witnessExecution.slot_at witnessConfig n = n) ∧
      (∀ s, witnessExecution.slot_start witnessConfig s = s) ∧
      (∀ w w' n,
        witnessExecution.schedule w n = witnessExecution.schedule w' n) ∧
      (∀ s, witnessExecution.committee s = {s % 4}) ∧
      (∀ v s n a, witnessExecution.vote v s = some (n, a) ↔
        (v = 0 ∧ s = 0 ∧ n = 0 ∧ a = vote0) ∨
        (v = 1 ∧ s = 1 ∧ n = 1 ∧ a = vote1) ∨
        (v = 2 ∧ s = 2 ∧ n = 2 ∧ a = vote2) ∨
        (v = 3 ∧ s = 3 ∧ n = 3 ∧ a = vote3)) ∧
      parentSignedBlock.message.parent_root = anchorRoot ∧
      candidateSignedBlock.message.parent_root = parentRoot ∧
      siblingSignedBlock.message.parent_root = parentRoot

theorem pinned_economics_strict_prefix_witness_environment :
    PinnedEconomicsStrictPrefixWitnessEnvironment := by
  refine ⟨⟨anchorState, anchorSignedBlock, rfl, rfl, by decide⟩,
    witnessWellFormedExecution, by decide, witnessHonestBehavior,
    witnessSynchrony,
    witnessExternalsCoherence, witnessStaticValidatorSet,
    witnessByzantineBound, rfl, rfl, time_at_eq, slot_at_eq, slot_start_eq,
    schedule_node_independent, ?_, ?_, rfl, rfl, rfl⟩
  · intro s
    rfl
  · intro v s n a
    exact vote_some_cases

/-- Public pinned-economics counterexample.  A well-formed, fully synchronous,
all-honest execution with proposer boost `40` and adversarial allowance `25`
admits a source-permitted pre-update extra query.  At one exact global action
position that query returns `candidate`, even though another honest node's
same-second prefix has head `sibling` and `candidate` is not its ancestor.

The statement does not assume safety, canonicality, a future head, or accepted
FFG semantics. -/
theorem extra_query_changes_head_counterexample :
    PinnedEconomicsStrictPrefixWitnessEnvironment ∧
      GlobalPinnedEconomicsStrictPrefixQuerySnapshot ∧
      0 ∈ witnessExecution.honest ∧
      1 ∈ witnessExecution.honest ∧
      witnessExecution.WithinHorizon witnessConfig 3 ∧
      actorPrefix.node = 0 ∧
      endpointPrefix.node = 1 ∧
      actorPrefix.previousSecond = endpointPrefix.previousSecond ∧
      actorPrefix.processedCount = 2 ∧
      endpointPrefix.processedCount = 1 ∧
      get_attestation_score witnessConfig
          (globalInitial.nodeState 0).fcrStore.store
          (get_node_for_root candidateRoot)
          (get_current_balance_source
            (globalInitial.nodeState 0).fcrStore) = 100 ∧
      compute_proposer_score witnessConfig
          (get_current_balance_source
            (globalInitial.nodeState 0).fcrStore) = 40 ∧
      get_adversarial_weight witnessConfig witnessExternals
          (globalInitial.nodeState 0).fcrStore.store
          (get_current_balance_source
            (globalInitial.nodeState 0).fcrStore) candidateRoot = 25 ∧
      compute_safety_threshold witnessConfig witnessExternals
          (globalInitial.nodeState 0).fcrStore.store candidateRoot
          (get_current_balance_source
            (globalInitial.nodeState 0).fcrStore) = 95 ∧
      get_latest_confirmed witnessConfig witnessExternals
          (globalInitial.nodeState 0).fcrStore = candidateRoot ∧
      (get_head witnessConfig
          (globalInitial.nodeState 1).fcrStore.store).root = siblingRoot ∧
      is_ancestor (globalInitial.nodeState 1).fcrStore.store
        (get_head witnessConfig
          (globalInitial.nodeState 1).fcrStore.store)
        (get_node_for_root candidateRoot) = false ∧
      candidateRoot ≠ siblingRoot := by
  refine ⟨pinned_economics_strict_prefix_witness_environment,
    global_pinned_economics_strict_prefix_query_snapshot,
    by decide, by decide, within_of_lt_four (by decide),
    rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · set_option maxRecDepth 30000 in
      change get_attestation_score witnessConfig queryFcr.store
        (get_node_for_root candidateRoot)
        (get_current_balance_source queryFcr) = 100
    exact candidate_pinned_economic_calculation.1
  · set_option maxRecDepth 30000 in
      change compute_proposer_score witnessConfig
        (get_current_balance_source queryFcr) = 40
    exact candidate_pinned_economic_calculation.2.1
  · set_option maxRecDepth 30000 in
      change get_adversarial_weight witnessConfig witnessExternals queryFcr.store
        (get_current_balance_source queryFcr) candidateRoot = 25
    exact candidate_pinned_economic_calculation.2.2.1
  · set_option maxRecDepth 30000 in
      change compute_safety_threshold witnessConfig witnessExternals queryFcr.store
        candidateRoot (get_current_balance_source queryFcr) = 95
    exact candidate_pinned_economic_calculation.2.2.2.1
  · set_option maxRecDepth 30000 in
      change get_latest_confirmed witnessConfig witnessExternals queryFcr =
        candidateRoot
    exact strict_extra_query_result.2.2.1
  · set_option maxRecDepth 30000 in
      change (get_head witnessConfig
        (endpointPrefix.store witnessConfig witnessExternals)).root = siblingRoot
    exact strict_prefix_heads_diverge.2.1
  · set_option maxRecDepth 30000 in
      change is_ancestor
        (endpointPrefix.store witnessConfig witnessExternals)
        (get_head witnessConfig
          (endpointPrefix.store witnessConfig witnessExternals))
        (get_node_for_root candidateRoot) = false
    exact strict_prefix_heads_diverge.2.2


end PinnedEconomicsExtraQuery
end FastConfirmation.Spec

end
