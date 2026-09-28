module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.BridgeFixture
public import FastConfirmationProofs.Execution.Trajectory.PayloadPersistence
public import FastConfirmationProofs.Safety.ConfirmedCacheSafety
public import FastConfirmationProofs.Handlers.BlockTransitionProvenance
public import FastConfirmationProofs.Execution.Calls.ScheduledPrefixGeometry
public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Bridge run for the Byzantine witness

This run adapts the target-edge run. It has four epochs, one-second slots,
four honest validators, and one non-honest validator 4. Validators 0, 1, and 2
have weight 1000. Validator 3 has weight 800 and validator 4 has weight 200.
Validator 4 is always in the committee of validator 3. Thus every slot
committee has weight 1000, and the per-span non-honest share is at most 20%.

Validator 4 signs two different slot-four votes with the same target epoch.
Every node applies the resulting attester slashing at second five. The call
from second six to seven reads the equivocation and confirms the child.

Odd epochs reverse the committee order, and epoch two rotates it. Thus a
committee suffix before an epoch boundary overlaps the prefix after it, as
the committee union estimate requires. The slot-15 vote arrives at second 16,
outside the horizon.

The setup takes `zeroRoot := anchorRoot`, as `NextSlotBridgeRun` does. The
state functions of the run are `witnessBridge.interface`; the proofs evaluate
stores with the computable copy `witnessExternals`.
-/

namespace FastConfirmation.Spec
namespace ByzantineBridgeRun

open ConcreteFFG

abbrev WitnessRoot := Fin 5

def junkRoot : WitnessRoot := 0
def anchorRoot : WitnessRoot := 1
def childRoot : WitnessRoot := 2
def carrierRoot : WitnessRoot := 3
def dRoot : WitnessRoot := 4

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

def anchorCheckpoint : Checkpoint WitnessRoot := { epoch := 0, root := anchorRoot }
def childEpochOneCheckpoint : Checkpoint WitnessRoot := { epoch := 1, root := childRoot }
def carrierEpochTwoCheckpoint : Checkpoint WitnessRoot := { epoch := 2, root := carrierRoot }
def carrierEpochThreeCheckpoint : Checkpoint WitnessRoot := { epoch := 3, root := carrierRoot }
def dEpochThreeCheckpoint : Checkpoint WitnessRoot := { epoch := 3, root := dRoot }

/-! ## The concrete setup -/

def witnessPreset : FFGPreset where
  slots_per_historical_root := 8
  max_committees_per_slot := 1
  max_validators_per_committee := 4
  max_attestations := 4
  max_proposer_slashings := 0
  max_attester_slashings := 0
  max_voluntary_exits := 0
  max_bls_to_execution_changes := 0
  max_payload_attestations := 0
  min_attestation_inclusion_delay := 1
  ring_pos := by decide
  min_delay_pos := by decide

def witnessValidatorOf (balance : Gwei) : Validator :=
  { effective_balance := balance
    slashed := false
    activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH }

def witnessValidator : Validator := witnessValidatorOf 1000

/-- The non-honest validator. -/
def byzantineIndex : ValidatorIndex := 4

def witnessScope : FixedFFGScope where
  validators := [witnessValidator, witnessValidator, witnessValidator,
    witnessValidatorOf 800, witnessValidatorOf 200]
  first_epoch := 0
  last_epoch := 3
  epoch_order := by decide
  activity_fixed := by decide

/-- Reverse each odd epoch so committees across its boundary overlap.
Epoch two rotates its order to `3, 0, 1, 2`. Its first two slots still
overlap the last two slots of epoch one, and its last two slots overlap the
first two slots of epoch three. -/
def committeeIndex (s : Slot) : ValidatorIndex :=
  if s / 4 % 4 = 2 then (s % 4 + 3) % 4
  else if s / 4 % 2 = 0 then s % 4 else 3 - s % 4

/-- The slot committee: validator 4 is always with validator 3. -/
def committeeList (s : Slot) : List ValidatorIndex :=
  if committeeIndex s = 3 then [3, byzantineIndex] else [committeeIndex s]

theorem committeeIndex_lt_four (s : Slot) : committeeIndex s < 4 := by
  have := Nat.mod_lt s (by decide : 0 < 4)
  unfold committeeIndex
  split_ifs <;> simp only [Slot, ValidatorIndex] at * <;> omega

/-- One committee per slot. -/
def committeeSchedule : FixedCommitteeSchedule where
  committees := (List.range 20).map fun s => (s, 0, committeeList s)
  counts := (List.range 5).map fun e => (e, 1)

def witnessOracle : BlockValidityOracle WitnessRoot := ⟨fun _ _ _ => true⟩

def witnessSetup : FFGSetup WitnessRoot where
  cfg := witnessConfig
  preset := witnessPreset
  scope := witnessScope
  schedule := committeeSchedule
  oracle := witnessOracle
  zeroRoot := anchorRoot
  genesisRoot := anchorRoot
  genesisTime := 0

/-! ## Wire blocks and concrete states -/

def childWire : FFGWireBlock WitnessRoot where
  slot := 4
  parent_root := anchorRoot
  proposer_index := 0
  root := childRoot
  parent_block_hash := anchorRoot
  block_hash := anchorRoot
  parent_requests_empty := true
  parent_requests_match := true
  attestations := []

/-- A wire vote of the committee member `committeeIndex s`. -/
def wireVote (s : Slot) : FFGWireAttestation WitnessRoot where
  aggregation_bits := if committeeIndex s = 3 then [true, false] else [true]
  committee_bits := [true]
  data := ⟨s, 0, childRoot, anchorCheckpoint, childEpochOneCheckpoint⟩
  signature := 0

def carrierWire : FFGWireBlock WitnessRoot where
  slot := 8
  parent_root := childRoot
  proposer_index := 0
  root := carrierRoot
  parent_block_hash := childRoot
  block_hash := childRoot
  parent_requests_empty := true
  parent_requests_match := true
  attestations := [wireVote 4, wireVote 5, wireVote 6]

/-- A wire vote of slot `s` with the carrier head and the epoch-two target. -/
def wireVoteD (s : Slot) : FFGWireAttestation WitnessRoot where
  aggregation_bits := if committeeIndex s = 3 then [true, false] else [true]
  committee_bits := [true]
  data := ⟨s, 0, carrierRoot, anchorCheckpoint, carrierEpochTwoCheckpoint⟩
  signature := 0

/-- Block D at slot 11, the last slot of epoch 2. Its body has the votes of
slots 8 to 10. -/
def dWire : FFGWireBlock WitnessRoot where
  slot := 11
  parent_root := carrierRoot
  proposer_index := 0
  root := dRoot
  parent_block_hash := carrierRoot
  block_hash := carrierRoot
  parent_requests_empty := true
  parent_requests_match := true
  attestations := [wireVoteD 8, wireVoteD 9, wireVoteD 10]

def childFFGState : FFGBeaconState WitnessRoot where
  genesis_time := 0
  slot := 4
  validators := witnessScope.validators
  justification_bits := [false, false, false, false]
  previous_justified_checkpoint := ⟨0, anchorRoot⟩
  current_justified_checkpoint := ⟨0, anchorRoot⟩
  finalized_checkpoint := ⟨0, anchorRoot⟩
  previous_epoch_participation := [0, 0, 0, 0, 0]
  current_epoch_participation := [0, 0, 0, 0, 0]
  block_roots := [anchorRoot, anchorRoot, anchorRoot, anchorRoot,
    anchorRoot, anchorRoot, anchorRoot, anchorRoot]
  latest_block_header := ⟨4, 0, anchorRoot, childRoot⟩
  execution_payload_availability := [true, false, false, false, false, false, false, false]
  latest_block_hash := anchorRoot
  latest_bid_block_hash := anchorRoot

def carrierFFGState : FFGBeaconState WitnessRoot where
  genesis_time := 0
  slot := 8
  validators := witnessScope.validators
  justification_bits := [false, false, false, false]
  previous_justified_checkpoint := ⟨0, anchorRoot⟩
  current_justified_checkpoint := ⟨0, anchorRoot⟩
  finalized_checkpoint := ⟨0, anchorRoot⟩
  previous_epoch_participation := [0, 3, 2, 2, 0]
  current_epoch_participation := [0, 0, 0, 0, 0]
  block_roots := [anchorRoot, anchorRoot, anchorRoot, anchorRoot,
    childRoot, childRoot, childRoot, childRoot]
  latest_block_header := ⟨8, 0, childRoot, carrierRoot⟩
  execution_payload_availability := [false, false, false, false, false, false, false, false]
  latest_block_hash := anchorRoot
  latest_bid_block_hash := childRoot

def dFFGState : FFGBeaconState WitnessRoot where
  genesis_time := 0
  slot := 11
  validators := witnessScope.validators
  justification_bits := [false, false, false, false]
  previous_justified_checkpoint := ⟨0, anchorRoot⟩
  current_justified_checkpoint := ⟨0, anchorRoot⟩
  finalized_checkpoint := ⟨0, anchorRoot⟩
  previous_epoch_participation := [0, 3, 2, 2, 0]
  current_epoch_participation := [3, 7, 0, 2, 0]
  block_roots := [carrierRoot, carrierRoot, carrierRoot, anchorRoot,
    childRoot, childRoot, childRoot, childRoot]
  latest_block_header := ⟨11, 0, carrierRoot, dRoot⟩
  execution_payload_availability := [false, false, false, false, false, false, false, false]
  latest_block_hash := anchorRoot
  latest_bid_block_hash := carrierRoot

theorem child_transition :
    state_transition witnessConfig witnessPreset committeeSchedule witnessOracle
      witnessSetup.genesis childWire = .ok childFFGState := by
  rw [state_transition_eq_pointwise]
  decide +kernel

theorem carrier_transition :
    state_transition witnessConfig witnessPreset committeeSchedule witnessOracle
      childFFGState carrierWire = .ok carrierFFGState := by
  rw [state_transition_eq_pointwise]
  decide +kernel

theorem d_transition :
    state_transition witnessConfig witnessPreset committeeSchedule witnessOracle
      carrierFFGState dWire = .ok dFFGState := by
  rw [state_transition_eq_pointwise]
  decide +kernel

/-! ## The bridge -/

def stateEntries : List (WitnessRoot × FFGBeaconState WitnessRoot) :=
  [(anchorRoot, witnessSetup.genesis), (childRoot, childFFGState),
    (carrierRoot, carrierFFGState), (dRoot, dFFGState)]

theorem stateEntries_nodup : (stateEntries.map Prod.snd).Nodup := by decide +kernel

def blockEntries : List (WitnessRoot × (FFGWireBlock WitnessRoot × WitnessRoot)) :=
  [(childRoot, (childWire, childRoot)), (carrierRoot, (carrierWire, carrierRoot)),
    (dRoot, (dWire, dRoot))]

/-! ### Ground honest votes -/

def voteData (slot : Slot) : AttestationData WitnessRoot :=
  if slot = 0 then
    { slot := slot, index := 0, beacon_block_root := anchorRoot
      source := anchorCheckpoint, target := anchorCheckpoint }
  else if slot < 4 then
    { slot := slot, index := 0, beacon_block_root := anchorRoot
      source := anchorCheckpoint, target := anchorCheckpoint }
  else if slot < 8 then
    { slot := slot, index := 0, beacon_block_root := childRoot
      source := anchorCheckpoint, target := childEpochOneCheckpoint }
  else if slot < 11 then
    { slot := slot, index := 0, beacon_block_root := carrierRoot
      source := anchorCheckpoint, target := carrierEpochTwoCheckpoint }
  else if slot < 12 then
    { slot := slot, index := 0, beacon_block_root := dRoot
      source := anchorCheckpoint, target := carrierEpochTwoCheckpoint }
  else
    { slot := slot, index := 0, beacon_block_root := dRoot
      source := carrierEpochTwoCheckpoint, target := dEpochThreeCheckpoint }

def vote (slot : Slot) : Attestation WitnessRoot :=
  { attesting_indices := [committeeIndex slot], data := voteData slot }

def groundVotes : List (Attestation WitnessRoot) := (List.range 16).map vote

/-! ### Byzantine double vote -/

/-- The recorded slot-four vote of validator 4 uses the child head. -/
def byzantineVoteChild : Attestation WitnessRoot :=
  { attesting_indices := [byzantineIndex], data := voteData 4 }

/-- The second slot-four vote uses the anchor head and the same target epoch. -/
def byzantineVoteAnchor : Attestation WitnessRoot :=
  { attesting_indices := [byzantineIndex]
    data :=
      { slot := 4, index := 0, beacon_block_root := anchorRoot
        source := anchorCheckpoint, target := { epoch := 1, root := anchorRoot } } }

def byzantineVotes : List (Attestation WitnessRoot) :=
  [byzantineVoteChild, byzantineVoteAnchor]

def byzantineSlashing : AttesterSlashing WitnessRoot :=
  { attestation_1 := byzantineVoteChild, attestation_2 := byzantineVoteAnchor }

/-- The base interface: signature checks accept exactly the ground votes and
the two Byzantine votes on a state with a registry. Envelope and PTC methods
keep their defaults. -/
def baseExternals : BeaconFunctionInterface WitnessRoot where
  get_beacon_committee := fun _ slot _ => committeeList slot
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st _ => st
  state_transition := fun _ _ => none
  process_justification_and_finalization := fun st => st
  is_valid_indexed_attestation := fun state a =>
    decide (state.validators ≠ [] ∧ (a ∈ groundVotes ∨ a ∈ byzantineVotes))

def witnessBridge : ConcreteBridge WitnessRoot where
  setup := witnessSetup
  states := tableStates stateEntries junkRoot stateEntries_nodup
  blocks := tableBlocks blockEntries
  base := baseExternals

/-- The computable copy of `witnessBridge.interface`. -/
def witnessExternals : BeaconFunctionInterface WitnessRoot := lookupInterface witnessBridge

def anchorState : BeaconState WitnessRoot := witnessBridge.project witnessSetup.genesis

def anchorSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 0, parent_root := junkRoot }
    root := anchorRoot }

def childSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 4, parent_root := anchorRoot }
    root := childRoot }

/-- The carrier message has the indexed forms of the three wire votes. -/
def carrierSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 8, parent_root := childRoot, attestations := [vote 4, vote 5, vote 6] }
    root := carrierRoot }

/-- The message of D has the indexed forms of its three wire votes. -/
def dSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 11, parent_root := carrierRoot, attestations := [vote 8, vote 9, vote 10] }
    root := dRoot }

/-! ### The decode domain -/

theorem stateEntries_cases {id : WitnessRoot} {state : FFGBeaconState WitnessRoot}
    (h : witnessBridge.states.open_ id = some state) :
    (id = anchorRoot ∧ state = witnessSetup.genesis) ∨
      (id = childRoot ∧ state = childFFGState) ∨
      (id = carrierRoot ∧ state = carrierFFGState) ∨
      (id = dRoot ∧ state = dFFGState) := by
  have hmem := tableOpen_mem (entries := stateEntries) h
  simpa [stateEntries] using hmem

theorem witness_inDomain :
    ∀ id state, witnessBridge.states.open_ id = some state → witnessBridge.InDomain state := by
  intro id state h
  rcases stateEntries_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨⟨[], [], .genesis⟩, by decide +kernel⟩
  · exact ⟨⟨_, _, .block childWire .genesis child_transition⟩, by decide +kernel⟩
  · exact ⟨⟨_, _, .block carrierWire (.block childWire .genesis child_transition)
      carrier_transition⟩, by decide +kernel⟩
  · exact ⟨⟨_, _, .block dWire (.block carrierWire (.block childWire .genesis
      child_transition) carrier_transition) d_transition⟩, by decide +kernel⟩

/-- **The run interface is the computable copy.** -/
theorem interface_eq : witnessBridge.interface = witnessExternals :=
  interface_eq_lookupInterface witnessBridge witness_inDomain

theorem open_validators {id : WitnessRoot} {state : FFGBeaconState WitnessRoot}
    (h : witnessBridge.states.open_ id = some state) :
    state.validators = witnessScope.validators := by
  rcases stateEntries_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-! ## Schedule and execution -/

/-- Symmetric schedule. False copies implement ordinary gossip. At second
eight the slot-seven receipt precedes the carrier; the true copies after it
are the three attestations of the carrier body. -/
def witnessSchedule (_w : ValidatorIndex) (n : ℕ) : List (Event WitnessRoot) :=
  if n = 4 then [Event.block childSignedBlock, Event.attestation (vote 3) false]
  else if n = 5 then
    [Event.attestation (vote 4) false, Event.attester_slashing byzantineSlashing]
  else if n = 8 then
    [Event.attestation (vote 7) false, Event.block carrierSignedBlock,
      Event.attestation (vote 4) true, Event.attestation (vote 5) true,
      Event.attestation (vote 6) true]
  else if n = 11 then
    [Event.attestation (vote 10) false, Event.block dSignedBlock,
      Event.attestation (vote 8) true, Event.attestation (vote 9) true,
      Event.attestation (vote 10) true]
  else if 1 ≤ n ∧ n ≤ 16 then
    [Event.attestation (vote (n - 1)) false]
  else []

def witnessCommittee (slot : Slot) : Finset ValidatorIndex :=
  if committeeIndex slot = 3 then {3, byzantineIndex} else {committeeIndex slot}

def witnessVote (v : ValidatorIndex) (slot : Slot) : Option (ℕ × Attestation WitnessRoot) :=
  if slot < 16 ∧ v = committeeIndex slot then some (slot, vote slot)
  else if v = byzantineIndex ∧ slot = 4 then some (4, byzantineVoteChild)
  else none

def witnessExecution : Execution WitnessRoot where
  verification_horizon := 4
  genesis_store := get_forkchoice_store witnessConfig anchorState anchorSignedBlock
  schedule := witnessSchedule
  honest := {0, 1, 2, 3}
  committee := witnessCommittee
  vote := witnessVote

def confirmingFcr : FastConfirmationStore WitnessRoot :=
  witnessExecution.fcrStoreAtCall witnessConfig witnessExternals 0 6

/-! ## Clock and finite classifiers -/

theorem genesis_store_time : witnessExecution.genesis_store.time = 0 := by decide +kernel

theorem genesis_store_genesis_time : witnessExecution.genesis_store.genesis_time = 0 := by
  decide +kernel

theorem time_at_eq (n : ℕ) : witnessExecution.time_at n = n := by
  simp [Execution.time_at, genesis_store_time]

theorem slot_at_eq (n : ℕ) : witnessExecution.slot_at witnessConfig n = n := by
  simp [Execution.slot_at, time_at_eq, genesis_store_genesis_time, witnessConfig, GENESIS_SLOT]

theorem slot_start_eq (s : Slot) : witnessExecution.slot_start witnessConfig s = s := by
  simp [Execution.slot_start, genesis_store_time, genesis_store_genesis_time, witnessConfig]

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
    (hv : v ∈ witnessExecution.honest) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  simpa [witnessExecution] using hv

theorem honest_ne_byzantine {v : ValidatorIndex}
    (hv : v ∈ witnessExecution.honest) : v ≠ byzantineIndex := by
  rcases honest_eq_zero_or_one_or_two_or_three hv with rfl | rfl | rfl | rfl <;> decide

theorem byzantine_not_honest : byzantineIndex ∉ witnessExecution.honest := by
  decide

theorem mem_witnessCommittee_iff {i : ValidatorIndex} {s : Slot} :
    i ∈ witnessCommittee s ↔
      i = committeeIndex s ∨ (committeeIndex s = 3 ∧ i = byzantineIndex) := by
  unfold witnessCommittee
  by_cases h : committeeIndex s = 3
  · rw [ite_eq_left h, h]
    simp
  · rw [ite_eq_right h]
    simp [h]

theorem registry_eq : witnessExecution.registry = witnessScope.validators := by
  decide +kernel

theorem witness_vote_some_iff {v : ValidatorIndex} {s : Slot} {n : ℕ}
    {a : Attestation WitnessRoot} (hvByz : v ≠ byzantineIndex) :
    witnessExecution.vote v s = some (n, a) ↔
      s < 16 ∧ v = committeeIndex s ∧ n = s ∧ a = vote s := by
  change (if s < 16 ∧ v = committeeIndex s then some (s, vote s)
      else if v = byzantineIndex ∧ s = 4 then some (4, byzantineVoteChild)
      else none) = some (n, a) ↔ _
  by_cases h : s < 16 ∧ v = committeeIndex s
  · rw [ite_eq_left h]
    constructor
    · intro heq
      have hp : (s, vote s) = (n, a) := Option.some.inj heq
      exact ⟨h.1, h.2, (congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rw [ite_eq_right h, ite_eq_right (fun hbyz => hvByz hbyz.1)]
    constructor
    · intro himpossible
      contradiction
    · rintro ⟨hs, hv, -, -⟩
      exact (h ⟨hs, hv⟩).elim

theorem byzantine_vote_recorded :
    witnessExecution.vote byzantineIndex 4 = some (4, byzantineVoteChild) := by
  decide +kernel

theorem byzantineVote_attesters {a : Attestation WitnessRoot}
    (ha : a ∈ byzantineVotes) {i : ValidatorIndex} (hi : i ∈ a.attesting_indices) :
    i = byzantineIndex ∧ a.data.slot = 4 := by
  simp only [byzantineVotes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> simpa [byzantineVoteChild, byzantineVoteAnchor, voteData] using hi

theorem vote_mem_ground {s : Slot} (hs : s < 16) : vote s ∈ groundVotes :=
  List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩

theorem groundVote_exists {a : Attestation WitnessRoot} (ha : a ∈ groundVotes) :
    ∃ s : Slot, s < 16 ∧ a = vote s := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  exact ⟨s, List.mem_range.mp hs, rfl⟩

theorem vote_data_slot (s : Slot) : (vote s).data.slot = s := by
  simp only [vote, voteData]
  split_ifs <;> simp_all

/-- The indexed validity check of the run: the fixed-schedule structure check
and the ground-vote signature check. -/
theorem witness_valid_iff (state : BeaconState WitnessRoot) (a : Attestation WitnessRoot) :
    witnessExternals.is_valid_indexed_attestation state a = true ↔
      legacy_indexed_structure witnessPreset state a = true ∧
        state.validators ≠ [] ∧ (a ∈ groundVotes ∨ a ∈ byzantineVotes) := by
  change (legacy_indexed_structure witnessPreset state a &&
    decide (state.validators ≠ [] ∧ (a ∈ groundVotes ∨ a ∈ byzantineVotes))) = true ↔ _
  simp

theorem ground_structure {state : BeaconState WitnessRoot}
    (hreg : state.validators = witnessScope.validators) {s : Slot} :
    legacy_indexed_structure witnessPreset state (vote s) = true := by
  have hmod : committeeIndex s < 5 := (committeeIndex_lt_four s).trans (by decide)
  simp [legacy_indexed_structure, vote, hreg, witnessScope, witnessPreset, hmod]

/-! ## Direct executable checks -/

theorem find_latest_confirmed_descendant_strict_advance :
    find_latest_confirmed_descendant witnessConfig witnessExternals confirmingFcr
      anchorRoot = childRoot := by
  decide +kernel

theorem actual_fcr_transition_strict_advance :
    witnessExecution.confirmed witnessConfig witnessExternals 0 7 = childRoot := by
  decide +kernel

/-! ## Operational classifiers -/

theorem block_mem_schedule_iff {w n} {b : SignedBeaconBlock WitnessRoot} :
    Event.block b ∈ witnessExecution.schedule w n ↔
      (n = 4 ∧ b = childSignedBlock) ∨ (n = 8 ∧ b = carrierSignedBlock) ∨
        (n = 11 ∧ b = dSignedBlock) := by
  change Event.block b ∈ witnessSchedule w n ↔ _
  by_cases h1 : n = 4
  · subst n
    simp [witnessSchedule]
  · by_cases h5 : n = 5
    · subst n
      simp [witnessSchedule]
    · by_cases h7 : n = 8
      · subst n
        simp [witnessSchedule]
      · by_cases h11 : n = 11
        · subst n
          simp [witnessSchedule]
        · simp [witnessSchedule, h1, h5, h7, h11]

theorem attestation_mem_schedule_ground {w n a ifb}
    (h : Event.attestation a ifb ∈ witnessExecution.schedule w n) : a ∈ groundVotes := by
  change Event.attestation a ifb ∈ witnessSchedule w n at h
  by_cases h1 : n = 4
  · subst n
    simp [witnessSchedule] at h
    rcases h with ⟨rfl, rfl⟩
    exact vote_mem_ground (s := 3) (by decide)
  · by_cases h5 : n = 5
    · subst n
      simp [witnessSchedule] at h
      rcases h with ⟨rfl, rfl⟩
      exact vote_mem_ground (s := 4) (by decide)
    · by_cases h7 : n = 8
      · subst n
        simp [witnessSchedule] at h
        rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
          exact vote_mem_ground (by decide)
      · by_cases h11 : n = 11
        · subst n
          simp [witnessSchedule] at h
          rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
            exact vote_mem_ground (by decide)
        · by_cases hb : 1 ≤ n ∧ n ≤ 16
          · simp [witnessSchedule, h1, h5, h7, h11, hb] at h
            rcases h with ⟨rfl, rfl⟩
            have hpred : n - 1 < n := Nat.sub_lt (by omega) (by decide)
            exact vote_mem_ground (s := n - 1) (hpred.trans_le hb.2)
          · simp [witnessSchedule, h1, h5, h7, h11, hb] at h

/-- Every scheduled copy of a ground vote is received after that vote's
recorded send second. -/
theorem scheduled_vote_sent_before {w n s ifb}
    (h : Event.attestation (vote s) ifb ∈ witnessExecution.schedule w n) : s ≤ n := by
  have vote_slot_eq {t : Slot} (heq : vote s = vote t) : s = t := by
    have hslot := congrArg (fun a : Attestation WitnessRoot => a.data.slot) heq
    simpa only [vote_data_slot] using hslot
  change Event.attestation (vote s) ifb ∈ witnessSchedule w n at h
  by_cases h1 : n = 4
  · subst n
    simp [witnessSchedule] at h
    have hs := vote_slot_eq h.1
    rw [hs]
    decide
  · by_cases h5 : n = 5
    · subst n
      simp [witnessSchedule] at h
      have hs := vote_slot_eq h.1
      rw [hs]
      decide
    · by_cases h7 : n = 8
      · subst n
        simp [witnessSchedule, h1] at h
        rcases h with h | h | h | h
        all_goals
          have hs := vote_slot_eq h.1
          rw [hs]
          decide
      · by_cases h11 : n = 11
        · subst n
          simp [witnessSchedule, h1] at h
          rcases h with h | h | h | h
          all_goals
            have hs := vote_slot_eq h.1
            rw [hs]
            decide
        · by_cases hb : 1 ≤ n ∧ n ≤ 16
          · simp [witnessSchedule, h1, h5, h7, h11, hb] at h
            have hs := vote_slot_eq h.1
            rw [hs]
            exact Nat.sub_le n 1
          · simp [witnessSchedule, h1, h5, h7, h11, hb] at h

theorem recorded_vote_of_attester {s : Slot} (hs : s < 16) {v : ValidatorIndex}
    (hvin : v ∈ (vote s).attesting_indices) :
    ∃ m a', witnessExecution.vote v (vote s).data.slot = some (m, a') ∧
      (vote s).data = a'.data := by
  have hv : v = committeeIndex s := by simpa [vote] using hvin
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

theorem genesis_roots_iff (r : WitnessRoot) :
    r ∈ witnessExecution.genesis_store.block_roots ↔ r = anchorRoot := by
  revert r
  decide +kernel

theorem witnessWellFormedExecution : WellFormedExecution witnessExecution := by
  constructor
  · intro w n b hb w' n' b' hb' hroot
    rcases block_mem_schedule_iff.mp hb with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      rcases block_mem_schedule_iff.mp hb' with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      first | rfl | exact absurd hroot (by decide)
  · intro w n b hb hgen
    rw [genesis_roots_iff] at hgen
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact absurd hgen (by decide)
  · intro r hr w n b hb
    rw [genesis_roots_iff] at hr
    subst r
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide +kernel

theorem honest_vote_recorded {s : Slot} (hs : s < 16) :
    witnessExecution.vote (committeeIndex s) s =
      some (s, honest_attestation witnessConfig witnessExternals
        (witnessExecution.store witnessConfig witnessExternals (committeeIndex s) s) s 0
          (committeeIndex s)) := by
  interval_cases s
  all_goals (set_option maxRecDepth 100000 in decide +kernel)

theorem ground_votes_not_slashable :
    ∀ (s t : Fin 16), committeeIndex s.val = committeeIndex t.val →
      is_slashable_attestation_data (vote s.val).data (vote t.val).data = false := by
  decide +kernel

theorem witnessHonestBehavior :
    HonestBehavior witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := slot_lt_sixteen hs
    have hvmod : v = committeeIndex s := by
      rcases mem_witnessCommittee_iff.mp hcommittee with h | ⟨_, h⟩
      · exact h
      · exact (honest_ne_byzantine hv h).elim
    subst v
    exact ⟨s, 0, time_within_of_lt_sixteen hslt, slot_at_eq s, honest_vote_recorded hslt⟩
  · intro v hv s n a hvote
    obtain ⟨_, _, rfl, _⟩ := (witness_vote_some_iff (honest_ne_byzantine hv)).mp hvote
    rw [slot_start_eq]
    simp
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨na, hna⟩
    rcases na with ⟨n, a⟩
    obtain ⟨hs, hvmod, _hn, _ha⟩ := (witness_vote_some_iff (honest_ne_byzantine hv)).mp hna
    exact mem_witnessCommittee_iff.mpr (Or.inl hvmod)
  · intro w n a ifb hschedule v hv hvin
    obtain ⟨s, hs, rfl⟩ := groundVote_exists (attestation_mem_schedule_ground hschedule)
    have hv : v = committeeIndex s := by simpa [vote] using hvin
    refine ⟨s, vote s, scheduled_vote_sent_before hschedule, ?_, rfl⟩
    rw [vote_data_slot]
    simp [witnessExecution, witnessVote, hs, hv]
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hs, hvmod, hn, ha⟩ := (witness_vote_some_iff (honest_ne_byzantine hv)).mp hvote
    obtain ⟨hs', hvmod', hn', ha'⟩ :=
      (witness_vote_some_iff (honest_ne_byzantine hv)).mp hvote'
    subst n a n' a'
    exact ground_votes_not_slashable ⟨s, hs⟩ ⟨s', hs'⟩ (hvmod.symm.trans hvmod')
  · intro v hv
    rcases honest_eq_zero_or_one_or_two_or_three hv with rfl | rfl | rfl | rfl <;>
      decide +kernel

/-! ## Registry and state-function laws -/

theorem witnessProcessSlots_registry (st : BeaconState WitnessRoot) (s : Slot) :
    (witnessExternals.process_slots st s).validators = st.validators := by
  rw [← interface_eq]
  exact witnessBridge.slots_validators st s

theorem witnessTransition_frame {st st' : BeaconState WitnessRoot}
    {b : SignedBeaconBlock WitnessRoot}
    (h : witnessExternals.state_transition st b = some st') :
    st'.slot = b.message.slot ∧ st.slot < b.message.slot ∧ st'.validators = st.validators := by
  rw [← interface_eq] at h
  exact witnessBridge.transition_frame h

theorem witnessTransition_registry (st : BeaconState WitnessRoot)
    (b : SignedBeaconBlock WitnessRoot) (st' : BeaconState WitnessRoot)
    (h : witnessExternals.state_transition st b = some st') :
    st'.validators = st.validators :=
  (witnessTransition_frame h).2.2

/-- Every successful transition of the run lands on a table state, whose
checkpoints are the anchor checkpoint. -/
theorem witnessTransition_checkpoints {st st' : BeaconState WitnessRoot}
    {b : SignedBeaconBlock WitnessRoot}
    (h : witnessExternals.state_transition st b = some st') :
    st'.current_justified_checkpoint = anchorCheckpoint ∧
      st'.finalized_checkpoint = anchorCheckpoint := by
  rw [← interface_eq] at h
  obtain ⟨-, -, stateRoot, cpost, -, -, -, -, -, hopen, -, rfl⟩ :=
    witnessBridge.transition_eq_some h
  rcases stateEntries_cases hopen with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    exact ⟨rfl, rfl⟩

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

theorem witness_reachable_registry {state : BeaconState WitnessRoot}
    (hstate : witnessExecution.ReachableValidationState witnessConfig witnessExternals state) :
    state.validators = witnessScope.validators := by
  obtain ⟨store, hstore, hstate⟩ := hstate
  have hreg := witnessCausalStore_registryConstant (hstore.causal witnessConfig witnessExternals)
  rw [← registry_eq]
  rcases hstate with ⟨root, hroot, rfl⟩ | ⟨checkpoint, hcheckpoint, rfl⟩
  · exact hreg.1 root hroot
  · exact hreg.2 checkpoint hcheckpoint

theorem active_index_lt_five {i : ValidatorIndex} {e : Epoch}
    (hactive : is_active_validator (witnessExecution.registry.getD i default) e = true) :
    i < 5 := by
  rw [registry_eq] at hactive
  by_contra hi
  have hnone : witnessScope.validators.getD i default = default := by
    simp [witnessScope, List.getD_eq_getElem?_getD, Nat.le_of_not_lt hi]
  rw [hnone] at hactive
  have hexit : (default : Validator).exit_epoch = 0 := rfl
  simp [is_active_validator, hexit] at hactive

/-- The slot offset of validator `i` in epoch `e`; validator 4 shares the
position of validator 3. -/
def committeePosition (e : Epoch) (i : ValidatorIndex) : Slot :=
  let j := if i = byzantineIndex then 3 else i
  if e % 4 = 2 then (j + 1) % 4
  else if e % 2 = 0 then j else 3 - j

theorem witness_committee_coverage_at {i : ValidatorIndex} {e : Epoch}
    (hi : i < 5) (he : e < 4) :
    ∃ s : Slot, witnessExecution.SlotWithinHorizon witnessConfig s ∧
      compute_epoch_at_slot witnessConfig s = e ∧ i ∈ witnessExecution.committee s := by
  refine ⟨e * 4 + committeePosition e i, slot_within_of_lt_sixteen ?_, ?_, ?_⟩
  all_goals interval_cases e <;> interval_cases i <;> decide

theorem slot_committee_eq {s : Slot} (hs : s < 16) (store : Store WitnessRoot) :
    get_slot_committee witnessConfig witnessExternals store s = witnessCommittee s := by
  have hread := witnessBridge.get_slot_committee_interface store s
  rw [← interface_eq]
  refine hread.trans ?_
  interval_cases s <;> decide +kernel

theorem witnessExternalsCoherence :
    BeaconExternalsPremises witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro st s _
    rw [← interface_eq]
    exact witnessBridge.slots_slot st s
  · intro state hscope
    rw [registry_eq]
    rcases hscope with hreachable | ⟨base, slot, hreachable, _hslot, rfl⟩
    · exact witness_reachable_registry hreachable
    · rw [witnessProcessSlots_registry]
      exact witness_reachable_registry hreachable
  · intro st b st' h
    exact (witnessTransition_frame h).1
  · intro st b st' h
    exact (witnessTransition_frame h).2.1
  · intro st b st' _ _ h
    obtain ⟨hj, hf⟩ := witnessTransition_checkpoints h
    rw [hj, hf]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · intro st hst
    rw [← interface_eq]
    exact witnessBridge.pjf_checkpoint_epoch st hst
  · refine ⟨?_, ?_⟩ <;> decide +kernel
  · intro v hv n s hn hs
    exact slot_committee_eq (slot_lt_sixteen hs) _
  · intro state a hreachable v hv hsingle hcommittee hvote
    rcases hvote with ⟨m, a', hvote, hdata⟩
    obtain ⟨hs, hvmod, hm, ha'⟩ := (witness_vote_some_iff (honest_ne_byzantine hv)).mp hvote
    subst m a'
    have ha : a = vote a.data.slot := by
      rcases a with ⟨idx, data⟩
      change idx = [v] at hsingle
      change data = (vote data.slot).data at hdata
      change v = committeeIndex data.slot at hvmod
      subst hsingle hvmod
      change (⟨[committeeIndex data.slot], data⟩ : Attestation WitnessRoot) =
        ⟨[committeeIndex data.slot], voteData data.slot⟩
      change data = voteData data.slot at hdata
      rw [← hdata]
    rw [ha]
    exact (witness_valid_iff state _).2
      ⟨ground_structure (witness_reachable_registry hreachable),
        by rw [witness_reachable_registry hreachable]; decide, Or.inl (vote_mem_ground hs)⟩
  · intro state a _hreachable hvalid v hv hvin
    rcases ((witness_valid_iff state a).mp hvalid).2.2 with haGround | haByz
    · obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
      exact recorded_vote_of_attester hs hvin
    · exact (honest_ne_byzantine hv (byzantineVote_attesters haByz hvin).1).elim
  · intro store store' a ifb _hpost hh i hi
    simp only [on_attestation] at hh
    split_ifs at hh with hv hvi
    cases hh
    rcases ((witness_valid_iff _ a).mp hvi).2.2 with haGround | haByz
    · obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
      have hi' : i = committeeIndex s := by simpa [vote] using hi
      rw [vote_data_slot]
      exact mem_witnessCommittee_iff.mpr (Or.inl hi')
    · obtain ⟨rfl, hslot⟩ := byzantineVote_attesters haByz hi
      rw [hslot]
      decide
  · intro i s s' hs hs' hepoch
    have hindex : committeeIndex s = committeeIndex s' := by
      rcases mem_witnessCommittee_iff.mp hs with his | ⟨h3, hbyz⟩ <;>
        rcases mem_witnessCommittee_iff.mp hs' with his' | ⟨h3', hbyz'⟩
      · exact his.symm.trans his'
      · have := committeeIndex_lt_four s
        rw [← his, hbyz'] at this
        exact absurd this (by decide)
      · have := committeeIndex_lt_four s'
        rw [← his', hbyz] at this
        exact absurd this (by decide)
      · exact h3.trans h3'.symm
    have hdiv : s / 4 = s' / 4 := by
      simpa [witnessConfig, compute_epoch_at_slot] using hepoch
    have hsmod := Nat.mod_lt s (by decide : 0 < 4)
    have hsmod' := Nat.mod_lt s' (by decide : 0 < 4)
    unfold committeeIndex at hindex
    rw [hdiv] at hindex
    split_ifs at hindex <;> simp only [Slot, ValidatorIndex] at * <;> omega
  · intro i e he hactive
    have helt : e < 4 := by simpa [witnessExecution] using he
    exact witness_committee_coverage_at (active_index_lt_five hactive) helt
  · intro i s hs hi
    have hslt := slot_lt_sixteen hs
    rw [registry_eq]
    interval_cases s <;>
      rcases mem_witnessCommittee_iff.mp hi with rfl | ⟨_, rfl⟩ <;> decide
  · intro a
    have hdefault : (default : BeaconState WitnessRoot).validators = [] := rfl
    change (legacy_indexed_structure witnessPreset default a &&
      decide ((default : BeaconState WitnessRoot).validators ≠ [] ∧
        (a ∈ groundVotes ∨ a ∈ byzantineVotes))) = false
    simp [hdefault]
  · intro state slot a _hreachable _hlt _hslotH hreg
    change (legacy_indexed_structure witnessPreset
        (witnessExternals.process_slots state slot) a &&
      decide ((witnessExternals.process_slots state slot).validators ≠ [] ∧
        (a ∈ groundVotes ∨ a ∈ byzantineVotes))) =
      (legacy_indexed_structure witnessPreset state a &&
        decide (state.validators ≠ [] ∧ (a ∈ groundVotes ∨ a ∈ byzantineVotes)))
    simp only [legacy_indexed_structure, hreg]
  · intro state signed o o'
    rfl

theorem witnessStaticValidatorSet : StaticValidatorSet witnessConfig witnessExecution := by
  constructor
  · exact time_within_of_lt_sixteen (by decide)
  · intro i e e' he he'
    have helt : e < 4 := by simpa [witnessExecution] using he
    have helt' : e' < 4 := by simpa [witnessExecution] using he'
    rw [registry_eq]
    by_cases hi : i < 5
    · interval_cases e <;> interval_cases e' <;> interval_cases i <;> decide
    · have hnone : witnessScope.validators.getD i default = default := by
        simp [witnessScope, List.getD_eq_getElem?_getD, Nat.le_of_not_lt hi]
      rw [hnone]
      rfl

theorem witnessByzantineBound : ByzantineWeightPremises witnessConfig witnessExecution := by
  constructor
  · intro i
    rw [Execution.weight_of, registry_eq]
    by_cases hi : i < 5
    · interval_cases i <;> decide
    · have hnone : witnessScope.validators.getD i default = default := by
        simp [witnessScope, List.getD_eq_getElem?_getD, Nat.le_of_not_lt hi]
      rw [hnone]
      exact dvd_zero 100
  · intro a b ha hb
    have halt := slot_lt_sixteen ha
    have hblt := slot_lt_sixteen hb
    interval_cases a <;> interval_cases b <;> decide +kernel
  · intro a b ha hb
    have halt := slot_lt_sixteen ha
    have hblt := slot_lt_sixteen hb
    interval_cases a <;> interval_cases b <;> decide +kernel

/-! ## Synchrony -/

theorem witness_vote_false_delivery {s : Slot} (hs : s < 16) (w : ValidatorIndex) :
    Event.attestation (vote s) false ∈
      witnessExecution.schedule w (witnessExecution.slot_start witnessConfig (s + 1)) := by
  rw [slot_start_eq]
  interval_cases s <;> simp [witnessExecution, witnessSchedule]

theorem witness_slot15_delivery_at_second16 (w : ValidatorIndex) :
    Event.attestation (vote 15) false ∈ witnessExecution.schedule w 16 := by
  simp [witnessExecution, witnessSchedule]

theorem witnessSynchrony : Synchrony witnessConfig witnessExternals witnessExecution := by
  refine {
    attestation_delivery := ?_
    deadline_block_relay := ?_
    boundary_block_prefix := ?_
    attester_slashing_relay := ?_
  }
  · intro v hv s n a hs hn hvote _hdeadline hdelivery w hw
    obtain ⟨hslt, hvmod, hn', ha⟩ := (witness_vote_some_iff (honest_ne_byzantine hv)).mp hvote
    subst n a
    exact witness_vote_false_delivery hslt w
  · intro v hv n r hn hr _hdeadline w hw m hm _hnext hlt
    left
    rw [← witness_store_symmetric v w m]
    exact (witnessExecution.store_storeLE witnessConfig witnessExternals v hlt.le).1 hr
  · intro v hv n r hn hr _hdeadline w hw boundary hHboundary hlt
      a before after _hschedule _hnotExcluded
    have hnpred : n ≤ boundary - 1 := by omega
    have hrootPred : r ∈
        (witnessExecution.store witnessConfig witnessExternals w (boundary - 1)).block_roots := by
      rw [← witness_store_symmetric v w (boundary - 1)]
      exact (witnessExecution.store_storeLE witnessConfig witnessExternals v hnpred).1 hr
    have hrootTick : r ∈
        (on_tick witnessConfig
          (witnessExecution.store witnessConfig witnessExternals w (boundary - 1))
          (witnessExecution.time_at boundary)).block_roots :=
      (on_tick_storeLE witnessConfig _ _).1 hrootPred
    exact (foldl_storeLE witnessConfig witnessExternals before _).1 hrootTick
  · intro v hv n i hn hi _hdue w hw m hm _hnext hlt
    rw [← witness_store_symmetric v w m]
    exact (witnessExecution.store_storeLE witnessConfig witnessExternals v hlt.le).2.2.1 hi

/-- No event in this finite witness carries an execution envelope. -/
private theorem witnessSchedule_no_envelope (v n : ℕ) (event : Event WitnessRoot)
    (hmem : event ∈ witnessSchedule v n) :
    ∀ signed observation, event ≠ Event.execution_payload_envelope signed observation := by
  intro signed observation heq
  subst event
  simp [witnessSchedule] at hmem
  split_ifs at hmem <;> simp_all

private theorem witness_other_event_payloads (store : Store WitnessRoot)
    (event : Event WitnessRoot)
    (hne : ∀ signed observation, event ≠ Event.execution_payload_envelope signed observation) :
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
      cases h : on_payload_attestation_message witnessConfig witnessExternals store message
          fromBlock with
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

private theorem witness_payloads_empty (v n : ℕ) :
    (witnessExecution.store witnessConfig witnessExternals v n).payloads =
      witnessExecution.genesis_store.payloads := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [Execution.store,
        show witnessExecution.schedule = witnessSchedule from rfl] using
        (witness_fold_no_envelope (witnessSchedule v (n + 1))
          (on_tick witnessConfig
            (witnessExecution.store witnessConfig witnessExternals v n)
            (witnessExecution.time_at (n + 1)))
          (fun event hmem => witnessSchedule_no_envelope v (n + 1) event hmem)).trans
          ((on_tick_payloads witnessConfig _ _).trans ih)

theorem witnessHorizonVoteDeliveryLookahead :
    HorizonVoteDeliveryLookahead witnessConfig witnessExecution := by
  constructor
  intro v hv s n a hs hn hvote _hdeadline w hw
  obtain ⟨hslt, hvmod, hn', ha⟩ := (witness_vote_some_iff (honest_ne_byzantine hv)).mp hvote
  subst n a
  exact witness_vote_false_delivery hslt w

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

end ByzantineBridgeRun
end FastConfirmation.Spec

end
