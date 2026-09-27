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
# Bridge run for the twelve-second envelope witness

This run adapts `FullTwelveBridgeRun`. It adds a verified execution payload
envelope for the child. Nodes other than node 1 receive the envelope at
second 168; node 1 receives it at second 170. Each node receives it once,
before the boundary at second 180, and keeps the payload. The base interface
of the bridge reports the child data as available and accepts exactly the
child envelope.
-/

namespace FastConfirmation.Spec
namespace FullTwelveEnvelopeBridgeRun
open ConcreteFFG

abbrev WitnessRoot := Fin 4

def junkRoot : WitnessRoot := 0
def anchorRoot : WitnessRoot := 1
def childRoot : WitnessRoot := 2
def carrierRoot : WitnessRoot := 3

def witnessConfig : Config where
  slots_per_epoch := 4
  slots_per_epoch_pos := by decide
  slot_duration_ms := 12000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 0
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 2500
  min_seed_lookahead := 0

def anchorCheckpoint : Checkpoint WitnessRoot := { epoch := 0, root := anchorRoot }
def childEpochOneCheckpoint : Checkpoint WitnessRoot := { epoch := 1, root := childRoot }
def carrierEpochTwoCheckpoint : Checkpoint WitnessRoot := { epoch := 2, root := carrierRoot }
def carrierEpochThreeCheckpoint : Checkpoint WitnessRoot := { epoch := 3, root := carrierRoot }

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

def witnessValidator : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH }

def witnessScope : FixedFFGScope where
  validators := [witnessValidator, witnessValidator, witnessValidator, witnessValidator]
  first_epoch := 0
  last_epoch := 3
  epoch_order := by decide
  activity_fixed := by decide

/-- One committee per slot: validator `s % 4` at slot `s`. -/
def committeeSchedule : FixedCommitteeSchedule where
  committees := (List.range 20).map fun s => (s, 0, [s % 4])
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
  slot := 1
  parent_root := anchorRoot
  proposer_index := 0
  root := childRoot
  parent_block_hash := anchorRoot
  block_hash := anchorRoot
  parent_requests_empty := true
  parent_requests_match := true
  attestations := []

def wireVote (s : Slot) : FFGWireAttestation WitnessRoot where
  aggregation_bits := [true]
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

def childFFGState : FFGBeaconState WitnessRoot where
  genesis_time := 0
  slot := 1
  validators := witnessScope.validators
  justification_bits := [false, false, false, false]
  previous_justified_checkpoint := anchorCheckpoint
  current_justified_checkpoint := anchorCheckpoint
  finalized_checkpoint := anchorCheckpoint
  previous_epoch_participation := [0, 0, 0, 0]
  current_epoch_participation := [0, 0, 0, 0]
  block_roots := List.replicate 8 anchorRoot
  latest_block_header := ⟨1, 0, anchorRoot, childRoot⟩
  execution_payload_availability := [true, false, false, false, false, false, false, false]
  latest_block_hash := anchorRoot
  latest_bid_block_hash := anchorRoot

def carrierFFGState : FFGBeaconState WitnessRoot where
  genesis_time := 0
  slot := 8
  validators := witnessScope.validators
  justification_bits := [false, false, false, false]
  previous_justified_checkpoint := anchorCheckpoint
  current_justified_checkpoint := anchorCheckpoint
  finalized_checkpoint := anchorCheckpoint
  previous_epoch_participation := [2, 2, 3, 0]
  current_epoch_participation := [0, 0, 0, 0]
  block_roots := [anchorRoot, childRoot, childRoot, childRoot, childRoot, childRoot, childRoot,
    childRoot]
  latest_block_header := ⟨8, 0, childRoot, carrierRoot⟩
  execution_payload_availability := List.replicate 8 false
  latest_block_hash := anchorRoot
  latest_bid_block_hash := childRoot

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

/-! ## The bridge -/

def stateEntries : List (WitnessRoot × FFGBeaconState WitnessRoot) :=
  [(anchorRoot, witnessSetup.genesis), (childRoot, childFFGState),
    (carrierRoot, carrierFFGState)]

theorem stateEntries_nodup : (stateEntries.map Prod.snd).Nodup := by decide +kernel

def blockEntries : List (WitnessRoot × (FFGWireBlock WitnessRoot × WitnessRoot)) :=
  [(childRoot, (childWire, childRoot)), (carrierRoot, (carrierWire, carrierRoot))]

/-! ### Ground honest votes -/

def voteData (slot : Slot) : AttestationData WitnessRoot :=
  if slot = 0 then
    { slot := slot, index := 0, beacon_block_root := anchorRoot
      source := anchorCheckpoint, target := anchorCheckpoint }
  else if slot < 4 then
    { slot := slot, index := 0, beacon_block_root := childRoot
      source := anchorCheckpoint, target := anchorCheckpoint }
  else if slot < 8 then
    { slot := slot, index := 0, beacon_block_root := childRoot
      source := anchorCheckpoint, target := childEpochOneCheckpoint }
  else if slot < 12 then
    { slot := slot, index := 0, beacon_block_root := carrierRoot
      source := anchorCheckpoint, target := carrierEpochTwoCheckpoint }
  else
    { slot := slot, index := 0, beacon_block_root := carrierRoot
      source := childEpochOneCheckpoint, target := carrierEpochThreeCheckpoint }

def vote (slot : Slot) : Attestation WitnessRoot :=
  { attesting_indices := [slot % 4], data := voteData slot }

def groundVotes : List (Attestation WitnessRoot) := (List.range 16).map vote

def childEnvelope : SignedExecutionPayloadEnvelope WitnessRoot :=
  { message := { beacon_block_root := childRoot
                 parent_beacon_block_root := anchorRoot
                 identity := childRoot }
    signature := childRoot }

def payloadObservation : EnvelopeObservation WitnessRoot := { identity := childRoot }

/-- The base interface: signature checks accept exactly the ground votes on a
state with a registry. The child data is available, and envelope
verification accepts exactly the child envelope. PTC methods keep their
defaults. -/
def baseExternals : BeaconFunctionInterface WitnessRoot where
  get_beacon_committee := fun _ slot _ => [slot % 4]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st _ => st
  state_transition := fun _ _ => none
  process_justification_and_finalization := fun st => st
  is_valid_indexed_attestation := fun state a =>
    decide (state.validators ≠ [] ∧ a ∈ groundVotes)
  is_data_available := fun r _ => decide (r = childRoot)
  verify_execution_payload_envelope := fun _ signed _ => decide (signed = childEnvelope)

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
  { message := { slot := 1, parent_root := anchorRoot }
    root := childRoot }

/-- The carrier message has the indexed forms of the three wire votes. -/
def carrierSignedBlock : SignedBeaconBlock WitnessRoot :=
  { message := { slot := 8, parent_root := childRoot, attestations := [vote 4, vote 5, vote 6] }
    root := carrierRoot }

/-! ### The decode domain -/

theorem stateEntries_cases {id : WitnessRoot} {state : FFGBeaconState WitnessRoot}
    (h : witnessBridge.states.open_ id = some state) :
    (id = anchorRoot ∧ state = witnessSetup.genesis) ∨
      (id = childRoot ∧ state = childFFGState) ∨
      (id = carrierRoot ∧ state = carrierFFGState) := by
  have hmem := tableOpen_mem (entries := stateEntries) h
  simpa [stateEntries] using hmem

theorem witness_inDomain :
    ∀ id state, witnessBridge.states.open_ id = some state → witnessBridge.InDomain state := by
  intro id state h
  rcases stateEntries_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨⟨[], [], .genesis⟩, by decide +kernel⟩
  · exact ⟨⟨_, _, .block childWire .genesis child_transition⟩, by decide +kernel⟩
  · exact ⟨⟨_, _, .block carrierWire (.block childWire .genesis child_transition)
      carrier_transition⟩, by decide +kernel⟩

/-- **The run interface is the computable copy.** -/
theorem interface_eq : witnessBridge.interface = witnessExternals :=
  interface_eq_lookupInterface witnessBridge witness_inDomain

theorem open_validators {id : WitnessRoot} {state : FFGBeaconState WitnessRoot}
    (h : witnessBridge.states.open_ id = some state) :
    state.validators = witnessScope.validators := by
  rcases stateEntries_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-! ## Schedule and execution -/

/-- The receipts at the start of slot `s`. False copies implement ordinary
gossip. At slot eight the slot-seven receipt precedes the carrier; the true
copies after it are the three attestations of the carrier body. -/
def boundarySchedule (s : Slot) : List (Event WitnessRoot) :=
  if s = 1 then [Event.block childSignedBlock, Event.attestation (vote 0) false]
  else if s = 8 then
    [Event.attestation (vote 7) false, Event.block carrierSignedBlock,
      Event.attestation (vote 4) true, Event.attestation (vote 5) true,
      Event.attestation (vote 6) true]
  else if 2 ≤ s ∧ s ≤ 16 then
    [Event.attestation (vote (s - 1)) false]
  else []

/-- The events of node `w` at offset `o` of slot `s`: the boundary receipts,
three delayed or early receipts, and one receipt of the child envelope. -/
def slotEvents (w : ValidatorIndex) (s o : ℕ) : List (Event WitnessRoot) :=
  if s = 0 ∧ o = 4 ∧ w = 0 then [Event.attestation (vote 0) false]
  else if s = 0 ∧ o = 6 ∧ w = 1 then [Event.attestation (vote 0) false]
  else if s = 1 ∧ o = 2 ∧ w = 1 then [Event.block childSignedBlock]
  else if s = 14 ∧ o = 2 ∧ w = 1 then
    [Event.execution_payload_envelope childEnvelope payloadObservation]
  else if o = 0 then
    if s = 1 ∧ w = 1 then [Event.attestation (vote 0) false]
    else if s = 14 then
      if w = 1 then [Event.attestation (vote 13) false]
      else [Event.execution_payload_envelope childEnvelope payloadObservation,
        Event.attestation (vote 13) false]
    else boundarySchedule s
  else []

def witnessSchedule (w : ValidatorIndex) (n : ℕ) : List (Event WitnessRoot) :=
  slotEvents w (n / 12) (n % 12)

def witnessCommittee (slot : Slot) : Finset ValidatorIndex := {slot % 4}

def witnessVote (v : ValidatorIndex) (slot : Slot) : Option (ℕ × Attestation WitnessRoot) :=
  if slot < 16 ∧ v = slot % 4 then some (12 * slot + 3, vote slot) else none

def witnessExecution : Execution WitnessRoot where
  verification_horizon := 4
  genesis_store := get_forkchoice_store witnessConfig anchorState anchorSignedBlock
  schedule := witnessSchedule
  honest := {0, 1, 2, 3}
  committee := witnessCommittee
  vote := witnessVote

def confirmingFcr : FastConfirmationStore WitnessRoot :=
  witnessExecution.fcrStoreAtCall witnessConfig witnessExternals 0 23

/-! ## Clock -/

theorem genesis_store_time : witnessExecution.genesis_store.time = 0 := by decide +kernel

theorem genesis_store_genesis_time : witnessExecution.genesis_store.genesis_time = 0 := by
  decide +kernel

theorem time_at_eq (n : ℕ) : witnessExecution.time_at n = n := by
  simp [Execution.time_at, genesis_store_time]

theorem slot_at_eq (n : ℕ) : witnessExecution.slot_at witnessConfig n = n / 12 := by
  simp only [Execution.slot_at, time_at_eq, genesis_store_genesis_time, Nat.sub_zero,
    GENESIS_SLOT, Nat.zero_add]
  change n * 1000 / 12000 = n / 12
  simpa only [show (12000 : ℕ) = 12 * 1000 by decide] using
    (Nat.mul_div_mul_right n 12 (by decide : 0 < 1000))

theorem slot_start_eq (s : Slot) : witnessExecution.slot_start witnessConfig s = 12 * s := by
  simp [Execution.slot_start, genesis_store_time, genesis_store_genesis_time, witnessConfig]
  omega

theorem due_eq : get_attestation_due_ms witnessConfig = 3000 := by decide

theorem slot_lt_sixteen {s : Slot}
    (hs : witnessExecution.SlotWithinHorizon witnessConfig s) : s < 16 := by
  have hepoch := hs.2
  change s / 4 < 4 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)] at hepoch

theorem time_lt_horizon {n : ℕ}
    (hn : witnessExecution.WithinHorizon witnessConfig n) : n < 192 := by
  have hepoch := hn.2.2
  rw [slot_at_eq] at hepoch
  change n / 12 / 4 < 4 at hepoch
  omega

theorem time_within {n : ℕ} (hn : n < 192) :
    witnessExecution.WithinHorizon witnessConfig n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [time_at_eq]
    exact (Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    exact (Nat.div_le_self n 12).trans ((Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX]))
  · rw [slot_at_eq]
    change n / 12 / 4 < 4
    omega

theorem slot_within_of_lt_sixteen {s : Slot} (hs : s < 16) :
    witnessExecution.SlotWithinHorizon witnessConfig s := by
  refine ⟨(Nat.le_of_lt hs).trans (by norm_num [UINT64_MAX]), ?_⟩
  change s / 4 < 4
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)]

theorem honest_eq_zero_or_one_or_two_or_three {v : ValidatorIndex}
    (hv : v ∈ witnessExecution.honest) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  simpa [witnessExecution] using hv

theorem registry_eq : witnessExecution.registry = witnessScope.validators := by
  decide +kernel

theorem witness_vote_some_iff {v : ValidatorIndex} {s : Slot} {n : ℕ}
    {a : Attestation WitnessRoot} :
    witnessExecution.vote v s = some (n, a) ↔
      s < 16 ∧ v = s % 4 ∧ n = 12 * s + 3 ∧ a = vote s := by
  change (if s < 16 ∧ v = s % 4 then some (12 * s + 3, vote s) else none) = some (n, a) ↔ _
  by_cases h : s < 16 ∧ v = s % 4
  · rw [if_pos h]
    constructor
    · intro heq
      have hp : (12 * s + 3, vote s) = (n, a) := Option.some.inj heq
      exact ⟨h.1, h.2, (congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rw [if_neg h]
    constructor
    · intro himpossible
      contradiction
    · rintro ⟨hs, hv, -, -⟩
      exact (h ⟨hs, hv⟩).elim

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
        state.validators ≠ [] ∧ a ∈ groundVotes := by
  change (legacy_indexed_structure witnessPreset state a &&
    decide (state.validators ≠ [] ∧ a ∈ groundVotes)) = true ↔ _
  simp

theorem ground_structure {state : BeaconState WitnessRoot}
    (hreg : state.validators = witnessScope.validators) {s : Slot} :
    legacy_indexed_structure witnessPreset state (vote s) = true := by
  have hmod : s % 4 < 4 := Nat.mod_lt s (by decide)
  simp [legacy_indexed_structure, vote, hreg, witnessScope, witnessPreset, hmod]

/-! ## Direct executable checks -/

/-- The call from second 23 to 24 changes the confirmed root from the anchor
to the child. -/
theorem changed_confirmed_root :
    witnessExecution.confirmed witnessConfig witnessExternals 0 23 = anchorRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 24 = childRoot := by
  set_option maxRecDepth 100000 in decide +kernel

/-! ## Operational classifiers -/

theorem boundary_block_iff {s : Slot} {b : SignedBeaconBlock WitnessRoot} :
    Event.block b ∈ boundarySchedule s ↔
      (s = 1 ∧ b = childSignedBlock) ∨ (s = 8 ∧ b = carrierSignedBlock) := by
  by_cases h1 : s = 1
  · subst s
    simp [boundarySchedule]
  · by_cases h8 : s = 8
    · subst s
      simp [boundarySchedule]
    · simp [boundarySchedule, h1, h8]

theorem block_event_cases {w n} {b : SignedBeaconBlock WitnessRoot}
    (h : Event.block b ∈ witnessExecution.schedule w n) :
    (b = childSignedBlock ∧ 12 ≤ n) ∨ (b = carrierSignedBlock ∧ n = 96) := by
  change Event.block b ∈ slotEvents w (n / 12) (n % 12) at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 h170 ho h1 hs14 hw1
  · simp at h
  · simp at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Event.block.injEq] at h
    exact Or.inl ⟨h, by omega⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rcases boundary_block_iff.mp h with ⟨hs, hb⟩ | ⟨hs, hb⟩
    · exact Or.inl ⟨hb, by simp only [Slot] at *; omega⟩
    · exact Or.inr ⟨hb, by simp only [Slot] at *; omega⟩
  · simp at h

theorem child_mem_schedule : Event.block childSignedBlock ∈ witnessExecution.schedule 0 12 := by
  simp [witnessExecution, witnessSchedule, slotEvents, boundarySchedule]

theorem carrier_mem_schedule :
    Event.block carrierSignedBlock ∈ witnessExecution.schedule 0 96 := by
  simp [witnessExecution, witnessSchedule, slotEvents, boundarySchedule]

theorem scheduledBlock_cases {b : SignedBeaconBlock WitnessRoot}
    (h : IsScheduledBlock witnessExecution b) :
    b = childSignedBlock ∨ b = carrierSignedBlock := by
  obtain ⟨w, n, h⟩ := h
  exact (block_event_cases h).imp And.left And.left

private theorem boundary_vote_before {s a ifb}
    (h : Event.attestation a ifb ∈ boundarySchedule s) :
    ∃ t : Slot, t < 16 ∧ a = vote t ∧ t < s := by
  unfold boundarySchedule at h
  split_ifs at h with h1 h8 hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Event.attestation.injEq] at h
    exact ⟨0, by decide, h.1, by simp only [Slot] at *; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Event.attestation.injEq] at h
    rcases h with h | h | h | h
    · exact ⟨7, by decide, h.1, by simp only [Slot] at *; omega⟩
    · exact ⟨4, by decide, h.1, by simp only [Slot] at *; omega⟩
    · exact ⟨5, by decide, h.1, by simp only [Slot] at *; omega⟩
    · exact ⟨6, by decide, h.1, by simp only [Slot] at *; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Event.attestation.injEq] at h
    exact ⟨s - 1, by simp only [Slot] at *; omega, h.1, by simp only [Slot] at *; omega⟩
  · simp at h

/-- Every scheduled attestation is a ground vote, received after its
recorded send second. -/
theorem scheduled_attestation {w n a ifb}
    (h : Event.attestation a ifb ∈ witnessExecution.schedule w n) :
    ∃ s : Slot, s < 16 ∧ a = vote s ∧ 12 * s + 3 ≤ n := by
  change Event.attestation a ifb ∈ slotEvents w (n / 12) (n % 12) at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 h170 ho h1 hs14 hw1
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Event.attestation.injEq] at h
    exact ⟨0, by decide, h.1, by simp only [Slot] at *; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Event.attestation.injEq] at h
    exact ⟨0, by decide, h.1, by simp only [Slot] at *; omega⟩
  · simp at h
  · simp at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Event.attestation.injEq] at h
    exact ⟨0, by decide, h.1, by simp only [Slot] at *; omega⟩
  · simp at h
    exact ⟨13, by decide, h.1, by simp only [Slot] at *; omega⟩
  · simp at h
    exact ⟨13, by decide, h.1, by simp only [Slot] at *; omega⟩
  · obtain ⟨s, hs, ha, hsq⟩ := boundary_vote_before h
    exact ⟨s, hs, ha, by simp only [Slot] at *; omega⟩
  · simp at h

theorem attestation_mem_schedule_ground {w n a ifb}
    (h : Event.attestation a ifb ∈ witnessExecution.schedule w n) : a ∈ groundVotes := by
  obtain ⟨s, hs, rfl, -⟩ := scheduled_attestation h
  exact vote_mem_ground hs

theorem recorded_vote_of_attester {s : Slot} (hs : s < 16) {v : ValidatorIndex}
    (hvin : v ∈ (vote s).attesting_indices) :
    ∃ m a', witnessExecution.vote v (vote s).data.slot = some (m, a') ∧
      (vote s).data = a'.data := by
  have hv : v = s % 4 := by simpa [vote] using hvin
  refine ⟨12 * s + 3, vote s, ?_, rfl⟩
  rw [vote_data_slot]
  exact witness_vote_some_iff.mpr ⟨hs, hv, rfl, rfl⟩

/-- Nodes have three schedule classes, including nodes outside the honest
set. -/
def nodeClass (w : ValidatorIndex) : ValidatorIndex :=
  if w = 0 then 0 else if w = 1 then 1 else 2

theorem nodeClass_lt (w : ValidatorIndex) : nodeClass w < 3 := by
  unfold nodeClass
  split_ifs <;> decide

private theorem schedule_nodeClass (w : ValidatorIndex) (n : ℕ) :
    witnessExecution.schedule w n = witnessExecution.schedule (nodeClass w) n := by
  change slotEvents w (n / 12) (n % 12) = slotEvents (nodeClass w) (n / 12) (n % 12)
  by_cases h0 : w = 0
  · subst w
    rfl
  by_cases h1 : w = 1
  · subst w
    rfl
  simp [slotEvents, nodeClass, h0, h1]

theorem store_nodeClass (w : ValidatorIndex) (n : ℕ) :
    witnessExecution.store witnessConfig witnessExternals w n =
      witnessExecution.store witnessConfig witnessExternals (nodeClass w) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Execution.store, schedule_nodeClass w (n + 1), ih]

theorem genesis_roots_iff (r : WitnessRoot) :
    r ∈ witnessExecution.genesis_store.block_roots ↔ r = anchorRoot := by
  revert r
  decide +kernel

theorem witnessWellFormedExecution : WellFormedExecution witnessExecution := by
  constructor
  · intro w n b hb w' n' b' hb' hroot
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl <;>
      rcases scheduledBlock_cases ⟨w', n', hb'⟩ with rfl | rfl
    · rfl
    · exact False.elim ((by decide : childRoot ≠ carrierRoot) hroot)
    · exact False.elim ((by decide : carrierRoot ≠ childRoot) hroot)
    · rfl
  · intro w n b hb hgen
    rw [genesis_roots_iff] at hgen
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl <;>
      exact absurd hgen (by decide)
  · intro r hr w n b hb
    rw [genesis_roots_iff] at hr
    subst r
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl <;>
      decide +kernel

theorem honest_vote_recorded {s : Slot} (hs : s < 16) :
    witnessExecution.vote (s % 4) s =
      some (12 * s + 3, honest_attestation witnessConfig witnessExternals
        (witnessExecution.store witnessConfig witnessExternals (s % 4) (12 * s + 3)) s 0
          (s % 4)) := by
  interval_cases s
  all_goals (set_option maxRecDepth 100000 in decide +kernel)

theorem witnessHonestBehavior :
    HonestBehavior witnessConfig witnessExternals witnessExecution := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := slot_lt_sixteen hs
    have hvmod : v = s % 4 := by
      simpa [witnessExecution, witnessCommittee] using hcommittee
    subst v
    refine ⟨12 * s + 3, 0, time_within ?_, ?_, honest_vote_recorded hslt⟩
    · simp only [Slot] at *
      omega
    · rw [slot_at_eq]
      simp only [Slot] at *
      omega
  · intro v hv s n a hvote
    obtain ⟨_, _, rfl, _⟩ := witness_vote_some_iff.mp hvote
    rw [slot_start_eq, due_eq]
    simp only [Slot] at *
    omega
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨na, hna⟩
    rcases na with ⟨n, a⟩
    obtain ⟨hs, hvmod, _hn, _ha⟩ := witness_vote_some_iff.mp hna
    simp [witnessExecution, witnessCommittee, hvmod]
  · intro w n a ifb hschedule v hv hvin
    obtain ⟨s, hs, rfl, hsent⟩ := scheduled_attestation hschedule
    have hv : v = s % 4 := by simpa [vote] using hvin
    refine ⟨12 * s + 3, vote s, hsent, ?_, rfl⟩
    rw [vote_data_slot]
    exact witness_vote_some_iff.mpr ⟨hs, hv, rfl, rfl⟩
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hs, hvmod, hn, ha⟩ := witness_vote_some_iff.mp hvote
    obtain ⟨hs', hvmod', hn', ha'⟩ := witness_vote_some_iff.mp hvote'
    subst n a n' a'
    interval_cases s <;> interval_cases s' <;>
      simp_all [vote, voteData, is_slashable_attestation_data, anchorCheckpoint,
        childEpochOneCheckpoint, carrierEpochTwoCheckpoint, carrierEpochThreeCheckpoint]
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
  rcases stateEntries_cases hopen with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
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

theorem active_index_lt_four {i : ValidatorIndex} {e : Epoch}
    (hactive : is_active_validator (witnessExecution.registry.getD i default) e = true) :
    i < 4 := by
  rw [registry_eq] at hactive
  by_contra hi
  have hnone : witnessScope.validators.getD i default = default := by
    simp [witnessScope, List.getD_eq_getElem?_getD, Nat.le_of_not_lt hi]
  rw [hnone] at hactive
  have hexit : (default : Validator).exit_epoch = 0 := rfl
  simp [is_active_validator, hexit] at hactive

theorem witness_committee_coverage_at {i : ValidatorIndex} {e : Epoch}
    (hi : i < 4) (he : e < 4) :
    ∃ s : Slot, witnessExecution.SlotWithinHorizon witnessConfig s ∧
      compute_epoch_at_slot witnessConfig s = e ∧ i ∈ witnessExecution.committee s := by
  have he3 : e ≤ 3 := Nat.le_of_lt_succ he
  have hi3 : i ≤ 3 := Nat.le_of_lt_succ hi
  have hslt : e * 4 + i < 16 := by
    calc
      e * 4 + i ≤ 3 * 4 + 3 := Nat.add_le_add (Nat.mul_le_mul_right 4 he3) hi3
      _ < 16 := by decide
  refine ⟨e * 4 + i, slot_within_of_lt_sixteen hslt, ?_, ?_⟩
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
    obtain ⟨hs, hvmod, hm, ha'⟩ := witness_vote_some_iff.mp hvote
    subst m a'
    have ha : a = vote a.data.slot := by
      rcases a with ⟨idx, data⟩
      change idx = [v] at hsingle
      change data = (vote data.slot).data at hdata
      change v = data.slot % 4 at hvmod
      subst hsingle hvmod
      change (⟨[data.slot % 4], data⟩ : Attestation WitnessRoot) =
        ⟨[data.slot % 4], voteData data.slot⟩
      change data = voteData data.slot at hdata
      rw [← hdata]
    rw [ha]
    exact (witness_valid_iff state _).2
      ⟨ground_structure (witness_reachable_registry hreachable),
        by rw [witness_reachable_registry hreachable]; decide, vote_mem_ground hs⟩
  · intro state a _hreachable hvalid v hv hvin
    have haGround := ((witness_valid_iff state a).mp hvalid).2.2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    exact recorded_vote_of_attester hs hvin
  · intro store store' a ifb _hpost hh i hi
    simp only [on_attestation] at hh
    split_ifs at hh with hv hvi
    cases hh
    have haGround := ((witness_valid_iff _ a).mp hvi).2.2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    have hi' : i = s % 4 := by simpa [vote] using hi
    rw [vote_data_slot]
    simp [witnessExecution, witnessCommittee, hi']
  · intro i s s' hs hs' hepoch
    have his : i = s % 4 := by simpa [witnessExecution, witnessCommittee] using hs
    have his' : i = s' % 4 := by simpa [witnessExecution, witnessCommittee] using hs'
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
    rw [registry_eq]
    interval_cases s <;>
      simp [witnessExecution, witnessCommittee] at hi <;>
      subst i <;> decide
  · intro a
    have hdefault : (default : BeaconState WitnessRoot).validators = [] := rfl
    change (legacy_indexed_structure witnessPreset default a &&
      decide ((default : BeaconState WitnessRoot).validators ≠ [] ∧ a ∈ groundVotes)) = false
    simp [hdefault]
  · intro state slot a _hreachable _hlt _hslotH hreg
    change (legacy_indexed_structure witnessPreset
        (witnessExternals.process_slots state slot) a &&
      decide ((witnessExternals.process_slots state slot).validators ≠ [] ∧
        a ∈ groundVotes)) =
      (legacy_indexed_structure witnessPreset state a &&
        decide (state.validators ≠ [] ∧ a ∈ groundVotes))
    simp only [legacy_indexed_structure, hreg]
  · intro state signed o o'
    rfl

theorem witnessStaticValidatorSet : StaticValidatorSet witnessConfig witnessExecution := by
  constructor
  · exact time_within (by decide)
  · intro i e e' he he'
    have helt : e < 4 := by simpa [witnessExecution] using he
    have helt' : e' < 4 := by simpa [witnessExecution] using he'
    rw [registry_eq]
    by_cases hi : i < 4
    · interval_cases e <;> interval_cases e' <;> interval_cases i <;> decide
    · have hnone : witnessScope.validators.getD i default = default := by
        simp [witnessScope, List.getD_eq_getElem?_getD, Nat.le_of_not_lt hi]
      rw [hnone]
      rfl

theorem witnessByzantineBound : ByzantineWeightPremises witnessConfig witnessExecution := by
  constructor
  · intro i
    rw [Execution.weight_of, registry_eq]
    by_cases hi : i < 4
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

theorem root_kind {v : ValidatorIndex} {n : ℕ} {r : WitnessRoot}
    (hr : r ∈ (witnessExecution.store witnessConfig witnessExternals v n).block_roots) :
    r = anchorRoot ∨ r = childRoot ∨ r = carrierRoot := by
  rcases (witnessExecution.blockProvenance witnessConfig witnessExternals v n) r hr with
    ⟨hg, _⟩ | ⟨b, hb, hbr, _⟩
  · exact Or.inl ((genesis_roots_iff r).mp hg)
  · rcases scheduledBlock_cases hb with rfl | rfl
    · exact Or.inr (Or.inl hbr.symm)
    · exact Or.inr (Or.inr hbr.symm)

theorem anchor_known {w : ValidatorIndex} {m : ℕ} :
    anchorRoot ∈ (witnessExecution.store witnessConfig witnessExternals w m).block_roots := by
  have h0 : anchorRoot ∈ (witnessExecution.store witnessConfig witnessExternals w 0).block_roots :=
    (genesis_roots_iff anchorRoot).mpr rfl
  exact (witnessExecution.store_storeLE witnessConfig witnessExternals w (Nat.zero_le m)).1 h0

private theorem root_timing_table : ∀ w : Fin 3,
    childRoot ∉ (witnessExecution.store witnessConfig witnessExternals w.val 11).block_roots ∧
    childRoot ∈ (witnessExecution.store witnessConfig witnessExternals w.val 14).block_roots ∧
    carrierRoot ∉ (witnessExecution.store witnessConfig witnessExternals w.val 95).block_roots ∧
    carrierRoot ∈ (witnessExecution.store witnessConfig witnessExternals w.val 96).block_roots := by
  set_option maxRecDepth 100000 in decide +kernel

theorem child_known_after14 (w : ValidatorIndex) {m : ℕ} (hm : 14 ≤ m) :
    childRoot ∈ (witnessExecution.store witnessConfig witnessExternals w m).block_roots := by
  have h := (root_timing_table ⟨nodeClass w, nodeClass_lt w⟩).2.1
  rw [← store_nodeClass w 14] at h
  exact (witnessExecution.store_storeLE witnessConfig witnessExternals w hm).1 h

theorem carrier_known_after96 (w : ValidatorIndex) {m : ℕ} (hm : 96 ≤ m) :
    carrierRoot ∈ (witnessExecution.store witnessConfig witnessExternals w m).block_roots := by
  have h := (root_timing_table ⟨nodeClass w, nodeClass_lt w⟩).2.2.2
  rw [← store_nodeClass w 96] at h
  exact (witnessExecution.store_storeLE witnessConfig witnessExternals w hm).1 h

theorem child_source_after12 {v : ValidatorIndex} {n : ℕ}
    (hr : childRoot ∈ (witnessExecution.store witnessConfig witnessExternals v n).block_roots) :
    12 ≤ n := by
  by_contra h
  have hno := (root_timing_table ⟨nodeClass v, nodeClass_lt v⟩).1
  rw [← store_nodeClass v 11] at hno
  exact hno ((witnessExecution.store_storeLE witnessConfig witnessExternals v
    (by omega : n ≤ 11)).1 hr)

theorem carrier_source_after96 {v : ValidatorIndex} {n : ℕ}
    (hr : carrierRoot ∈ (witnessExecution.store witnessConfig witnessExternals v n).block_roots) :
    96 ≤ n := by
  by_contra h
  have hno := (root_timing_table ⟨nodeClass v, nodeClass_lt v⟩).2.2.1
  rw [← store_nodeClass v 95] at hno
  exact hno ((witnessExecution.store_storeLE witnessConfig witnessExternals v
    (by omega : n ≤ 95)).1 hr)

private theorem root_known_before_boundary {v : ValidatorIndex} {n : ℕ} {r : WitnessRoot}
    (hr : r ∈ (witnessExecution.store witnessConfig witnessExternals v n).block_roots)
    (w : ValidatorIndex) :
    r ∈ (witnessExecution.store witnessConfig witnessExternals w
      (witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig n + 1) - 1)).block_roots := by
  rcases root_kind hr with rfl | rfl | rfl
  · exact anchor_known
  · apply child_known_after14
    have hn := child_source_after12 hr
    rw [slot_start_eq, slot_at_eq]
    omega
  · apply carrier_known_after96
    have hn := carrier_source_after96 hr
    rw [slot_start_eq, slot_at_eq]
    omega

theorem deadline_block_relay :
    DeadlineBlockRelay witnessConfig witnessExternals witnessExecution := by
  intro v hv n r hn hr _hdeadline w hw m hm hboundary _hlt
  left
  exact (witnessExecution.store_storeLE witnessConfig witnessExternals w (by omega)).1
    (root_known_before_boundary hr w)

theorem boundary_block_prefix :
    DeadlineBoundaryBlockPrefix witnessConfig witnessExternals witnessExecution := by
  intro v hv n r hn hr _hdeadline w hw boundary hHboundary hlt
    a before after _hschedule _hnotExcluded
  have hpred := root_known_before_boundary hr w
  exact (foldl_storeLE witnessConfig witnessExternals before _).1
    ((on_tick_storeLE witnessConfig _ _).1 hpred)

/-- The event kinds of the schedule: blocks, attestations, and envelopes. -/
def scheduledKind : Event WitnessRoot → Bool
  | .block _ => true
  | .attestation _ _ => true
  | .execution_payload_envelope _ _ => true
  | _ => false

private theorem slotEvents_kind (w : ValidatorIndex) (s o : ℕ) :
    (slotEvents w s o).all scheduledKind = true := by
  unfold slotEvents boundarySchedule
  repeat' split
  all_goals rfl

theorem event_kind {w : ValidatorIndex} {n : ℕ} {e : Event WitnessRoot}
    (he : e ∈ witnessExecution.schedule w n) :
    (∃ b, e = Event.block b) ∨ (∃ a ifb, e = Event.attestation a ifb) ∨
      (∃ signed observation, e = Event.execution_payload_envelope signed observation) := by
  have hk := List.all_eq_true.mp (slotEvents_kind w (n / 12) (n % 12)) e he
  cases e with
  | block b => exact Or.inl ⟨b, rfl⟩
  | attestation a ifb => exact Or.inr (Or.inl ⟨a, ifb, rfl⟩)
  | execution_payload_envelope signed o => exact Or.inr (Or.inr ⟨signed, o, rfl⟩)
  | _ => simp [scheduledKind] at hk

theorem vote_at_boundary {v : ValidatorIndex} {s : Slot} {n : ℕ} {a : Attestation WitnessRoot}
    (hvote : witnessExecution.vote v s = some (n, a)) (w : ValidatorIndex) :
    Event.attestation a false ∈
      witnessExecution.schedule w (witnessExecution.slot_start witnessConfig (s + 1)) := by
  obtain ⟨hs, _, _, rfl⟩ := witness_vote_some_iff.mp hvote
  rw [slot_start_eq]
  change Event.attestation (vote s) false ∈ slotEvents w (12 * (s + 1) / 12) (12 * (s + 1) % 12)
  rw [Nat.mul_div_cancel_left (s + 1) (by decide : 0 < 12), Nat.mul_mod_right 12 (s + 1)]
  interval_cases s <;> by_cases hw : w = 1 <;> simp [slotEvents, boundarySchedule, hw]

theorem event_equiv (store : Store WitnessRoot) {w : ValidatorIndex} {n : ℕ}
    {e : Event WitnessRoot} (he : e ∈ witnessExecution.schedule w n) :
    ((apply_event witnessConfig witnessExternals store e).getD store).equivocating_indices =
      store.equivocating_indices := by
  rcases event_kind he with ⟨b, rfl⟩ | ⟨a, ifb, rfl⟩ | ⟨signed, observation, rfl⟩
  · cases h : on_block witnessConfig witnessExternals store b with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_block_equiv witnessConfig witnessExternals h
  · cases h : on_attestation witnessConfig witnessExternals store a ifb with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_attestation_equiv witnessConfig witnessExternals h
  · cases h : on_execution_payload_envelope witnessExternals store signed observation with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using
          (on_execution_payload_envelope_frame witnessExternals h).equivocating_indices

private theorem fold_field {α : Type} (field : Store WitnessRoot → α) (w : ValidatorIndex)
    (n : ℕ)
    (hevent : ∀ store e, e ∈ witnessExecution.schedule w n →
      field ((apply_event witnessConfig witnessExternals store e).getD store) = field store)
    (events : List (Event WitnessRoot)) (hsub : ∀ e ∈ events, e ∈ witnessExecution.schedule w n)
    (store : Store WitnessRoot) :
    field (events.foldl
      (fun st e => (apply_event witnessConfig witnessExternals st e).getD st) store) =
      field store := by
  induction events generalizing store with
  | nil => rfl
  | cons e tail ih =>
      simp only [List.foldl_cons]
      rw [ih (fun x hx => hsub x (List.mem_cons_of_mem e hx))]
      exact hevent store e (hsub e List.mem_cons_self)

theorem no_evidence (w : ValidatorIndex) (n : ℕ) :
    (witnessExecution.store witnessConfig witnessExternals w n).equivocating_indices = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((witnessExecution.schedule w (n + 1)).foldl
        (fun s e => (apply_event witnessConfig witnessExternals s e).getD s)
        (on_tick witnessConfig (witnessExecution.store witnessConfig witnessExternals w n)
          (witnessExecution.time_at (n + 1)))).equivocating_indices = ∅
      rw [fold_field Store.equivocating_indices w (n + 1) (fun store _ he => event_equiv store he)
        _ (fun _ he => he), on_tick_equiv, ih]

theorem attester_slashing_relay :
    DeadlineAttesterSlashingRelay witnessConfig witnessExternals witnessExecution := by
  intro v hv n i hn hi _hdeadline w hw m hm _hnext _hlt
  rw [no_evidence] at hi
  simp at hi

theorem witnessSynchrony : Synchrony witnessConfig witnessExternals witnessExecution := by
  refine {
    delta := ⟨2000, by decide, by decide⟩
    attestation_delivery := ?_
    deadline_block_relay := deadline_block_relay
    boundary_block_prefix := boundary_block_prefix
    attester_slashing_relay := attester_slashing_relay
  }
  intro v hv s n a hs hn hvote _hdeadline _hdelivery w hw
  exact vote_at_boundary hvote w

theorem scheduled_envelope_cases {w : ValidatorIndex} {n : ℕ}
    {signed : SignedExecutionPayloadEnvelope WitnessRoot}
    {observation : EnvelopeObservation WitnessRoot}
    (h : Event.execution_payload_envelope signed observation ∈ witnessExecution.schedule w n) :
    signed = childEnvelope ∧ observation = payloadObservation ∧
      (n = 168 ∨ n = 170) := by
  change Event.execution_payload_envelope signed observation ∈
    slotEvents w (n / 12) (n % 12) at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 h170 ho h1 hs14 hw1
  · simp at h
  · simp at h
  · simp at h
  · simp at h
    exact ⟨h.1, h.2, Or.inr (by omega)⟩
  · simp at h
  · simp at h
  · simp at h
    exact ⟨h.1, h.2, Or.inl (by omega)⟩
  · unfold boundarySchedule at h
    split_ifs at h <;> simp at h
  · simp at h

private theorem no_verified_at_167 : ∀ w : Fin 3, ∀ r : WitnessRoot,
    is_payload_verified (witnessExecution.store witnessConfig witnessExternals w.val 167) r =
      false := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem only_child_verified_at_191 : ∀ w : Fin 3, ∀ r : WitnessRoot, r ≠ childRoot →
    is_payload_verified (witnessExecution.store witnessConfig witnessExternals w.val 191) r =
      false := by
  set_option maxRecDepth 100000 in decide +kernel

theorem verified_requires_168 {v : ValidatorIndex} {n : ℕ} {r : WitnessRoot}
    (h : is_payload_verified (witnessExecution.store witnessConfig witnessExternals v n) r =
      true) :
    168 ≤ n := by
  by_contra hn
  have hlate := witnessExecution.is_payload_verified_mono witnessConfig witnessExternals v
    (show n ≤ 167 by omega) h
  rw [store_nodeClass] at hlate
  rw [no_verified_at_167 ⟨nodeClass v, nodeClass_lt v⟩ r] at hlate
  cases hlate

theorem verified_root_child {v : ValidatorIndex} {n : ℕ} {r : WitnessRoot} (hn : n < 192)
    (h : is_payload_verified (witnessExecution.store witnessConfig witnessExternals v n) r =
      true) :
    r = childRoot := by
  by_contra hne
  have hlate := witnessExecution.is_payload_verified_mono witnessConfig witnessExternals v
    (show n ≤ 191 by omega) h
  rw [store_nodeClass] at hlate
  rw [only_child_verified_at_191 ⟨nodeClass v, nodeClass_lt v⟩ r hne] at hlate
  cases hlate

private theorem child_verified_at_170 : ∀ w : Fin 3,
    is_payload_verified (witnessExecution.store witnessConfig witnessExternals w.val 170)
      childRoot = true := by
  set_option maxRecDepth 100000 in decide +kernel

theorem child_verified_after170 (w : ValidatorIndex) {m : ℕ} (hm : 170 ≤ m) :
    is_payload_verified (witnessExecution.store witnessConfig witnessExternals w m)
      childRoot = true := by
  have h := child_verified_at_170 ⟨nodeClass w, nodeClass_lt w⟩
  rw [← store_nodeClass w 170] at h
  exact witnessExecution.is_payload_verified_mono witnessConfig witnessExternals w hm h

/-- A verified payload is the child payload, verified from second 168 on.
Its next boundary is at second 180 or later. -/
private theorem verified_boundary {v : ValidatorIndex} {n : ℕ} {r : WitnessRoot}
    (hn : witnessExecution.WithinHorizon witnessConfig n)
    (hverified : is_payload_verified
      (witnessExecution.store witnessConfig witnessExternals v n) r = true) :
    r = childRoot ∧
      180 ≤ witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig n + 1) := by
  have hn192 := time_lt_horizon hn
  have hn168 := verified_requires_168 hverified
  refine ⟨verified_root_child hn192 hverified, ?_⟩
  rw [slot_start_eq, slot_at_eq]
  simp only [Slot]
  omega

theorem boundary_envelope_prefix :
    DeadlineBoundaryEnvelopePrefix witnessConfig witnessExternals witnessExecution := by
  intro v hv n r hn hverified _hr _hdeadline w hw boundary _hHboundary _hlt
    a before after _hschedule _hnotExcluded
  obtain ⟨rfl, h180⟩ := verified_boundary hn hverified
  have hpred : is_payload_verified
      (witnessExecution.store witnessConfig witnessExternals w (boundary - 1)) childRoot =
        true :=
    child_verified_after170 w (by
      show 170 ≤ witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig n + 1) - 1
      omega)
  have htick : is_payload_verified
      (on_tick witnessConfig
        (witnessExecution.store witnessConfig witnessExternals w (boundary - 1))
        (witnessExecution.time_at boundary)) childRoot = true := by
    simpa only [is_payload_verified, on_tick_payloads] using hpred
  exact foldl_apply_event_payloadLE witnessConfig witnessExternals before _ childRoot htick

/-- Regression for the envelope premise: each node receives the child
envelope once, before the boundary at second 180, and no envelope event
occurs at or after that boundary. Every node has the verified payload at the
boundary, and the boundary prefix holds, because the receiver keeps the
verified payload. -/
theorem single_early_envelope_receipt :
    (∀ w n (signed : SignedExecutionPayloadEnvelope WitnessRoot)
        (observation : EnvelopeObservation WitnessRoot),
      Event.execution_payload_envelope signed observation ∈ witnessExecution.schedule w n →
        n < 180) ∧
    (∀ w, w ≠ 1 → ∀ n (signed : SignedExecutionPayloadEnvelope WitnessRoot)
        (observation : EnvelopeObservation WitnessRoot),
      Event.execution_payload_envelope signed observation ∈ witnessExecution.schedule w n →
        n = 168) ∧
    (∀ n (signed : SignedExecutionPayloadEnvelope WitnessRoot)
        (observation : EnvelopeObservation WitnessRoot),
      Event.execution_payload_envelope signed observation ∈ witnessExecution.schedule 1 n →
        n = 170) ∧
    (∀ w, is_payload_verified (witnessExecution.store witnessConfig witnessExternals w 180)
      childRoot = true) ∧
    DeadlineBoundaryEnvelopePrefix witnessConfig witnessExternals witnessExecution := by
  refine ⟨?_, ?_, ?_, fun w => child_verified_after170 w (by decide), boundary_envelope_prefix⟩
  · intro w n signed observation h
    rcases (scheduled_envelope_cases h).2.2 with rfl | rfl <;> decide
  · intro w hw1 n signed observation h
    rcases (scheduled_envelope_cases h).2.2 with rfl | rfl
    · rfl
    · simp [witnessExecution, witnessSchedule, slotEvents, hw1] at h
  · intro n signed observation h
    rcases (scheduled_envelope_cases h).2.2 with rfl | rfl
    · simp [witnessExecution, witnessSchedule, slotEvents] at h
    · rfl

theorem witnessHorizonVoteDeliveryLookahead :
    HorizonVoteDeliveryLookahead witnessConfig witnessExecution := by
  constructor
  intro v hv s n a hs hn hvote _hdeadline w hw
  exact vote_at_boundary hvote w

theorem witnessPaperSafetySynchrony :
    NextSlotSynchronyPremises witnessConfig witnessExternals witnessExecution :=
  witnessSynchrony.toPaperSafetySynchrony witnessConfig witnessExternals
    witnessHorizonVoteDeliveryLookahead boundary_envelope_prefix

end FullTwelveEnvelopeBridgeRun
end FastConfirmation.Spec

end
