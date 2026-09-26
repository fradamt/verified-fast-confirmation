module
public import FastConfirmationModel.Spec.BeaconChain.ConcreteTypes

@[expose] public section

/-! Defines the checked FFG projection of the pinned Gloas beacon transition.
Python: `specs/phase0/beacon-chain.md`, State transition;
`specs/gloas/beacon-chain.md`, Beacon state transition. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

/-- Altair participation flag index used for timely target FFG weight. -/
def TIMELY_TARGET_FLAG_INDEX : ℕ := 1

inductive Error where
  | state | slot | root | header | parentPayload | operations | committee
  | bitfield | target | inclusion | payloadIndex | source | indexed | oracle
  deriving DecidableEq, Repr

abbrev Checked (α : Type*) := Except Error α

def guard (condition : Bool) (error : Error) : Checked PUnit :=
  if condition then .ok ⟨⟩ else .error error

/-- `get_previous_epoch`. Python: `specs/phase0/beacon-chain.md:1389-1393`. -/
def get_previous_epoch (cfg : Config) {Root : Type} (state : FFGBeaconState Root) : Epoch :=
  (compute_epoch_at_slot cfg state.slot) - 1

/-- `get_block_root_at_slot`. Python: `specs/phase0/beacon-chain.md:1409-1414`. -/
def get_block_root_at_slot (preset : FFGPreset) {Root : Type}
    (state : FFGBeaconState Root) (slot : Slot) : Checked Root := do
  guard (slot + preset.slots_per_historical_root ≤ UINT64_MAX) .root
  guard (slot < state.slot && state.slot ≤ slot + preset.slots_per_historical_root) .root
  guard (state.block_roots.length == preset.slots_per_historical_root) .state
  match state.block_roots[slot % preset.slots_per_historical_root]? with
  | some root => return root
  | none => throw .root

/-- `get_block_root`. Python: `specs/phase0/beacon-chain.md:1399-1403`. -/
def get_block_root (cfg : Config) (preset : FFGPreset) {Root : Type}
    (state : FFGBeaconState Root) (epoch : Epoch) : Checked Root := do
  guard (epoch * cfg.slots_per_epoch ≤ UINT64_MAX) .root
  get_block_root_at_slot preset state (compute_start_slot_at_epoch cfg epoch)

/-- `add_flag`. Python: `specs/altair/beacon-chain.md:279-284`. -/
def add_flag (flags flag_index : ℕ) : ℕ :=
  if flags / 2 ^ flag_index % 2 == 1 then flags else flags + 2 ^ flag_index

/-- `has_flag`. Python: `specs/altair/beacon-chain.md:290-295`. -/
def has_flag (flags flag_index : ℕ) : Bool :=
  flags / 2 ^ flag_index % 2 == 1

/-- `get_active_validator_indices`. Python: `specs/phase0/beacon-chain.md:1430-1436`. -/
def get_active_validator_indices {Root : Type}
    (state : FFGBeaconState Root) (epoch : Epoch) : List ValidatorIndex :=
  (List.range state.validators.length).filter fun i =>
    is_active_validator (state.validators.getD i default) epoch

/-- `get_total_balance`, including the increment floor. Python:
`specs/phase0/beacon-chain.md:1518-1529`. -/
def get_total_balance (cfg : Config) {Root : Type} (state : FFGBeaconState Root)
    (indices : Finset ValidatorIndex) : Gwei :=
  max cfg.effective_balance_increment
    (∑ i ∈ indices, (state.validators.getD i default).effective_balance)

/-- `get_total_active_balance`. Python: `specs/phase0/beacon-chain.md:1535-1542`. -/
def get_total_active_balance (cfg : Config) {Root : Type}
    (state : FFGBeaconState Root) : Gwei :=
  get_total_balance cfg state
    ((get_active_validator_indices state (compute_epoch_at_slot cfg state.slot)).toFinset)

/-- `get_unslashed_participating_indices`. Python:
`specs/altair/beacon-chain.md:397-412`. -/
def get_unslashed_participating_indices (cfg : Config) {Root : Type}
    (state : FFGBeaconState Root) (flag_index : ℕ) (epoch : Epoch) :
    Checked (Finset ValidatorIndex) := do
  let current := compute_epoch_at_slot cfg state.slot
  guard (epoch == current || epoch == get_previous_epoch cfg state) .target
  let participation := if epoch == current then state.current_epoch_participation
    else state.previous_epoch_participation
  guard (participation.length == state.validators.length) .state
  return ((get_active_validator_indices state epoch).filter fun i =>
    has_flag (participation.getD i 0) flag_index &&
    !(state.validators.getD i default).slashed).toFinset

/-- `weigh_justification_and_finalization`, including its four ordered rules.
Python: `specs/phase0/beacon-chain.md:1909-1948`. -/
def weigh_justification_and_finalization (cfg : Config) (preset : FFGPreset)
    {Root : Type} (state : FFGBeaconState Root) (total previous current : Gwei) :
    Checked (FFGBeaconState Root) := do
  guard (state.justification_bits.length == 4) .state
  let previousEpoch := get_previous_epoch cfg state
  let currentEpoch := compute_epoch_at_slot cfg state.slot
  let oldPrevious := state.previous_justified_checkpoint
  let oldCurrent := state.current_justified_checkpoint
  let bits := false :: state.justification_bits.take 3
  let mut result := { state with
    previous_justified_checkpoint := oldCurrent
    justification_bits := bits }
  if previous * 3 ≥ total * 2 then
    let root ← get_block_root cfg preset state previousEpoch
    result := { result with
      current_justified_checkpoint := ⟨previousEpoch, root⟩
      justification_bits := result.justification_bits.set 1 true }
  if current * 3 ≥ total * 2 then
    let root ← get_block_root cfg preset state currentEpoch
    result := { result with
      current_justified_checkpoint := ⟨currentEpoch, root⟩
      justification_bits := result.justification_bits.set 0 true }
  let bits := result.justification_bits
  if (bits.drop 1 |>.take 3).all id && oldPrevious.epoch + 3 == currentEpoch then
    result := { result with finalized_checkpoint := oldPrevious }
  if (bits.drop 1 |>.take 2).all id && oldPrevious.epoch + 2 == currentEpoch then
    result := { result with finalized_checkpoint := oldPrevious }
  if (bits.take 3).all id && oldCurrent.epoch + 2 == currentEpoch then
    result := { result with finalized_checkpoint := oldCurrent }
  if (bits.take 2).all id && oldCurrent.epoch + 1 == currentEpoch then
    result := { result with finalized_checkpoint := oldCurrent }
  return result

/-- `process_justification_and_finalization`, with the epoch 0/1 return.
Python: `specs/altair/beacon-chain.md:728-744`. -/
def process_justification_and_finalization (cfg : Config) (preset : FFGPreset)
    {Root : Type} (state : FFGBeaconState Root) : Checked (FFGBeaconState Root) := do
  if compute_epoch_at_slot cfg state.slot ≤ 1 then return state
  let previousIndices ← (get_unslashed_participating_indices cfg state TIMELY_TARGET_FLAG_INDEX
    (get_previous_epoch cfg state) : Checked (Finset ValidatorIndex))
  let currentIndices ← (get_unslashed_participating_indices cfg state TIMELY_TARGET_FLAG_INDEX
    (compute_epoch_at_slot cfg state.slot) : Checked (Finset ValidatorIndex))
  weigh_justification_and_finalization cfg preset state
    (get_total_active_balance cfg state)
    (get_total_balance cfg state previousIndices)
    (get_total_balance cfg state currentIndices)

/-- `process_participation_flag_updates`. Python:
`specs/altair/beacon-chain.md:824-828`. -/
def process_participation_flag_updates {Root : Type} (state : FFGBeaconState Root) :
    FFGBeaconState Root :=
  { state with
    previous_epoch_participation := state.current_epoch_participation
    current_epoch_participation := List.replicate state.validators.length 0 }

/-- Identity frame on retained fields. Python:
`specs/altair/beacon-chain.md:752-769`. -/
def process_inactivity_updates {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/altair/beacon-chain.md:778-791`. -/
def process_rewards_and_penalties {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity only under `FixedFFGScope`. Python:
`specs/electra/beacon-chain.md:1057-1073`. -/
def process_registry_updates {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/electra/beacon-chain.md:1082-1102`. -/
def process_slashings {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/phase0/beacon-chain.md:2206`. -/
def process_eth1_data_reset {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity only under `FixedFFGScope`. Python:
`specs/gloas/beacon-chain.md:1620-1674`. -/
def process_pending_deposits {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/electra/beacon-chain.md:1208-1229`. -/
def process_pending_consolidations {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/gloas/beacon-chain.md:1680-1692`. -/
def process_builder_pending_payments {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity only under `FixedFFGScope`. Python:
`specs/electra/beacon-chain.md:1238-1254`. -/
def process_effective_balance_updates {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/phase0/beacon-chain.md:2235`. -/
def process_slashings_reset {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/phase0/beacon-chain.md:2244`. -/
def process_randao_mixes_reset {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/capella/beacon-chain.md:379-387`. -/
def process_historical_summaries_update {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/altair/beacon-chain.md:836`. -/
def process_sync_committee_updates {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/fulu/beacon-chain.md:481-489`. -/
def process_proposer_lookahead {Root : Type} (state : FFGBeaconState Root) := state
/-- Identity frame on retained fields. Python:
`specs/gloas/beacon-chain.md:1698-1709`. -/
def process_ptc_window {Root : Type} (state : FFGBeaconState Root) := state

/-- `process_epoch` projection. The 15 other substeps have the identity frame
under `FixedFFGScope`; see the source inventory. Python:
`specs/gloas/beacon-chain.md:1594-1614`. -/
def process_epoch (cfg : Config) (preset : FFGPreset) {Root : Type}
    (state : FFGBeaconState Root) : Checked (FFGBeaconState Root) := do
  let state ← process_justification_and_finalization cfg preset state
  let state := process_inactivity_updates state
  let state := process_rewards_and_penalties state
  let state := process_registry_updates state
  let state := process_slashings state
  let state := process_eth1_data_reset state
  let state := process_pending_deposits state
  let state := process_pending_consolidations state
  let state := process_builder_pending_payments state
  let state := process_effective_balance_updates state
  let state := process_slashings_reset state
  let state := process_randao_mixes_reset state
  let state := process_historical_summaries_update state
  let state := process_participation_flag_updates state
  let state := process_sync_committee_updates state
  let state := process_proposer_lookahead state
  return process_ptc_window state

/-- `process_slot` retained root/availability projection. The oracle binds the
full state-root and header-root commitments. Python:
`specs/gloas/beacon-chain.md:1569-1583`. -/
def process_slot (preset : FFGPreset) {Root : Type} (state : FFGBeaconState Root) :
    Checked (FFGBeaconState Root) := do
  guard (state.block_roots.length == preset.slots_per_historical_root &&
    state.execution_payload_availability.length == preset.slots_per_historical_root) .state
  let index := state.slot % preset.slots_per_historical_root
  let nextIndex := (state.slot + 1) % preset.slots_per_historical_root
  return { state with
    block_roots := state.block_roots.set index state.latest_block_header.root
    execution_payload_availability :=
      state.execution_payload_availability.set nextIndex false }

/-- `process_slots`: strict target, slot, epoch at the last slot, increment.
Python: `specs/phase0/beacon-chain.md:1795-1803`. -/
def process_slots (cfg : Config) (preset : FFGPreset) {Root : Type}
    (state : FFGBeaconState Root) (target : Slot) : Checked (FFGBeaconState Root) := do
  guard (target ≤ UINT64_MAX) .slot
  guard (state.slot < target) .slot
  (List.range (target - state.slot)).foldlM (init := state) fun state _ => do
    let state ← process_slot preset state
    let state ← if (state.slot + 1) % cfg.slots_per_epoch == 0 then
      process_epoch cfg preset state else .ok state
    return { state with slot := state.slot + 1 }

/-- `get_committee_indices`. Python: `specs/electra/beacon-chain.md:736-737`. -/
def get_committee_indices (bits : List Bool) : List CommitteeIndex :=
  (List.range bits.length).filter fun i => bits.getD i false

/-- `get_attesting_indices`. Python: `specs/electra/beacon-chain.md:801-819`.
Admission checks the bit ranges before this fold. -/
def get_attesting_indices (schedule : FixedCommitteeSchedule) {Root : Type}
    (vote : FFGWireAttestation Root) : Finset ValidatorIndex :=
  let selected := get_committee_indices vote.committee_bits
  let (_, indices) := selected.foldl (fun (offset, found) committeeIndex =>
    let committee := (schedule.committee vote.data.slot committeeIndex).getD []
    let members := ((List.range committee.length).filter fun i =>
      vote.aggregation_bits.getD (offset + i) false).map fun i => committee.getD i 0
    (offset + committee.length, found ++ members)) (0, [])
  indices.toFinset

/-- `get_indexed_attestation`. Python:
`specs/phase0/beacon-chain.md:1564-1574`. -/
def get_indexed_attestation (schedule : FixedCommitteeSchedule) {Root : Type}
    (vote : FFGWireAttestation Root) : FFGIndexedAttestation Root :=
  { attesting_indices := (get_attesting_indices schedule vote).sort (· ≤ ·)
    data := vote.data
    signature := vote.signature }

/-- Structural projection of `is_valid_indexed_attestation`. BLS is checked
by the block oracle. Python: `specs/gloas/beacon-chain.md:1022-1041`. -/
def is_valid_indexed_attestation (preset : FFGPreset) {Root : Type}
    (state : FFGBeaconState Root) (vote : FFGIndexedAttestation Root) : Bool :=
  !vote.attesting_indices.isEmpty &&
  vote.attesting_indices.length ≤
    preset.max_validators_per_committee * preset.max_committees_per_slot &&
  decide (vote.attesting_indices.Pairwise (· < ·)) &&
  vote.attesting_indices.all (· < state.validators.length)

/-- `integer_squareroot`. Python: `specs/phase0/beacon-chain.md:986`. -/
def integer_squareroot (n : ℕ) : ℕ := Nat.sqrt n

/-- `is_attestation_same_slot`. Python:
`specs/gloas/beacon-chain.md:1077-1088`. -/
def is_attestation_same_slot (preset : FFGPreset) {Root : Type} [BEq Root]
    (state : FFGBeaconState Root) (data : AttestationData Root) : Checked Bool := do
  if data.slot == 0 then return true
  let root ← (get_block_root_at_slot preset state data.slot : Checked Root)
  let previous ← (get_block_root_at_slot preset state (data.slot - 1) : Checked Root)
  return data.beacon_block_root == root && data.beacon_block_root != previous

/-- `get_attestation_participation_flag_indices`. Python:
`specs/gloas/beacon-chain.md:1339-1386`. -/
def get_attestation_participation_flag_indices (cfg : Config) (preset : FFGPreset)
    {Root : Type} [BEq Root] (state : FFGBeaconState Root)
    (data : AttestationData Root) (delay : ℕ) (parentSlot : Slot) :
    Checked (List ℕ) := do
  let current := compute_epoch_at_slot cfg state.slot
  let justified := if data.target.epoch == current then
    state.current_justified_checkpoint else state.previous_justified_checkpoint
  let sourceMatches := data.source.epoch == justified.epoch &&
    data.source.root == justified.root
  let targetRoot ← (get_block_root cfg preset state data.target.epoch : Checked Root)
  let targetMatches := sourceMatches && data.target.root == targetRoot
  let sameSlot ← is_attestation_same_slot preset state data
  let payloadMatches ← if sameSlot then do
    guard (data.index == 0) .payloadIndex
    pure true
  else do
    let availability := state.execution_payload_availability.getD
      (parentSlot % preset.slots_per_historical_root) false
    pure (data.index == (if availability then 1 else 0))
  let headRoot ← (get_block_root_at_slot preset state data.slot : Checked Root)
  let headMatches := targetMatches && data.beacon_block_root == headRoot && payloadMatches
  guard sourceMatches .source
  let mut flags := []
  if delay ≤ integer_squareroot cfg.slots_per_epoch then flags := flags ++ [0]
  if targetMatches then flags := flags ++ [1]
  if headMatches && delay == preset.min_attestation_inclusion_delay then
    flags := flags ++ [2]
  return flags

/-- `process_attestation` FFG guards, ordered committee bits and flag union.
Python: `specs/gloas/beacon-chain.md:2336-2420`. -/
def process_attestation (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) {Root : Type} [BEq Root]
    (state : FFGBeaconState Root) (vote : FFGWireAttestation Root)
    (parentSlot : Slot) : Checked (FFGBeaconState Root) := do
  let data := vote.data
  let current := compute_epoch_at_slot cfg state.slot
  guard (data.target.epoch == current || data.target.epoch == get_previous_epoch cfg state) .target
  guard (data.target.epoch == compute_epoch_at_slot cfg data.slot) .target
  guard (data.slot + preset.min_attestation_inclusion_delay ≤ state.slot) .inclusion
  guard (data.index < 2) .payloadIndex
  guard (vote.committee_bits.length == preset.max_committees_per_slot) .committee
  let count ← (match schedule.count data.target.epoch with
    | some n => (pure n : Checked ℕ)
    | none => throw .committee : Checked ℕ)
  let mut offset := 0
  for committeeIndex in get_committee_indices vote.committee_bits do
    guard (committeeIndex < count) .committee
    let committee ← (match schedule.committee data.slot committeeIndex with
      | some members => (pure members : Checked (List ValidatorIndex))
      | none => throw .committee : Checked (List ValidatorIndex))
    guard (committee.length ≤ preset.max_validators_per_committee) .committee
    guard (offset + committee.length ≤ vote.aggregation_bits.length) .bitfield
    guard ((List.range committee.length).any fun i =>
      vote.aggregation_bits.getD (offset + i) false) .bitfield
    offset := offset + committee.length
  guard (vote.aggregation_bits.length == offset) .bitfield
  let flags ← (get_attestation_participation_flag_indices cfg preset state data
    (state.slot - data.slot) parentSlot : Checked (List ℕ))
  let indexed := get_indexed_attestation schedule vote
  guard (is_valid_indexed_attestation preset state indexed) .indexed
  let indices := get_attesting_indices schedule vote
  let participation := if data.target.epoch == current then
    state.current_epoch_participation else state.previous_epoch_participation
  guard (participation.length == state.validators.length) .state
  let updated := (indices.sort (· ≤ ·)).foldl (fun values i =>
    values.set i (flags.foldl add_flag (values.getD i 0))) participation
  if data.target.epoch == current then
    return { state with current_epoch_participation := updated }
  else
    return { state with previous_epoch_participation := updated }

/-- `apply_parent_execution_payload` retained writes. Python:
`specs/gloas/beacon-chain.md:1745-1790`. -/
def apply_parent_execution_payload (preset : FFGPreset) {Root : Type}
    (state : FFGBeaconState Root) : FFGBeaconState Root :=
  { state with
    execution_payload_availability := state.execution_payload_availability.set
      (state.latest_block_header.slot % preset.slots_per_historical_root) true
    latest_block_hash := state.latest_bid_block_hash }

/-- `process_parent_execution_payload` parent-full branch. Python:
`specs/gloas/beacon-chain.md:1801-1813`. -/
def process_parent_execution_payload (preset : FFGPreset) {Root : Type} [BEq Root]
    (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    Checked (FFGBeaconState Root) := do
  if block.parent_block_hash != state.latest_bid_block_hash then
    guard block.parent_requests_empty .parentPayload
    return state
  guard block.parent_requests_match .parentPayload
  return apply_parent_execution_payload preset state

/-- `process_block_header` retained guards and header install. Proposer
selection and header hashing belong to the oracle. Python:
`specs/phase0/beacon-chain.md:2288-2308`. -/
def process_block_header {Root : Type} [BEq Root]
    (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    Checked (FFGBeaconState Root) := do
  guard (block.slot == state.slot) .header
  guard (block.slot > state.latest_block_header.slot) .header
  guard (block.parent_root == state.latest_block_header.root) .header
  guard (block.proposer_index < state.validators.length) .header
  guard (!(state.validators.getD block.proposer_index default).slashed) .header
  return { state with latest_block_header :=
    ⟨block.slot, block.proposer_index, block.parent_root, block.root⟩ }

/-- `process_execution_payload_bid` cache projection. Python:
`specs/gloas/beacon-chain.md:2104-2157`. -/
def process_execution_payload_bid {Root : Type} (state : FFGBeaconState Root)
    (block : FFGWireBlock Root) : FFGBeaconState Root :=
  { state with latest_bid_block_hash := block.block_hash }

/-- `process_operations` retains the ordered attestation fold. All other
operation validity and frame checks belong to the oracle. Python:
`specs/gloas/beacon-chain.md:2170-2205`. -/
def process_operations (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) {Root : Type} [BEq Root]
    (state : FFGBeaconState Root) (block : FFGWireBlock Root)
    (parentSlot : Slot) : Checked (FFGBeaconState Root) := do
  guard (block.deposit_count == 0) .operations
  guard (block.proposer_slashing_count ≤ preset.max_proposer_slashings &&
    block.attester_slashing_count ≤ preset.max_attester_slashings &&
    block.attestations.length ≤ preset.max_attestations &&
    block.voluntary_exit_count ≤ preset.max_voluntary_exits &&
    block.bls_to_execution_change_count ≤ preset.max_bls_to_execution_changes &&
    block.payload_attestation_count ≤ preset.max_payload_attestations) .operations
  block.attestations.foldlM (init := state) fun state vote =>
    process_attestation cfg preset schedule state vote parentSlot

/-- `process_block` retained Gloas order. Python:
`specs/gloas/beacon-chain.md:1715-1732`. -/
def process_block (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) {Root : Type} [BEq Root]
    (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    Checked (FFGBeaconState Root) := do
  let parentSlot := state.latest_block_header.slot
  let state ← process_parent_execution_payload preset state block
  let state ← process_block_header state block
  let state := process_execution_payload_bid state block
  process_operations cfg preset schedule state block parentSlot

/-- The sole opaque validity oracle can reject a candidate but supplies no
FFG state. It binds cryptography, full hashes, proposer selection and the
fixed-scope frames of erased operations. -/
structure BlockValidityOracle (Root : Type) where
  accepts : FFGBeaconState Root → FFGWireBlock Root → FFGBeaconState Root → Bool

/-- `state_transition`: slots, concrete block, then commitment validity.
Python: `specs/phase0/beacon-chain.md:1769-1782`. -/
def state_transition (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) {Root : Type} (oracle : BlockValidityOracle Root)
    [BEq Root] (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    Checked (FFGBeaconState Root) := do
  guard (state.slot ≤ UINT64_MAX && block.slot ≤ UINT64_MAX) .slot
  guard (state.justification_bits.length == 4 &&
    state.previous_epoch_participation.length == state.validators.length &&
    state.current_epoch_participation.length == state.validators.length &&
    state.block_roots.length == preset.slots_per_historical_root &&
    state.execution_payload_availability.length == preset.slots_per_historical_root) .state
  let atSlot ← process_slots cfg preset state block.slot
  let result ← process_block cfg preset schedule atSlot block
  guard (oracle.accepts atSlot block result) .oracle
  return result

end FastConfirmation.Spec.ConcreteFFG

end
