module
public import FastConfirmationModel.Spec.BeaconChain.Helpers

@[expose] public section

/-! Defines the concrete fixed-scope Gloas FFG state and wire containers.
Python: `specs/gloas/beacon-chain.md`, Containers; `specs/phase0/beacon-chain.md`, Containers. -/

namespace FastConfirmation.Spec

/-- Fixed preset values used by the concrete projection. Python:
`presets/minimal/phase0.yaml:6,10,32,42,75,83`;
`presets/minimal/electra.yaml:29,31`;
`presets/minimal/capella.yaml:6`; `presets/minimal/gloas.yaml:11`. -/
structure FFGPreset where
  slots_per_historical_root : ℕ
  max_committees_per_slot : ℕ
  max_validators_per_committee : ℕ
  max_attestations : ℕ
  max_proposer_slashings : ℕ
  max_attester_slashings : ℕ
  max_voluntary_exits : ℕ
  max_bls_to_execution_changes : ℕ
  max_payload_attestations : ℕ
  min_attestation_inclusion_delay : ℕ
  ring_pos : 0 < slots_per_historical_root
  min_delay_pos : 0 < min_attestation_inclusion_delay

/-- The fixed registry view holds every field that can affect FFG weights.
`is_active_validator` must have the same result throughout the horizon.
Python: `specs/phase0/beacon-chain.md:741-749,1088`. -/
structure FixedFFGScope where
  validators : List Validator
  first_epoch : Epoch
  last_epoch : Epoch
  epoch_order : first_epoch ≤ last_epoch
  activity_fixed : ∀ (i : Fin validators.length) (e : Epoch),
    first_epoch ≤ e → e ≤ last_epoch →
    is_active_validator (validators[i]) e =
      is_active_validator (validators[i]) first_epoch

/-- Active weight at the first epoch. Fixed activity keeps this weight stable
throughout the scope. -/
def FixedFFGScope.activeBalance (scope : FixedFFGScope) : Gwei :=
  (((List.range scope.validators.length).filter fun i =>
    is_active_validator (scope.validators.getD i default) scope.first_epoch).map fun i =>
      (scope.validators.getD i default).effective_balance).sum

/-- The finite Python `uint64` domain for weighted FFG arithmetic. The
threefold bound also covers the twofold threshold product and the balance
floor. Python: `specs/phase0/beacon-chain.md`, `uint64` arithmetic. -/
def FixedFFGScope.NumericBounds (scope : FixedFFGScope) (cfg : Config) : Prop :=
  scope.last_epoch * cfg.slots_per_epoch ≤ UINT64_MAX ∧
  3 * (scope.validators.map Validator.effective_balance).sum ≤ UINT64_MAX ∧
  2 * cfg.effective_balance_increment ≤ scope.activeBalance

/-- One ordered, branch-independent committee schedule. Rows must cover all
in-horizon queries. The predicate below checks the finite assignment data.
Python: `specs/phase0/beacon-chain.md`, `get_beacon_committee`;
`specs/electra/beacon-chain.md:736-737`. -/
structure FixedCommitteeSchedule where
  committees : List (Slot × CommitteeIndex × List ValidatorIndex)
  counts : List (Epoch × ℕ)

def FixedCommitteeSchedule.committee (schedule : FixedCommitteeSchedule)
    (slot : Slot) (index : CommitteeIndex) : Option (List ValidatorIndex) :=
  (schedule.committees.find? fun row => row.1 == slot && row.2.1 == index).map
    fun row => row.2.2

def FixedCommitteeSchedule.count (schedule : FixedCommitteeSchedule)
    (epoch : Epoch) : Option ℕ :=
  (schedule.counts.find? fun row => row.1 == epoch).map Prod.snd

/-- Check finite committee rows: the active set is assigned once per epoch,
with no duplicate positions or out-of-range indices. This is an explicit
idealization of committee selection, not a RANDAO derivation. -/
def FixedCommitteeSchedule.WellFormed (schedule : FixedCommitteeSchedule)
    (cfg : Config) (preset : FFGPreset) (scope : FixedFFGScope) : Prop :=
  (schedule.committees.map fun row => (row.1, row.2.1)).Nodup ∧
  (schedule.counts.map Prod.fst).Nodup ∧
  (∀ epoch, scope.first_epoch ≤ epoch → epoch ≤ scope.last_epoch →
    ∃ n, schedule.count epoch = some n ∧ 0 < n ∧ n ≤ preset.max_committees_per_slot) ∧
  (∀ slot index committee, schedule.committee slot index = some committee →
    index < preset.max_committees_per_slot ∧
    committee.length ≤ preset.max_validators_per_committee ∧
    committee.Nodup ∧
    ∀ i ∈ committee, i < scope.validators.length) ∧
  (∀ epoch, scope.first_epoch ≤ epoch → epoch ≤ scope.last_epoch →
    let slots := List.range cfg.slots_per_epoch |>.map (epoch * cfg.slots_per_epoch + ·)
    let assigned := slots.flatMap fun slot =>
      (List.range preset.max_committees_per_slot).flatMap fun index =>
        (schedule.committee slot index).getD []
    assigned.Nodup ∧
    assigned.toFinset =
      ((List.range scope.validators.length).filter fun i =>
        is_active_validator (scope.validators.getD i default) epoch).toFinset)

/-- The authenticated root label is supplied by the block commitment oracle.
The full SSZ header fields are outside this projection. Python:
`specs/phase0/beacon-chain.md:823,2298-2304`. -/
structure FFGBlockHeader (Root : Type*) where
  slot : Slot
  proposer_index : ValidatorIndex
  parent_root : Root
  root : Root
  deriving Inhabited

/-- Gloas wire attestation. `data.index` is the 0/1 payload status;
`committee_bits` selects committees. Python:
`specs/gloas/beacon-chain.md:801-807,814-819`. -/
structure FFGWireAttestation (Root : Type*) where
  aggregation_bits : List Bool
  committee_bits : List Bool
  data : AttestationData Root
  signature : Root
  deriving Inhabited

/-- Indexed form of the wire attestation. Its signature identity is retained
for the opaque BLS check. Python: `specs/gloas/beacon-chain.md:808-812`. -/
structure FFGIndexedAttestation (Root : Type*) where
  attesting_indices : List ValidatorIndex
  data : AttestationData Root
  signature : Root
  deriving Inhabited

/-- Gloas wire block with the fields read by the FFG projection. Its root,
request commitment, proposer and signature checks belong to the one oracle.
Python: `specs/gloas/beacon-chain.md:829-859,1715-1732`. -/
structure FFGWireBlock (Root : Type*) where
  slot : Slot
  parent_root : Root
  proposer_index : ValidatorIndex
  root : Root
  parent_block_hash : Root
  block_hash : Root
  parent_requests_empty : Bool
  parent_requests_match : Bool
  deposit_count : ℕ := 0
  proposer_slashing_count : ℕ := 0
  attester_slashing_count : ℕ := 0
  voluntary_exit_count : ℕ := 0
  bls_to_execution_change_count : ℕ := 0
  payload_attestation_count : ℕ := 0
  attestations : List (FFGWireAttestation Root)
  deriving Inhabited

/-- The retained FFG fields of Gloas `BeaconState`. Ring cells are ordered by
slot modulo `slots_per_historical_root`. Reachable-state checks bind the root
labels and array lengths. Python: `specs/gloas/beacon-chain.md:869-929`. -/
structure FFGBeaconState (Root : Type*) where
  genesis_time : ℕ
  slot : Slot
  validators : List Validator
  justification_bits : List Bool
  previous_justified_checkpoint : Checkpoint Root
  current_justified_checkpoint : Checkpoint Root
  finalized_checkpoint : Checkpoint Root
  previous_epoch_participation : List ℕ
  current_epoch_participation : List ℕ
  block_roots : List Root
  latest_block_header : FFGBlockHeader Root
  execution_payload_availability : List Bool
  latest_block_hash : Root
  latest_bid_block_hash : Root
  source_identity : Option Root := none
  deriving Inhabited

/-- A finite structural check. The scope and oracle bind the constant registry
and root labels across transitions. -/
def FFGBeaconState.WellFormed {Root : Type*} (state : FFGBeaconState Root)
    (preset : FFGPreset) (scope : FixedFFGScope) : Prop :=
  state.validators = scope.validators ∧
  state.justification_bits.length = 4 ∧
  state.previous_epoch_participation.length = state.validators.length ∧
  state.current_epoch_participation.length = state.validators.length ∧
  state.block_roots.length = preset.slots_per_historical_root ∧
  state.execution_payload_availability.length = preset.slots_per_historical_root

/-- Python genesis keeps raw zero-root checkpoint stubs and zeroed bits and
participation. The actual genesis block-root binding is an oracle obligation.
Python: `specs/phase0/beacon-chain.md`, `initialize_beacon_state_from_eth1`. -/
def FFGBeaconState.genesis {Root : Type*} (zeroRoot genesisRoot : Root)
    (genesisTime : ℕ) (scope : FixedFFGScope) (preset : FFGPreset) :
    FFGBeaconState Root :=
  let stub : Checkpoint Root := ⟨0, zeroRoot⟩
  { genesis_time := genesisTime
    slot := 0
    validators := scope.validators
    justification_bits := List.replicate 4 false
    previous_justified_checkpoint := stub
    current_justified_checkpoint := stub
    finalized_checkpoint := stub
    previous_epoch_participation := List.replicate scope.validators.length 0
    current_epoch_participation := List.replicate scope.validators.length 0
    block_roots := List.replicate preset.slots_per_historical_root zeroRoot
    latest_block_header := ⟨0, 0, zeroRoot, genesisRoot⟩
    execution_payload_availability :=
      List.replicate preset.slots_per_historical_root false
    latest_block_hash := zeroRoot
    latest_bid_block_hash := zeroRoot }

/-- Project a concrete FFG state to the current fork-choice read state.
Committee reads come from the single fixed schedule. -/
def FFGBeaconState.toBeaconState {Root : Type*} (state : FFGBeaconState Root)
    (schedule : FixedCommitteeSchedule) : BeaconState Root :=
  { genesis_time := state.genesis_time
    slot := state.slot
    validators := state.validators
    current_justified_checkpoint := state.current_justified_checkpoint
    finalized_checkpoint := state.finalized_checkpoint
    source_identity := state.source_identity
    beacon_committee_reads := schedule.committees
    committee_count_reads := schedule.counts }

end FastConfirmation.Spec

end
