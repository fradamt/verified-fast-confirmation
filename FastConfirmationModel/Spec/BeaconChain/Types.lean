module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Interval.Finset.Nat
public import FastConfirmationModel.Spec.Config

@[expose] public section

/-! Types declarations from FastConfirmation.Spec.Model.Types. -/

namespace FastConfirmation.Spec
/-- `Slot` (python `uint64`). -/
abbrev Slot := ℕ
/-- `Epoch` (python `uint64`). -/
abbrev Epoch := ℕ
/-- `Gwei` (python `uint64`). -/
abbrev Gwei := ℕ
/-- `ValidatorIndex` (python `uint64`). -/
abbrev ValidatorIndex := ℕ
/-- `CommitteeIndex` (python `uint64`). -/
abbrev CommitteeIndex := ℕ

/-- Phase0 `Checkpoint` container: `class Checkpoint(epoch: Epoch, root: Root)`. -/
structure Checkpoint (Root : Type*) where
  epoch : Epoch
  root : Root
deriving DecidableEq, Inhabited

/-- Gloas payload status (`specs/gloas/fork-choice.md:78`, constants at :102).
The source values are EMPTY = 0, FULL = 1, and PENDING = 2. -/
inductive PayloadStatus where
  | empty
  | full
  | pending
  deriving DecidableEq, Inhabited

/-- Numeric source representation (`specs/gloas/fork-choice.md:102`). -/
def PayloadStatus.toNat : PayloadStatus → ℕ
  | .empty => 0
  | .full => 1
  | .pending => 2

/-- Gloas fork-choice node (`specs/gloas/fork-choice.md:153`).
The root and payload status together identify a node. -/
structure ForkChoiceNode (Root : Type*) where
  root : Root
  payload_status : PayloadStatus := .pending
  deriving DecidableEq, Inhabited

/-- Gloas latest message (`specs/gloas/fork-choice.md:181`). -/
structure LatestMessage (Root : Type*) where
  slot : Slot
  root : Root
  payload_present : Bool := false
  deriving DecidableEq, Inhabited

/-- PTC vote data (`specs/gloas/beacon-chain.md:708`). -/
structure PayloadAttestationData (Root : Type*) where
  beacon_block_root : Root
  slot : Slot
  payload_present : Bool
  blob_data_available : Bool
  deriving DecidableEq, Inhabited

/-- Indexed PTC vote (`specs/gloas/beacon-chain.md:738`). The opaque signature
identity is retained for external signature verification. -/
structure IndexedPayloadAttestation (Root : Type*) where
  attesting_indices : List ValidatorIndex
  data : PayloadAttestationData Root
  signature : Root
  deriving DecidableEq, Inhabited

/-- Wire PTC message (`specs/gloas/beacon-chain.md:729`). -/
structure PayloadAttestationMessage (Root : Type*) where
  validator_index : ValidatorIndex
  data : PayloadAttestationData Root
  signature : Root
  deriving DecidableEq, Inhabited

/-- Projected execution envelope (`specs/gloas/beacon-chain.md:777`).
The opaque identity binds all fields read by external envelope validation. -/
structure ExecutionPayloadEnvelope (Root : Type*) where
  beacon_block_root : Root
  parent_beacon_block_root : Root
  identity : Root
  deriving DecidableEq, Inhabited

/-- Signed execution envelope (`specs/gloas/beacon-chain.md:790`). -/
structure SignedExecutionPayloadEnvelope (Root : Type*) where
  message : ExecutionPayloadEnvelope Root
  signature : Root
  deriving DecidableEq, Inhabited

/-- Local observation context for data retrieval and execution verification
(`specs/gloas/fork-choice.md:293`, :658). Equal identities denote equal
observations. The coherence contract binds their meaning to source calls. -/
structure EnvelopeObservation (Root : Type*) where
  identity : Root
  deriving DecidableEq, Inhabited

/-- Phase0 `AttestationData` container (`specs/phase0/beacon-chain.md`,
`AttestationData`). -/
structure AttestationData (Root : Type*) where
  slot : Slot
  index : CommitteeIndex
  beacon_block_root : Root
  source : Checkpoint Root
  target : Checkpoint Root
deriving DecidableEq, Inhabited

/-- Phase0 indexed attestation projection (`specs/phase0/beacon-chain.md`,
`IndexedAttestation`). Signature validation is external. -/
structure IndexedAttestation (Root : Type*) where
  attesting_indices : List ValidatorIndex
  data : AttestationData Root
deriving DecidableEq, Inhabited

/-- Wire attestation represented by its indexed projection. -/
abbrev Attestation (Root : Type*) := IndexedAttestation Root

/-- Gloas block read projection (`specs/gloas/beacon-chain.md`,
`BeaconBlockBody` and `BeaconBlock`; `specs/phase0/beacon-chain.md`,
`BeaconBlockBody`). Ordinary FFG `attestations` and payload attestations
retain their source order. -/
structure BeaconBlock (Root : Type*) where
  slot : Slot
  parent_root : Root
  proposer_index : ValidatorIndex := 0
  parent_block_hash : Root := parent_root
  block_hash : Root := parent_root
  attestations : List (Attestation Root) := []
  payload_attestations : List (IndexedPayloadAttestation Root) := []
  deriving DecidableEq, Inhabited

/-- Beacon-chain `Validator`, projected to the fields the FCR reads:
`effective_balance`, `slashed`, and the activation/exit epochs consumed by
`is_active_validator`. -/
structure Validator where
  effective_balance : Gwei
  slashed : Bool
  activation_epoch : Epoch
  exit_epoch : Epoch
deriving DecidableEq, Inhabited

/-- `BeaconState`, projected to the fields the FCR and the fork-choice
handlers read: `genesis_time` (`get_forkchoice_store`), `slot`, the validator
registry, and the justified/finalized checkpoints (`get_voting_source`,
`on_block`, `compute_pulled_up_tip`). `state.validators[i]` list accesses are
totalized with `List.getD` (junk outside the domain; unreachable from a
well-formed store). -/
structure BeaconState (Root : Type*) where
  genesis_time : ℕ
  slot : Slot
  validators : List Validator
  current_justified_checkpoint : Checkpoint Root
  finalized_checkpoint : Checkpoint Root
  /-- Opaque source-state commitment. A concrete source projection retains
  this identity so external reads can distinguish states with the same other
  projected fields. Synthetic states can leave it absent. -/
  source_identity : Option Root := none
  /-- Exact ordered committee query results used by Gloas `is_head_weak`
  (`specs/gloas/fork-choice.md:785`). Absent queries are outside the read
  projection domain. The source contract requires all reached queries. -/
  beacon_committee_reads : List (Slot × CommitteeIndex × List ValidatorIndex) := []
  /-- Exact committee counts for the same read domain
  (`specs/gloas/fork-choice.md:797`). -/
  committee_count_reads : List (Epoch × ℕ) := []
deriving Inhabited

/-- Lookup in the committee read projection. Outside its domain, return junk.
Source read: `specs/gloas/fork-choice.md:798`. -/
def BeaconState.beacon_committees {Root : Type*} (state : BeaconState Root)
    (slot : Slot) (index : CommitteeIndex) : List ValidatorIndex :=
  ((state.beacon_committee_reads.find? fun row =>
    row.1 == slot && row.2.1 == index).map fun row => row.2.2).getD []

/-- Lookup in the count read projection. Outside its domain, return junk.
Source read: `specs/gloas/fork-choice.md:797`. -/
def BeaconState.committee_count_per_slot {Root : Type*} (state : BeaconState Root)
    (epoch : Epoch) : ℕ :=
  ((state.committee_count_reads.find? fun row => row.1 == epoch).map Prod.snd).getD 0

/-- Wire `SignedBeaconBlock`, projected: the block `message` (projection) plus
its `root` — `hash_tree_root(block.message)` is absorbed into the wire object
(roots are unique commitments to blocks; distinctness of roots across distinct
wire blocks is a well-formedness invariant of executions). Signatures are
absorbed into `Externals.state_transition` validity. -/
structure SignedBeaconBlock (Root : Type*) where
  message : BeaconBlock Root
  root : Root
deriving DecidableEq, Inhabited

/-- Phase0 `AttesterSlashing` container:
```python
class AttesterSlashing(Container):
    attestation_1: IndexedAttestation
    attestation_2: IndexedAttestation
``` -/
structure AttesterSlashing (Root : Type*) where
  attestation_1 : IndexedAttestation Root
  attestation_2 : IndexedAttestation Root
deriving DecidableEq, Inhabited

/-- `is_slashable_attestation_data`: Check if ``data_1`` and ``data_2`` are
slashable according to Casper FFG rules.
```python
return (
    # Double vote
    (data_1 != data_2 and data_1.target.epoch == data_2.target.epoch)
    or
    # Surround vote
    (data_1.source.epoch < data_2.source.epoch and data_2.target.epoch < data_1.target.epoch)
)
``` -/
def is_slashable_attestation_data {Root : Type*} [DecidableEq Root]
    (data_1 data_2 : AttestationData Root) : Bool :=
  decide ((data_1 ≠ data_2 ∧ data_1.target.epoch = data_2.target.epoch) ∨
    (data_1.source.epoch < data_2.source.epoch ∧ data_2.target.epoch < data_1.target.epoch))

variable {Root : Type*}
variable (cfg : Config)
end FastConfirmation.Spec

end
