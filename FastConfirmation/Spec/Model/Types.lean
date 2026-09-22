import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import FastConfirmation.Spec.Model.Config

/-!
# Spec / Model / Types

The data structures the Fast Confirmation Rule reads, transcribed from
`consensus-specs` phase0 (`beacon-chain.md` containers projected to the fields
the FCR touches, and the `fork-choice.md` helper dataclasses), plus the
`Externals` bundle of abstract beacon-chain primitives and the abstract
anchor commitment (see `docs/spec-model-design.md`).

`Root` is a type parameter: hash digests are opaque; `LinearOrder` models the
lexicographic tie-break of `get_head`, `Inhabited.default` models the python
`Root()` default value.
-/

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

/-- Fork-choice `ForkChoiceNode`: `@dataclass(eq=True, frozen=True)` wrapping a
`root`. Kept as a distinct structure (not collapsed into `Root`) because the
spec introduced it for upgradability — Gloas extends it. -/
structure ForkChoiceNode (Root : Type*) where
  root : Root
deriving DecidableEq, Inhabited

/-- Fork-choice `LatestMessage`: the LMD vote recorded per validator
(`epoch: Epoch, root: Root`). -/
structure LatestMessage (Root : Type*) where
  epoch : Epoch
  root : Root
deriving DecidableEq, Inhabited

/-- `BeaconBlock`, projected to the fields the FCR and the fork-choice helpers
read: `slot` and `parent_root`. -/
structure BeaconBlock (Root : Type*) where
  slot : Slot
  parent_root : Root
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
deriving Inhabited

/-- Wire `SignedBeaconBlock`, projected: the block `message` (projection) plus
its `root` — `hash_tree_root(block.message)` is absorbed into the wire object
(roots are unique commitments to blocks; distinctness of roots across distinct
wire blocks is a well-formedness invariant of executions). Signatures are
absorbed into `Externals.state_transition` validity. -/
structure SignedBeaconBlock (Root : Type*) where
  message : BeaconBlock Root
  root : Root
deriving DecidableEq, Inhabited

/-- Phase0 `AttestationData` container (transcribed in full):
```python
class AttestationData(Container):
    slot: Slot
    index: CommitteeIndex
    beacon_block_root: Root
    source: Checkpoint
    target: Checkpoint
``` -/
structure AttestationData (Root : Type*) where
  slot : Slot
  index : CommitteeIndex
  beacon_block_root : Root
  source : Checkpoint Root
  target : Checkpoint Root
deriving DecidableEq, Inhabited

/-- Phase0 `IndexedAttestation`, projected: `attesting_indices` + `data`
(the BLS `signature` is absorbed into
`Externals.is_valid_indexed_attestation`). -/
structure IndexedAttestation (Root : Type*) where
  attesting_indices : List ValidatorIndex
  data : AttestationData Root
deriving DecidableEq, Inhabited

/-- The wire `Attestation`, modelled as its indexed projection: the
aggregation-bits → indices extraction (`get_indexed_attestation`) is absorbed
into the wire object, and its validity into
`Externals.is_valid_indexed_attestation` — no transcribed logic reads bits or
signatures (design decision 12). -/
abbrev Attestation (Root : Type*) := IndexedAttestation Root

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

/-- The abstract beacon-chain primitives the transcription bottoms out in:
committee shuffling, the state transition, signature/index validity, and the
abstract anchor commitment.
Everything else in the FCR spec and its fork-choice environment is transcribed
concretely on top of these (see `docs/spec-model-design.md`, "Faithfulness
contract" and decisions 12–13). -/
structure Externals (Root : Type*) where
  /-- beacon-chain `get_beacon_committee(state, slot, index)`. -/
  get_beacon_committee : BeaconState Root → Slot → CommitteeIndex → List ValidatorIndex
  /-- beacon-chain `get_committee_count_per_slot(state, epoch)`. -/
  get_committee_count_per_slot : BeaconState Root → Epoch → ℕ
  /-- phase0 `process_slots(state, slot)` (used by `get_pulled_up_head_state`,
      `store_target_checkpoint_state`, and the honest attester's pulled-up
      head state). -/
  process_slots : BeaconState Root → Slot → BeaconState Root
  /-- phase0 `state_transition(state, signed_block, validate_result=True)`:
      `none` = the block is invalid (python raises), `some` = the post-state
      (used by `on_block`). -/
  state_transition : BeaconState Root → SignedBeaconBlock Root → Option (BeaconState Root)
  /-- phase0 `process_justification_and_finalization(state)` (used by
      `compute_pulled_up_tip` to pull the post-state up to the next epoch
      boundary). -/
  process_justification_and_finalization : BeaconState Root → BeaconState Root
  /-- beacon-chain `is_valid_indexed_attestation(state, indexed_attestation)`
      (sorted/nonempty indices + aggregate BLS signature — all absorbed here;
      used by `on_attestation` and `on_attester_slashing`). -/
  is_valid_indexed_attestation : BeaconState Root → IndexedAttestation Root → Bool
  /-- Abstract contract for `anchor_block.state_root == hash_tree_root(anchor_state)`.
      The external interpretation must relate the full block and state before
      projection. The accepted trajectory requires this relation at its anchor;
      slot agreement is a separate premise. This model does not prove a concrete
      hashing result. The default supplies no commitment evidence. -/
  AnchorCommitsToState : BeaconBlock Root → BeaconState Root → Prop :=
    fun _ _ => False

variable {Root : Type*}
variable (cfg : Config)

/-! ## Beacon-chain helpers (transcribed)

`compute_epoch_at_slot`, `compute_start_slot_at_epoch`, `is_active_validator`,
`get_active_validator_indices`, `get_current_epoch`, `get_total_balance`,
`get_total_active_balance` from `specs/phase0/beacon-chain.md`. -/

/-- `compute_epoch_at_slot`: Return the epoch number at ``slot``.
```python
return Epoch(slot // SLOTS_PER_EPOCH)
``` -/
def compute_epoch_at_slot (slot : Slot) : Epoch :=
  slot / cfg.slots_per_epoch

/-- `compute_start_slot_at_epoch`: Return the start slot of ``epoch``.
```python
return Slot(epoch * SLOTS_PER_EPOCH)
``` -/
def compute_start_slot_at_epoch (epoch : Epoch) : Slot :=
  epoch * cfg.slots_per_epoch

/-- `is_active_validator`: Check if ``validator`` is active.
```python
return validator.activation_epoch <= epoch < validator.exit_epoch
``` -/
def is_active_validator (validator : Validator) (epoch : Epoch) : Bool :=
  decide (validator.activation_epoch ≤ epoch ∧ epoch < validator.exit_epoch)

/-- `get_active_validator_indices`: Return the sequence of active validator
indices at ``epoch``.
```python
return [ValidatorIndex(i) for i, v in enumerate(state.validators) if is_active_validator(v, epoch)]
```
(`enumerate` becomes an order-preserving filter over `List.range`.) -/
def get_active_validator_indices (state : BeaconState Root) (epoch : Epoch) :
    List ValidatorIndex :=
  (List.range state.validators.length).filter
    (fun i => is_active_validator (state.validators.getD i default) epoch)

/-- `get_current_epoch`: Return the current epoch.
```python
return compute_epoch_at_slot(state.slot)
``` -/
def get_current_epoch (state : BeaconState Root) : Epoch :=
  compute_epoch_at_slot cfg state.slot

/-- `get_total_balance`: Return the combined effective balance of the
``indices``; ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by
zero.
```python
return Gwei(max(EFFECTIVE_BALANCE_INCREMENT,
                sum([state.validators[index].effective_balance for index in indices])))
``` -/
def get_total_balance (state : BeaconState Root) (indices : Finset ValidatorIndex) : Gwei :=
  max cfg.effective_balance_increment
    (∑ index ∈ indices, (state.validators.getD index default).effective_balance)

/-- `get_total_active_balance`: Return the combined effective balance of the
active validators.
```python
return get_total_balance(state, set(get_active_validator_indices(state, get_current_epoch(state))))
``` -/
def get_total_active_balance (state : BeaconState Root) : Gwei :=
  get_total_balance cfg state
    (get_active_validator_indices state (get_current_epoch cfg state)).toFinset

end FastConfirmation.Spec
