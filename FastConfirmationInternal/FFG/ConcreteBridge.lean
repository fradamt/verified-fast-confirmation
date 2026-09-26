module
public import FastConfirmationInternal.FFG.ConcreteJustification
public import FastConfirmationModel.Execution.ConcreteFFGAdapter
public import FastConfirmationModel.Execution.Run

@[expose] public section

/-! Defines the bridge from the concrete FFG transition to the reduced
`BeaconFunctionInterface`. The reduced `BeaconState` keeps an opaque
`source_identity`. The bridge sets it to a state commitment of the concrete
state, as `hash_tree_root(state)` does in Python. A block root opens to the
concrete wire block and to the committed post-state root, as
`hash_tree_root(block)` commits to `block.state_root` in Python.

The state-valued interface methods decode the input state, run the concrete
function, and project the result. The decode domain is the reachable
concrete states of the setup within the fixed scope. Outside that domain the
methods return a fixed junk value; `state_transition` rejects. Python:
`specs/phase0/beacon-chain.md`, `state_transition` with
`validate_result=True`; `specs/phase0/fork-choice.md`, `on_block`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-- A collision-free commitment to concrete states: `open_` recovers every
committed state. -/
structure StateCommitment (Root : Type) where
  root : FFGBeaconState Root → Root
  open_ : Root → Option (FFGBeaconState Root)
  open_root : ∀ state, open_ (root state) = some state

/-- The opening of a block root: the concrete wire block and the committed
post-state root (`block.state_root`). -/
structure BlockCommitment (Root : Type) where
  open_ : Root → Option (FFGWireBlock Root × Root)

/-- The inputs of the bridge: one concrete setup, the two commitments, and a
base interface for the methods that the concrete FFG projection does not
model (signatures, PTC, payload envelopes, data availability). -/
structure ConcreteBridge (Root : Type) where
  setup : FFGSetup Root
  states : StateCommitment Root
  blocks : BlockCommitment Root
  base : BeaconFunctionInterface Root

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The reduced read state of a concrete state. Its `source_identity` is the
state commitment. -/
def project (state : FFGBeaconState Root) : BeaconState Root :=
  { state.toBeaconState B.setup.schedule with source_identity := some (B.states.root state) }

/-- The indexed projection of a wire attestation. -/
def indexed (vote : FFGWireAttestation Root) : IndexedAttestation Root :=
  ⟨(get_indexed_attestation B.setup.schedule vote).attesting_indices, vote.data⟩

/-- The reduced block message agrees with the concrete wire block on every
field that both containers keep. -/
def MessageMatches (message : BeaconBlock Root) (wire : FFGWireBlock Root) : Prop :=
  message.slot = wire.slot ∧ message.parent_root = wire.parent_root ∧
    message.proposer_index = wire.proposer_index ∧
    message.parent_block_hash = wire.parent_block_hash ∧
    message.block_hash = wire.block_hash ∧
    message.attestations = wire.attestations.map B.indexed ∧
    message.payload_attestations.length = wire.payload_attestation_count

/-- The decode domain: a concrete state reachable from the setup genesis,
with its epoch in the fixed scope. -/
def Admits [BEq Root] (state : FFGBeaconState Root) : Prop :=
  (∃ blocks votes, Reachable B.setup blocks votes state) ∧
    compute_epoch_at_slot B.setup.cfg state.slot ≤ B.setup.scope.last_epoch

open Classical in
/-- Decode a reduced state to the concrete state that it projects, inside the
decode domain. -/
noncomputable def decode [BEq Root] (st : BeaconState Root) : Option (FFGBeaconState Root) :=
  match st.source_identity with
  | none => none
  | some id =>
    match B.states.open_ id with
    | none => none
    | some state => if B.project state = st ∧ B.Admits state then some state else none

/-- Junk value of PJF outside the decode domain. It keeps the state, except
that a current justified checkpoint from a later epoch reads as a genesis
checkpoint. -/
def fallbackPJF (cfg : Config) (st : BeaconState Root) : BeaconState Root :=
  if st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot then st
  else { st with current_justified_checkpoint :=
    ⟨GENESIS_EPOCH, st.current_justified_checkpoint.root⟩ }

/-- `process_justification_and_finalization` on a copy of the decoded state. -/
noncomputable def pjf [BEq Root] (st : BeaconState Root) : BeaconState Root :=
  match B.decode st with
  | some state =>
    match process_justification_and_finalization B.setup.cfg B.setup.preset state with
    | .ok next => B.project next
    | .error _ => fallbackPJF B.setup.cfg st
  | none => fallbackPJF B.setup.cfg st

/-- Junk value of `process_slots` outside the decode domain or the fixed
scope: the target slot, and the PJF checkpoint when an epoch boundary is
crossed. -/
noncomputable def fallbackSlots [BEq Root] (st : BeaconState Root) (target : Slot) :
    BeaconState Root :=
  { st with
    slot := target
    current_justified_checkpoint :=
      if compute_epoch_at_slot B.setup.cfg st.slot < compute_epoch_at_slot B.setup.cfg target then
        (B.pjf st).current_justified_checkpoint
      else st.current_justified_checkpoint }

/-- `process_slots` on the decoded state, for targets in the fixed scope. -/
noncomputable def slots [BEq Root] (st : BeaconState Root) (target : Slot) : BeaconState Root :=
  match B.decode st with
  | some state =>
    if compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch then
      match process_slots B.setup.cfg B.setup.preset state target with
      | .ok next => B.project next
      | .error _ => B.fallbackSlots st target
    else B.fallbackSlots st target
  | none => B.fallbackSlots st target

open Classical in
/-- `state_transition(state, signed_block, validate_result=True)`: the block
root opens to a wire block with this root and a matching message, the
concrete transition succeeds within the fixed scope, and the post-state
commitment equals the committed state root. -/
noncomputable def transition [BEq Root] (st : BeaconState Root) (sb : SignedBeaconBlock Root) :
    Option (BeaconState Root) :=
  match B.decode st, B.blocks.open_ sb.root with
  | some state, some (wire, stateRoot) =>
    if wire.root = sb.root ∧ B.MessageMatches sb.message wire then
      match state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle
          state wire with
      | .ok post =>
        if B.states.root post = stateRoot ∧
            compute_epoch_at_slot B.setup.cfg post.slot ≤ B.setup.scope.last_epoch then
          some (B.project post)
        else none
      | .error _ => none
    else none
  | _, _ => none

/-- The concrete `BeaconFunctionInterface`. Committee reads and the indexed
structural check come from the fixed schedule; the three state-valued methods
run the concrete FFG transition. -/
noncomputable def ext [BEq Root] : BeaconFunctionInterface Root :=
  { fixed_schedule_compatibility_bundle B.setup.preset B.setup.schedule B.base with
    process_slots := B.slots
    state_transition := B.transition
    process_justification_and_finalization := B.pjf }

/-- The committed concrete state of a block root: the genesis state at the
genesis root, and otherwise the state that the committed state root opens
to. -/
def stateOf [DecidableEq Root] (r : Root) : Option (FFGBeaconState Root) :=
  if r = B.setup.genesisRoot then some B.setup.genesis
  else match B.blocks.open_ r with
    | some (_, stateRoot) => B.states.open_ stateRoot
    | none => none

/-- The setup conditions of the bridge laws: the admissible setup, and a
`uint64` bound that covers every root read of the fixed scope. -/
structure Admissible (B : ConcreteBridge Root) : Prop where
  setup : B.setup.Admissible
  numeric : (B.setup.scope.last_epoch + 1) * B.setup.cfg.slots_per_epoch +
    B.setup.preset.slots_per_historical_root ≤ UINT64_MAX

/-- An execution starts from the Python genesis store of the setup: the
anchor state is the projected genesis state and the anchor block is the
genesis block. Its parent root (Python `ZERO_HASH`) is not the genesis root
and opens to no block. -/
def ConcreteGenesis (B : ConcreteBridge Root) [LinearOrder Root] [Inhabited Root]
    (E : Execution Root) : Prop :=
  ∃ anchorBlock : SignedBeaconBlock Root,
    anchorBlock.root = B.setup.genesisRoot ∧ anchorBlock.message.slot = 0 ∧
      anchorBlock.message.parent_root ≠ B.setup.genesisRoot ∧
      B.blocks.open_ anchorBlock.message.parent_root = none ∧
      E.genesis_store = get_forkchoice_store B.setup.cfg (B.project B.setup.genesis) anchorBlock

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
