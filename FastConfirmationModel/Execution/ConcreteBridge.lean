module
public import FastConfirmationModel.Spec.BeaconChain.ConcreteRun
public import FastConfirmationModel.Execution.ConcreteFFGAdapter
public import FastConfirmationModel.Execution.Run
public import FastConfirmationModel.Execution.ScheduledPrefixes

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
methods return fallback values that satisfy the universal interface laws by
construction; they depend on the input state. `state_transition` rejects
outside the domain. Python:
`specs/phase0/beacon-chain.md`, `state_transition` with
`validate_result=True`; `specs/phase0/fork-choice.md`, `on_block`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-- A commitment to concrete states, as `hash_tree_root(state)` in Python.
`open_` is a partial inverse: a root opens only to a state with that root.
The commitment is not required to be injective on all states. Collision
resistance is required only on the states of one run
(`ConcreteBridge.StateRootsCommit`), so a finite root type, such as real
32-byte roots, can instantiate it. -/
structure StateCommitment (Root : Type) where
  root : FFGBeaconState Root → Root
  open_ : Root → Option (FFGBeaconState Root)
  open_sound : ∀ id state, open_ id = some state → root state = id

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
def InDomain [BEq Root] (state : FFGBeaconState Root) : Prop :=
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
    | some state => if B.project state = st ∧ B.InDomain state then some state else none

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
concrete transition succeeds within the fixed scope, and the committed state
root opens to the post-state. By `StateCommitment.open_sound` the post-state
root then equals the committed state root, which is the Python check
`block.state_root == hash_tree_root(state)`. -/
noncomputable def transition [BEq Root] (st : BeaconState Root) (sb : SignedBeaconBlock Root) :
    Option (BeaconState Root) :=
  match B.decode st, B.blocks.open_ sb.root with
  | some state, some (wire, stateRoot) =>
    if wire.root = sb.root ∧ B.MessageMatches sb.message wire then
      match state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle
          state wire with
      | .ok post =>
        if B.states.open_ stateRoot = some post ∧
            compute_epoch_at_slot B.setup.cfg post.slot ≤ B.setup.scope.last_epoch then
          some (B.project post)
        else none
      | .error _ => none
    else none
  | _, _ => none

/-- The concrete `BeaconFunctionInterface`. Committee reads and the indexed
structural check come from the fixed schedule; the three state-valued methods
run the concrete FFG transition. The anchor commitment is fixed by the bridge:
the anchor block is at slot 0 and the anchor state is the projected setup
genesis state. It does not come from `base`. -/
noncomputable def interface [BEq Root] : BeaconFunctionInterface Root :=
  { fixed_schedule_compatibility_bundle B.setup.preset B.setup.schedule B.base with
    process_slots := B.slots
    state_transition := B.transition
    process_justification_and_finalization := B.pjf
    AnchorCommitsToState := fun block state =>
      block.slot = 0 ∧ state = B.project B.setup.genesis }

/-- The committed concrete state of a block root: the genesis state at the
genesis root, and otherwise the state that the committed state root opens
to. -/
def committedState [DecidableEq Root] (r : Root) : Option (FFGBeaconState Root) :=
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
and opens to no block. The state commitment opens the genesis state root to
the genesis state. -/
def ConcreteGenesis (B : ConcreteBridge Root) [LinearOrder Root] [Inhabited Root]
    (E : Execution Root) : Prop :=
  ∃ anchorBlock : SignedBeaconBlock Root,
    anchorBlock.root = B.setup.genesisRoot ∧ anchorBlock.message.slot = 0 ∧
      anchorBlock.message.parent_root ≠ B.setup.genesisRoot ∧
      B.blocks.open_ anchorBlock.message.parent_root = none ∧
      B.states.open_ (B.states.root B.setup.genesis) = some B.setup.genesis ∧
      E.genesis_store = get_forkchoice_store B.setup.cfg (B.project B.setup.genesis) anchorBlock

/-- Collision resistance of `hash_tree_root` on the states of one run (class
I). If the concrete transition of a scheduled block from the committed state of
its parent computes a post-state whose root is the committed state root of the
block, then that root opens to the post-state. Under this condition the bridge
accepts every in-scope scheduled block that Python accepts
(`transition_of_stateRootsCommit`). The safety theorem does not need it. -/
def StateRootsCommit (B : ConcreteBridge Root) [DecidableEq Root] (E : Execution Root) : Prop :=
  ∀ w n (sb : SignedBeaconBlock Root), Event.block sb ∈ E.schedule w n →
    ∀ wire stateRoot cp post, B.blocks.open_ sb.root = some (wire, stateRoot) →
      B.committedState wire.parent_root = some cp →
      state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle cp wire =
        .ok post →
      B.states.root post = stateRoot → B.states.open_ stateRoot = some post

end ConcreteBridge

section Selectors

variable [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-! ### Selectors -/

/-- The genesis anchor: `Checkpoint(GENESIS_EPOCH, genesis_root)`. -/
def anchorCheckpoint : Checkpoint Root := ⟨GENESIS_EPOCH, B.setup.genesisRoot⟩

/-- A genesis-epoch checkpoint reads as the anchor; other checkpoints read as
themselves. -/
def readAsAnchor (c : Checkpoint Root) : Checkpoint Root :=
  if c.epoch = GENESIS_EPOCH then B.anchorCheckpoint else c

/-- One eager PJF copy of the committed state of a root. -/
noncomputable def unrealizedState (r : Root) : Option (FFGBeaconState Root) :=
  match B.committedState r with
  | some cs =>
    match process_justification_and_finalization B.setup.cfg B.setup.preset cs with
    | .ok Y => some Y
    | .error _ => none
  | none => none

/-- Realized justification: the current justified checkpoint of the
committed state (`AcceptedBlockFFGState.realized_justified`). -/
noncomputable def realizedJustified (r : Root) : Checkpoint Root :=
  match B.committedState r with
  | some cs => B.readAsAnchor cs.current_justified_checkpoint
  | none => B.anchorCheckpoint

/-- Realized finalization: the finalized checkpoint of the committed state
(`AcceptedBlockFFGState.realized_finalized`). -/
noncomputable def realizedFinalized (r : Root) : Checkpoint Root :=
  match B.committedState r with
  | some cs => B.readAsAnchor cs.finalized_checkpoint
  | none => B.anchorCheckpoint

/-- Unrealized justification: the current justified checkpoint after one
PJF pass on a copy of the committed state, as `compute_pulled_up_tip`
computes it (`AcceptedBlockFFGState.unrealized_justified`). -/
noncomputable def unrealizedJustified (r : Root) : Checkpoint Root :=
  match B.unrealizedState r with
  | some Y => B.readAsAnchor Y.current_justified_checkpoint
  | none => B.anchorCheckpoint

/-- Unrealized finalization: the finalized checkpoint after one PJF pass on a
copy of the committed state (`AcceptedBlockFFGState.unrealized_finalized`). -/
noncomputable def unrealizedFinalized (r : Root) : Checkpoint Root :=
  match B.unrealizedState r with
  | some Y => B.readAsAnchor Y.finalized_checkpoint
  | none => B.anchorCheckpoint

/-- The committed parent walk down to the last block at or before `slot`. The
genesis root stops the walk. -/
def ancestorWalk (slot : Slot) : ℕ → Root → Root
  | 0, r => r
  | fuel + 1, r =>
    if r = B.setup.genesisRoot then r
    else match B.blocks.open_ r with
      | some (wire, _) => if slot < wire.slot then ancestorWalk slot fuel wire.parent_root else r
      | none => r

/-- The slot of the committed state of a root. -/
def slotOfRoot (r : Root) : Slot :=
  match B.committedState r with
  | some cs => cs.slot
  | none => 0

/-- The checkpoint selector `C(r, e)`: epoch `e` and the committed ancestor of
`r` at or before the start slot of `e`. -/
def checkpointAt (r : Root) (e : Epoch) : Checkpoint Root :=
  ⟨e, B.ancestorWalk (compute_start_slot_at_epoch B.setup.cfg e) (B.slotOfRoot r + 1) r⟩

/-! ### Inclusion -/

/-- A body vote of the accepted block `carrier`: one successful
`process_attestation` call that the concrete `state_transition` of the block
ran, from the committed state of its parent. The genesis block has no body.
Python: `specs/gloas/beacon-chain.md`, `process_operations`. -/
def CarrierVote (E : Execution Root) (carrier : Root) (r : IncludedVote Root) : Prop :=
  E.RootKnownInScheduledPrefix B.setup.cfg B.interface carrier ∧
    carrier ≠ B.setup.genesisRoot ∧
    ∃ wire stateRoot cp, B.blocks.open_ carrier = some (wire, stateRoot) ∧
      B.committedState wire.parent_root = some cp ∧ r ∈ blockVotes B.setup cp wire

/-- The canonical inclusion relation of the certificates: the attestation is
the indexed form of a body vote of the accepted block `carrier` whose
`process_attestation` call set the timely-target flag. Only these votes
count for justification in Python `get_unslashed_participating_indices`. -/
def TargetIncludedAt (E : Execution Root) (carrier : Root) (a : Attestation Root) : Prop :=
  ∃ r, B.CarrierVote E carrier r ∧ a = B.indexed r.vote ∧
    ∃ flags, r.flags B.setup = .ok flags ∧ timelyTargetFlagIndex ∈ flags

/-- The block-body relation of the slashing evidence `D_b`: the attestation
is the indexed form of an attestation in the body of the accepted non-genesis
block `carrier`, with or without the timely-target flag. -/
def BodyIncludedAt (E : Execution Root) (carrier : Root) (a : Attestation Root) : Prop :=
  E.RootKnownInScheduledPrefix B.setup.cfg B.interface carrier ∧
    carrier ≠ B.setup.genesisRoot ∧
    ∃ wire stateRoot, B.blocks.open_ carrier = some (wire, stateRoot) ∧
      ∃ vote ∈ wire.attestations, a = B.indexed vote

/-- Every attestation in the body of an accepted block reaches some node as an
`on_attestation(store, attestation, is_from_block=True)` call. Python
`on_block` does not process body attestations; the pyspec fork-choice test
steps add them: "An on_block step implies receiving block's attestations"
(`tests/core/pyspec/eth_consensus_specs/test/helpers/fork_choice.py:397`). -/
def BodyAttestationsDelivered (E : Execution Root) : Prop :=
  ∀ r b, E.BlockKnownInScheduledPrefix B.setup.cfg B.interface r b →
    ∀ a ∈ b.attestations, ∃ w n, Event.attestation a true ∈ E.schedule w n

end ConcreteBridge

end Selectors

end FastConfirmation.Spec.ConcreteFFG

end
