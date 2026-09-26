module
public import FastConfirmationModel
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Economics
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-! Defines well-formed scheduled blocks and the execution, boundary, and finalization conditions used by the safety proof. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- Execution-level well-formedness: wire block roots are injective labels.
Equal labels identify equal block messages across scheduled block events and
the genesis store. This record does not assert a `hash_tree_root` equation. -/
structure WellFormedExecution (E : Execution Root) : Prop where
  blocks_root_injective : ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n →
    ∀ w' n' (b' : SignedBeaconBlock Root), Event.block b' ∈ E.schedule w' n' →
      b.root = b'.root → b.message = b'.message
  genesis_blocks_agree : ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n → b.root ∈ E.genesis_store.block_roots →
      b.message = E.genesis_store.blocks b.root
  /-- No scheduled block reuses the unresolved parent root of a genesis-store
      block. In the concrete protocol, a block root commits to its block, so a
      block at that root is the anchor's lower-slot parent and is rejected by
      `on_block`'s finalized-slot gate. This projection treats roots as data and
      omits the pre-anchor block, so the coherence fact is explicit. -/
  anchor_parent_unscheduled : ∀ r ∈ E.genesis_store.block_roots,
    ∀ w n (b : SignedBeaconBlock Root), Event.block b ∈ E.schedule w n →
      b.root ≠ (E.genesis_store.blocks r).parent_root

end FastConfirmation.Spec

/-!
# Premises/ScheduledExecutionConditions

Execution, timing, and boundary premises. Reads the Spec Model. Read Claims next.
-/

section

/-! ## Scheduled prefix premises -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- The exact trajectory assumptions used to replay store-local invariants to
an in-second prefix: whole-second slots, well-formed roots, external-function
contracts, honest behavior, and an anchor store with an explicit anchor
commitment. No Byzantine estimate, selected-margin domain, or head conclusion
is included. -/
structure ScheduledExecutionPremises : Prop where
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  wellFormed : WellFormedExecution E
  externals_coherence : BeaconExternalsPremises cfg ext E
  honest_behavior : HonestBehavior cfg ext E
  genesis : ∃ (anchorState : BeaconState Root)
      (anchorBlock : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root

end Execution
end FastConfirmation.Spec

end

section

/-! ## Anchor active set -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- Active validator set whose sum appears under the minimum-balance floor in
`E.total_active`. -/
def currentTargetAnchorActive : Finset ValidatorIndex :=
  (get_active_validator_indices E.anchor_state
    (get_current_epoch cfg E.anchor_state)).toFinset

end Execution
end FastConfirmation.Spec

end

section

/-! ## Realized finalization lag -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- Faithful primitive at the opaque beacon-state transition boundary.

For an actual accepted block, its realized finalized checkpoint (`GF`) is
either the checkpoint-sync anchor or at least two epochs behind the block.
This is exactly the reachable-post-state consequence of Phase0's
process-epoch-before-slot-increment order which is erased by the abstract
`state_transition` field. -/
def ImportedBlockFinalizationLag
    (B : ScheduledFFGInterpretation cfg ext E) : Prop :=
  ∀ t : E.SuccessfulScheduledBlockImport cfg ext,
    let finalized :=
      (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
    finalized = B.anchor ∨
      finalized.epoch + 2 ≤
        compute_epoch_at_slot cfg t.signedBlock.message.slot

end Execution
end FastConfirmation.Spec

end

section

/-! ## Checkpoint-sync anchor boundary -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
variable {E : Execution Root} {anchor : Checkpoint Root}
namespace Execution
variable (E : Execution Root)
/-- Minimal checkpoint-sync boundary premise.  It asks only that the trusted
anchor block represent a block at or before its declared epoch boundary; it
does not require the anchor epoch or slot to be genesis.  Together with the
ordinary slot/epoch relation this is exactly boundary alignment. -/
def InitialAnchorAtEpochBoundary : Prop :=
  (E.genesis_store.blocks anchor.root).slot ≤
    compute_start_slot_at_epoch cfg anchor.epoch

end Execution
end FastConfirmation.Spec

end

end
