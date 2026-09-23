module
public import FastConfirmationModel
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Economics
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-! ExecutionConditions declarations from FastConfirmation.Spec.Model.Assumptions. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution
/-- Execution-level well-formedness: wire block roots are genuine commitments.
Equal roots identify equal block messages across scheduled block events and the
genesis store. -/
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
# Premises/Execution

Execution, timing, and boundary premises. Reads the Spec Model. Read Claims next.
-/

section

/-! ## From CausalQueryTraceAdapter -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
/-- The exact trajectory assumptions used to replay store-local invariants to
an in-second prefix. These are the operational fields of
`SelectedMarginAssumptions`, with an explicit anchor commitment. No Byzantine
estimate, selected-margin domain, or head conclusion is included. -/
structure ScheduledPrefixTrajectoryAssumptions : Prop where
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  wellFormed : WellFormedExecution E
  externals_coherence : ExternalsCoherence cfg ext E
  honest_behavior : HonestBehavior cfg ext E
  genesis : ∃ (anchorState : BeaconState Root)
      (anchorBlock : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root

end Execution
namespace AllowedFCRCalls
open Execution
end AllowedFCRCalls
namespace Execution
variable (E : Execution Root)
end Execution
namespace AllowedFCRCalls
open Execution
end AllowedFCRCalls
end FastConfirmation.Spec

end

section

/-! ## From CurrentTargetFutureSupport -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
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

/-! ## From AcceptedFinalizationTiming -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
/-- Faithful primitive at the opaque beacon-state transition boundary.

For an actual accepted block, its realized finalized checkpoint (`GF`) is
either the checkpoint-sync anchor or at least two epochs behind the block.
This is exactly the reachable-post-state consequence of Phase0's
process-epoch-before-slot-increment order which is erased by the abstract
`state_transition` field. -/
def AcceptedRealizedFinalizationDelay
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) : Prop :=
  ∀ t : E.AcceptedBlockTransition cfg ext,
    let finalized :=
      (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
    finalized = B.anchor ∨
      finalized.epoch + 2 ≤
        compute_epoch_at_slot cfg t.signedBlock.message.slot

namespace AcceptedFinalizationLagAt
end AcceptedFinalizationLagAt
end Execution
namespace AcceptedFinalizationLagCounterpattern
end AcceptedFinalizationLagCounterpattern
end FastConfirmation.Spec

end

section

/-! ## From FFGGlobalCheckpointTrajectory -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E : Execution Root} {anchor : Checkpoint Root}
namespace FFGGlobalCheckpointOrigins
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}
end FFGGlobalCheckpointOrigins
namespace Execution
variable (E : Execution Root)
/-- Minimal checkpoint-sync boundary premise.  It asks only that the trusted
anchor block represent a block at or before its declared epoch boundary; it
does not require the anchor epoch or slot to be genesis.  Together with the
ordinary slot/epoch relation this is exactly boundary alignment. -/
def TrustedAnchorBoundaryAligned : Prop :=
  (E.genesis_store.blocks anchor.root).slot ≤
    compute_start_slot_at_epoch cfg anchor.epoch

end Execution
namespace FFGGlobalCheckpointLedger
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}
end FFGGlobalCheckpointLedger
namespace Execution
variable (E : Execution Root)
end Execution
end FastConfirmation.Spec

end

section

/-! ## From L4Fold -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
/-- **The trajectory predicate.** From second `n` on, the safe block `b` is an
ancestor of every honest node's fork-choice head. This is `EngineInv` with the
cutoff-slot cap removed (`∀ k` folded in), retaining the pinned executable
spec's current-moment claim. -/
def SafeFrom (b : Root) (n : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root b) = true

end Execution
namespace Execution
variable (E : Execution Root)
end Execution
end FastConfirmation.Spec

end

end
