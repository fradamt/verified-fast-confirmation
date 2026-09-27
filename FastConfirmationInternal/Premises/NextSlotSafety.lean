module
public import FastConfirmationModel
public import FastConfirmationInternal.Premises.CheckpointLinks
public import FastConfirmationInternal.Premises.FFG
public import FastConfirmationInternal.Premises.ScheduledExecution
public import FastConfirmationInternal.Premises.FCRCallPremises

@[expose] public section

/-! Defines the accepted next-slot safety premise bundle from exact FFG semantics, scheduled calls, timing, and checkpoint projection. -/

section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- The trusted anchor is a genesis anchor, or its state is normalized: the
anchor state's current justified and finalized checkpoints equal the anchor.
Real genesis satisfies the first case; its anchor state carries the stub
`Checkpoint(GENESIS_EPOCH, ZERO_HASH)`, which `CheckpointReadsAs` reads as
the anchor. A raw checkpoint-sync anchor state, whose checkpoints are older
than the anchor, satisfies neither case. -/
def GenesisOrNormalizedAnchor (anchor : Checkpoint Root) : Prop :=
  anchor.epoch = GENESIS_EPOCH ∨
    (E.anchor_state.current_justified_checkpoint = anchor ∧
      E.anchor_state.finalized_checkpoint = anchor)

/-- Assumptions for the stored-output following-slot theorem.

There is deliberately no finalized-reset, observed-adoption, observed-lock,
head-ancestry, filter-result, or safety field.  Finalized next-slot safety and
active-observed restart safety are already derived by the fold. -/
structure NextSlotSafetyPremises where
  ffg_interpretation : ScheduledFFGInterpretation cfg ext E
  scheduled_execution : E.ScheduledExecutionPremises cfg ext
  call_conditions :
    E.ScheduledFCRCallPremises cfg ext
  epoch_ends_fit : EpochEndsFitUint64 cfg
  anchor_eq : ffg_interpretation.anchor = E.genesis_store.justified_checkpoint
  anchor_state_checkpoints : E.GenesisOrNormalizedAnchor ffg_interpretation.anchor
  anchor_boundary : InitialAnchorAtEpochBoundary (cfg := cfg)
    (E := E) (anchor := ffg_interpretation.anchor)
  imported_block_finalization_lag :
    E.ImportedBlockFinalizationLag cfg ext ffg_interpretation
  slots_per_epoch_gt_one : 1 < cfg.slots_per_epoch
  checkpoint_inclusion : ffg_interpretation.state.CompatibleCheckpointInclusion cfg ext
  checkpoint_projection : EpochCheckpointProjectionLaws
    ffg_interpretation.anchor (E.RootKnownInScheduledPrefix cfg ext) ffg_interpretation.state.checkpoint_at_epoch
  link_checkpoint_agreement : ffg_interpretation.state.LinkCheckpointAgreement

end Execution

/-- Whole-output safety under the internal premise record, for fixed state
functions `ext`. The public claim `ConfirmedRootSafeFromNextSlot` reduces to
it through `ConcreteBridge.SafetyPremises.nextSlotSafetyPremises`. -/
def AcceptedConfirmedRootSafeFromNextSlot : Prop :=
  ∀ E : Execution Root,
    E.NextSlotSafetyPremises cfg ext →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
          E.WithinHorizon cfg m →
            E.confirmed cfg ext v n ∈ (E.store cfg ext w m).block_roots ∧
              is_ancestor (E.store cfg ext w m)
                (get_head cfg (E.store cfg ext w m))
                (get_node_for_root (E.confirmed cfg ext v n)) = true
end FastConfirmation.Spec
end

end
