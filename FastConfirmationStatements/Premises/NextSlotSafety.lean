module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
public import FastConfirmationStatements.Premises.FCRCallPremises

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
  trajectory : E.ScheduledExecutionPremises cfg ext
  completed_calls :
    E.ScheduledFCRCallPremises cfg ext
  epoch_ends_fit : EpochEndsFitUint64 cfg
  anchor_eq : ffg_interpretation.anchor = E.genesis_store.justified_checkpoint
  anchor_state_checkpoints : E.GenesisOrNormalizedAnchor ffg_interpretation.anchor
  anchor_boundary : InitialAnchorAtEpochBoundary (cfg := cfg)
    (E := E) (anchor := ffg_interpretation.anchor)
  finalization_delay :
    E.ImportedBlockFinalizationLag cfg ext ffg_interpretation
  slots_per_epoch_gt_one : 1 < cfg.slots_per_epoch
  checkpoint_inclusion : ffg_interpretation.state.EventualCheckpointInclusion cfg ext
  checkpoint_projection : EpochCheckpointProjectionLaws
    ffg_interpretation.anchor (E.RootKnownInScheduledPrefix cfg ext) ffg_interpretation.state.checkpoint_at_epoch
  exact_link_validity : ffg_interpretation.state.LinkCheckpointAgreement

end Execution
end FastConfirmation.Spec
end

end
