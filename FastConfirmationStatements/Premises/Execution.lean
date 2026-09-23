module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Traces
public import FastConfirmationStatements.Premises.Live
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.ExecutionConditions
public import FastConfirmationStatements.Premises.Trajectory

@[expose] public section

/-! Defines the accepted next-slot safety premise bundle from exact FFG semantics, scheduled calls, timing, and checkpoint projection. -/

section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
/-- Assumptions for the stored-output following-slot theorem.

There is deliberately no finalized-reset, observed-adoption, observed-lock,
head-ancestry, filter-result, or safety field.  Finalized next-slot safety and
active-observed restart safety are already derived by the fold. -/
structure NextSlotSafetyPremises where
  semantics : ExactPrefixAcceptedFFGSemantics cfg ext E
  trajectory : E.ScheduledPrefixPremises cfg ext
  completed_calls :
    E.CompletedFCRCallPremises cfg ext
  epoch_ends_fit : EpochEndsFitUint64 cfg
  anchor_eq : semantics.anchor = E.genesis_store.justified_checkpoint
  anchor_boundary : TrustedAnchorBoundaryAligned (cfg := cfg)
    (E := E) (anchor := semantics.anchor)
  finalization_delay :
    E.RealizedFinalizationDelay cfg ext semantics
  slots_per_epoch_gt_one : 1 < cfg.slots_per_epoch
  paper_a32 : semantics.state.PaperA32Inclusion cfg ext
  checkpoint_projection : AcceptedEpochCheckpointProjection
    semantics.anchor (E.AcceptedRoot cfg ext) semantics.state.C
  exact_link_validity : semantics.state.ExactLinkValidity

namespace NextSlotSafetyPremises
end NextSlotSafetyPremises
end Execution
end FastConfirmation.Spec
end

end
