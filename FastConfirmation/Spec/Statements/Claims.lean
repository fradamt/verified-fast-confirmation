module
public import FastConfirmation.Spec.Model
public import FastConfirmation.Spec.Model.ExactCheckpointLinks
public import FastConfirmation.Spec.Statements.Traces
public import FastConfirmation.Spec.Statements.Premises.Live
public import FastConfirmation.Spec.Statements.Premises.FFG
public import FastConfirmation.Spec.Statements.Premises.Execution
public import FastConfirmation.Spec.Statements.Premises.Trajectory

@[expose] public section

/-!
# Claims

The accepted safety and live monotonicity claims and their premise record. Reads the Spec Model and Statements premises. Read the proof facade next.
-/

section

/-! ## From AcceptedActualFCRNextSlotSafetyFacade -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
/-- Assumptions for the stored-output following-slot theorem.

There is deliberately no finalized-reset, observed-adoption, observed-lock,
head-ancestry, filter-result, or safety field.  Finalized next-slot safety and
active-observed restart safety are already derived by the fold. -/
structure AcceptedActualFCRNextSlotSafetyAssumptions where
  semantics : ExactPrefixAcceptedFFGSemantics cfg ext E
  trajectory : E.ScheduledPrefixTrajectoryAssumptions cfg ext
  completed_calls :
    E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext
  epoch_ends_fit : EpochEndsFitUint64 cfg
  anchor_eq : semantics.anchor = E.genesis_store.justified_checkpoint
  anchor_boundary : TrustedAnchorBoundaryAligned (cfg := cfg)
    (E := E) (anchor := semantics.anchor)
  finalization_delay :
    E.AcceptedRealizedFinalizationDelay cfg ext semantics
  slots_per_epoch_gt_one : 1 < cfg.slots_per_epoch
  paper_a32 : semantics.state.PaperA32Inclusion cfg ext
  checkpoint_projection : AcceptedEpochCheckpointProjection
    semantics.anchor (E.AcceptedRoot cfg ext) semantics.state.C
  exact_link_validity : semantics.state.ExactLinkValidity

namespace AcceptedActualFCRNextSlotSafetyAssumptions
end AcceptedActualFCRNextSlotSafetyAssumptions
end Execution
/-- Accepted whole-output safety with the same endpoint quantifiers and timing
as `Spec_Safety_next_slot`, under the accepted executable-semantics bundle.

The global `PaperSafetySynchrony` inside `completed_calls` makes this the
current model's GST-0 specialization. Its four fields are honest-attestation
delivery, block relay, payload-envelope relay, and equivocation-evidence relay;
it does not require the additional `latest_message_relay` premise of the full
`Synchrony` bundle. -/
def AcceptedSpec_Safety_next_slot : Prop :=
  ∀ E : Execution Root,
    E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
          E.WithinHorizon cfg m →
            is_ancestor (E.store cfg ext w m)
              (get_head cfg (E.store cfg ext w m))
              (get_node_for_root (E.confirmed cfg ext v n)) = true

/-- Accepted-bundle specialization of the upstream strict-monotonicity
statement. The fifth live field now bounds FFG checkpoint visibility at
epoch boundaries. The one-confirmation, reconfirmation, and fork-choice
bridges are developed in the live-monotonicity proof modules. -/
def AcceptedSpec_Monotonicity_live : Prop :=
  Spec_Monotonicity_live cfg ext
    (fun E => Nonempty (E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext))

end FastConfirmation.Spec

end

end
