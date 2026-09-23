module
public import FastConfirmationProofs.ForkChoice.Filter.SelectedTraceFilter
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedCompatibility
public import FastConfirmationProofs.Checkpoints.SelectedPreQueryAnchor
public import FastConfirmationProofs.Execution.History.CausalCheckpointEpochBound
public import FastConfirmationProofs.FFG.SelectedSource.SelectedFFGRealization
public import FastConfirmationProofs.FFG.Certificates.PaperCheckpointInclusionProjectionCore
public import FastConfirmationProofs.FFG.State.ScheduledFFGStateTrajectory
public import FastConfirmationProofs.Safety.BlockAgreement
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Non-circular selected-trace FFG realization

This module replaces the legacy `SelectedTraceFFGPipeline` boundary with the
causal/state-facing pieces actually used by the coupled proof.  The contract is
indexed by the exact selected call.  It does not contain filter membership,
`TipSourceFresh`, a leaf, a common-descendant placement, or a future head/safety
conclusion.

The remaining semantic fields have deliberately different roles:

* endpoint certificate, selector, finalized-boundary, and source-persistence
  realization describe concrete values read from honest endpoint stores;
* pre-query result/checkpoint comparability is the initial SIR / helper-gate
  soundness boundary;
* every non-anchor endpoint justification exposes a causal honest target vote;
  votes at or after the query are discharged by the actual head induction; and
* source availability exposes the paper's early-recency / later-inclusion
  alternative at a **seed** below an already-compatible selected result.
  Finite leaf selection, availability propagation, filter placement, and
  filtered membership are then proved mechanically.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The exact earlier-slot canonicality window available at one endpoint of
the coupled selected-result induction. -/
def SelectedCanonicalBeforeEndpointAt (q : ℕ) (glc : Root) (m : ℕ) : Prop :=
  ∀ w' ∈ E.honest, ∀ m' : ℕ,
    E.slot_start cfg (E.slot_at cfg q) ≤ m' →
    E.slot_at cfg m' < E.slot_at cfg m →
    E.WithinHorizon cfg m' →
    is_ancestor (E.store cfg ext w' m')
      (get_head cfg (E.store cfg ext w' m'))
      (get_node_for_root glc) = true



/-- The selected-margin bundle already contains every premise used by
concrete Casper accountability; the FFG realization must not ask for a
duplicate economic assumption. -/
def SelectedMarginAssumptions.toFFGAccountabilityAssumptions
    (hA : SelectedMarginAssumptions cfg ext E) :
    FFGAccountabilityAssumptions cfg ext E where
  genesis_store := by
    obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hA.genesis
    exact ⟨ast, ablk, hgen⟩
  whole_seconds := hA.whole_seconds
  honest_behavior := hA.honest_behavior
  externals_coherence := hA.externals_coherence
  static_validator_set := hA.static_validators
  byzantine_bound := hA.byzantine_bound





end Execution

end FastConfirmation.Spec

end
