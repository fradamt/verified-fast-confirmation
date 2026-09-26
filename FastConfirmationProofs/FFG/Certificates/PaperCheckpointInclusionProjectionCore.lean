module
public import FastConfirmationProofs.FFG.State.ProcessedFFGStateTrajectory
public import FastConfirmationProofs.FFG.SelectedSource.SelectedFFGRealization

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Generic and accepted paper-A3.2 projection

This module projects the exact paper conclusion into an executable store
without mentioning the migration-only `ChainFFGState`.  The state view is
fixed before the endpoint; the root projection records the concrete causal
store and known root at which GU maximality and unrealized-map reflection are
used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- Executable projection laws at one concrete known root.  Making the causal
store and finite-domain witness fields prevents total-map equations from
being applied to rejected or unknown roots. -/
structure PaperA32RootProjectionAt
    {E : Execution Root} (V : CheckpointInclusionView cfg E)
    (store : Store Root) (r : Root) : Prop where
  causal_store : E.ScheduledPrefixStore cfg ext store
  root_known : r ∈ store.block_roots
  unrealized_justified_max : ∀ {c : Checkpoint Root}, V.AvailableCheckpoint cfg r c →
    c.epoch ≤ (V.GU r).epoch
  unrealized_justification :
    store.unrealized_justifications r = V.GU r

/-- Strong paper-facing endpoint result.  The executable GU-epoch projection
is retained together with the exact AU witness from Assumption 3.2, including
its underlying formed carrier. -/
structure PaperA32IncludedAtTip
    {E : Execution Root} (V : CheckpointInclusionView cfg E)
    (store : Store Root) (e : Epoch) (selected seed : Root) : Prop where
  executable : A32IncludedAtTip cfg store e selected seed
  exact_AU : V.AvailableCheckpoint cfg seed (V.C selected e)

namespace PaperA32IncludedAtTip


end PaperA32IncludedAtTip

namespace AcceptedBlockFFGState


/-- Accepted-state realization of the root-local executable projection. -/
def paperA32RootProjectionAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (hcoh : FFGStateReadAgreement cfg ext S)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    {r : Root} (hr : r ∈ store.block_roots) :
    PaperA32RootProjectionAt cfg ext (S.checkpoint_inclusion_view cfg ext) store r where
  causal_store := hstore
  root_known := hr
  unrealized_justified_max := by
    intro c hAU
    change c.epoch ≤ (S.unrealized_justified r).epoch
    apply S.unrealized_justified_max (E.acceptedRoot_of_causal_known cfg ext hstore hr)
    change S.AvailableCheckpoint cfg ext r c at hAU
    exact hAU
  unrealized_justification := by
    change store.unrealized_justifications r = S.unrealized_justified r
    exact (hstore.acceptedFFGStoreProjection hcoh).unrealized_justification
      r hr

end AcceptedBlockFFGState

namespace PaperA32RootProjectionAt

/-- Exact AU inclusion at a concrete carrier implies the weaker executable
epoch projection used by the endpoint pipeline. -/
theorem a32IncludedAtTip_of_existing_AU
    {E : Execution Root} {V : CheckpointInclusionView cfg E}
    {selected seed : Root} {e : Epoch} {store : Store Root}
    (P : PaperA32RootProjectionAt cfg ext V store seed)
    (hseedSelected : is_ancestor store
      (get_node_for_root seed) (get_node_for_root selected) = true)
    (hseedEpoch : get_block_epoch cfg store seed < e + 2)
    (hAU : V.AvailableCheckpoint cfg seed (V.C selected e)) :
    A32IncludedAtTip cfg store e selected seed := by
  refine ⟨P.root_known, hseedSelected, hseedEpoch, ?_⟩
  rw [P.unrealized_justification]
  have hmax : (V.C selected e).epoch ≤ (V.GU seed).epoch :=
    P.unrealized_justified_max hAU
  simpa only [V.checkpoint_epoch] using hmax

end PaperA32RootProjectionAt

namespace Execution

variable (E : Execution Root)

/-- Strong generic paper-A3.2 projection.  The liveness assumption, state
view, and root-local executable projection are independent inputs; no
selected-tip, placement, safety, JI, or finality premise is introduced. -/
theorem paperA32IncludedAtTip_of_paperCore
    {V : CheckpointInclusionView cfg E}
    (hpaper : EventualCheckpointInclusion cfg ext V)
    {b : Root} {bb : BeaconBlock Root} {e : Epoch}
    (hb : V.BlockAt b bb)
    (hbe : compute_epoch_at_slot cfg bb.slot ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : SourceTargetSupportThroughoutEpoch cfg ext V b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m)
    (hprojection : ∀ {r : Root},
      r ∈ (E.store cfg ext w m).block_roots →
        PaperA32RootProjectionAt cfg ext V
          (E.store cfg ext w m) r) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg V
        (E.store cfg ext w m) e b seed := by
  obtain ⟨seed, hseed, _hbKnown, hseedB, hseedEpoch, hAU⟩ :=
    hpaper.included hb hbe hcanonical hsupport w hw m hHm hboundary
  exact ⟨seed, {
    executable :=
      (hprojection hseed).a32IncludedAtTip_of_existing_AU cfg ext
        hseedB hseedEpoch hAU
    exact_AU := hAU }⟩


/-- Strong production accepted-state consumer of the paper assumption.  The
base block is accepted, and the exact AU/formed-carrier result survives the
executable projection. -/
theorem accepted_paperA32IncludedAtTip_of_paper
    {anchor : Checkpoint Root}
    {S : AcceptedBlockFFGState cfg ext E anchor}
    (hcoh : FFGStateReadAgreement cfg ext S)
    (hpaper : S.EventualCheckpointInclusion cfg ext)
    {b : Root} {bb : BeaconBlock Root} {e : Epoch}
    (hb : E.BlockKnownInScheduledPrefix cfg ext b bb)
    (hbe : compute_epoch_at_slot cfg bb.slot ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : S.SourceTargetSupportThroughoutEpoch cfg ext b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg (S.checkpoint_inclusion_view cfg ext)
        (E.store cfg ext w m) e b seed := by
  apply E.paperA32IncludedAtTip_of_paperCore cfg ext hpaper hb hbe
    hcanonical hsupport hw hHm hboundary
  intro r hr
  exact S.paperA32RootProjectionAt cfg ext hcoh
    (E.store_causal cfg ext w m) hr


/-- Strong reachable-store specialization deriving the accepted base-block
witness from finite-domain knownness. -/
theorem accepted_paperA32IncludedAtTip_of_paper_at_known
    {anchor : Checkpoint Root}
    {S : AcceptedBlockFFGState cfg ext E anchor}
    (hcoh : FFGStateReadAgreement cfg ext S)
    (hpaper : S.EventualCheckpointInclusion cfg ext)
    {u : ValidatorIndex} {q : ℕ} {b : Root}
    (hbKnown : b ∈ (E.store cfg ext u q).block_roots)
    {e : Epoch}
    (hbe : get_block_epoch cfg (E.store cfg ext u q) b ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : S.SourceTargetSupportThroughoutEpoch cfg ext b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg (S.checkpoint_inclusion_view cfg ext)
        (E.store cfg ext w m) e b seed := by
  let bb := (E.store cfg ext u q).blocks b
  have hb : E.BlockKnownInScheduledPrefix cfg ext b bb :=
    E.acceptedBlockAt_of_store_known cfg ext u q hbKnown
  apply E.accepted_paperA32IncludedAtTip_of_paper cfg ext hcoh hpaper hb
  · simpa only [bb, get_block_epoch] using hbe
  · exact hcanonical
  · exact hsupport
  · exact hw
  · exact hHm
  · exact hboundary


end Execution

end FastConfirmation.Spec

end
