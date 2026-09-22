module
public import FastConfirmation.Spec.Proof.PaperA32ProjectionCore
public import FastConfirmation.Spec.Proof.FFGStateTrajectory
public import FastConfirmation.Spec.Proof.BlockAgreement
public import FastConfirmation.Spec.Proof.ExecutionRootReflection

@[expose] public section

/-!
# Exact paper-A3.2 conclusion projected into the executable store

The paper assumption concludes the root-sensitive fact
`C(b,e) ∈ AU(seed)` at a concrete descendant.  This file proves the weaker
executable state fact used by the filter pipeline; it does not assume that
state fact independently.

The scheduled-root specialization has only two ingredients:

* `ChainFFGState.gu_max` turns exact AU membership into the epoch lower bound
  on `GU(seed)`; and
* `FFGStateTrajectory.unrealized_justification_eq` identifies that selector
  with the reachable store's per-root unrealized map.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Scheduled-root realization of the generic root-local projection. -/
def legacyPaperA32RootProjectionAt
    {anchor : Checkpoint Root}
    (S : ChainFFGState cfg E anchor)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (m : ℕ)
    {r : Root} (hr : r ∈ (E.store cfg ext w m).block_roots) :
    PaperA32RootProjectionAt cfg ext (S.paperA32View cfg)
      (E.store cfg ext w m) r where
  causal_store := E.store_causal cfg ext w m
  root_known := hr
  gu_max := by
    intro c hAU
    change c.epoch ≤ (S.GU r).epoch
    apply S.gu_max ⟨_, E.blockAt_of_store_known cfg ext hr⟩
    change S.AU cfg r c at hAU
    exact hAU
  unrealized_justification := by
    change (E.store cfg ext w m).unrealized_justifications r = S.GU r
    exact E.unrealized_justification_eq hcoh w m hr

/-- If the target checkpoint is already available/unrealized on a concrete
descendant of the selected block, no invocation of paper Assumption 3.2 is
needed.  State-trajectory coherence projects that existing AU fact directly
to the executable unrealized-justification map.

This is deliberately carrier-local: AU is not moved backward from a later
tip to `selected`.  The caller supplies the concrete descendant carrier and
its endpoint ancestry, normally by relaying a query-store carrier. -/
theorem a32IncludedAtTip_of_existing_AU
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    {selected seed : Root} {e : Epoch}
    {w : ValidatorIndex} {m : ℕ}
    (hseed : seed ∈ (E.store cfg ext w m).block_roots)
    (hseedSelected : is_ancestor (E.store cfg ext w m)
      (get_node_for_root seed) (get_node_for_root selected) = true)
    (hseedEpoch : get_block_epoch cfg (E.store cfg ext w m) seed < e + 2)
    (hAU : S.AU cfg seed (S.C selected e)) :
    A32IncludedAtTip cfg (E.store cfg ext w m) e selected seed := by
  exact (E.legacyPaperA32RootProjectionAt cfg ext S hcoh w m hseed)
    |>.a32IncludedAtTip_of_existing_AU cfg ext
      hseedSelected hseedEpoch hAU

/-- The exact conclusion of paper Assumption 3.2 implies the executable
`A32IncludedAtTip` projection at every eligible endpoint.

No target-only support premise appears here: `hsupport` is the paper's full
source-specific, per-view/per-descendant antecedent. -/
theorem a32IncludedAtTip_of_paper
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hpaper : PaperA32Inclusion cfg ext S)
    {b : Root} {bb : BeaconBlock Root} {e : Epoch}
    (hb : E.BlockAt b bb)
    (hbe : compute_epoch_at_slot cfg bb.slot ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : PaperA32SupportThroughoutEpoch cfg ext S b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      A32IncludedAtTip cfg (E.store cfg ext w m) e b seed := by
  apply E.a32IncludedAtTip_of_paperCore cfg ext hpaper hb hbe
    hcanonical hsupport hw hHm hboundary
  intro r hr
  exact E.legacyPaperA32RootProjectionAt cfg ext S hcoh w m hr

/-- Reachable-store specialization which obtains the paper's concrete block
witness from block provenance. -/
theorem a32IncludedAtTip_of_paper_at_known
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hpaper : PaperA32Inclusion cfg ext S)
    {u : ValidatorIndex} {q : ℕ} {b : Root}
    (hbKnown : b ∈ (E.store cfg ext u q).block_roots)
    {e : Epoch}
    (hbe : get_block_epoch cfg (E.store cfg ext u q) b ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : PaperA32SupportThroughoutEpoch cfg ext S b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      A32IncludedAtTip cfg (E.store cfg ext w m) e b seed := by
  let bb := (E.store cfg ext u q).blocks b
  have hb : E.BlockAt b bb := E.blockAt_of_store_known cfg ext hbKnown
  apply E.a32IncludedAtTip_of_paper cfg ext hcoh hpaper hb
  · simpa only [bb, get_block_epoch] using hbe
  · exact hcanonical
  · exact hsupport
  · exact hw
  · exact hHm
  · exact hboundary

end Execution

end FastConfirmation.Spec

end
