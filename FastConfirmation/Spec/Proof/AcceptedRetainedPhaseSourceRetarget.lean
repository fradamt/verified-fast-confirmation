module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedRetainedFilterCertificate

@[expose] public section

/-!
# Retargeting one retained phase-source carrier down the selected chain

`SelectedStrictEdgeFilterSupplyAt` quantifies over every strict edge below a
single selected result.  The expensive source-history argument should not be
repeated for each edge: a childless retained tip above the final selected
result is also above every ancestor edge child.  This module records that
purely mechanical retargeting step while preserving the exact same tip,
source AU witness, and numeric recency proof.

There is no finalized-placement, filter-membership, safety, or history premise
here.  Finality can subsequently be proved once for this unchanged tip and
reused for every retargeted edge.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution
namespace AcceptedRetainedPhaseSourceCarrierAt

variable {E : Execution Root}

/-- Retarget a retained source carrier from `selected` to an ancestor
`candidate`.  The returned carrier has definitionally the same retained tip;
only the selected-root fields are changed. -/
def retarget_ancestor
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {selected candidate : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hparent : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hcandidate : candidate ∈ store.block_roots)
    (hselectedCandidate : is_ancestor store
      (get_node_for_root selected) (get_node_for_root candidate) = true) :
    E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store candidate := by
  refine {
    store_causal := h.store_causal
    tip := h.tip
    selected_known := hcandidate
    tip_known := h.tip_known
    tip_descends_selected := ?_
    tip_is_leaf := h.tip_is_leaf
    source_au := h.source_au
    source_recent := h.source_recent
  }
  exact is_ancestor_trans (a := get_node_for_root h.tip)
    (b := get_node_for_root selected) (c := get_node_for_root candidate) hparent
    (hwalkK candidate hcandidate h.tip h.tip_known)
    (hwalkK candidate hcandidate selected h.selected_known)
    h.tip_descends_selected hselectedCandidate

/-- The retargeting theorem preserves the concrete retained tip exactly. -/
@[simp] theorem retarget_ancestor_tip
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {selected candidate : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hparent : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hcandidate : candidate ∈ store.block_roots)
    (hselectedCandidate : is_ancestor store
      (get_node_for_root selected) (get_node_for_root candidate) = true) :
    (h.retarget_ancestor cfg ext hparent hwalkK hcandidate
      hselectedCandidate).tip = h.tip := rfl

/-- Reuse one finalized check on the unchanged retained tip after retargeting
the carrier to an ancestor edge child.  This is the direct bridge from one
final-result source/finality proof to the per-edge filter quantifier. -/
theorem filterTipCertificate_retarget_ancestor
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {selected candidate : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hparent : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjustifiedKnown : store.justified_checkpoint.root ∈ store.block_roots)
    (hcandidate : candidate ∈ store.block_roots)
    (hselectedCandidate : is_ancestor store
      (get_node_for_root selected) (get_node_for_root candidate) = true)
    (hcandidateJustified : is_ancestor store
      (get_node_for_root candidate)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hnotCovered : is_ancestor store
      (get_node_for_root store.justified_checkpoint.root)
      (get_node_for_root candidate) ≠ true)
    (hfinalizedCheck : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store h.tip
          store.finalized_checkpoint.epoch) :
    Nonempty (FilterTipCertificate cfg store candidate) := by
  let hc := h.retarget_ancestor cfg ext hparent hwalkK hcandidate
    hselectedCandidate
  apply hc.filterTipCertificate_of_finalizedCheck cfg ext hfinalized hparent
    hwalkK hjustifiedKnown hcandidateJustified hnotCovered
  simpa only [hc, retarget_ancestor_tip] using hfinalizedCheck

end AcceptedRetainedPhaseSourceCarrierAt
end Execution


end FastConfirmation.Spec

end
