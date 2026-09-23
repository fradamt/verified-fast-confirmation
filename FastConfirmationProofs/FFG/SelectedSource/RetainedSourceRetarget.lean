module
public import FastConfirmationProofs.FFG.State.PathLocalFinalizedTransport
public import FastConfirmationProofs.ForkChoice.Filter.SelectedFilterChainGeometry
public import Mathlib.Tactic

@[expose] public section

/-!
# Accepted retained-source filter certificates

This module is the mechanical merge point for the early phase-source and
finalized-placement developments.  A retained accepted source carrier already
owns a recent voting source on a concrete childless descendant of the selected
block.  Once the surrounding hierarchy proof places the selected block below
the endpoint justified checkpoint, and one proved finality branch supplies
the exact finalized checkpoint equation at that same tip, the executable
`FilterTipCertificate` follows without another semantic premise.

In particular, this file does not assume filter membership, `SafeFrom`,
source visibility, a free finalized seed, legacy JI, or a safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

namespace AcceptedRetainedPhaseSourceCarrierAt

variable {E : Execution Root}

/-- Add the justified and finalized-boundary geometry to an accepted retained
source carrier.  The carrier itself supplies every source/leaf/selected fact;
the two remaining inputs are ordinary endpoint hierarchy and walk facts. -/
def retainedFilterTipPlacement
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hparent : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjustifiedKnown : store.justified_checkpoint.root ∈ store.block_roots)
    (hselectedJustified : is_ancestor store
      (get_node_for_root selected)
      (get_node_for_root store.justified_checkpoint.root) = true) :
    RetainedFilterTipPlacement cfg store selected := by
  have htipJustified : is_ancestor store (get_node_for_root h.tip)
      (get_node_for_root store.justified_checkpoint.root) = true :=
    is_ancestor_trans (a := get_node_for_root h.tip) (b := get_node_for_root selected)
      (c := get_node_for_root store.justified_checkpoint.root) hparent
      (hwalkK store.justified_checkpoint.root hjustifiedKnown h.tip h.tip_known)
      (hwalkK store.justified_checkpoint.root hjustifiedKnown selected
        h.selected_known)
      h.tip_descends_selected hselectedJustified
  exact {
    tip := h.tip
    tip_known := h.tip_known
    tip_descends_justified := htipJustified
    tip_descends_child := h.tip_descends_selected
    tip_is_leaf := h.tip_is_leaf
    finalized_walk_known :=
      hfinalized.finalizedWalkKnown cfg hwalkK h.tip_known
  }

/-- Consumer-shaped merge theorem.

The finalized equation is deliberately indexed by `h.tip`: this prevents an
existential finalized carrier elsewhere in the store from being mistaken for
the leaf actually used by the executable filter. -/
theorem filterTipCertificate_of_finalizedCheck
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hparent : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjustifiedKnown : store.justified_checkpoint.root ∈ store.block_roots)
    (hselectedJustified : is_ancestor store
      (get_node_for_root selected)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hnotCovered : is_ancestor store
      (get_node_for_root store.justified_checkpoint.root)
      (get_node_for_root selected) ≠ true)
    (hfinalizedCheck : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store h.tip
          store.finalized_checkpoint.epoch) :
    Nonempty (FilterTipCertificate cfg store selected) := by
  let hplace := h.retainedFilterTipPlacement cfg ext hfinalized hparent hwalkK
    hjustifiedKnown hselectedJustified
  obtain ⟨hskel, htip⟩ :=
    SelectedFilterChainGeometry.exists_filterTipSkeleton_of_placement
      cfg hparent hwalkK hjustifiedKnown h.selected_known hnotCovered hplace
  have htip' : hskel.tip = h.tip := by
    simpa only [hplace, retainedFilterTipPlacement] using htip
  refine ⟨{
    mids := hskel.mids
    tip := hskel.tip
    chain := hskel.chain
    child_on_chain := hskel.child_on_chain
    tip_is_leaf := hskel.tip_is_leaf
    parent_slot_lt := hskel.parent_slot_lt
    justified_ok := ?_
    finalized_ok := ?_
  }⟩
  · exact Or.inr (Or.inr (by simpa only [htip'] using h.source_recent))
  · simpa only [htip'] using hfinalizedCheck





end AcceptedRetainedPhaseSourceCarrierAt

end Execution


end FastConfirmation.Spec

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
