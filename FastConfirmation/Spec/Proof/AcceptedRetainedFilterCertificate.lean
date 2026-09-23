module
public import FastConfirmation.Spec.Proof.AcceptedPathLocalFinalizedTransport
public import FastConfirmation.Spec.Proof.SelectedFilterChainGeometry

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

end
