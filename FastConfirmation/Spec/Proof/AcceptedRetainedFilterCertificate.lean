import FastConfirmation.Spec.Proof.AcceptedPathLocalFinalizedTransport
import FastConfirmation.Spec.Proof.SelectedFilterChainGeometry

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
    is_ancestor_trans hparent
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

/-- Direct executable filtered-child output from the same consumer-shaped
inputs. -/
theorem child_filtered_of_finalizedCheck
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {parent selected : Root}
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
          store.finalized_checkpoint.epoch)
    (hparentEdge : (store.blocks selected).parent_root = parent) :
    ForkChoiceNode.mk selected ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk parent) := by
  obtain ⟨hcert⟩ := h.filterTipCertificate_of_finalizedCheck cfg ext hfinalized
    hparent hwalkK hjustifiedKnown hselectedJustified hnotCovered
      hfinalizedCheck
  exact hcert.child_filtered cfg hparentEdge

/-- Exact-stable specialization.  The query contributes the concrete viable
leaf which passed its executable finalized check; paired causal walks move
that check to the endpoint carrier without a whole-store inclusion premise. -/
theorem filterTipCertificate_of_exactStableQuery
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hwfExecution : WellFormedExecution E)
    {query endpoint : Store Root}
    (hquery : E.CausalStore cfg ext query)
    (hfinalized : FinalizedBoundaryRealization cfg endpoint)
    (hqueryParent : ParentSlotLt query)
    (hendpointParent : ParentSlotLt endpoint)
    (hendpointWalk : ∀ t ∈ endpoint.block_roots,
      ∀ r ∈ endpoint.block_roots,
        WalkKnown endpoint (endpoint.blocks t).slot r)
    (hjustifiedKnown : endpoint.justified_checkpoint.root ∈
      endpoint.block_roots)
    {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B endpoint selected)
    (hselectedQuery : selected ∈ query.block_roots)
    (hselectedJustified : is_ancestor endpoint
      (get_node_for_root selected)
      (get_node_for_root endpoint.justified_checkpoint.root) = true)
    (hnotCovered : is_ancestor endpoint
      (get_node_for_root endpoint.justified_checkpoint.root)
      (get_node_for_root selected) ≠ true)
    (hviable : PathLocalFilterViableLeafBelow cfg query selected)
    (hstable : endpoint.finalized_checkpoint =
      query.finalized_checkpoint)
    (hboundarySelected : compute_start_slot_at_epoch cfg
      query.finalized_checkpoint.epoch ≤ (query.blocks selected).slot)
    (hquerySelectedBoundaryWalk : WalkKnown query
      (compute_start_slot_at_epoch cfg
        query.finalized_checkpoint.epoch) selected)
    (hendpointSelectedBoundaryWalk : WalkKnown endpoint
      (compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch) selected) :
    Nonempty (FilterTipCertificate cfg endpoint selected) := by
  have htipBoundaryWalk := hfinalized.finalizedWalkKnown cfg
    hendpointWalk h.tip_known
  have hfinalizedCheck := h.finalized_check_of_exactStable_query cfg ext
    hwfExecution hquery hendpointParent hqueryParent hselectedQuery hviable
      hstable hboundarySelected hquerySelectedBoundaryWalk
        hendpointSelectedBoundaryWalk htipBoundaryWalk
  exact h.filterTipCertificate_of_finalizedCheck cfg ext hfinalized
    hendpointParent hendpointWalk hjustifiedKnown hselectedJustified
      hnotCovered hfinalizedCheck

/-- Visibility specialization for late/A3.2 branches.  Visibility is used
only to derive a dominating accepted `GJ`/`GU` target at this exact retained
tip; cross-carrier certificate accountability then proves the finalized
checkpoint equation before the generic merge constructs the filter. -/
theorem filterTipCertificate_of_sourceVisible
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
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
    (hvisible : SourceVisibleAtTip cfg store h.tip) :
    Nonempty (FilterTipCertificate cfg store selected) := by
  let hplace := h.retainedFilterTipPlacement cfg ext hfinalized hparent
    hwalkK hjustifiedKnown hselectedJustified
  have hfinalizedCheck : store.finalized_checkpoint.root =
      get_checkpoint_block cfg store h.tip
        store.finalized_checkpoint.epoch := by
    have hcheck := hplace.finalizedRoot_eq_checkpointBlock_of_acceptedVisible
      cfg ext B hgen hanchor P V hanchorExact hacc h.store_causal hparent
        hvisible
    simpa only [hplace, retainedFilterTipPlacement] using hcheck
  exact h.filterTipCertificate_of_finalizedCheck cfg ext hfinalized hparent
    hwalkK hjustifiedKnown hselectedJustified hnotCovered
      (Or.inr hfinalizedCheck)

/-- Trusted-anchor specialization of the merge theorem.  Positive AU at the
retained tip proves the anchor checkpoint equation; no source visibility or
additional finalized carrier is supplied. -/
theorem filterTipCertificate_of_anchorFinality
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
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
    (hfinalizedAnchor : store.finalized_checkpoint = B.anchor) :
    Nonempty (FilterTipCertificate cfg store selected) := by
  have hwalk := hfinalized.finalizedWalkKnown cfg hwalkK h.tip_known
  have hfinalizedCheck := h.finalizedRoot_eq_checkpointBlock_of_anchor
    cfg ext B P V hanchorExact hparent hfinalizedAnchor hwalk
  exact h.filterTipCertificate_of_finalizedCheck cfg ext hfinalized hparent hwalkK
    hjustifiedKnown hselectedJustified hnotCovered (Or.inr hfinalizedCheck)

end AcceptedRetainedPhaseSourceCarrierAt

end Execution


end FastConfirmation.Spec
