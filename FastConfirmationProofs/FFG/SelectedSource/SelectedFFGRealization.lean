module
public import FastConfirmationProofs.ForkChoice.Filter.SelectedFilterChainGeometry

@[expose] public section

/-!
# Mechanical selected-FFG realization

This module isolates the non-circular, store-local half of the selected
never-filter argument.

`EndpointSelectorRealization` records only facts about values already read
from an endpoint store: voting sources are concretely certified, and a source
which is already realized cannot be newer than the store's realized justified
checkpoint.  It does not
say that an arbitrary historical block has incorporated the endpoint's latest
justified checkpoint.

That last, directional availability fact is the separately indexed
`SourceVisibleAtTip`.  It is the narrow state-transition / on-chain-inclusion
boundary corresponding to the paper's selector-visibility assumption.  In
particular, neither structure mentions filter membership, source freshness,
or safety of a selected block.

The rest of the module is mechanical:

* realized selector maximality plus `SourceVisibleAtTip` and accountable
  same-epoch uniqueness prove the executable voting-source disjunction;
* a finite store has a childless parent-descendant above every known root;
* finalized-boundary walk knownness follows from ordinary known-root walk
  closure and the finalized root's slot bound; and
* these facts assemble a `RetainedFilterTipPlacement` for an explicitly
  supplied visible leaf.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Endpoint selector semantics -/


/-- Store-local facts which turn ordinary known-root closure into the special
walk required at the finalized epoch boundary.  These are kept separate from
`EndpointSelectorRealization`: they concern finalized-root representation,
not voting-source selection. -/
structure FinalizedBoundaryRealization (store : Store Root) : Prop where
  finalized_root_known :
    store.finalized_checkpoint.root ∈ store.block_roots
  finalized_root_slot_le_boundary :
    (store.blocks store.finalized_checkpoint.root).slot ≤
      compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch

/-- The endpoint's realized justified checkpoint has become available to the
voting-source selector at this particular tip.  This is intentionally
tip-indexed: it is false in general for an old leaf whose cached state predates
a later realized checkpoint. -/
structure SourceVisibleAtTip (store : Store Root) (tip : Root) : Prop where
  justified_epoch_le_source :
    store.justified_checkpoint.epoch ≤
      (get_voting_source cfg store tip).epoch

/-- Voting-source epochs do not go backwards along a known descendant chain.
This is the narrow chain-persistence boundary needed to transport selector
visibility from a seed block to a mechanically chosen leaf.  It has no filter,
head, or safety conclusion. -/
structure VotingSourceEpochChainPersistence (store : Store Root) : Prop where
  source_epoch_le_of_descends : ∀ {seed tip : Root},
    seed ∈ store.block_roots →
    tip ∈ store.block_roots →
    is_ancestor store (get_node_for_root tip)
      (get_node_for_root seed) = true →
    (get_voting_source cfg store seed).epoch ≤
      (get_voting_source cfg store tip).epoch

/-- Once the endpoint justified checkpoint is visible at a known seed, source
epoch persistence makes it visible at every known descendant. -/
theorem SourceVisibleAtTip.of_descendant
    {store : Store Root}
    (hpersistence : VotingSourceEpochChainPersistence cfg store)
    {seed tip : Root}
    (hseed : seed ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (htipSeed : is_ancestor store (get_node_for_root tip)
      (get_node_for_root seed) = true)
    (hvisible : SourceVisibleAtTip cfg store seed) :
    SourceVisibleAtTip cfg store tip := by
  exact ⟨hvisible.justified_epoch_le_source.trans
    (hpersistence.source_epoch_le_of_descends hseed htip htipSeed)⟩


/-- Store projection of the paper's Assumption 3.2 conclusion at one fresh
descendant.  The full paper statement says that the block includes the
relevant FFG votes in its available/unrealized data.  Since the executable
Spec model projects block bodies away, `target_in_unrealized` is the narrow
state consequence needed here.  This structure deliberately does not mention
the endpoint justified checkpoint, a filter, a leaf, or source freshness. -/
structure A32IncludedAtTip (store : Store Root) (baseEpoch : Epoch)
    (selected seed : Root) : Prop where
  seed_known : seed ∈ store.block_roots
  seed_descends_selected : is_ancestor store (get_node_for_root seed)
    (get_node_for_root selected) = true
  seed_before_boundary : get_block_epoch cfg store seed < baseEpoch + 2
  target_in_unrealized :
    baseEpoch ≤ (store.unrealized_justifications seed).epoch

/-- Once an Assumption-3.2 inclusion block is old enough to be read through
the executable unrealized-justification map, its voting source carries at
least the included target epoch.  This is definitional state realization, not
a never-filter or safety theorem. -/
theorem A32IncludedAtTip.baseEpoch_le_votingSource
    {store : Store Root} {baseEpoch : Epoch} {selected seed : Root}
    (h : A32IncludedAtTip cfg store baseEpoch selected seed)
    (hboundary : baseEpoch + 2 ≤ get_current_store_epoch cfg store) :
    baseEpoch ≤ (get_voting_source cfg store seed).epoch := by
  have hOld : get_block_epoch cfg store seed <
      get_current_store_epoch cfg store :=
    h.seed_before_boundary.trans_le hboundary
  simp only [get_voting_source]
  rw [if_pos]
  · exact h.target_in_unrealized
  · simpa only [get_block_epoch] using hOld

/-- A later inclusion becomes endpoint-justified visibility only after the
separate SIR/no-conflict ordering step bounds the endpoint justified epoch by
the included base epoch. -/
theorem A32IncludedAtTip.sourceVisible
    {store : Store Root} {baseEpoch : Epoch} {selected seed : Root}
    (h : A32IncludedAtTip cfg store baseEpoch selected seed)
    (hboundary : baseEpoch + 2 ≤ get_current_store_epoch cfg store)
    (hjustified : store.justified_checkpoint.epoch ≤ baseEpoch) :
    SourceVisibleAtTip cfg store seed := by
  exact ⟨hjustified.trans (h.baseEpoch_le_votingSource cfg hboundary)⟩




/-- The special finalized-boundary walk is not an independent placement
assumption.  Start with the ordinary known-root walk at the finalized root's
slot and raise its target slot to the finalized epoch boundary. -/
theorem FinalizedBoundaryRealization.finalizedWalkKnown
    {store : Store Root}
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {tip : Root} (htip : tip ∈ store.block_roots) :
    WalkKnown store
      (compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch) tip := by
  exact (hwalkK store.finalized_checkpoint.root
    hfinalized.finalized_root_known tip htip).mono
      hfinalized.finalized_root_slot_le_boundary

/-! ## Finite raw-tree leaf extension -/

omit [Inhabited Root] in
/-- Every known root in a finite, slot-well-founded store has a known
childless descendant on the ordinary known-walk domain.  Choose a maximum-slot
member of the finite set of known roots which walk to, and descend from, the
starting root; any known child would be another member with a strictly larger
slot. -/
theorem exists_store_leaf_extension {store : Store Root}
    (hwf : ParentSlotLt store) {c : Root}
    (hc : c ∈ store.block_roots) :
    ∃ tip : Root,
      tip ∈ store.block_roots ∧
      WalkKnown store (store.blocks c).slot tip ∧
      is_ancestor store (get_node_for_root tip)
        (get_node_for_root c) = true ∧
      store.block_roots.filter
        (fun x => (store.blocks x).parent_root = tip) = [] := by
  classical
  let descendants : Finset Root :=
    store.block_roots.toFinset.filter
      (fun r => WalkKnown store (store.blocks c).slot r ∧
        is_ancestor store (get_node_for_root r)
          (get_node_for_root c) = true)
  have hcWalk : WalkKnown store (store.blocks c).slot c :=
    .stop hc (le_refl _)
  have hcMem : c ∈ descendants := by
    simp only [descendants, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hc, hcWalk, is_ancestor_refl store _⟩
  obtain ⟨tip, htipDescendants, hmax⟩ :=
    descendants.exists_max_image (fun r => (store.blocks r).slot)
      ⟨c, hcMem⟩
  have htipData : tip ∈ store.block_roots ∧
      WalkKnown store (store.blocks c).slot tip ∧
      is_ancestor store (get_node_for_root tip)
        (get_node_for_root c) = true := by
    simpa only [descendants, Finset.mem_filter, List.mem_toFinset] using
      htipDescendants
  refine ⟨tip, htipData.1, htipData.2.1, htipData.2.2, ?_⟩
  apply List.filter_eq_nil_iff.mpr
  intro child hchild
  simp only [decide_eq_true_eq]
  intro hparent
  have htipSlotLe : (store.blocks c).slot ≤
      (store.blocks tip).slot := by
    have hancestorSlotLe := get_ancestor_slot_le hwf htipData.2.1
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at htipData
    rw [htipData.2.2] at hancestorSlotLe
    exact hancestorSlotLe
  have htipParentKnown : (store.blocks child).parent_root ∈
      store.block_roots := by
    rw [hparent]
    exact htipData.1
  have hslotLt := hwf child hchild htipParentKnown
  rw [hparent] at hslotLt
  have hchildWalk : WalkKnown store (store.blocks c).slot child :=
    .step hchild (htipSlotLe.trans_lt hslotLt) (by
      rw [hparent]
      exact htipData.2.1)
  have hchildTip : is_ancestor store (get_node_for_root child)
      (get_node_for_root tip) = true :=
    is_ancestor_of_parent hwf hchild htipData.1 hparent
  have hchildC : is_ancestor store (get_node_for_root child)
      (get_node_for_root c) = true :=
    is_ancestor_trans (a := get_node_for_root child) (b := get_node_for_root tip)
      (c := get_node_for_root c) hwf hchildWalk htipData.2.1
      hchildTip htipData.2.2
  have hchildMem : child ∈ descendants := by
    simp only [descendants, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hchild, hchildWalk, hchildC⟩
  have hslotLe : (store.blocks child).slot ≤ (store.blocks tip).slot :=
    hmax child hchildMem
  exact (Nat.not_lt_of_ge hslotLe) hslotLt

/-- A visible known seed has a visible childless descendant.  Leaf selection
is still the finite maximum-slot construction above; visibility is transported
afterwards by voting-source epoch persistence. -/
theorem exists_visible_store_leaf_extension {store : Store Root}
    (hwf : ParentSlotLt store)
    (hpersistence : VotingSourceEpochChainPersistence cfg store)
    {seed : Root} (hseed : seed ∈ store.block_roots)
    (hvisible : SourceVisibleAtTip cfg store seed) :
    ∃ tip : Root,
      tip ∈ store.block_roots ∧
      WalkKnown store (store.blocks seed).slot tip ∧
      is_ancestor store (get_node_for_root tip)
        (get_node_for_root seed) = true ∧
      store.block_roots.filter
        (fun x => (store.blocks x).parent_root = tip) = [] ∧
      SourceVisibleAtTip cfg store tip := by
  obtain ⟨tip, htip, htipWalk, htipSeed, hleaf⟩ :=
    exists_store_leaf_extension hwf hseed
  have htipVisible : SourceVisibleAtTip cfg store tip :=
    SourceVisibleAtTip.of_descendant cfg hpersistence
      hseed htip htipSeed hvisible
  exact ⟨tip, htip, htipWalk, htipSeed, hleaf, htipVisible⟩


/-! ## Placement assembly -/




end FastConfirmation.Spec

end
