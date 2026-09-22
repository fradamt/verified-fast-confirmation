module
public import FastConfirmation.Spec.Proof.SelectedFilterChainGeometry

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

/-- Store-local realization of the FFG selectors used by the executable
filter.  Every field is independent of a selected FCR result.

The source fields are restricted to known, non-future roots, exactly the
domain on which the real fork-choice state has a meaningful block-state /
pulled-up-source read.  `source_realized_le_justified` is only the upper
greatest-realized bound.  The converse bound is deliberately absent: old
blocks do not retroactively refresh their stored voting source. -/
structure EndpointSelectorRealization (E : Execution Root)
    (anchor : Checkpoint Root) (store : Store Root) : Prop where
  source_certificate : ∀ tip : Root, tip ∈ store.block_roots →
    (store.blocks tip).slot ≤ get_current_slot cfg store →
      Nonempty
        (CertifiedJustified cfg E anchor (get_voting_source cfg store tip))
  source_realized_le_justified : ∀ tip : Root,
    tip ∈ store.block_roots →
    (store.blocks tip).slot ≤ get_current_slot cfg store →
    (get_voting_source cfg store tip).epoch <
        get_current_store_epoch cfg store →
      (get_voting_source cfg store tip).epoch ≤
        store.justified_checkpoint.epoch

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

/-- The weakest seed-side availability needed for source freshness.  A seed is
available either because it has incorporated the endpoint justified epoch, or
because its voting source is recent enough that incorporation is immaterial.
This predicate contains no leaf, filter, head, or safety conclusion. -/
def SourceAvailableAtTip (store : Store Root) (tip : Root) : Prop :=
  SourceVisibleAtTip cfg store tip ∨
    (get_voting_source cfg store tip).epoch + 2 ≥
      get_current_store_epoch cfg store

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

/-- Source availability propagates down a known descendant chain.  Visibility
uses `SourceVisibleAtTip.of_descendant`; recency uses monotonicity of the
voting-source epoch. -/
theorem SourceAvailableAtTip.of_descendant
    {store : Store Root}
    (hpersistence : VotingSourceEpochChainPersistence cfg store)
    {seed tip : Root}
    (hseed : seed ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (htipSeed : is_ancestor store (get_node_for_root tip)
      (get_node_for_root seed) = true)
    (havailable : SourceAvailableAtTip cfg store seed) :
    SourceAvailableAtTip cfg store tip := by
  rcases havailable with hvisible | hrecent
  · exact Or.inl (SourceVisibleAtTip.of_descendant cfg hpersistence
      hseed htip htipSeed hvisible)
  · right
    have hsourceMono :=
      hpersistence.source_epoch_le_of_descends hseed htip htipSeed
    exact hrecent.trans (Nat.add_le_add_right hsourceMono 2)

/-- At a visible tip, a realized voting source is exactly the endpoint's
realized justified checkpoint; a not-yet-realized source is recent.  The
checkpoint equality (not merely epoch equality) follows from the two concrete
certificates and accountable same-epoch uniqueness. -/
theorem EndpointSelectorRealization.votingSource_eq_justified_or_recent
    {E : Execution Root} {anchor : Checkpoint Root} {store : Store Root}
    (hselector : EndpointSelectorRealization cfg E anchor store)
    (hacc : CertificateAccountability cfg E anchor)
    (hendpoint : EndpointFFGPipeline cfg E anchor store)
    {tip : Root} (htip : tip ∈ store.block_roots)
    (htipSlot : (store.blocks tip).slot ≤ get_current_slot cfg store)
    (hvisible : SourceVisibleAtTip cfg store tip) :
    get_voting_source cfg store tip = store.justified_checkpoint ∨
      (get_voting_source cfg store tip).epoch + 2 ≥
        get_current_store_epoch cfg store := by
  by_cases hrealized : (get_voting_source cfg store tip).epoch <
      get_current_store_epoch cfg store
  · left
    have hle : (get_voting_source cfg store tip).epoch ≤
        store.justified_checkpoint.epoch :=
      hselector.source_realized_le_justified tip htip htipSlot hrealized
    have hepoch : (get_voting_source cfg store tip).epoch =
        store.justified_checkpoint.epoch :=
      Nat.le_antisymm hle hvisible.justified_epoch_le_source
    obtain ⟨hsource⟩ := hselector.source_certificate tip htip htipSlot
    obtain ⟨hjustified⟩ := hendpoint.justified_certificate
    have hroot : (get_voting_source cfg store tip).root =
        store.justified_checkpoint.root :=
      hacc.justified_unique hsource hjustified hepoch
    cases hsourceCheckpoint : get_voting_source cfg store tip with
    | mk sourceEpoch sourceRoot =>
      cases hjustifiedCheckpoint : store.justified_checkpoint with
      | mk justifiedEpoch justifiedRoot =>
        simp only [hsourceCheckpoint, hjustifiedCheckpoint] at hepoch hroot ⊢
        cases hepoch
        cases hroot
        rfl
  · right
    have hcurrentLeSource : get_current_store_epoch cfg store ≤
        (get_voting_source cfg store tip).epoch :=
      Nat.le_of_not_gt hrealized
    exact hcurrentLeSource.trans
      (Nat.le_add_right (get_voting_source cfg store tip).epoch 2)

/-- The exact executable `correct_justified` disjunction follows from the
stronger checkpoint-equality-or-recency theorem. -/
theorem EndpointSelectorRealization.tipSourceFresh
    {E : Execution Root} {anchor : Checkpoint Root} {store : Store Root}
    (hselector : EndpointSelectorRealization cfg E anchor store)
    (hacc : CertificateAccountability cfg E anchor)
    (hendpoint : EndpointFFGPipeline cfg E anchor store)
    {tip : Root} (htip : tip ∈ store.block_roots)
    (htipSlot : (store.blocks tip).slot ≤ get_current_slot cfg store)
    (hvisible : SourceVisibleAtTip cfg store tip) :
    TipSourceFresh cfg store tip := by
  rcases hselector.votingSource_eq_justified_or_recent cfg hacc hendpoint
      htip htipSlot hvisible with heq | hrecent
  · exact Or.inr (Or.inl (congrArg Checkpoint.epoch heq))
  · exact Or.inr (Or.inr hrecent)

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
    simp only [is_ancestor, get_node_for_root, decide_eq_true_eq] at htipData
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
    is_ancestor_trans hwf hchildWalk htipData.2.1
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

/-- An available known seed has an available childless descendant.  This is
the early-endpoint variant of `exists_visible_store_leaf_extension`: the
transported witness may remain in the recency branch rather than asserting
that the endpoint checkpoint was already visible. -/
theorem exists_available_store_leaf_extension {store : Store Root}
    (hwf : ParentSlotLt store)
    (hpersistence : VotingSourceEpochChainPersistence cfg store)
    {seed : Root} (hseed : seed ∈ store.block_roots)
    (havailable : SourceAvailableAtTip cfg store seed) :
    ∃ tip : Root,
      tip ∈ store.block_roots ∧
      WalkKnown store (store.blocks seed).slot tip ∧
      is_ancestor store (get_node_for_root tip)
        (get_node_for_root seed) = true ∧
      store.block_roots.filter
        (fun x => (store.blocks x).parent_root = tip) = [] ∧
      SourceAvailableAtTip cfg store tip := by
  obtain ⟨tip, htip, htipWalk, htipSeed, hleaf⟩ :=
    exists_store_leaf_extension hwf hseed
  have htipAvailable : SourceAvailableAtTip cfg store tip :=
    SourceAvailableAtTip.of_descendant cfg hpersistence
      hseed htip htipSeed havailable
  exact ⟨tip, htip, htipWalk, htipSeed, hleaf, htipAvailable⟩

/-! ## Placement assembly -/

/-- Assemble the non-circular placement object from an explicitly visible
raw leaf.  Leaf existence is mechanical (`exists_store_leaf_extension`);
`SourceVisibleAtTip` remains the separately named rule/state-transition
availability boundary.

`hcJustified` says the selected child descends from the endpoint justified
root.  The opposite direction is the surrounding proof's direct-coverage
branch and does not need a filter witness. -/
theorem retainedFilterTipPlacement_of_visible_leaf
    {E : Execution Root} {anchor : Checkpoint Root} {store : Store Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hendpoint : EndpointFFGPipeline cfg E anchor store)
    (hselector : EndpointSelectorRealization cfg E anchor store)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {c tip : Root} (hc : c ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (htipC : is_ancestor store (get_node_for_root tip)
      (get_node_for_root c) = true)
    (hcJustified : is_ancestor store (get_node_for_root c)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hleaf : store.block_roots.filter
      (fun x => (store.blocks x).parent_root = tip) = [])
    (htipSlot : (store.blocks tip).slot ≤ get_current_slot cfg store)
    (hvisible : SourceVisibleAtTip cfg store tip) :
    ∃ hplace : RetainedFilterTipPlacement cfg store c,
      hplace.tip = tip ∧ TipSourceFresh cfg store hplace.tip := by
  have hjustKnown : store.justified_checkpoint.root ∈ store.block_roots :=
    hendpoint.justified_root_known
  have htipJustified : is_ancestor store (get_node_for_root tip)
      (get_node_for_root store.justified_checkpoint.root) = true :=
    is_ancestor_trans hwf
      (hwalkK store.justified_checkpoint.root hjustKnown tip htip)
      (hwalkK store.justified_checkpoint.root hjustKnown c hc)
      htipC hcJustified
  let hplace : RetainedFilterTipPlacement cfg store c :=
    { tip := tip
      tip_known := htip
      tip_descends_justified := htipJustified
      tip_descends_child := htipC
      tip_is_leaf := hleaf
      finalized_walk_known := hfinalized.finalizedWalkKnown cfg hwalkK htip }
  have hfresh : TipSourceFresh cfg store tip :=
    hselector.tipSourceFresh cfg hacc hendpoint htip htipSlot hvisible
  exact ⟨hplace, rfl, hfresh⟩

/-- Starting from a visible known seed above `c`, mechanically select a raw
leaf, transport visibility to it, and assemble placement.  Unlike
`retainedFilterTipPlacement_of_visible_leaf`, this theorem does not assume a
visible leaf.  `hknownNonfuture` is the ordinary store-domain fact needed to
apply the executable selector to whichever finite leaf is chosen. -/
theorem retainedFilterTipPlacement_of_visible_seed
    {E : Execution Root} {anchor : Checkpoint Root} {store : Store Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hendpoint : EndpointFFGPipeline cfg E anchor store)
    (hselector : EndpointSelectorRealization cfg E anchor store)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hpersistence : VotingSourceEpochChainPersistence cfg store)
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hknownNonfuture : ∀ r ∈ store.block_roots,
      (store.blocks r).slot ≤ get_current_slot cfg store)
    {c seed : Root} (hc : c ∈ store.block_roots)
    (hseed : seed ∈ store.block_roots)
    (hseedC : is_ancestor store (get_node_for_root seed)
      (get_node_for_root c) = true)
    (hcJustified : is_ancestor store (get_node_for_root c)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hvisible : SourceVisibleAtTip cfg store seed) :
    ∃ hplace : RetainedFilterTipPlacement cfg store c,
      SourceVisibleAtTip cfg store hplace.tip ∧
      TipSourceFresh cfg store hplace.tip := by
  obtain ⟨tip, htip, _htipWalk, htipSeed, hleaf, htipVisible⟩ :=
    exists_visible_store_leaf_extension cfg hwf hpersistence hseed hvisible
  have htipC : is_ancestor store (get_node_for_root tip)
      (get_node_for_root c) = true :=
    is_ancestor_trans hwf
      (hwalkK c hc tip htip)
      (hwalkK c hc seed hseed)
      htipSeed hseedC
  obtain ⟨hplace, hplaceTip, hfresh⟩ :=
    retainedFilterTipPlacement_of_visible_leaf cfg hacc hendpoint hselector
      hfinalized hwf hwalkK hc htip htipC hcJustified hleaf
      (hknownNonfuture tip htip) htipVisible
  refine ⟨hplace, ?_, hfresh⟩
  simpa only [hplaceTip] using htipVisible

/-- Early-endpoint placement from an available seed.  The leaf and its
availability are selected mechanically.  In the visibility branch freshness
comes from the endpoint selector/accountability argument; in the recency
branch it is immediate from the executable disjunction. -/
theorem retainedFilterTipPlacement_of_available_seed
    {E : Execution Root} {anchor : Checkpoint Root} {store : Store Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hendpoint : EndpointFFGPipeline cfg E anchor store)
    (hselector : EndpointSelectorRealization cfg E anchor store)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hpersistence : VotingSourceEpochChainPersistence cfg store)
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hknownNonfuture : ∀ r ∈ store.block_roots,
      (store.blocks r).slot ≤ get_current_slot cfg store)
    {c seed : Root} (hc : c ∈ store.block_roots)
    (hseed : seed ∈ store.block_roots)
    (hseedC : is_ancestor store (get_node_for_root seed)
      (get_node_for_root c) = true)
    (hcJustified : is_ancestor store (get_node_for_root c)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (havailable : SourceAvailableAtTip cfg store seed) :
    ∃ hplace : RetainedFilterTipPlacement cfg store c,
      TipSourceFresh cfg store hplace.tip := by
  obtain ⟨tip, htip, _htipWalk, htipSeed, hleaf, htipAvailable⟩ :=
    exists_available_store_leaf_extension cfg hwf hpersistence
      hseed havailable
  have htipC : is_ancestor store (get_node_for_root tip)
      (get_node_for_root c) = true :=
    is_ancestor_trans hwf
      (hwalkK c hc tip htip)
      (hwalkK c hc seed hseed)
      htipSeed hseedC
  have hjustKnown : store.justified_checkpoint.root ∈ store.block_roots :=
    hendpoint.justified_root_known
  have htipJustified : is_ancestor store (get_node_for_root tip)
      (get_node_for_root store.justified_checkpoint.root) = true :=
    is_ancestor_trans hwf
      (hwalkK store.justified_checkpoint.root hjustKnown tip htip)
      (hwalkK store.justified_checkpoint.root hjustKnown c hc)
      htipC hcJustified
  let hplace : RetainedFilterTipPlacement cfg store c :=
    { tip := tip
      tip_known := htip
      tip_descends_justified := htipJustified
      tip_descends_child := htipC
      tip_is_leaf := hleaf
      finalized_walk_known := hfinalized.finalizedWalkKnown cfg hwalkK htip }
  have hfresh : TipSourceFresh cfg store tip := by
    rcases htipAvailable with htipVisible | htipRecent
    · exact hselector.tipSourceFresh cfg hacc hendpoint htip
        (hknownNonfuture tip htip) htipVisible
    · exact Or.inr (Or.inr htipRecent)
  exact ⟨hplace, hfresh⟩

end FastConfirmation.Spec

end
