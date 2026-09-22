module
public import FastConfirmation.Spec.Proof.CausalQueryTraceAdapter
public import FastConfirmation.Spec.Proof.SelectedMarginConstruction

@[expose] public section

/-!
# Strict-prefix ground-vote accounting at an accepted query prefix

`PrefixWindowRecordedEpochMax` is sufficient for the query-store base strip,
but need not hold at a source-permitted strict prefix: a visible
latest-message cell can precede a newer, already-cast honest vote whose wire
event is still queued.  Epoch domination is stronger than the accounting
argument actually needs.

This module states the exact weaker accounting condition.  A visible honest supporter
must be represented by the newest ground vote through the cutoff in the
supporting class.  A visible honest parent supporter may have moved forward,
so its newest ground vote may lie in either the supporting or ancestor class.
The latter relaxation is important: requiring the parent cell itself to replay
would merely reintroduce the false boundary premise.

The resulting base strip has no `SafeFrom`, canonicality, selected-result, or
future-head premise.  It is therefore an actor-side accounting lemma, not a
cross-node exact-current safety criterion.  In particular, the finite
strict-prefix execution in `AcceptedStrictPrefixExtraQueryCounterexample`
can satisfy this replay footprint while another honest endpoint has processed
a conflicting block but not yet the same-second synchronized vote.  Closing
an all-runtime-prefix safety theorem would require an additional multi-node
event-prefix coupling; this local replay condition alone does not imply it.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The exact ground-vote footprint consumed by the stale-cell-aware weak
base.  Both fields are classifications of concrete validator votes through
`es`; neither is a safety conclusion.

The parent field deliberately permits `StoreSclass`: an honest validator
whose visible cell is stuck at the parent may already have cast a newer vote
for `b`.  The confirmation supporters and parent supporters are disjoint in
the visible query store, so this forward movement can be charged without
double counting. -/
structure PrefixGroundVoteAccountingReplay
    (queryStore : Store Root) (bs : BeaconState Root)
    (b : Root) (lo es : Slot) : Prop where
  supporter_replay :
    ∀ i ∈ AttSupporters cfg queryStore (get_node_for_root b) bs,
      i ∈ E.honest → i ∈ E.StoreSclass queryStore b lo es
  parent_replay :
    ParentStuck cfg E queryStore bs b ⊆
      E.StoreSclass queryStore b lo es ∪
        E.StoreAclass queryStore b lo es

/-! ## Set geometry at the visible prefix -/

omit [Inhabited Root] in
/-- Honest visible supporters of `b` and honest visible supporters pinned to
`b`'s parent are disjoint.  This is a query-store fact; no ground-vote replay
or trajectory conclusion is used. -/
theorem queryHonestSupporters_disjoint_parentStuck
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    (hknown : b ∈ queryStore.block_roots)
    (hparentKnown : (queryStore.blocks b).parent_root ∈ queryStore.block_roots)
    (hparentSlots : ParentSlotLt queryStore) :
    Disjoint
      ((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).toFinset
      (ParentStuck cfg E queryStore bs b) := by
  rw [Finset.disjoint_left]
  intro i hiSupport hiParent
  simp only [List.mem_toFinset, List.mem_filter] at hiSupport
  obtain ⟨lm, hlm, _hne, hsupports⟩ :=
    mem_AttSupporters cfg hiSupport.1
  simp only [ParentStuck, Finset.mem_filter] at hiParent
  have hparent := hiParent.1
  simp only [ParentSupport, Finset.mem_filter] at hparent
  obtain ⟨_hactive, hcell⟩ := hparent
  rw [hlm] at hcell
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hcell
  have hlmParent : lm.root = (queryStore.blocks b).parent_root := hcell.1
  have hparentNotSupport :
      is_ancestor queryStore
        (get_node_for_root (queryStore.blocks b).parent_root)
        (get_node_for_root b) ≠ true := by
    intro htrue
    have hEq :
        (get_ancestor queryStore
            (get_node_for_root (queryStore.blocks b).parent_root)
            (queryStore.blocks b).slot).root = b := by
      simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using htrue
    have hstop :
        get_ancestor queryStore
            (get_node_for_root (queryStore.blocks b).parent_root)
            (queryStore.blocks b).slot =
          get_node_for_root (queryStore.blocks b).parent_root :=
      get_ancestor_stop (le_of_lt
        (hparentSlots b hknown hparentKnown))
    rw [hstop] at hEq
    have hroot : (queryStore.blocks b).parent_root = b := hEq
    have hlt := hparentSlots b hknown hparentKnown
    rw [hroot] at hlt
    exact (lt_irrefl _ hlt).elim
  simp only [get_node_for_root, is_ancestor_supported_pending, hlmParent] at hsupports
  exact hparentNotSupport hsupports

omit [Inhabited Root] in
/-- The two ground honest classes used by the relaxed parent charge are
disjoint by construction. -/
theorem storeSclass_disjoint_storeAclass
    (queryStore : Store Root) (b : Root) (lo es : Slot) :
    Disjoint (E.StoreSclass queryStore b lo es)
      (E.StoreAclass queryStore b lo es) := by
  rw [Finset.disjoint_left]
  intro i hiS hiA
  simp only [StoreSclass, Finset.mem_filter] at hiS
  simp only [StoreAclass, Finset.mem_filter] at hiA
  exact hiA.2.1 hiS.2

/-! ## Stale-cell-aware accounting -/

/-- The visible honest-support score plus the honest parent discount source
fits in the ground supporting/ancestor classes.  A parent supporter that cast
a newer supporting vote is allowed in `S`; disjointness in the visible store
prevents it from being charged once as support and again as discount. -/
theorem honestSupporters_add_parentStuck_le_storeSA
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hreplay : E.PrefixGroundVoteAccountingReplay cfg queryStore bs b lo es) :
    (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + E.weight (ParentStuck cfg E queryStore bs b) ≤
        E.StoreSval queryStore b lo es +
          E.StoreAval queryStore b lo es := by
  let supporters : Finset ValidatorIndex :=
    ((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
      (fun i => i ∈ E.honest)).toFinset
  have hscore :
      (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
            (fun i => i ∈ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum =
        E.weight supporters := by
    simpa only [supporters] using
      (honest_score_eq_weight cfg E hev.balance_validators)
  rw [hscore]
  have hvisibleDisjoint :
      Disjoint supporters (ParentStuck cfg E queryStore bs b) := by
    simpa only [supporters] using
      E.queryHonestSupporters_disjoint_parentStuck cfg
        hev.block_known hev.parent_known hev.parent_slot_lt
  rw [← E.weight_union_disjoint hvisibleDisjoint]
  have hunion :
      supporters ∪ ParentStuck cfg E queryStore bs b ⊆
        E.StoreSclass queryStore b lo es ∪
          E.StoreAclass queryStore b lo es := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiSupport | hiParent
    · apply Finset.mem_union_left
      have hi' :
          i ∈ (AttSupporters cfg queryStore (get_node_for_root b) bs).filter
            (fun i => i ∈ E.honest) := by
        simpa only [supporters, List.mem_toFinset] using hiSupport
      exact hreplay.supporter_replay i (List.mem_filter.mp hi').1
        (of_decide_eq_true (List.mem_filter.mp hi').2)
    · exact hreplay.parent_replay hiParent
  refine (E.weight_mono hunion).trans_eq ?_
  rw [E.weight_union_disjoint
    (E.storeSclass_disjoint_storeAclass queryStore b lo es)]
  rfl

private theorem stale_queryStore_weak_base_arith
    {Hsup discount maximum boost s a x B J : ℕ}
    (hsm : maximum + boost + 1 ≤ 2 * Hsup + discount)
    (hcombined : Hsup + discount ≤ s + a)
    (hHsup : Hsup ≤ s)
    (hMS : J + B ≤ maximum) (hpart : J = s + a + x) :
    x + B + boost + 1 ≤ s := by
  omega

/-- Confirmation at an arbitrary causal query store yields the weak selected
margin from the exact ground-vote replay footprint.  Unlike the existing
constructor, this theorem does not require recorded-epoch domination and
therefore admits genuinely stale latest-message cells. -/
theorem base_strip_of_confirmed_in_store_stale_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hreplay : E.PrefixGroundVoteAccountingReplay cfg queryStore bs b lo es) :
    E.StoreXval queryStore b lo es + E.Bval lo es
        + compute_proposer_score cfg bs + 1 ≤
      E.StoreSval queryStore b lo es := by
  have hcombined0 :=
    honestSupporters_add_parentStuck_le_storeSA (cfg := cfg) (ext := ext)
      (E := E) hev hreplay
  have hcombined :
      (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
            (fun i => i ∈ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum
        + get_support_discount cfg ext queryStore bs b ≤
          E.StoreSval queryStore b lo es +
            E.StoreAval queryStore b lo es := by
    exact (Nat.add_le_add_left hev.support_discount_le_parent_stuck _).trans
      hcombined0
  have hHsup :
      (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
            (fun i => i ∈ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
        E.StoreSval queryStore b lo es := by
    rw [honest_score_eq_weight cfg E hev.balance_validators, StoreSval]
    apply E.weight_mono
    intro i hi
    rw [List.mem_toFinset, List.mem_filter] at hi
    exact hreplay.supporter_replay i hi.1 (of_decide_eq_true hi.2)
  have hsm := honest_support_majority_of_byz_le cfg ext hev.confirmation
    hev.byzantine_support_le_adversarial
  rw [hev.total_active] at hsm
  rw [← hev.lo_eq, ← hev.cutoff_eq] at hsm
  have hsplit : E.weight (E.span_committee lo es) =
      E.Jspec lo es + E.Bval lo es := by
    rw [Execution.Jspec, Execution.Bval, Execution.Bwin]
    exact E.weight_split_honest _
  have hMS := hA.byzantine_bound.estimate_sound lo es
    hev.lo_horizon hev.es_horizon
  rw [hsplit] at hMS
  have hpart := E.store_weight_partition queryStore b lo es
  exact stale_queryStore_weak_base_arith hsm hcombined hHsup hMS hpart

/-! ## Compatibility with the completed-boundary proof -/

/-- The old recorded-epoch premise implies the new replay footprint.  This
shows that the stale-cell route strictly generalizes the existing constructor
rather than changing its meaning on completed stores. -/
theorem prefixGroundVoteAccountingReplay_of_recordedEpochMax
    (hA : SelectedMarginAssumptions cfg ext E)
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hdom : PrefixWindowRecordedEpochMax cfg E queryStore lo es) :
    E.PrefixGroundVoteAccountingReplay cfg queryStore bs b lo es := by
  refine ⟨?_, ?_⟩
  · intro i hiSupport hiHonest
    exact E.recorded_supporter_mem_storeSclass cfg ext hA hev hdom
      hiSupport hiHonest
  · intro i hiParent
    exact Finset.mem_union_right _
      (E.ParentStuck_subset_storeAclass cfg ext hA hev hdom hiParent)

end Execution

/-! ## Exact global-prefix facade -/

namespace AllowedFCRCalls

variable (E : Execution Root)

/-- The action-facing stale-cell base strip.  Global legality and exact
scheduled-prefix simulation construct the structural store evidence; the
only additional query-specific LMD premise is the two-field ground replay
above. -/
theorem GlobalScheduledQueryPrefixCompatibility.baseStrip_of_staleGroundReplay
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : GlobalScheduledQueryPrefixCompatibility cfg ext E runtime actions
      position before after querySecond scheduledPrefix)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (actor : ValidatorIndex) (kind : QueryKind)
    (haction : actions.getD position (.honestVoteCast 0 0 0) =
      .nodeAction actor (.query kind))
    (hhonest : scheduledPrefix.node ∈ E.honest)
    {bs : BeaconState Root} {b : Root} {lo es : Slot}
    (hres : E.QueryStoreBaseStripTraceResidual cfg ext
      (before.nodeState actor).fcrStore.store bs b lo es querySecond)
    (hreplay : E.PrefixGroundVoteAccountingReplay cfg
      (before.nodeState actor).fcrStore.store bs b lo es) :
    E.StoreXval (before.nodeState actor).fcrStore.store b lo es +
        E.Bval lo es + compute_proposer_score cfg bs + 1 ≤
      E.StoreSval (before.nodeState actor).fcrStore.store b lo es := by
  apply E.base_strip_of_confirmed_in_store_stale_minimal cfg ext hA
  · exact h.queryStoreBaseStripEvidence cfg ext hT actor kind haction hhonest hres
  · exact hreplay


end AllowedFCRCalls
end FastConfirmation.Spec

end
