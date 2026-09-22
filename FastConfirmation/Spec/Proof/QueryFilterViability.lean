module
public import FastConfirmation.Spec.Proof.HeadReroot
public import FastConfirmation.Spec.Proof.EngineStore

@[expose] public section

/-!
# Query-local inversion of the executable FFG filter

The selected-call proof knows that a strict result lies below the query's
`get_head`.  This file records exactly what the executable query filter adds
to that geometry, without any endpoint, future-finality, or selected-safety
premise.

Membership in a `filter_block_tree_aux` output can be inverted to a concrete
raw leaf below the member.  At that leaf, both executable viability checks
hold, including the exact finalized checkpoint-block equality.  Applying the
inversion to the query head gives the call-site split used by the endpoint
proof:

* if the head stayed at the justified root, the selected result is directly
  covered by that root; or
* the head is a filtered member and therefore has a viable raw leaf below it,
  hence below the selected result.

The theorem deliberately says nothing about transporting this leaf or its
finalized checkpoint to another store.  In particular, ordered finalized
epochs alone do not preserve the exact checkpoint-block equality.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-- A raw store leaf below `r` which passes the two exact executable
`filter_block_tree` leaf checks. -/
def FilterViableLeafBelow (store : Store Root) (r : Root) : Prop :=
  ∃ tip : Root,
    tip ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root tip) (get_node_for_root r) = true ∧
      store.block_roots.filter
          (fun x => (store.blocks x).parent_root = tip) = [] ∧
      (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
        (get_voting_source cfg store tip).epoch =
            store.justified_checkpoint.epoch ∨
        (get_voting_source cfg store tip).epoch + 2 ≥
          get_current_store_epoch cfg store) ∧
      (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
        store.finalized_checkpoint.root =
          get_checkpoint_block cfg store tip
            store.finalized_checkpoint.epoch)

omit [Inhabited Root] in
/-- Splice a known walk to `middle` with a known walk from the node reached at
`middle` down to `lower`.  This is the domain counterpart of
`get_ancestor_comp`; unlike a blanket boundary-walk premise, it exposes only
the two actual path segments used below. -/
theorem WalkKnown.splice_at_ancestor
    {store : Store Root} (hwf : ParentSlotLt store)
    {lower middle : Slot} (hlowerMiddle : lower ≤ middle)
    {tip ancestor : Root}
    (hprefix : WalkKnown store middle tip)
    (hlands : (get_ancestor store (get_node_for_root tip) middle).root =
      ancestor)
    (hsuffix : WalkKnown store lower ancestor) :
    WalkKnown store lower tip := by
  induction hprefix with
  | @stop tip htip htipSlot =>
      simp only [get_node_for_root] at hlands
      rw [get_ancestor_stop htipSlot] at hlands
      have htipAncestor : tip = ancestor := hlands
      subst ancestor
      exact hsuffix
  | @step tip htip hmiddleTip hparent ih =>
      simp only [get_node_for_root] at hlands
      rw [get_ancestor_step hwf htip hmiddleTip hparent] at hlands
      exact WalkKnown.step htip
        (lt_of_le_of_lt hlowerMiddle hmiddleTip)
        (ih hlands)

omit [Inhabited Root] in
/-- Exact-stable finalized checkpoints transport from a query filter witness
to a later endpoint descendant.

The query witness first puts the finalized checkpoint on a raw viable tip.
The boundary-age premise moves that equation up to `result`; block agreement
then moves the checkpoint computation across stores; finally the endpoint
descendant geometry moves it down to `endpointTip`.

`hboundaryResult` is essential.  A child first appearing exactly at a later
epoch boundary can change `get_checkpoint_block` even when the stored
finalized checkpoint itself is unchanged.  Thus exact checkpoint stability
and root ancestry alone do not imply this theorem. -/
theorem finalized_check_of_exactStable_viableLeaf
    {query endpoint : Store Root}
    (hwfQuery : ParentSlotLt query)
    (hwfEndpoint : ParentSlotLt endpoint)
    {result endpointTip : Root}
    (hresultQuery : result ∈ query.block_roots)
    (hviable : FilterViableLeafBelow cfg query result)
    (hstable : endpoint.finalized_checkpoint =
      query.finalized_checkpoint)
    (hblocksAgree : ∀ r ∈ query.block_roots,
      query.blocks r = endpoint.blocks r)
    (hboundaryResult : compute_start_slot_at_epoch cfg
      query.finalized_checkpoint.epoch ≤ (query.blocks result).slot)
    (hqueryWalkToResult : ∀ r ∈ query.block_roots,
      WalkKnown query (query.blocks result).slot r)
    (hqueryResultBoundaryWalk : WalkKnown query
      (compute_start_slot_at_epoch cfg
        query.finalized_checkpoint.epoch) result)
    (hendpointTipResult : is_ancestor endpoint
      (get_node_for_root endpointTip) (get_node_for_root result) = true)
    (hendpointBoundaryWalk : WalkKnown endpoint
      (compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch) endpointTip) :
    endpoint.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      endpoint.finalized_checkpoint.root =
        get_checkpoint_block cfg endpoint endpointTip
          endpoint.finalized_checkpoint.epoch := by
  obtain ⟨queryTip, hqueryTip, hqueryTipResult, _hleaf,
      _hjustified, hfinalized⟩ := hviable
  rcases hfinalized with hgenesis | hqueryTipFinalized
  · left
    simpa only [hstable] using hgenesis
  · right
    have hqueryTipLandsOnResult : (get_ancestor query
        (get_node_for_root queryTip) (query.blocks result).slot).root =
          result := by
      simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hqueryTipResult
    have hqueryTipBoundaryWalk : WalkKnown query
        (compute_start_slot_at_epoch cfg
          query.finalized_checkpoint.epoch) queryTip :=
      WalkKnown.splice_at_ancestor hwfQuery hboundaryResult
        (hqueryWalkToResult queryTip hqueryTip) hqueryTipLandsOnResult
        hqueryResultBoundaryWalk
    have hqueryTipResultCheckpoint :
        get_checkpoint_block cfg query queryTip
            query.finalized_checkpoint.epoch =
          get_checkpoint_block cfg query result
            query.finalized_checkpoint.epoch :=
      get_checkpoint_block_of_ancestor cfg hwfQuery hqueryTipResult
        hboundaryResult hqueryTipBoundaryWalk
    have hqueryResultFinalized : query.finalized_checkpoint.root =
        get_checkpoint_block cfg query result
          query.finalized_checkpoint.epoch :=
      hqueryTipFinalized.trans hqueryTipResultCheckpoint
    have hresultCheckpointTransport :
        get_checkpoint_block cfg query result
            query.finalized_checkpoint.epoch =
          get_checkpoint_block cfg endpoint result
            query.finalized_checkpoint.epoch := by
      simp only [get_checkpoint_block]
      rw [get_ancestor_congr hblocksAgree hresultQuery
        hqueryResultBoundaryWalk]
    have hstableRoot : endpoint.finalized_checkpoint.root =
        query.finalized_checkpoint.root :=
      congrArg Checkpoint.root hstable
    have hstableEpoch : endpoint.finalized_checkpoint.epoch =
        query.finalized_checkpoint.epoch :=
      congrArg Checkpoint.epoch hstable
    have hendpointResultFinalized : endpoint.finalized_checkpoint.root =
        get_checkpoint_block cfg endpoint result
          endpoint.finalized_checkpoint.epoch := by
      calc
        endpoint.finalized_checkpoint.root =
            query.finalized_checkpoint.root := hstableRoot
        _ = get_checkpoint_block cfg query result
            query.finalized_checkpoint.epoch := hqueryResultFinalized
        _ = get_checkpoint_block cfg endpoint result
            query.finalized_checkpoint.epoch := hresultCheckpointTransport
        _ = get_checkpoint_block cfg endpoint result
            endpoint.finalized_checkpoint.epoch := by rw [hstableEpoch]
    have hendpointBoundaryResult : compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch ≤
          (endpoint.blocks result).slot := by
      rw [hstableEpoch, ← hblocksAgree result hresultQuery]
      exact hboundaryResult
    exact finalized_check_of_ancestor cfg hwfEndpoint hendpointTipResult
      hendpointBoundaryResult hendpointBoundaryWalk hendpointResultFinalized

namespace Execution

variable (ext : Externals Root)

/-- Execution-store wrapper for the exact-stable transport.  The generic
block-agreement premise reduces to ordinary execution provenance once the
query block domain is contained in the endpoint domain. -/
theorem finalized_check_of_exactStable_viableLeaf_of_execution
    {E : Execution Root}
    (hwfExecution : WellFormedExecution E)
    {v w : ValidatorIndex} {q m : ℕ}
    (hsub : (E.store cfg ext v q).block_roots ⊆
      (E.store cfg ext w m).block_roots)
    (hwfQuery : ParentSlotLt (E.store cfg ext v q))
    (hwfEndpoint : ParentSlotLt (E.store cfg ext w m))
    {result endpointTip : Root}
    (hresultQuery : result ∈ (E.store cfg ext v q).block_roots)
    (hviable : FilterViableLeafBelow cfg (E.store cfg ext v q) result)
    (hstable : (E.store cfg ext w m).finalized_checkpoint =
      (E.store cfg ext v q).finalized_checkpoint)
    (hboundaryResult : compute_start_slot_at_epoch cfg
      (E.store cfg ext v q).finalized_checkpoint.epoch ≤
        ((E.store cfg ext v q).blocks result).slot)
    (hqueryWalkToResult : ∀ r ∈ (E.store cfg ext v q).block_roots,
      WalkKnown (E.store cfg ext v q)
        ((E.store cfg ext v q).blocks result).slot r)
    (hqueryResultBoundaryWalk : WalkKnown (E.store cfg ext v q)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext v q).finalized_checkpoint.epoch) result)
    (hendpointTipResult : is_ancestor (E.store cfg ext w m)
      (get_node_for_root endpointTip) (get_node_for_root result) = true)
    (hendpointBoundaryWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) endpointTip) :
    (E.store cfg ext w m).finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg (E.store cfg ext w m) endpointTip
          (E.store cfg ext w m).finalized_checkpoint.epoch := by
  apply finalized_check_of_exactStable_viableLeaf cfg hwfQuery hwfEndpoint
    hresultQuery hviable hstable
  · intro r hr
    exact hwfExecution.blocks_agree
      (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m) hr (hsub hr)
  · exact hboundaryResult
  · exact hqueryWalkToResult
  · exact hqueryResultBoundaryWalk
  · exact hendpointTipResult
  · exact hendpointBoundaryWalk

end Execution

omit [Inhabited Root] in
/-- Every emitted filter root has a viable raw leaf below it.  This is the
backwards counterpart of `confirmed_mem_filtered`: it follows solely by
inverting the recursive worker. -/
theorem filter_block_tree_aux_mem_viableLeafBelow
    {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    ∀ (fuel : ℕ) (base : Root), base ∈ store.block_roots →
      ∀ r ∈ (filter_block_tree_aux cfg store fuel base).2,
        FilterViableLeafBelow cfg store r := by
  intro fuel
  induction fuel with
  | zero =>
      intro base _ r hr
      simp only [filter_block_tree_aux, List.not_mem_nil] at hr
  | succ fuel ih =>
      intro base hbase r hr
      by_cases hchildren : store.block_roots.filter
          (fun x => (store.blocks x).parent_root = base) = []
      · rw [filter_block_tree_aux_leaf cfg store fuel base hchildren] at hr
        dsimp only at hr
        split_ifs at hr with hchecks
        · have hrbase : r = base := List.mem_singleton.mp hr
          subst r
          have hchecks' :
              (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
                (get_voting_source cfg store base).epoch =
                    store.justified_checkpoint.epoch ∨
                (get_voting_source cfg store base).epoch + 2 ≥
                  get_current_store_epoch cfg store) ∧
              (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
                store.finalized_checkpoint.root =
                  get_checkpoint_block cfg store base
                    store.finalized_checkpoint.epoch) := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hchecks
          exact ⟨base, hbase, is_ancestor_refl store _, hchildren,
            hchecks'.1, hchecks'.2⟩
        · exact absurd hr List.not_mem_nil
      · rw [filter_block_tree_aux_internal cfg store fuel base hchildren] at hr
        dsimp only at hr
        let children := store.block_roots.filter
          (fun x => (store.blocks x).parent_root = base)
        let results := children.map
          (fun child => filter_block_tree_aux cfg store fuel child)
        have fromFlatten :
            r ∈ (results.map Prod.snd).flatten →
              FilterViableLeafBelow cfg store r := by
          intro hflat
          obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hflat
          obtain ⟨result, hresult, rfl⟩ := List.mem_map.mp hl
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hresult
          have hchildKnown : child ∈ store.block_roots :=
            (List.mem_filter.mp hchild).1
          exact ih child hchildKnown r hrl
        split_ifs at hr with hany
        · have hr' : r ∈ (results.map Prod.snd).flatten ++ [base] := by
            simpa only [results, children] using hr
          rcases List.mem_append.mp hr' with hflat | hrbase
          · exact fromFlatten hflat
          · have hrEq : r = base := List.mem_singleton.mp hrbase
            subst r
            have hany' : results.any Prod.fst = true := by
              simpa only using hany
            obtain ⟨result, hresult, hresultTrue⟩ :=
              List.any_eq_true.mp hany'
            obtain ⟨child, hchild, hchildResult⟩ :=
              List.mem_map.mp hresult
            have hchildKnown : child ∈ store.block_roots :=
              (List.mem_filter.mp hchild).1
            have hchildTrue :
                (filter_block_tree_aux cfg store fuel child).1 = true := by
              rw [hchildResult]
              exact hresultTrue
            have hchildMem : child ∈
                (filter_block_tree_aux cfg store fuel child).2 := by
              cases fuel with
              | zero =>
                  have : False := by
                    simpa [filter_block_tree_aux] using hchildTrue
                  exact this.elim
              | succ childFuel =>
                  apply filter_block_tree_aux_true_mem cfg
                  apply Prod.ext
                  · exact hchildTrue
                  · rfl
            obtain ⟨tip, htip, htipChild, hleaf, hjustified,
                hfinalized⟩ := ih child hchildKnown child hchildMem
            have hchildBase : is_ancestor store
                (get_node_for_root child) (get_node_for_root base) = true :=
              is_ancestor_of_parent hwf hchildKnown hbase (by
                have hp := (List.mem_filter.mp hchild).2
                simpa using hp)
            have htipBase : is_ancestor store
                (get_node_for_root tip) (get_node_for_root base) = true :=
              is_ancestor_trans hwf (b := get_node_for_root child)
                (hwalkK base hbase tip htip)
                (hwalkK base hbase child hchildKnown)
                htipChild hchildBase
            exact ⟨tip, htip, htipBase, hleaf, hjustified, hfinalized⟩
        · apply fromFlatten
          simpa only [results, children] using hr

omit [Inhabited Root] in
/-- Wrapper-level inversion: every member of `get_filtered_block_tree` has a
raw viable descendant carrying the exact query-store finalized check. -/
theorem filtered_member_viableLeafBelow
    {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjustified : store.justified_checkpoint.root ∈ store.block_roots)
    {r : Root} (hr : r ∈ get_filtered_block_tree cfg store) :
    FilterViableLeafBelow cfg store r := by
  exact filter_block_tree_aux_mem_viableLeafBelow cfg hwf hwalkK
    (store.block_roots.length + 1) store.justified_checkpoint.root
      hjustified r hr

/-- Actual query-head split.  If `result` lies on the query head chain, then
either the query head is the justified root (direct coverage), or a concrete
raw viable leaf lies below `result` and passes the query store's exact
finalized checkpoint test.

`Execution.strictSelectedResult_below_head` supplies `hheadResult` at the
strict `find_latest_confirmed_descendant` call site. -/
theorem queryHead_direct_or_viableLeafBelow
    {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjustified : store.justified_checkpoint.root ∈ store.block_roots)
    {result : Root} (hresult : result ∈ store.block_roots)
    (hheadResult : is_ancestor store (get_head cfg store)
      (get_node_for_root result) = true) :
    is_ancestor store
        (get_node_for_root store.justified_checkpoint.root)
        (get_node_for_root result) = true ∨
      FilterViableLeafBelow cfg store result := by
  have hhead : (get_head cfg store).root ∈
        get_filtered_block_tree cfg store ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg
      (2 * (get_filtered_block_tree cfg store).length + 2)
      (ForkChoiceNode.mk store.justified_checkpoint.root .pending)
  rcases hhead with hheadFiltered | hheadJustified
  · right
    obtain ⟨tip, htip, htipHead, hleaf, hjustifiedCheck,
        hfinalizedCheck⟩ :=
      filtered_member_viableLeafBelow cfg hwf hwalkK hjustified
        hheadFiltered
    have hheadKnown : (get_head cfg store).root ∈ store.block_roots := by
      have houtput : (get_head cfg store).root ∈
          (filter_block_tree_aux cfg store
            (store.block_roots.length + 1)
            store.justified_checkpoint.root).2 := hheadFiltered
      rcases filter_block_tree_aux_output_mem cfg _ _ _ houtput with
        hknown | hbase
      · exact hknown
      · rw [hbase]
        exact hjustified
    have htipResult : is_ancestor store
        (get_node_for_root tip) (get_node_for_root result) = true :=
      is_ancestor_trans hwf (b := get_node_for_root (get_head cfg store).root)
        (hwalkK result hresult tip htip)
        (hwalkK result hresult (get_head cfg store).root hheadKnown)
        htipHead ((is_ancestor_node_root store (get_head cfg store) result).symm.trans
          hheadResult)
    exact ⟨tip, htip, htipResult, hleaf, hjustifiedCheck,
      hfinalizedCheck⟩
  · left
    change is_ancestor store
      (ForkChoiceNode.mk store.justified_checkpoint.root .pending)
      (get_node_for_root result) = true
    rw [is_ancestor_node_root] at hheadResult
    rwa [hheadJustified] at hheadResult

end FastConfirmation.Spec

end
