import FastConfirmation.Spec.Proof.CoveredMargin
import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
import FastConfirmation.Spec.Proof.SelectedTraceFilterPipeline
import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
import FastConfirmation.Spec.Proof.SelectedCommitteeSupport
import FastConfirmation.Spec.Proof.SelectedMarginConstruction
import FastConfirmation.Spec.Proof.EndpointLedgerMinimal
import FastConfirmation.Spec.Proof.FutureSiblingScore

/-!
# Complete construction of coverage-aware selected margins

This module assembles the concrete obligations for every strict edge retained
by an arbitrary permitted `find_latest_confirmed_descendant` call.

The only semantic boundaries left explicit are the ones the executable model
does not define internally:

* post-anchor honest target-walk adequacy, needed to interpret delivered votes;
* the exact retained-edge FFG/filter pipeline; and
* the helper support provisos stated by the pinned specification.

The crossing edge uses an exhaustive timing split.  At an endpoint in the
query slot, its completed-vote cutoff equals the query cutoff, so the ordinary
full-`Bval` confirmation strip transports directly.  At a strictly later
endpoint, attester-slashing relay excludes query-known prefix equivocators and
supplies the subtractive crossing sibling bound.  No same-slot visibility
assumption is introduced.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The filter-membership input consumed by the arithmetic/ledger half of the
selected-margin construction.  It is deliberately parameterized by the
earlier-slot induction hypothesis: causal endpoint-justification compatibility
cannot be proved before that hypothesis is in scope. -/
def SelectedStrictEdgeFilterSupplyAt
    (glc r₀ : Root) (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop :=
  ∀ {a c : Root} {w : ValidatorIndex} {m : ℕ}
      {lo es sigma querySlot : Slot},
    w ∈ E.honest →
    E.WithinHorizon cfg m →
    StrictSelectedEdgeGeometry cfg ext E glc r₀ a c
      v q query w m lo es sigma querySlot →
    c ≠ r₀ →
    c ∈ (E.store cfg ext w m).block_roots →
    ((E.store cfg ext w m).blocks c).parent_root = a →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true →
    (∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots) →
    (∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true) →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true →
    ForkChoiceNode.mk c ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a)

/-- Every strict selected edge is either already covered by the endpoint's
realized justified root or has the exact margin record consumed by the
coverage-aware chain fold. -/
theorem selectedCoveredMarginSupplyAt_of_filterSupply_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (glc : Root)
    (hresult : find_latest_confirmed_descendant cfg ext query r₀ = glc)
    (hstrict : glc ≠ r₀)
    (hfilter : E.SelectedStrictEdgeFilterSupplyAt cfg ext
      glc r₀ v q query) :
    E.SelectedCoveredMarginSupplyAt cfg ext glc r₀ v q query := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hr₀Q : r₀ ∈ (E.store cfg ext v q).block_roots := by
    simpa only [hquery] using hr₀
  rcases E.find_latest_confirmed_descendant_selected_minimal cfg ext hA
      v hv q hqH query hquery r₀ hr₀ with
    hsame | ⟨hglcConf₀, hglcQ₀, hglcParentQ₀⟩
  · exact False.elim (hstrict (hresult.symm.trans hsame))
  have hglcConf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true := by
    rw [hresult] at hglcConf₀
    exact hglcConf₀
  have hglcQ : glc ∈ (E.store cfg ext v q).block_roots := by
    rw [hresult] at hglcQ₀
    simpa only [hquery] using hglcQ₀
  have hglcParentQ : ((E.store cfg ext v q).blocks glc).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    rw [hresult] at hglcParentQ₀
    simpa only [hquery] using hglcParentQ₀
  obtain ⟨_hstartLeQ, _hstartH, hslotStart, _hstartGate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  have hcur₀ : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgenEq,
      get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
    rw [← ht, hanchorSlot]
  intro w hw m hslotQM hmH hIH a c haM hcM hparentM hglcC_M hcR₀_M hcne
  by_cases hcovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) = true
  · exact Or.inl hcovered
  right
  obtain ⟨lo, es, sigma, querySlot, hgeom⟩ :=
    E.strictSelectedEdgeGeometry_of_query_minimal cfg ext hA
      v hv q hqH query hquery r₀ hr₀ glc hresult hstrict
      w hw m hslotQM hmH a c haM hcM hparentM hglcC_M hcR₀_M hcne
  have hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hm' hm'H
    have hslotQM' : E.slot_at cfg q ≤ E.slot_at cfg m' := by
      rw [← hslotStart]
      exact E.slot_at_mono cfg hm'
    exact E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hquery glc hqH hglcQ hglcParentQ hglcConf
      w' hw' m' hslotQM' hm'H
  have hchild := hfilter hw hmH hgeom hcne hcM hparentM hglcC_M
    hglcKnown hIH hcovered
  have haQ : a ∈ (E.store cfg ext v q).block_roots := by
    rw [← hgeom.parent_eq]
    exact hgeom.parent_known
  have hagreeA : (E.store cfg ext v q).blocks a =
      (E.store cfg ext w m).blocks a :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q) (E.blockProvenance cfg ext w m)
      haQ haM
  have hloEnd : lo = ((E.store cfg ext w m).blocks a).slot + 1 := by
    calc
      lo = ((E.store cfg ext v q).blocks
          ((E.store cfg ext v q).blocks c).parent_root).slot + 1 := hgeom.lo_eq
      _ = ((E.store cfg ext v q).blocks a).slot + 1 := by rw [hgeom.parent_eq]
      _ = ((E.store cfg ext w m).blocks a).slot + 1 := by rw [hagreeA]
  have hanchorA : ablk.message.slot ≤
      ((E.store cfg ext v q).blocks a).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorParent v q a haQ
  have hlo₀ : E.slot_at cfg 0 ≤ lo := by
    rw [hcur₀, hgeom.lo_eq, hgeom.parent_eq]
    exact hanchorA.trans (Nat.le_succ _)
  have hloMid : lo ≤ ((E.store cfg ext v q).blocks c).slot := by
    rw [hgeom.lo_eq]
    exact Nat.succ_le_of_lt hgeom.parent_slot_lt
  have hcutoffQ : es =
      get_current_slot cfg (E.store cfg ext v q) - 1 := by
    calc
      es = get_current_slot cfg query.store - 1 := hgeom.cutoff_eq
      _ = get_current_slot cfg (E.store cfg ext v q) - 1 := by rw [hquery]
  have hquerySlotQ : querySlot =
      get_current_slot cfg (E.store cfg ext v q) := by
    calc
      querySlot = get_current_slot cfg query.store := hgeom.query_slot_eq
      _ = get_current_slot cfg (E.store cfg ext v q) := by rw [hquery]
  have hsigmaEnd : sigma =
      get_current_slot cfg (E.store cfg ext w m) - 1 := by
    calc
      sigma = E.slot_at cfg m - 1 := hgeom.sigma_eq
      _ = get_current_slot cfg (E.store cfg ext w m) - 1 := by
        rw [E.store_current_slot cfg ext w m]
  have hesLtQ : es < E.slot_at cfg q := by
    rw [hgeom.confirming_cutoff]
    exact Nat.lt_succ_self es
  have hmaxQuery : E.WindowRecordedEpochMax cfg ext v q lo es :=
    E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
      hv hqH hlo₀ hcutoffQ hesLtQ
  obtain ⟨hSt, hAt⟩ :=
    E.confirmed_honest_class_transports_of_cutoff_minimal cfg ext hA
      v hv q query hquery c hqH hgeom.block_known hgeom.parent_known
      hgeom.confirmation w hw m hmH
      (hslotQM.trans (E.slot_at_mono cfg (Nat.le_succ m)))
      lo es hlo₀ hgeom.cutoff_eq
  have hledger : E.EndpointLedgerFields cfg ext w m a c lo sigma :=
    E.endpointLedgerFields_from_execution_minimal cfg ext hA hwalkDomain
      hw hmH hsigmaEnd haM hcM hparentM (le_of_eq hloEnd) hlo₀
  have hbase := E.base_strip_of_confirmed_at_minimal cfg ext hA hv hqH
    hquery hgeom.block_known hgeom.parent_known hgeom.confirmation
    lo es hgeom.lo_eq hcutoffQ hmaxQuery hw hmH
  by_cases heqCutoff : sigma = es
  · have hledgerEs : E.EndpointLedgerFields cfg ext w m a c lo es := by
      simpa only [heqCutoff] using hledger
    exact SelectedEdgeMarginInputsAt.directWindow lo es
      { support_transport := hSt
        ancestor_transport := hAt
        base_strip := hbase
        child_filtered := hchild
        selected_score := hledgerEs.selected_score
        sibling_score := hledgerEs.sibling_score }
  have hesLtSigma : es < sigma :=
    lt_of_le_of_ne hgeom.cutoff_le_sigma (Ne.symm heqCutoff)
  have hrelaySlot : E.slot_at cfg q + 1 ≤ E.slot_at cfg m := by
    have hqLeSigma : E.slot_at cfg q ≤ sigma := by
      rw [hgeom.confirming_cutoff]
      exact Nat.succ_le_of_lt hesLtSigma
    exact (Nat.add_le_add_right hqLeSigma 1).trans
      (Nat.succ_le_of_lt hgeom.sigma_lt_endpoint)
  have hcommittee : ∀ t : Slot, es < t → t ≤ sigma →
      E.CommitteeSupportsAt cfg ext w m c t := by
    intro t hesT htSigma
    apply E.committeeSupportsAt_of_slotStart_IH_minimal cfg ext hA hw
      (by rw [hgeom.confirming_cutoff]; exact Nat.succ_le_of_lt hesT)
      (htSigma.trans_lt hgeom.sigma_lt_endpoint) hmH hcM hglcC_M
      hglcKnown hIH (hgeom.start_le_cutoff.trans (le_of_lt hesT))
  have hmid₀ : E.slot_at cfg 0 ≤ ((E.store cfg ext v q).blocks c).slot :=
    hlo₀.trans hloMid
  have hmaxMid : E.WindowRecordedEpochMax cfg ext v q
      ((E.store cfg ext v q).blocks c).slot es :=
    E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
      hv hqH hmid₀ hcutoffQ hesLtQ
  obtain ⟨hStMid, hAtMid⟩ :=
    E.confirmed_honest_class_transports_of_cutoff_minimal cfg ext hA
      v hv q query hquery c hqH hgeom.block_known hgeom.parent_known
      hgeom.confirmation w hw m hmH
      (hslotQM.trans (E.slot_at_mono cfg (Nat.le_succ m)))
      ((E.store cfg ext v q).blocks c).slot es hmid₀ hgeom.cutoff_eq
  have hparentSub : E.weight (E.crossingParentSub cfg
      (E.store cfg ext v q) (get_current_balance_source query) c
      ((E.store cfg ext v q).blocks c).slot es) ≤
      E.Aval cfg ext w m c ((E.store cfg ext v q).blocks c).slot es :=
    E.crossingParentSub_le_endpoint_Aval_minimal cfg ext hA
      hcutoffQ haQ hgeom.block_known hgeom.parent_eq
      haM hcM hparentM (by simpa only [hgeom.lo_eq] using hmaxQuery)
  have hselectedMid : ∀ i ∈ E.Sclass cfg ext w m c
      ((E.store cfg ext v q).blocks c).slot sigma,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) := by
    intro i hi
    apply hledger.selected_recording i
    have hi' := hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi' ⊢
    exact ⟨⟨span_committee_mono_lo hloMid hi'.1.1, hi'.1.2⟩, hi'.2⟩
  rcases hgeom.regime with hsame | hcross | ⟨hedge, hwindow⟩
  · exact SelectedEdgeMarginInputsAt.sameEpoch lo es sigma
      { query_store_eq := hquery
        confirming_cutoff := hgeom.confirming_cutoff
        lo_le_es := hgeom.lo_le_cutoff
        es_le_σ := hgeom.cutoff_le_sigma
        start_le_es := hgeom.start_le_cutoff
        σ_lt_endpoint := hgeom.sigma_lt_endpoint
        same_epoch := hsame
        support_transport := hSt
        ancestor_transport := hAt
        base_strip := hbase
        child_filtered := hchild
        selected_recording := hledger.selected_recording
        honest_sibling_confinement := hledger.honest_sibling_confinement
        byzantine_sibling_confinement := hledger.byzantine_sibling_confinement }
  · have hsibling :=
      E.crossingEdge_sibling_score_of_endpointLedger_minimal cfg ext hA
        (bs := get_current_balance_source query)
        hv hqH hw hmH hrelaySlot hgeom.block_known hgeom.parent_known
        hgeom.lo_eq hcutoffQ hgeom.child_slot_le_cutoff
        hgeom.cutoff_le_sigma hcross hmaxQuery hSt hAt hcommittee hledger
    exact SelectedEdgeMarginInputsAt.crossing es sigma querySlot
      { query_store_eq := hquery
        confirmation := hgeom.confirmation
        block_known := hgeom.block_known
        parent_known := hgeom.parent_known
        cutoff_eq := hcutoffQ
        query_slot_eq := hquerySlotQ
        es_le_sigma := hgeom.cutoff_le_sigma
        sigma_horizon := hgeom.sigma_horizon
        edge_crosses := hcross
        recorded_epoch_max := hmaxMid
        support_transport := hStMid
        ancestor_transport := hAtMid
        parent_sub_endpoint := hparentSub
        committee_support := hcommittee
        child_filtered := hchild
        selected_recording := hselectedMid
        sibling_score := by
          simpa only [hgeom.lo_eq] using hsibling }
  · have hsibling :=
      E.futureCrossing_sibling_score_of_endpointLedger_minimal cfg ext hA
        (bs := get_current_balance_source query)
        hgeom.block_known hgeom.parent_known hgeom.lo_eq hcutoffQ
        hgeom.child_slot_le_cutoff hgeom.cutoff_le_sigma hmaxQuery
        hSt hAt hcommittee hledger
    exact SelectedEdgeMarginInputsAt.futureCrossing es sigma querySlot
      { query_store_eq := hquery
        confirmation := hgeom.confirmation
        block_known := hgeom.block_known
        parent_known := hgeom.parent_known
        cutoff_eq := hcutoffQ
        query_slot_eq := hquerySlotQ
        es_le_sigma := hgeom.cutoff_le_sigma
        sigma_horizon := hgeom.sigma_horizon
        edge_same_epoch := hedge
        future_window_crosses := hwindow
        recorded_epoch_max := hmaxMid
        support_transport := hStMid
        ancestor_transport := hAtMid
        parent_sub_endpoint := hparentSub
        committee_support := hcommittee
        child_filtered := hchild
        selected_recording := hselectedMid
        sibling_score := by
          simpa only [hgeom.lo_eq] using hsibling }

/-- Compatibility wrapper for the legacy retained-tip contract.  It is kept
as a compatibility API; the non-circular public path below uses
`SelectedTraceFFGStateRealizationAt`. -/
theorem selectedCoveredMarginSupplyAt_of_pipeline_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (glc : Root)
    (hresult : find_latest_confirmed_descendant cfg ext query r₀ = glc)
    (hstrict : glc ≠ r₀)
    (hpipeline : SelectedTraceFFGPipeline cfg ext E anchor v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SelectedCoveredMarginSupplyAt cfg ext glc r₀ v q query := by
  apply E.selectedCoveredMarginSupplyAt_of_filterSupply_minimal cfg ext hA
    hwalkDomain v hv q hqH query hquery r₀ hr₀ glc hresult hstrict
  intro a c w m lo es sigma querySlot hw hmH hgeom hcne _hcM
    hparentM _hglcC_M _hglcKnown _hIH hnotCovered
  exact E.strictSelectedEdge_child_filtered_of_trace_pipeline_minimal
    cfg ext hA v hv q hqH query r₀ hr₀ hpipeline hprovisos
      hw hmH hgeom hcne hparentM hnotCovered

/-- Coverage-aware selected margins from the decomposed causal/state FFG
realization.  Unlike the legacy wrapper, this path passes the actual
earlier-slot induction hypothesis into checkpoint compatibility before it
constructs filter membership. -/
theorem selectedCoveredMarginSupplyAt_of_stateRealization_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hr₀Epoch :
      get_block_epoch cfg query.store r₀ =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store r₀ + 1 =
          get_current_store_epoch cfg query.store)
    (glc : Root)
    (hresult : find_latest_confirmed_descendant cfg ext query r₀ = glc)
    (hstrict : glc ≠ r₀)
    (hrealization : E.SelectedTraceFFGStateRealizationAt cfg ext anchor
      v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SelectedCoveredMarginSupplyAt cfg ext glc r₀ v q query := by
  apply E.selectedCoveredMarginSupplyAt_of_filterSupply_minimal cfg ext hA
    hwalkDomain v hv q hqH query hquery r₀ hr₀ glc hresult hstrict
  intro a c w m lo es sigma querySlot hw hmH hgeom hcne hcM
    hparentM hglcC_M hglcKnown hIH hnotCovered
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [hgeom.confirming_cutoff]
    exact Nat.succ_le_of_lt
      (lt_of_le_of_lt hgeom.cutoff_le_sigma hgeom.sigma_lt_endpoint)
  exact E.child_filtered_of_selectedTraceFFGStateRealization_minimal
    cfg ext hA hwalkDomain hv hqH hresult hr₀ hr₀Epoch hstrict
      hrealization hprovisos
      hw hslotQM hmH hcM hparentM hglcC_M hglcKnown hIH hnotCovered

/-! ## Exact function-level safety bridges -/

/-- Safety of an arbitrary permitted `find_latest_confirmed_descendant` call,
with every strict selected edge supplied by the concrete retained-trace
pipeline above. -/
theorem safeFrom_find_latest_confirmed_descendant_of_pipeline_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hbase : E.SafeFrom cfg ext r₀
      (E.slot_start cfg (E.slot_at cfg q)))
    (hpipeline : SelectedTraceFFGPipeline cfg ext E anchor v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query r₀) q := by
  apply E.safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal
    cfg ext hA v hv q hqH query hquery r₀ hr₀ hbase
  intro hstrict
  exact E.selectedCoveredMarginSupplyAt_of_pipeline_minimal cfg ext hA
    hwalkDomain v hv q hqH query hquery r₀ hr₀
    (find_latest_confirmed_descendant cfg ext query r₀) rfl hstrict
    hpipeline hprovisos

/-- Safety of the exact descendant search from the decomposed, non-circular
FFG state realization. -/
theorem safeFrom_find_latest_confirmed_descendant_of_stateRealization_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hr₀Epoch :
      get_block_epoch cfg query.store r₀ =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store r₀ + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext r₀
      (E.slot_start cfg (E.slot_at cfg q)))
    (hrealization : E.SelectedTraceFFGStateRealizationAt cfg ext anchor
      v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query r₀) q := by
  apply E.safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal
    cfg ext hA v hv q hqH query hquery r₀ hr₀ hbase
  intro hstrict
  exact E.selectedCoveredMarginSupplyAt_of_stateRealization_minimal
    cfg ext hA hwalkDomain v hv q hqH query hquery r₀ hr₀ hr₀Epoch
      (find_latest_confirmed_descendant cfg ext query r₀) rfl hstrict
      hrealization hprovisos

/-- Function-level monotonicity of the executable selector: its exact result
descends from the supplied `latest_confirmed_root` in the query store.  This
uses only the selected-margin store domain and input knownness; no margin,
FFG, helper, or future-safety premise is involved. -/
theorem find_latest_confirmed_descendant_input_ancestry_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots) :
    is_ancestor query.store
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query r₀))
      (get_node_for_root r₀) = true := by
  obtain ⟨hwf, hwalk, _hjust⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  have hhead : (get_head cfg (E.store cfg ext v q)).root ∈
      (E.store cfg ext v q).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  exact (find_latest_confirmed_descendant_ge cfg ext query
    (by simpa only [hquery] using hwf)
    (by simpa only [hquery] using hwalk)
    (by simpa only [hquery] using hhead) r₀ hr₀).1

/-- Public contract matching the pinned function note: the carried input is
already safe, and its block is from the query's current or previous epoch.
The epoch premise records the executable function's stated domain; the proof
of the strict branch itself is uniform in that choice. -/
theorem safeFrom_find_latest_confirmed_descendant_spec_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hrecent : get_block_epoch cfg query.store r₀ =
        get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store r₀ + 1 =
        get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext r₀
      (E.slot_start cfg (E.slot_at cfg q)))
    (hpipeline : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀ →
      ∃ anchor : Checkpoint Root,
        SelectedTraceFFGPipeline cfg ext E anchor v q query r₀ ∧
          SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query r₀) q := by
  have hsafety : E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query r₀) q := by
    by_cases hstrict : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀
    · obtain ⟨anchor, hpipeline, hprovisos⟩ := hpipeline hstrict
      exact E.safeFrom_find_latest_confirmed_descendant_of_pipeline_minimal
        cfg ext hA hwalkDomain v hv q hqH query hquery r₀ hr₀ hbase
        hpipeline hprovisos
    · have hsame : find_latest_confirmed_descendant cfg ext query r₀ = r₀ :=
        not_ne_iff.mp hstrict
      obtain ⟨hstart, _hstartH, _hslotStart, _hgate⟩ :=
        E.query_slot_start_facts_minimal cfg ext hA q hqH
      rw [hsame]
      exact hbase.mono cfg ext E hstart
  rcases hrecent with _hcurrent | _hprevious
  · exact hsafety
  · exact hsafety

/-- Public function contract with the same current/previous-epoch and carried-
safety premises, but with the causal/state FFG realization demanded only when
the exact search call advances. -/
theorem safeFrom_find_latest_confirmed_descendant_stateRealization_spec_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hrecent : get_block_epoch cfg query.store r₀ =
        get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store r₀ + 1 =
        get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext r₀
      (E.slot_start cfg (E.slot_at cfg q)))
    (hrealization : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀ →
      ∃ anchor : Checkpoint Root,
        E.SelectedTraceFFGStateRealizationAt cfg ext anchor
            v q query r₀ ∧
          SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query r₀) q := by
  have hsafety : E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query r₀) q := by
    by_cases hstrict : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀
    · obtain ⟨anchor, hstate, hprovisos⟩ := hrealization hstrict
      exact E.safeFrom_find_latest_confirmed_descendant_of_stateRealization_minimal
        cfg ext hA hwalkDomain v hv q hqH query hquery r₀ hr₀ hrecent
          hbase
          hstate hprovisos
    · have hsame : find_latest_confirmed_descendant cfg ext query r₀ = r₀ :=
        not_ne_iff.mp hstrict
      obtain ⟨hstart, _hstartH, _hslotStart, _hgate⟩ :=
        E.query_slot_start_facts_minimal cfg ext hA q hqH
      rw [hsame]
      exact hbase.mono cfg ext E hstart
  rcases hrecent with _hcurrent | _hprevious
  · exact hsafety
  · exact hsafety

/-- Normative function-level pair: the pinned current-moment safety result
and the selector's exact input-to-output ancestry monotonicity. -/
theorem safeFrom_and_input_ancestry_find_latest_confirmed_descendant_spec_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hrecent : get_block_epoch cfg query.store r₀ =
        get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store r₀ + 1 =
        get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext r₀
      (E.slot_start cfg (E.slot_at cfg q)))
    (hpipeline : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀ →
      ∃ anchor : Checkpoint Root,
        SelectedTraceFFGPipeline cfg ext E anchor v q query r₀ ∧
          SelectedHelperProvisosAt cfg ext E v q query r₀) :
    E.SafeFrom cfg ext
        (find_latest_confirmed_descendant cfg ext query r₀) q ∧
      is_ancestor query.store
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query r₀))
        (get_node_for_root r₀) = true := by
  exact ⟨
    E.safeFrom_find_latest_confirmed_descendant_spec_minimal cfg ext hA
      hwalkDomain v hv q hqH query hquery r₀ hr₀ hrecent hbase hpipeline,
    E.find_latest_confirmed_descendant_input_ancestry_minimal cfg ext hA
      v hv q hqH query hquery r₀ hr₀⟩

/-- Exact executable decomposition of `get_latest_confirmed`: it either
returns one of its three reset roots directly, or returns the result of the
single `find_latest_confirmed_descendant` call made from one of those roots.
Unlike `get_latest_confirmed_spec`, the advancing branch retains the actual
call input. -/
theorem get_latest_confirmed_call_cases_minimal
    (query : FastConfirmationStore Root) :
    (get_latest_confirmed cfg ext query = query.confirmed_root ∨
      get_latest_confirmed cfg ext query =
        query.store.finalized_checkpoint.root ∨
      get_latest_confirmed cfg ext query =
        query.current_epoch_observed_justified_checkpoint.root) ∨
    ∃ r₀ : Root,
      (r₀ = query.confirmed_root ∨
        r₀ = query.store.finalized_checkpoint.root ∨
        r₀ = query.current_epoch_observed_justified_checkpoint.root) ∧
      get_latest_confirmed cfg ext query =
        find_latest_confirmed_descendant cfg ext query r₀ := by
  generalize hout : get_latest_confirmed cfg ext query = result
  simp only [get_latest_confirmed] at hout
  split_ifs at hout <;>
    subst hout <;>
      first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr (Or.inl rfl))
      | exact Or.inl (Or.inr (Or.inr rfl))
      | exact Or.inr ⟨_, Or.inl rfl, rfl⟩
      | exact Or.inr ⟨_, Or.inr (Or.inl rfl), rfl⟩
      | exact Or.inr ⟨_, Or.inr (Or.inr rfl), rfl⟩

/-- The opaque-state-transition and helper-proviso boundary for the one
strict search call which `get_latest_confirmed` actually executes.  Reset
returns and called-but-unchanged searches impose no pipeline obligation. -/
structure SelectedGetLatestPipelineAt
    (anchor : Checkpoint Root)
    (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop where
  strict_call : ∀ r₀ : Root,
    (r₀ = query.confirmed_root ∨
      r₀ = query.store.finalized_checkpoint.root ∨
      r₀ = query.current_epoch_observed_justified_checkpoint.root) →
    get_latest_confirmed cfg ext query =
      find_latest_confirmed_descendant cfg ext query r₀ →
    find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀ →
    SelectedTraceFFGPipeline cfg ext E anchor v q query r₀ ∧
      SelectedHelperProvisosAt cfg ext E v q query r₀

/-- Non-circular FFG realization for the one strict search call actually made
by `get_latest_confirmed`.  Reset returns and unchanged searches impose no
state-realization obligation. -/
structure SelectedGetLatestStateRealizationAt
    (anchor : Checkpoint Root)
    (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop where
  strict_call : ∀ r₀ : Root,
    (r₀ = query.confirmed_root ∨
      r₀ = query.store.finalized_checkpoint.root ∨
      r₀ = query.current_epoch_observed_justified_checkpoint.root) →
    get_latest_confirmed cfg ext query =
      find_latest_confirmed_descendant cfg ext query r₀ →
    find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀ →
    (get_block_epoch cfg query.store r₀ =
        get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store r₀ + 1 =
        get_current_store_epoch cfg query.store) ∧
      E.SelectedTraceFFGStateRealizationAt cfg ext anchor v q query r₀ ∧
        SelectedHelperProvisosAt cfg ext E v q query r₀

/-- Safety of the exact `get_latest_confirmed` function at an arbitrary honest
query.  Its three possible reset roots must already be safe from the start of
the query slot; this is necessary for both direct reset returns and an
unchanged descendant search.  The trace pipeline is demanded only for the
actual strict search call. -/
theorem safeFrom_get_latest_confirmed_of_pipeline_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (hconfirmed : query.confirmed_root ∈ query.store.block_roots)
    (hfinalized : query.store.finalized_checkpoint.root ∈
      query.store.block_roots)
    (hobserved : query.current_epoch_observed_justified_checkpoint.root ∈
      query.store.block_roots)
    (hprev : E.SafeFrom cfg ext query.confirmed_root
      (E.slot_start cfg (E.slot_at cfg q)))
    (hfin : E.SafeFrom cfg ext query.store.finalized_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)))
    (hobs : E.SafeFrom cfg ext
      query.current_epoch_observed_justified_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)))
    (hcalls : E.SelectedGetLatestPipelineAt cfg ext anchor v q query) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext query) q := by
  obtain ⟨hstart, _hstartH, _hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  have hanchor : ∀ r₀ : Root,
      (r₀ = query.confirmed_root ∨
        r₀ = query.store.finalized_checkpoint.root ∨
        r₀ = query.current_epoch_observed_justified_checkpoint.root) →
      r₀ ∈ query.store.block_roots ∧
        E.SafeFrom cfg ext r₀ (E.slot_start cfg (E.slot_at cfg q)) := by
    intro r₀ hkind
    rcases hkind with h | h | h
    · rw [h]
      exact ⟨hconfirmed, hprev⟩
    · rw [h]
      exact ⟨hfinalized, hfin⟩
    · rw [h]
      exact ⟨hobserved, hobs⟩
  rcases get_latest_confirmed_call_cases_minimal cfg ext query with
    hreset | ⟨r₀, hkind, hcall⟩
  · rcases hreset with h | h | h
    · rw [h]
      exact hprev.mono cfg ext E hstart
    · rw [h]
      exact hfin.mono cfg ext E hstart
    · rw [h]
      exact hobs.mono cfg ext E hstart
  obtain ⟨hr₀, hbase⟩ := hanchor r₀ hkind
  by_cases hstrict : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀
  · obtain ⟨hpipeline, hprovisos⟩ :=
      hcalls.strict_call r₀ hkind hcall hstrict
    rw [hcall]
    exact E.safeFrom_find_latest_confirmed_descendant_of_pipeline_minimal
      cfg ext hA hwalkDomain v hv q hqH query hquery r₀ hr₀ hbase
      hpipeline hprovisos
  · have hsame : find_latest_confirmed_descendant cfg ext query r₀ = r₀ :=
      not_ne_iff.mp hstrict
    rw [hcall, hsame]
    exact hbase.mono cfg ext E hstart

/-- Safety of the exact `get_latest_confirmed` call from the decomposed
causal/state realization, demanded only for the strict call which the
executable branch actually takes. -/
theorem safeFrom_get_latest_confirmed_of_stateRealization_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (hconfirmed : query.confirmed_root ∈ query.store.block_roots)
    (hfinalized : query.store.finalized_checkpoint.root ∈
      query.store.block_roots)
    (hobserved : query.current_epoch_observed_justified_checkpoint.root ∈
      query.store.block_roots)
    (hprev : E.SafeFrom cfg ext query.confirmed_root
      (E.slot_start cfg (E.slot_at cfg q)))
    (hfin : E.SafeFrom cfg ext query.store.finalized_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)))
    (hobs : E.SafeFrom cfg ext
      query.current_epoch_observed_justified_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)))
    (hcalls : E.SelectedGetLatestStateRealizationAt cfg ext anchor v q query) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext query) q := by
  obtain ⟨hstart, _hstartH, _hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  have hanchor : ∀ r₀ : Root,
      (r₀ = query.confirmed_root ∨
        r₀ = query.store.finalized_checkpoint.root ∨
        r₀ = query.current_epoch_observed_justified_checkpoint.root) →
      r₀ ∈ query.store.block_roots ∧
        E.SafeFrom cfg ext r₀ (E.slot_start cfg (E.slot_at cfg q)) := by
    intro r₀ hkind
    rcases hkind with h | h | h
    · rw [h]
      exact ⟨hconfirmed, hprev⟩
    · rw [h]
      exact ⟨hfinalized, hfin⟩
    · rw [h]
      exact ⟨hobserved, hobs⟩
  rcases get_latest_confirmed_call_cases_minimal cfg ext query with
    hreset | ⟨r₀, hkind, hcall⟩
  · rcases hreset with h | h | h
    · rw [h]
      exact hprev.mono cfg ext E hstart
    · rw [h]
      exact hfin.mono cfg ext E hstart
    · rw [h]
      exact hobs.mono cfg ext E hstart
  obtain ⟨hr₀, hbase⟩ := hanchor r₀ hkind
  by_cases hstrict : find_latest_confirmed_descendant cfg ext query r₀ ≠ r₀
  · obtain ⟨hr₀Epoch, hstate, hprovisos⟩ :=
      hcalls.strict_call r₀ hkind hcall hstrict
    rw [hcall]
    exact E.safeFrom_find_latest_confirmed_descendant_of_stateRealization_minimal
      cfg ext hA hwalkDomain v hv q hqH query hquery r₀ hr₀ hr₀Epoch
        hbase
        hstate hprovisos
  · have hsame : find_latest_confirmed_descendant cfg ext query r₀ = r₀ :=
      not_ne_iff.mp hstrict
    rw [hcall, hsame]
    exact hbase.mono cfg ext E hstart

/-- A slot update between consecutive execution seconds occurs exactly at the
first second of the new slot. -/
theorem slot_start_eq_succ_of_advance_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (n : ℕ) (hHn1 : E.WithinHorizon cfg (n + 1))
    (hadvance : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 := by
  obtain ⟨hstart, _hstartH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA (n + 1) hHn1
  have hadvance' : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    simpa only [E.store_current_slot] using hadvance
  apply Nat.le_antisymm hstart
  by_contra hnot
  have hlt : E.slot_start cfg (E.slot_at cfg (n + 1)) < n + 1 :=
    Nat.lt_of_not_ge hnot
  have hleN : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ n :=
    Nat.lt_succ_iff.mp hlt
  have hslotLe := E.slot_at_mono cfg hleN
  rw [hslotStart] at hslotLe
  exact (Nat.not_lt_of_ge hslotLe) hadvance'

/-- The actual slot-update call used by the FCR trajectory.  At a genuine
slot advance, `n+1` is the query slot boundary, so the three `SafeFrom (n+1)`
witnesses already threaded by the trajectory fold have exactly the strength
required by the arbitrary-query theorem. -/
theorem safeFrom_get_latest_confirmed_fcrStep_of_pipeline_minimal
    (hSA : SpecAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hadvance : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n))
    (hprev : E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1))
    (hfin : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hobs : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root
      (n + 1))
    (hcalls : E.SelectedGetLatestPipelineAt cfg ext anchor v (n + 1)
      (E.fcrStep cfg ext v n)) :
    E.SafeFrom cfg ext
      (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) (n + 1) := by
  let hA : SelectedMarginAssumptions cfg ext E :=
    hSA.toSelectedMarginAssumptions cfg ext
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hadvance
  obtain ⟨hconfirmed, hfinalized, hobserved⟩ :=
    E.fcrStep_reset_roots_known_selected cfg ext hSA v hv n hHn1
  apply E.safeFrom_get_latest_confirmed_of_pipeline_minimal cfg ext hA
    hwalkDomain v hv (n + 1) hHn1 (E.fcrStep cfg ext v n)
    (E.fcrStep_store cfg ext v n) hconfirmed hfinalized hobserved
  · simpa only [hstartEq] using hprev
  · simpa only [hstartEq] using hfin
  · simpa only [hstartEq] using hobs
  · exact hcalls

/-- The actual slot-update call, using the decomposed state realization for
the strict `get_latest_confirmed` branch. -/
theorem safeFrom_get_latest_confirmed_fcrStep_of_stateRealization_minimal
    (hSA : SpecAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hadvance : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n))
    (hprev : E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1))
    (hfin : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hobs : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root
      (n + 1))
    (hcalls : E.SelectedGetLatestStateRealizationAt cfg ext anchor v (n + 1)
      (E.fcrStep cfg ext v n)) :
    E.SafeFrom cfg ext
      (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) (n + 1) := by
  let hA : SelectedMarginAssumptions cfg ext E :=
    hSA.toSelectedMarginAssumptions cfg ext
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hadvance
  obtain ⟨hconfirmed, hfinalized, hobserved⟩ :=
    E.fcrStep_reset_roots_known_selected cfg ext hSA v hv n hHn1
  apply E.safeFrom_get_latest_confirmed_of_stateRealization_minimal cfg ext hA
    hwalkDomain v hv (n + 1) hHn1 (E.fcrStep cfg ext v n)
    (E.fcrStep_store cfg ext v n) hconfirmed hfinalized hobserved
  · simpa only [hstartEq] using hprev
  · simpa only [hstartEq] using hfin
  · simpa only [hstartEq] using hobs
  · exact hcalls

end Execution

/-! ## Public trajectory theorems -/

/-- Conditional full-trajectory theorem from the exact selected-call
pipeline.  This is deliberately broader than the pinned function note: the
explicit `hfinalized` premise is the immediate cross-node safety of every
finalized reset root, which does not follow from one-slot synchrony alone.

The only reset
leg left explicit is the finalized root's `SafeFrom` invariant.  Genesis and
observed-justified safety are reconstructed from the pinned justification
interface; strict advances use the exact function-level theorem above.

The pipeline supplier is horizon-scoped because `SafeFrom` itself only
quantifies over in-horizon endpoints, and it is demanded only at a genuine
slot update. -/
theorem Spec_Safety_of_selectedPipeline_minimal
    (hwalkDomain : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hfinalized : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.SafeFrom cfg ext
          (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hpipeline : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.WithinHorizon cfg (n + 1) →
        get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n) →
        ∃ anchor : Checkpoint Root,
          E.SelectedGetLatestPipelineAt cfg ext anchor v (n + 1)
            (E.fcrStep cfg ext v n)) :
    Spec_Safety cfg ext := by
  apply spec_safety_of_residualGlc cfg ext
  intro E hSA
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hSA : SpecAssumptions cfg ext E :=
    ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
  have hdomK := E.store_domainK cfg ext hwfE hec hgen hji
  have hobs := E.observedFilterResiduals_of_interface cfg ext hji
    (E.prev_greatest_of_interface cfg ext hji)
  exact {
    genesis_safe := by
      intro v hv
      refine E.safeFrom_of_justified_dom_K cfg ext hdomK ?_
      intro w hw m _ hH
      exact E.genesis_dom_of_interface cfg ext hSA v hv w hw m hH
    finalized_safe := hfinalized E hSA
    observed_safe := fun v hv n =>
      E.safeFrom_observed_of_filter_K cfg ext hji hdomK
        hobs.prev_greatest_justifiedIn hobs.observed_known
        hobs.observed_head_ahead v hv n
    advance_safe_glc := by
      intro v hv n hadvance hprev hfin hobsSafe _hconf w hw m hm hHm
      have hHn1 : E.WithinHorizon cfg (n + 1) :=
        E.withinHorizon_mono cfg hm hHm
      obtain ⟨anchor, hcalls⟩ :=
        hpipeline E hSA v hv n hHn1 hadvance
      exact (E.safeFrom_get_latest_confirmed_fcrStep_of_pipeline_minimal
        cfg ext hSA (hwalkDomain E hSA) v hv n hHn1 hadvance
        hprev hfin hobsSafe hcalls) w hw m hm hHm
  }

/-- Conditional full-trajectory theorem from the decomposed, actual-call
state realization.  This replaces the broader
retained-tip supplier: its strict-call premise contains no leaf, filter
membership, source-freshness conclusion, or future head conclusion. -/
theorem Spec_Safety_of_selectedStateRealization_minimal
    (hwalkDomain : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hfinalized : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.SafeFrom cfg ext
          (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hrealization : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.WithinHorizon cfg (n + 1) →
        get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n) →
        ∃ anchor : Checkpoint Root,
          E.SelectedGetLatestStateRealizationAt cfg ext anchor v (n + 1)
            (E.fcrStep cfg ext v n)) :
    Spec_Safety cfg ext := by
  apply spec_safety_of_residualGlc cfg ext
  intro E hSA
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hSA : SpecAssumptions cfg ext E :=
    ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
  have hdomK := E.store_domainK cfg ext hwfE hec hgen hji
  have hobs := E.observedFilterResiduals_of_interface cfg ext hji
    (E.prev_greatest_of_interface cfg ext hji)
  exact {
    genesis_safe := by
      intro v hv
      refine E.safeFrom_of_justified_dom_K cfg ext hdomK ?_
      intro w hw m _ hH
      exact E.genesis_dom_of_interface cfg ext hSA v hv w hw m hH
    finalized_safe := hfinalized E hSA
    observed_safe := fun v hv n =>
      E.safeFrom_observed_of_filter_K cfg ext hji hdomK
        hobs.prev_greatest_justifiedIn hobs.observed_known
        hobs.observed_head_ahead v hv n
    advance_safe_glc := by
      intro v hv n hadvance hprev hfin hobsSafe _hconf w hw m hm hHm
      have hHn1 : E.WithinHorizon cfg (n + 1) :=
        E.withinHorizon_mono cfg hm hHm
      obtain ⟨anchor, hcalls⟩ :=
        hrealization E hSA v hv n hHn1 hadvance
      exact (E.safeFrom_get_latest_confirmed_fcrStep_of_stateRealization_minimal
        cfg ext hSA (hwalkDomain E hSA) v hv n hHn1 hadvance
        hprev hfin hobsSafe hcalls) w hw m hm hHm
  }

/-- Monotonicity paired with the causal/state realization theorem. -/
theorem Spec_Monotonicity_of_selectedStateRealization_minimal
    (hwalkDomain : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hfinalized : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.SafeFrom cfg ext
          (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hrealization : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.WithinHorizon cfg (n + 1) →
        get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n) →
        ∃ anchor : Checkpoint Root,
          E.SelectedGetLatestStateRealizationAt cfg ext anchor v (n + 1)
            (E.fcrStep cfg ext v n)) :
    Spec_Monotonicity cfg ext :=
  spec_monotonicity_of_safety cfg ext
    (Spec_Safety_of_selectedStateRealization_minimal cfg ext
      hwalkDomain hfinalized hrealization)
    (hkc_of_confirmed_known cfg ext
      (fun E hSA v hv k =>
        E.confirmed_root_known_selected cfg ext hSA v hv k))

/-- Public monotonicity from the same exact selected-call contract.  The
single-store knownness side is the executable selected-result induction. -/
theorem Spec_Monotonicity_of_selectedPipeline_minimal
    (hwalkDomain : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hfinalized : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.SafeFrom cfg ext
          (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hpipeline : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        E.WithinHorizon cfg (n + 1) →
        get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n) →
        ∃ anchor : Checkpoint Root,
          E.SelectedGetLatestPipelineAt cfg ext anchor v (n + 1)
            (E.fcrStep cfg ext v n)) :
    Spec_Monotonicity cfg ext :=
  spec_monotonicity_of_safety cfg ext
    (Spec_Safety_of_selectedPipeline_minimal cfg ext
      hwalkDomain hfinalized hpipeline)
    (hkc_of_confirmed_known cfg ext
      (fun E hSA v hv k =>
        E.confirmed_root_known_selected cfg ext hSA v hv k))

end FastConfirmation.Spec
