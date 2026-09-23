module
public import FastConfirmation.Spec.Proof.CoveredMargin
public import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
public import FastConfirmation.Spec.Proof.SelectedTraceFilterPipeline
public import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
public import FastConfirmation.Spec.Proof.SelectedCommitteeSupport
public import FastConfirmation.Spec.Proof.SelectedMarginConstruction
public import FastConfirmation.Spec.Proof.EndpointLedgerMinimal
public import FastConfirmation.Spec.Proof.FutureSiblingScore
public import FastConfirmation.Spec.Proof.StatusMarginConstruction

@[expose] public section

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
    ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c)))

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
  have hsigmaLt : sigma < E.slot_at cfg m := hgeom.sigma_lt_endpoint
  have hslotQM' : E.slot_at cfg q ≤ E.slot_at cfg m := hslotQM
  by_cases heqCutoff : sigma = es
  · have hledgerEs : E.EndpointLedgerFields cfg ext w m a c lo es := by
      simpa only [heqCutoff] using hledger
    have hstatus := E.statusMargin_loWindow_minimal cfg ext hA hwalkDomain
      hv hqH hquery hw hmH haQ hgeom.block_known
      (hgeom.parent_eq) haM hcM hparentM hgeom.confirmation hgeom.lo_eq hloEnd
      hlo₀ hcutoffQ (by rw [heqCutoff] at hsigmaEnd; exact hsigmaEnd)
      (by rw [← heqCutoff]; exact hsigmaLt) (le_refl es) hslotQM' hmaxQuery hSt
      (fun t h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _))
      (by simp only [Nat.sub_self, Nat.mul_zero, le_refl])
      hledgerEs.selected_recording
    exact SelectedEdgeMarginInputsAt.directWindow lo es
      { support_transport := hSt
        ancestor_transport := hAt
        base_strip := hbase
        child_filtered := hchild
        status_margin := hstatus
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
      hv hqH hcutoffQ haQ hgeom.block_known hgeom.parent_eq
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
  · have hsameT : ∀ t : Slot, lo ≤ t → t ≤ sigma →
        compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo :=
      fun t htlo htσ => epoch_eq_of_between cfg htlo htσ hsame
    have hbudget := E.hbudget_sameEpoch_of_IH cfg ext hA.byzantine_bound
      hA.externals_coherence hgeom.lo_le_cutoff hgeom.cutoff_le_sigma
      hgeom.sigma_horizon hsameT
    have hstatus := E.statusMargin_loWindow_minimal cfg ext hA hwalkDomain
      hv hqH hquery hw hmH haQ hgeom.block_known
      (hgeom.parent_eq) haM hcM hparentM hgeom.confirmation hgeom.lo_eq hloEnd
      hlo₀ hcutoffQ hsigmaEnd hsigmaLt hgeom.cutoff_le_sigma hslotQM' hmaxQuery
      hSt hcommittee hbudget hledger.selected_recording
    exact SelectedEdgeMarginInputsAt.sameEpoch lo es sigma
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
        status_margin := hstatus
        selected_recording := hledger.selected_recording
        honest_sibling_confinement := hledger.honest_sibling_confinement
        byzantine_sibling_confinement := hledger.byzantine_sibling_confinement }
  · have hstatus := E.statusMargin_crossing_minimal cfg ext hA hwalkDomain
      hv hqH hquery hw hmH haQ hgeom.block_known
      (hgeom.parent_eq) haM hcM hparentM hgeom.confirmation hgeom.lo_eq hloEnd
      hlo₀ hcutoffQ hsigmaEnd hsigmaLt hgeom.cutoff_le_sigma hgeom.sigma_horizon
      hslotQM' hgeom.child_slot_le_cutoff hmaxQuery hSt hAt hmaxMid hStMid hAtMid
      hcommittee hledger.selected_recording hselectedMid
      (Or.inr ⟨hcross, hrelaySlot⟩)
    have hsibling :=
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
        status_margin := hstatus
        selected_recording := hselectedMid
        sibling_score := by
          simpa only [hgeom.lo_eq] using hsibling }
  · have hstatus := E.statusMargin_crossing_minimal cfg ext hA hwalkDomain
      hv hqH hquery hw hmH haQ hgeom.block_known
      (hgeom.parent_eq) haM hcM hparentM hgeom.confirmation hgeom.lo_eq hloEnd
      hlo₀ hcutoffQ hsigmaEnd hsigmaLt hgeom.cutoff_le_sigma hgeom.sigma_horizon
      hslotQM' hgeom.child_slot_le_cutoff hmaxQuery hSt hAt hmaxMid hStMid hAtMid
      hcommittee hledger.selected_recording hselectedMid (Or.inl hedge)
    have hsibling :=
      E.futureCrossing_sibling_score_of_endpointLedger_minimal cfg ext hA
        hv hqH
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
        status_margin := hstatus
        selected_recording := hselectedMid
        sibling_score := by
          simpa only [hgeom.lo_eq] using hsibling }



/-! ## Exact function-level safety bridges -/












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



end Execution

/-! ## Public trajectory theorems -/





end FastConfirmation.Spec

end
