import FastConfirmation.Spec.Proof.WeakSelectedMarginInputs
import FastConfirmation.Spec.Proof.WeakSelectedEdgeGeometry
import FastConfirmation.Spec.Proof.EndpointLedgerMinimal
import FastConfirmation.Spec.Proof.SelectedCommitteeSupport

/-!
# Spec / Proof / WeakCoveredMarginConstruction

Margin-discharge wave, Stage J-e: the weak twin of
`SelectedCoveredMarginConstruction.selectedCoveredMarginSupplyAt_of_filterSupply_minimal`,
read at an arbitrary (not necessarily honest) observer.

Substitutions relative to the strong producer:

* the geometry producer `strictSelectedEdgeGeometry_of_query_minimal` becomes
  `Weak.strictSelectedEdgeGeometry_at_observer`;
* every `windowRecordedEpochMax_at_query_minimal` call at the OBSERVER is
  deleted (`F4`): both the base-strip use (replaced by
  `Weak.base_strip_of_confirmed_at_observer`, which needs no `hdom` at all)
  and the crossing/future-crossing `hparentSub` use (replaced by an inline
  reproduction of `WeakCrossingSets.lean`'s `private crossingParentSub_le_
  endpoint_Aval`, over `Weak.freshParentStuck_subset_endpoint_Aclass`);
* `confirmed_honest_class_transports_of_cutoff_minimal` (the query→endpoint
  honest-class transports) is deleted everywhere: the weak same-epoch and
  direct-window records carry one endpoint-side `endpoint_base_strip` field
  instead;
* `endpointLedgerFields_from_execution_minimal` is KEPT, unchanged — it runs
  entirely at the honest endpoint `(w, m)`, so `hwalkDomain` remains exactly
  as before, consumed only there;
* the crossing/future-crossing regime split still comes from
  `hgeom.regime`, but both arms now build the SAME weak structure
  (`Weak.CrossingSelectedMarginInputs`, `F3`), and their sibling-score field
  is populated by the single `Weak.crossing_sibling_score_of_endpointLedger`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-- Verbatim weak twin of `SelectedCoveredMarginConstruction.
SelectedStrictEdgeFilterSupplyAt`, over `Weak.StrictSelectedEdgeGeometry`. -/
def SelectedStrictEdgeFilterSupplyAt
    (E : Execution Root) (glc r₀ : Root) (obs : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop :=
  ∀ {a c : Root} {w : ValidatorIndex} {m : ℕ}
      {lo es sigma querySlot : Slot},
    w ∈ E.honest →
    E.WithinHorizon cfg m →
    Weak.StrictSelectedEdgeGeometry cfg ext E glc r₀ a c obs q query w m
      lo es sigma querySlot →
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

/-- **Stage J.** Weak twin of
`selectedCoveredMarginSupplyAt_of_filterSupply_minimal`. `hv` is gone (`obs`
need not be honest); `hwalkDomain` REMAINS (consumed only at the honest
endpoint, by `endpointLedgerFields_from_execution_minimal`). -/
theorem selectedCoveredMarginSupplyAt_of_filterSupply_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (glc : Root)
    (hresult : Weak.find_latest_confirmed_descendant cfg ext query r₀ = glc)
    (hstrict : glc ≠ r₀)
    (hfilter : Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E glc r₀ obs q query) :
    Weak.SelectedCoveredMarginSupplyAt cfg ext E glc r₀ obs q query := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  have hjrk : (E.store cfg ext obs q).justified_checkpoint.root ∈
      (E.store cfg ext obs q).block_roots :=
    hW.coherence.justified_root_known q hqH
  have hr₀Q : r₀ ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [hquery] using hr₀
  rcases E.find_latest_confirmed_descendant_selected_minimal_weak cfg ext hA
      obs q hqH hjrk query hquery r₀ hr₀ with
    hsame | ⟨hglcConf₀, _hglcWeak₀, hglcQ₀, hglcParentQ₀, _hguard⟩
  · exact False.elim (hstrict (hresult.symm.trans hsame))
  have hglcConf : Spec.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true := by
    rw [hresult] at hglcConf₀
    exact hglcConf₀
  have hglcQ : glc ∈ (E.store cfg ext obs q).block_roots := by
    rw [hresult] at hglcQ₀
    simpa only [hquery] using hglcQ₀
  have hglcParentQ : ((E.store cfg ext obs q).blocks glc).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hresult] at hglcParentQ₀
    simpa only [hquery] using hglcParentQ₀
  obtain ⟨_hstartLeQ, _hstartH, hslotStart, _hstartGate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  have hcur₀ : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext obs 0
    rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgenEq,
      get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
    rw [← ht, hanchorSlot]
  intro w hw m hslotQM hmH hIH a c haM hcM hparentM hglcC_M hcR₀_M hcne
  by_cases hcovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) = true
  · exact Or.inl hcovered
  right
  obtain ⟨lo, es, sigma, querySlot, hgeom⟩ :=
    Weak.strictSelectedEdgeGeometry_at_observer cfg ext hA hW q hqH query hquery r₀ hr₀ glc
      hresult hstrict w hw m hslotQM hmH a c haM hcM hparentM hglcC_M hcR₀_M hcne
  have hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hm' hm'H
    have hslotQM' : E.slot_at cfg q ≤ E.slot_at cfg m' := by
      rw [← hslotStart]
      exact E.slot_at_mono cfg hm'
    exact E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hquery glc hqH hglcQ hglcParentQ hglcConf
      w' hw' m' hslotQM' hm'H
  have hchild := hfilter hw hmH hgeom hcne hcM hparentM hglcC_M
    hglcKnown hIH hcovered
  have haQ : a ∈ (E.store cfg ext obs q).block_roots := by
    rw [← hgeom.parent_eq]
    exact hgeom.parent_known
  have hagreeA : (E.store cfg ext obs q).blocks a =
      (E.store cfg ext w m).blocks a :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs q) (E.blockProvenance cfg ext w m)
      haQ haM
  have hloEnd : lo = ((E.store cfg ext w m).blocks a).slot + 1 := by
    calc
      lo = ((E.store cfg ext obs q).blocks
          ((E.store cfg ext obs q).blocks c).parent_root).slot + 1 := hgeom.lo_eq
      _ = ((E.store cfg ext obs q).blocks a).slot + 1 := by rw [hgeom.parent_eq]
      _ = ((E.store cfg ext w m).blocks a).slot + 1 := by rw [hagreeA]
  have hanchorA : ablk.message.slot ≤
      ((E.store cfg ext obs q).blocks a).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorParent obs q a haQ
  have hlo₀ : E.slot_at cfg 0 ≤ lo := by
    rw [hcur₀, hgeom.lo_eq, hgeom.parent_eq]
    exact hanchorA.trans (Nat.le_succ _)
  have hloMid : lo ≤ ((E.store cfg ext obs q).blocks c).slot := by
    rw [hgeom.lo_eq]
    exact Nat.succ_le_of_lt hgeom.parent_slot_lt
  have hcutoffQ : es = get_current_slot cfg (E.store cfg ext obs q) - 1 := by
    calc
      es = get_current_slot cfg query.store - 1 := hgeom.cutoff_eq
      _ = get_current_slot cfg (E.store cfg ext obs q) - 1 := by rw [hquery]
  have hquerySlotQ : querySlot = get_current_slot cfg (E.store cfg ext obs q) := by
    calc
      querySlot = get_current_slot cfg query.store := hgeom.query_slot_eq
      _ = get_current_slot cfg (E.store cfg ext obs q) := by rw [hquery]
  have hsigmaEnd : sigma = get_current_slot cfg (E.store cfg ext w m) - 1 := by
    calc
      sigma = E.slot_at cfg m - 1 := hgeom.sigma_eq
      _ = get_current_slot cfg (E.store cfg ext w m) - 1 := by
        rw [E.store_current_slot cfg ext w m]
  have hesLtQ : es < E.slot_at cfg q := by
    rw [hgeom.confirming_cutoff]
    exact Nat.lt_succ_self es
  -- the endpoint-only ledger fields: `hwalkDomain`'s sole consumer
  have hledger : E.EndpointLedgerFields cfg ext w m a c lo sigma :=
    E.endpointLedgerFields_from_execution_minimal cfg ext hA hwalkDomain
      hw hmH hsigmaEnd haM hcM hparentM (le_of_eq hloEnd) hlo₀
  -- the weak-native base strip, entirely at the endpoint
  have hbase := Weak.base_strip_of_confirmed_at_observer cfg ext hA hqH hcomm hquery
    hgeom.block_known hgeom.parent_known hgeom.confirmation hgeom.lo_eq hcutoffQ hw hmH
    hslotQM hgeom.endpoint_parent_known hgeom.endpoint_block_known hgeom.endpoint_parent_eq
  by_cases heqCutoff : sigma = es
  · have hledgerEs : E.EndpointLedgerFields cfg ext w m a c lo es := by
      simpa only [heqCutoff] using hledger
    exact Weak.SelectedEdgeMarginInputsAt.directWindow lo es
      { endpoint_base_strip := hbase
        child_filtered := hchild
        selected_score := hledgerEs.selected_score
        sibling_score := hledgerEs.sibling_score }
  have hesLtSigma : es < sigma :=
    lt_of_le_of_ne hgeom.cutoff_le_sigma (Ne.symm heqCutoff)
  have hcommittee : ∀ t : Slot, es < t → t ≤ sigma →
      E.CommitteeSupportsAt cfg ext w m c t := by
    intro t hesT htSigma
    apply E.committeeSupportsAt_of_slotStart_IH_minimal cfg ext hA hw
      (by rw [hgeom.confirming_cutoff]; exact Nat.succ_le_of_lt hesT)
      (htSigma.trans_lt hgeom.sigma_lt_endpoint) hmH hcM hglcC_M
      hglcKnown hIH (hgeom.start_le_cutoff.trans (le_of_lt hesT))
  have hselectedMid : ∀ i ∈ E.Sclass cfg ext w m c
      ((E.store cfg ext obs q).blocks c).slot sigma,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) := by
    intro i hi
    apply hledger.selected_recording i
    have hi' := hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi' ⊢
    exact ⟨⟨span_committee_mono_lo hloMid hi'.1.1, hi'.1.2⟩, hi'.2⟩
  -- the balance source's registry/provenance facts, at the observer's own
  -- store, needed by the endpoint `Aclass` placement below (freshness-only,
  -- no `WindowRecordedEpochMax`)
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconfQ : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs c = true := by
    simpa only [bs, hquery] using hgeom.confirmation
  have hconfStrongC : Spec.is_one_confirmed cfg ext (E.store cfg ext obs q) bs c = true :=
    Spec.is_one_confirmed_of_weak cfg ext _ _ _ hconfQ
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hquery]
  have hkeyC : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp c
    rw [← hbsEq]
    exact hconfStrongC
  have hvalC : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen obs q).2 cp hkeyC
  have hprovC := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen obs q
  rw [← E.store_current_slot cfg ext obs q] at hprovC
  have hschedC : SchedLMProv E cfg (E.store cfg ext obs q) :=
    E.schedLMProv cfg ext hgen obs q
  -- fresh parent-stuck at the observer lands in the endpoint's `Aclass`, at
  -- `lo := parent.slot + 1` — replacing `crossingParentSub_le_endpoint_Aval_minimal`
  have hlo0Par : E.slot_at cfg 0 ≤
      ((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks c).parent_root).slot + 1 := by
    rw [← hgeom.lo_eq]
    exact hlo₀
  have hAclassLo := Weak.freshParentStuck_subset_endpoint_Aclass cfg ext hA hqH hcomm
    (a := ((E.store cfg ext obs q).blocks c).parent_root)
    hvalC hgeom.parent_known hgeom.block_known rfl hprovC hschedC
    hlo0Par (le_refl _) hcutoffQ hesLtQ hw hmH hslotQM
    (by rw [hgeom.parent_eq]; exact haM) hcM (by rw [hgeom.parent_eq]; exact hparentM)
  have hparentSub : E.weight (Weak.crossingParentSub cfg ext E (E.store cfg ext obs q) bs c
      ((E.store cfg ext obs q).blocks c).slot es) ≤
      E.Aval cfg ext w m c ((E.store cfg ext obs q).blocks c).slot es := by
    rw [Execution.Aval]
    apply E.weight_mono
    intro i hi
    have hi' : i ∈ Weak.FreshParentStuck cfg ext E (E.store cfg ext obs q) bs c ∩
        E.span_committee ((E.store cfg ext obs q).blocks c).slot es := by
      simpa only [Weak.crossingParentSub] using hi
    obtain ⟨hiP, hiS⟩ := Finset.mem_inter.mp hi'
    have hia := hAclassLo hiP
    simp only [Execution.Aclass, Finset.mem_filter] at hia ⊢
    exact ⟨⟨hiS, hia.1.2⟩, hia.2⟩
  rcases hgeom.regime with hsame | hcross | ⟨hedge, hwindow⟩
  · exact Weak.SelectedEdgeMarginInputsAt.sameEpoch lo es sigma
      { query_store_eq := hquery
        confirming_cutoff := hgeom.confirming_cutoff
        lo_le_es := hgeom.lo_le_cutoff
        es_le_σ := hgeom.cutoff_le_sigma
        start_le_es := hgeom.start_le_cutoff
        σ_lt_endpoint := hgeom.sigma_lt_endpoint
        same_epoch := hsame
        endpoint_base_strip := hbase
        child_filtered := hchild
        selected_recording := hledger.selected_recording
        honest_sibling_confinement := hledger.honest_sibling_confinement
        byzantine_sibling_confinement := hledger.byzantine_sibling_confinement }
  · have hsibling := Weak.crossing_sibling_score_of_endpointLedger cfg ext hA hAclassLo
      hgeom.child_slot_le_cutoff hgeom.cutoff_le_sigma hcommittee (hgeom.lo_eq ▸ hledger)
    exact Weak.SelectedEdgeMarginInputsAt.crossing es sigma querySlot
      { query_store_eq := hquery
        confirmation := hgeom.confirmation
        block_known := hgeom.block_known
        parent_known := hgeom.parent_known
        cutoff_eq := hcutoffQ
        cutoff_lt_query := hesLtQ
        query_slot_eq := hquerySlotQ
        es_le_sigma := hgeom.cutoff_le_sigma
        sigma_horizon := hgeom.sigma_horizon
        slot_q_le_m := hslotQM
        regime := Execution.StrictSelectedEdgeRegime.crossing hcross
        endpoint_block_known := hcM
        endpoint_parent_known := by rw [hgeom.parent_eq]; exact haM
        endpoint_parent_eq := hparentM.trans hgeom.parent_eq.symm
        parent_sub_endpoint := hparentSub
        committee_support := hcommittee
        child_filtered := hchild
        selected_recording := hselectedMid
        sibling_score := hsibling }
  · have hsibling := Weak.crossing_sibling_score_of_endpointLedger cfg ext hA hAclassLo
      hgeom.child_slot_le_cutoff hgeom.cutoff_le_sigma hcommittee (hgeom.lo_eq ▸ hledger)
    exact Weak.SelectedEdgeMarginInputsAt.crossing es sigma querySlot
      { query_store_eq := hquery
        confirmation := hgeom.confirmation
        block_known := hgeom.block_known
        parent_known := hgeom.parent_known
        cutoff_eq := hcutoffQ
        cutoff_lt_query := hesLtQ
        query_slot_eq := hquerySlotQ
        es_le_sigma := hgeom.cutoff_le_sigma
        sigma_horizon := hgeom.sigma_horizon
        slot_q_le_m := hslotQM
        regime := Execution.StrictSelectedEdgeRegime.futureCrossing hedge hwindow
        endpoint_block_known := hcM
        endpoint_parent_known := by rw [hgeom.parent_eq]; exact haM
        endpoint_parent_eq := hparentM.trans hgeom.parent_eq.symm
        parent_sub_endpoint := hparentSub
        committee_support := hcommittee
        child_filtered := hchild
        selected_recording := hselectedMid
        sibling_score := hsibling }

end Weak

end FastConfirmation.Spec
