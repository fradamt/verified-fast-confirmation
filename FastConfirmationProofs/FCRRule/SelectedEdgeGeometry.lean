module
public import FastConfirmationProofs.Discount.SelectedMarginConstruction

@[expose] public section

/-!
# Query-local geometry of a strict selected edge

This module discharges the structural part of an arbitrary-query selected
margin.  A consuming endpoint can be earlier than a late query in execution
index while lying in the same slot, so its store cannot be restricted to the
query by a whole-store inclusion.  Instead, strict confirmation supplies an
honest past descendant of the selected result.  The past store is relayed to
both endpoints and is used as the common store in which the selected segment
is recovered.

The resulting certificate contains only executable selection, block-domain,
clock, horizon, and epoch-regime facts.  It deliberately contains none of the
filter, recording, sibling-score, or cross-epoch accounting fields.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The three regimes expected by the selected-margin consumers, stated in
their exact query-store form. -/
inductive StrictSelectedEdgeRegime (cfg : Config)
    (queryStore : Store Root) (c : Root) (lo sigma : Slot) : Prop where
  | sameEpoch
      (h : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg sigma) :
      StrictSelectedEdgeRegime cfg queryStore c lo sigma
  | crossing
      (h : get_block_epoch cfg queryStore c >
        get_block_epoch cfg queryStore (queryStore.blocks c).parent_root) :
      StrictSelectedEdgeRegime cfg queryStore c lo sigma
  | futureCrossing
      (hedge : get_block_epoch cfg queryStore c =
        get_block_epoch cfg queryStore (queryStore.blocks c).parent_root)
      (hwindow : compute_epoch_at_slot cfg (queryStore.blocks c).slot <
        compute_epoch_at_slot cfg sigma) :
      StrictSelectedEdgeRegime cfg queryStore c lo sigma

/-- Query-local, canonical coordinates and geometry for one strict edge of an
actual `find_latest_confirmed_descendant` result. -/
structure StrictSelectedEdgeGeometry
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (glc r0 a c : Root) (v : ValidatorIndex) (q : Nat)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : Nat)
    (lo es sigma querySlot : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext v q
  result_eq : find_latest_confirmed_descendant cfg ext query r0 = glc
  confirmation : is_one_confirmed cfg ext query.store
    (get_current_balance_source query) c = true
  block_known : c ∈ (E.store cfg ext v q).block_roots
  parent_known : ((E.store cfg ext v q).blocks c).parent_root ∈
    (E.store cfg ext v q).block_roots
  parent_eq : ((E.store cfg ext v q).blocks c).parent_root = a
  result_to_child : is_ancestor (E.store cfg ext v q)
    (get_node_for_root glc) (get_node_for_root c) = true
  child_to_anchor : is_ancestor (E.store cfg ext v q)
    (get_node_for_root c) (get_node_for_root r0) = true
  parent_slot_lt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks c).parent_root).slot <
    ((E.store cfg ext v q).blocks c).slot
  child_slot_le_cutoff : ((E.store cfg ext v q).blocks c).slot ≤ es
  lo_eq : lo = ((E.store cfg ext v q).blocks
    ((E.store cfg ext v q).blocks c).parent_root).slot + 1
  cutoff_eq : es = get_current_slot cfg query.store - 1
  query_slot_eq : querySlot = get_current_slot cfg query.store
  sigma_eq : sigma = E.slot_at cfg m - 1
  confirming_cutoff : E.slot_at cfg q = es + 1
  lo_le_cutoff : lo ≤ es
  cutoff_le_sigma : es ≤ sigma
  start_le_cutoff : E.slot_at cfg 0 ≤ es
  sigma_lt_endpoint : sigma < E.slot_at cfg m
  lo_horizon : E.SlotWithinHorizon cfg lo
  cutoff_horizon : E.SlotWithinHorizon cfg es
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  regime : StrictSelectedEdgeRegime cfg
    (E.store cfg ext v q) c lo sigma

/-- Recover a strict endpoint edge of the actual selected segment back into
the query store and package its canonical confirmation window.  The endpoint
is ordered by slot, not by execution index, so this theorem also covers the
first second of a query slot when the query itself occurs later.

The only edge premise not implied by ancestry is `c != r0`; it is precisely
the strict scope used by the chain walker. -/
theorem strictSelectedEdgeGeometry_of_query_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : Nat)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (r0 : Root) (hr0 : r0 ∈ query.store.block_roots)
    (glc : Root)
    (hresult : find_latest_confirmed_descendant cfg ext query r0 = glc)
    (hstrict : glc ≠ r0)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : Nat)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hmH : E.WithinHorizon cfg m)
    (a c : Root)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hcR0_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root c) (get_node_for_root r0) = true)
    (hcne : c ≠ r0) :
    ∃ lo es sigma querySlot : Slot,
      StrictSelectedEdgeGeometry cfg ext E glc r0 a c v q query w m
        lo es sigma querySlot := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorRoot⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorRoot⟩
  have hr0Q : r0 ∈ (E.store cfg ext v q).block_roots := by
    simpa only [hquery] using hr0
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain v hv q hqH
  have hheadQ : (get_head cfg (E.store cfg ext v q)).root ∈
      (E.store cfg ext v q).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  rcases E.find_latest_confirmed_descendant_selected_minimal cfg ext hA
      v hv q hqH query hquery r0 hr0 with
    hsame | ⟨hglcConf0, hglcQ0, hglcParentQ0⟩
  · exact False.elim (hstrict (hresult.symm.trans hsame))
  have hglcConf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true := by
    rw [hresult] at hglcConf0
    exact hglcConf0
  have hglcQ : glc ∈ (E.store cfg ext v q).block_roots := by
    rw [hresult] at hglcQ0
    simpa only [hquery] using hglcQ0
  have hglcParentQ : ((E.store cfg ext v q).blocks glc).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    rw [hresult] at hglcParentQ0
    simpa only [hquery] using hglcParentQ0
  have hglcR0_Q : is_ancestor (E.store cfg ext v q)
      (get_node_for_root glc) (get_node_for_root r0) = true := by
    have hge := (find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hquery] using hwfQ)
      (by simpa only [hquery] using hwalkQ)
      (by simpa only [hquery] using hheadQ) r0 hr0).1
    rw [hresult] at hge
    simpa only [hquery] using hge
  obtain ⟨hr0M, _hglcM, _hglcR0M⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hquery glc r0 hqH hglcQ hglcParentQ hr0Q
        hglcR0_Q hglcConf w hw m hslotQM hmH
  obtain ⟨u, nu, d, hu, hnuH, hnuq, _hdeadline, _hhead, hdU, hdQ, hdGlc_Q⟩ :=
    E.confirmed_pastDescendant_minimal cfg ext hA v hv q query hquery
      glc hqH hglcQ hglcParentQ hglcConf
  obtain ⟨hwfM, hwalkM, _hjustM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain w hw m hmH
  obtain ⟨hcQ, hglcC_Q⟩ := E.ancestor_at_common_descendant_minimal cfg ext hA
    _hglcM hglcQ hcM hglcC_M
  have hcA_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root c) (get_node_for_root a) = true :=
    is_ancestor_of_parent hwfM hcM haM hparentM
  obtain ⟨haQ, _hcA_Q⟩ := E.ancestor_at_common_descendant_minimal cfg ext hA
    hcM hcQ haM hcA_M
  have hcR0_Q := (E.ancestor_at_common_descendant_minimal cfg ext hA
    hcM hcQ hr0M hcR0_M).2
  have hagreeMQ : ∀ r, r ∈ (E.store cfg ext w m).block_roots →
      r ∈ (E.store cfg ext v q).block_roots →
      (E.store cfg ext w m).blocks r = (E.store cfg ext v q).blocks r :=
    fun r hr hs => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext w m) (E.blockProvenance cfg ext v q) hr hs
  have hparentQ : ((E.store cfg ext v q).blocks c).parent_root = a := by
    rw [← hagreeMQ c hcM hcQ]
    exact hparentM
  have hparentKnownQ : ((E.store cfg ext v q).blocks c).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hpstr := find_latest_confirmed_descendant_between cfg ext query
    (by simpa only [hquery] using hwfQ)
    (by simpa only [hquery] using hwalkQ)
    (by simpa only [hquery] using hheadQ) r0 hr0
  have hcConf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) c = true := by
    have hcharge := hpstr.2.2 c (by simpa only [hquery] using hcQ)
      (by simpa only [hquery, hresult] using hglcC_Q)
      (by simpa only [hquery] using hcR0_Q)
    exact hcharge.resolve_left hcne
  have hparentSlotLtQ : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks c).parent_root).slot <
      ((E.store cfg ext v q).blocks c).slot :=
    hwfQ c hcQ hparentKnownQ
  have hdC_Q : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root c) = true :=
    is_ancestor_trans (b := get_node_for_root glc) hwfQ (hwalkQ c hcQ d hdQ)
      (hwalkQ c hcQ glc hglcQ) hdGlc_Q hglcC_Q
  obtain ⟨hcU, hdC_U⟩ := E.ancestor_at_common_descendant_minimal cfg ext hA
    hdQ hdU hcQ hdC_Q
  obtain ⟨hwfU, hwalkU, _hjustU⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain u hu nu hnuH
  have hcAgree : (E.store cfg ext u nu).blocks c =
      (E.store cfg ext v q).blocks c := hA.wellFormed.blocks_agree
    (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext v q) hcU hcQ
  have hcSlotLeD_U : ((E.store cfg ext u nu).blocks c).slot ≤
      ((E.store cfg ext u nu).blocks d).slot := by
    have h := get_ancestor_slot_le hwfU (hwalkU c hcU d hdU)
    rw [show (get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d .pending)
        ((E.store cfg ext u nu).blocks c).slot).root = c by
      simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hdC_U] at h
    exact h
  have hdSlotLeNu : ((E.store cfg ext u nu).blocks d).slot ≤
      E.slot_at cfg nu := by
    rw [← E.store_current_slot cfg ext u nu]
    exact E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hanchorSlot⟩ u nu d hdU
  have hcSlotLtQ : ((E.store cfg ext v q).blocks c).slot < E.slot_at cfg q := by
    rw [← hcAgree]
    exact hcSlotLeD_U.trans_lt (hdSlotLeNu.trans_lt hnuq)
  let lo : Slot := ((E.store cfg ext v q).blocks
    ((E.store cfg ext v q).blocks c).parent_root).slot + 1
  let es : Slot := get_current_slot cfg query.store - 1
  let sigma : Slot := E.slot_at cfg m - 1
  let querySlot : Slot := get_current_slot cfg query.store
  have hcurrentQ : get_current_slot cfg query.store = E.slot_at cfg q := by
    rw [hquery, E.store_current_slot cfg ext v q]
  have hqPos : 0 < E.slot_at cfg q := by
    exact lt_of_le_of_lt (Nat.zero_le _) hcSlotLtQ
  have hesEq : es = E.slot_at cfg q - 1 := by
    simp only [es, hcurrentQ]
  have hcutoff : E.slot_at cfg q = es + 1 := by
    rw [hesEq]
    exact (Nat.sub_one_add_one (Nat.ne_of_gt hqPos)).symm
  have hcSlotLeEs : ((E.store cfg ext v q).blocks c).slot ≤ es := by
    rw [hesEq]
    exact Nat.le_sub_one_of_lt hcSlotLtQ
  have hloLeEs : lo ≤ es := by
    simp only [lo]
    exact (Nat.succ_le_of_lt hparentSlotLtQ).trans hcSlotLeEs
  have hstartLeEs : E.slot_at cfg 0 ≤ es := by
    have hstartNu : E.slot_at cfg 0 ≤ E.slot_at cfg nu :=
      E.slot_at_mono cfg (Nat.zero_le nu)
    rw [hesEq]
    exact Nat.le_sub_one_of_lt (hstartNu.trans_lt hnuq)
  have hesLeSigma : es ≤ sigma := by
    simp only [es, sigma, hcurrentQ]
    exact Nat.sub_le_sub_right hslotQM 1
  have hmPos : 0 < E.slot_at cfg m := hqPos.trans_le hslotQM
  have hsigmaLt : sigma < E.slot_at cfg m := by
    simp only [sigma]
    exact Nat.sub_lt hmPos Nat.one_pos
  have hloLeM : lo ≤ E.slot_at cfg m :=
    hloLeEs.trans (hesLeSigma.trans (Nat.sub_le _ _))
  have hesLeM : es ≤ E.slot_at cfg m :=
    hesLeSigma.trans (Nat.sub_le _ _)
  have hsigmaLeM : sigma ≤ E.slot_at cfg m := Nat.sub_le _ _
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_of_le cfg hloLeM hmH
  have hesH : E.SlotWithinHorizon cfg es :=
    E.slotWithinHorizon_of_le cfg hesLeM hmH
  have hsigmaH : E.SlotWithinHorizon cfg sigma :=
    E.slotWithinHorizon_of_le cfg hsigmaLeM hmH
  have hregime : StrictSelectedEdgeRegime cfg
      (E.store cfg ext v q) c lo sigma := by
    by_cases hsame : compute_epoch_at_slot cfg lo =
        compute_epoch_at_slot cfg sigma
    · exact .sameEpoch hsame
    · have hparentChildEpoch : get_block_epoch cfg (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks c).parent_root ≤
          get_block_epoch cfg (E.store cfg ext v q) c := by
        simp only [get_block_epoch]
        exact Nat.div_le_div_right (Nat.le_of_lt hparentSlotLtQ)
      rcases lt_or_eq_of_le hparentChildEpoch with hcross | hedge
      · exact .crossing hcross
      · apply StrictSelectedEdgeRegime.futureCrossing hedge.symm
        have hloChild : lo ≤ ((E.store cfg ext v q).blocks c).slot := by
          simp only [lo]
          exact Nat.succ_le_of_lt hparentSlotLtQ
        have heLoChild : compute_epoch_at_slot cfg lo ≤
            compute_epoch_at_slot cfg ((E.store cfg ext v q).blocks c).slot :=
          Nat.div_le_div_right hloChild
        have heChildLo : compute_epoch_at_slot cfg
            ((E.store cfg ext v q).blocks c).slot ≤
            compute_epoch_at_slot cfg lo := by
          have hpLo : ((E.store cfg ext v q).blocks
              ((E.store cfg ext v q).blocks c).parent_root).slot ≤ lo := by
            simp only [lo]
            exact Nat.le_succ _
          have hepLo : compute_epoch_at_slot cfg
              ((E.store cfg ext v q).blocks
                ((E.store cfg ext v q).blocks c).parent_root).slot ≤
              compute_epoch_at_slot cfg lo :=
            Nat.div_le_div_right hpLo
          simpa only [get_block_epoch] using hedge.symm.trans_le hepLo
        have heChildEqLo := le_antisymm heChildLo heLoChild
        have hloSigma : lo ≤ sigma := hloLeEs.trans hesLeSigma
        have hwindowLe : compute_epoch_at_slot cfg lo ≤
            compute_epoch_at_slot cfg sigma := Nat.div_le_div_right hloSigma
        have hwindowLt : compute_epoch_at_slot cfg lo <
            compute_epoch_at_slot cfg sigma := lt_of_le_of_ne hwindowLe hsame
        rwa [heChildEqLo]
  exact ⟨lo, es, sigma, querySlot,
    { query_store_eq := hquery
      result_eq := hresult
      confirmation := hcConf
      block_known := hcQ
      parent_known := hparentKnownQ
      parent_eq := hparentQ
      result_to_child := hglcC_Q
      child_to_anchor := hcR0_Q
      parent_slot_lt := hparentSlotLtQ
      child_slot_le_cutoff := hcSlotLeEs
      lo_eq := rfl
      cutoff_eq := rfl
      query_slot_eq := rfl
      sigma_eq := rfl
      confirming_cutoff := hcutoff
      lo_le_cutoff := hloLeEs
      cutoff_le_sigma := hesLeSigma
      start_le_cutoff := hstartLeEs
      sigma_lt_endpoint := hsigmaLt
      lo_horizon := hloH
      cutoff_horizon := hesH
      sigma_horizon := hsigmaH
      regime := hregime }⟩

end Execution

end FastConfirmation.Spec

end
