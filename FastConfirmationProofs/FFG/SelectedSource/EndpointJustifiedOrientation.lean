module
public import FastConfirmationProofs.FFG.SelectedSource.TruncatedPredictionPinning

/-!
Actual-call endpoint orientation uses honest votes strictly before the endpoint.
The slot induction supplies their canonicity. The no-crossing branch retains
its historical producer until the history induction is changed.
-/

@[expose] public section

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root}

/-- A current-epoch strict result fixes the targets at earlier honest votes.
This uses the strict endpoint-slot induction, not the full safety theorem. -/
theorem currentResult_supportBefore_of_endpoint_induction
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hcurrent : get_block_epoch cfg query.store
        (find_latest_confirmed_descendant cfg ext query input) =
      get_current_store_epoch cfg query.store)
    {cutoff : Slot}
    (hknown : ∀ w ∈ E.honest, ∀ k : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ k → E.WithinHorizon cfg k →
      find_latest_confirmed_descendant cfg ext query input ∈ (E.store cfg ext w k).block_roots)
    (hIH : ∀ w ∈ E.honest, ∀ k : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ k → E.slot_at cfg k < cutoff →
      E.WithinHorizon cfg k →
      is_ancestor (E.store cfg ext w k) (get_head cfg (E.store cfg ext w k))
        (get_node_for_root (find_latest_confirmed_descendant cfg ext query input)) = true) :
    E.HonestVotesSupportTargetBefore cfg (get_current_target cfg query.store) q cutoff := by
  obtain ⟨hparent, hwalk, _⟩ := E.store_domainK_of_selectedMarginDomain cfg ext
    hA.wellFormed hA.externals_coherence hA.genesis hA.domain v hv q hqH
  rw [← hquery] at hparent hwalk
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    rw [hquery]
    exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  have hresult := (find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead input hinput).2
  have hheadResult := strictSelectedResult_below_head cfg ext hparent hwalk
    hhead hinput hstrict
  have hcanon := E.canonicalAtHonestVotesBefore_of_endpoint_induction
    cfg ext hA (e := get_current_store_epoch cfg query.store) hknown hIH
  have hresultE := hresult
  rw [hquery] at hresultE
  have hanchorLe : B.anchor.epoch ≤ get_current_store_epoch cfg query.store := by
    have hbound := (E.known_descends_trustedAnchor cfg ext hA hanchor v q hresultE).2
    rwa [← hquery, hcurrent] at hbound
  rw [hquery]
  exact E.currentTarget_supportBefore_of_canonical cfg ext hA hv hqH hresultE
    (by simpa only [hquery] using hcurrent)
    (by simpa only [hquery] using hheadResult)
    (fun w _ k _ r hr => E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory
      cfg ext hT hanchor hboundary w k (by simpa only [hquery] using hanchorLe) hr)
    (by simpa only [hquery] using hcanon)

set_option maxRecDepth 5000 in
/-- The strict endpoint-slot induction pins the endpoint checkpoint using
only earlier votes. The historical branch has a separate producer; the
current crossing and previous-result branches do not read helper provisos. -/
theorem preQueryVoteSelectedSIRBracketAt_of_earlierVotes
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hfloor : cfg.effective_balance_increment ≤ E.weight (E.currentTargetAnchorActive cfg))
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hqH : E.WithinHorizon cfg (n + 1))
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v (n + 1))
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input = get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store input + 1 = get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hhistorical : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query input (find_latest_confirmed_descendant cfg ext query input))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ k : ℕ,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ k → E.WithinHorizon cfg k →
      find_latest_confirmed_descendant cfg ext query input ∈
        (E.store cfg ext w' k).block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ k : ℕ,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ k →
      E.slot_at cfg k < E.slot_at cfg m → E.WithinHorizon cfg k →
      is_ancestor (E.store cfg ext w' k) (get_head cfg (E.store cfg ext w' k))
        (get_node_for_root (find_latest_confirmed_descendant cfg ext query input)) = true) :
    E.PreQueryVoteSelectedSIRBracketAt cfg ext (n + 1) input
      (find_latest_confirmed_descendant cfg ext query input) w m := by
  let result := find_latest_confirmed_descendant cfg ext query input
  have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
    query hquery input hinput hinputEpoch hstrict
  have hresultQ : result ∈ query.store.block_roots := hfacts.result_known
  obtain ⟨hparentQ, hwalkQ, _⟩ := E.store_domainK_of_selectedMarginDomain cfg ext
    hA.wellFormed hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hqH
  rw [← hquery] at hparentQ hwalkQ
  have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
    rw [hquery]
    exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv (n + 1) hqH
  have hheadInput : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root input) = true := by
    rw [hquery]
    exact hbase v hv (n + 1)
      (E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (Nat.le_refl _)) hqH
  have hheadResult := findLatestSelectedResult_below_head cfg ext query
    hparentQ hwalkQ hheadQ input hinput hheadInput
  have hcanon : E.CanonicalAtHonestVotesBefore cfg ext result
      (get_current_store_epoch cfg query.store) (n + 1) (E.slot_at cfg m) :=
    E.canonicalAtHonestVotesBefore_of_endpoint_induction cfg ext hA hselectedKnown hIH
  have hresultE : result ∈ (E.store cfg ext v (n + 1)).block_roots := by
    rwa [hquery] at hresultQ
  have hpin : is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
      ((get_block_epoch cfg query.store result = get_current_store_epoch cfg query.store →
        (E.store cfg ext w m).justified_checkpoint.epoch =
            (get_current_target cfg query.store).epoch →
          (E.store cfg ext w m).justified_checkpoint.root =
            (get_current_target cfg query.store).root) ∧
       (get_block_epoch cfg query.store result + 1 = get_current_store_epoch cfg query.store →
        (E.store cfg ext w m).justified_checkpoint.epoch =
            (get_current_target cfg query.store).epoch →
          E.RootDescends (E.store cfg ext w m).justified_checkpoint.root result)) := by
    by_cases hstart : is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true
    · exact Or.inl hstart
    right
    constructor
    · intro hcurrent hepoch
      by_cases hcross : ∃ a c, CurrentTargetSelectedEdge cfg ext query input a c
      · obtain ⟨a, c, hedge⟩ := hcross
        have hanchorLe : B.anchor.epoch ≤ get_current_store_epoch cfg query.store := by
          have hbound := (E.known_descends_trustedAnchor cfg ext hA hanchor
            v (n + 1) hresultE).2
          rw [← hquery, hcurrent] at hbound
          exact hbound
        have hsupport := E.currentTarget_supportBefore_of_canonical cfg ext hA hv hqH
          hresultE (by simpa only [hquery] using hcurrent)
          (by simpa only [hquery] using hheadResult)
          (fun w' _ k _ r hr => E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory
            cfg ext hT hanchor hboundary w' k (by simpa only [hquery] using hanchorLe) hr)
          (by simpa only [hquery] using hcanon)
        rw [hquery]
        exact E.completedPrefix_currentTarget_endpoint_root_eq_before cfg ext B hT
          hA.static_validators hA.byzantine_bound hfloor hfit hanchor hboundary hv hqH
          (by simpa only [hquery] using hedge.current_target_gate cfg ext)
          hsupport (by simpa only [hquery] using hepoch)
      · obtain ⟨e, htarget, ⟨hpayload⟩⟩ := hhistorical hcurrent hcross
        obtain ⟨hcert⟩ := hpayload.certified
        obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis_structure
        obtain ⟨hJ⟩ := CausalPrefixFFGInterpretation.endpointJustified_certificate
          cfg ext B ⟨ast, ablk, hgen, hslot⟩ hanchor (E.store_causal cfg ext w m)
        rw [← htarget] at hcert
        exact (E.certificateAccountability_of_selectedMarginAssumptions
          cfg ext hA).justified_unique hJ hcert hepoch
    · intro hprevious hepoch
      have hnotCurrent : get_block_epoch cfg query.store result ≠
          get_current_store_epoch cfg query.store := by
        intro heq
        rw [heq] at hprevious
        exact Nat.succ_ne_self _ hprevious
      have hgate := selected_previous_result_no_conflict_gate cfg ext query
        input result rfl hstrict hnotCurrent hstart
      have hboundaryWalk := E.currentEpochBoundaryWalk_of_knownEarlierEpochBlock
        cfg ext hA hv hqH query hquery hresultQ
          (by rw [← hprevious]; exact Nat.lt_succ_self _)
      obtain ⟨hTQ, hdesc⟩ := currentTarget_descends_previousEpochBlock cfg
        hparentQ hwalkQ hheadQ hresultQ hheadResult hboundaryWalk hprevious
      have htargetResult := E.rootDescends_of_store_ancestor
        (by rw [hquery]; exact E.blockProvenance cfg ext v (n + 1)) hparentQ
        (hwalkQ _ hresultQ _ hTQ) hdesc
      have hrslot : ((E.store cfg ext v (n + 1)).blocks result).slot ≤
          compute_start_slot_at_epoch cfg (get_current_store_epoch cfg query.store) := by
        rw [← hquery, ← hprevious]
        unfold get_block_epoch compute_start_slot_at_epoch compute_epoch_at_slot
        exact Nat.le_of_lt (Nat.lt_mul_of_div_lt
          (Nat.lt_succ_self _) cfg.slots_per_epoch_pos)
      have hsupport := E.previousResult_descendSupportBefore_of_canonical cfg ext hA
        hqH hresultE hrslot hcanon
      exact E.completedPrefix_noConflict_endpoint_descends_before cfg ext B hT
        hA.static_validators hA.byzantine_bound hfloor hfit hanchor hboundary hv hqH
        (by simpa only [hquery] using hgate)
        (by simpa only [hquery] using htargetResult)
        (by simpa only [hquery] using hsupport) (by simpa only [hquery] using hepoch)
  intro i hi s k a hs0 hsq _hsm hsH hvote htarget
  exact E.selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning cfg ext hA
    (E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary) hv hqH query hquery input hinput hinputEpoch
    hbase hstrict hw hslotQM hHm hi hs0 hsq hsH hvote htarget hpin

/-! ## Consumer-ready actual-call orientation -/

/-- Feed all three completed-prefix accepted producers into the endpoint
orientation theorem for one actual strict selector call.

The remaining premises are precisely the outer safety-induction inputs: the
carried input `SafeFrom`, selected-result relay/IH, the concrete child edge at
the endpoint, and noncoverage.  No FFG pipeline, filter conclusion, or
historical-certificate premise remains. -/
theorem actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hinvariant : E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n))
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.getLatestConfirmedTraceAt cfg ext v n).result)
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (E.getLatestConfirmedTraceAt cfg ext v n).result) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root c)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.getLatestConfirmedTraceAt cfg ext v n).result)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true := by
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.static_validators
      byzantine_bound := hC.byzantine_bound
      domain := hdomain }
  have hquery : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hinput' : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, trace] using hinput
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hinputUpper : get_block_epoch cfg query.store trace.afterObserved ≤
      get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (by
      rw [hquery]
      simpa only [E.store_current_slot] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          v (n + 1) trace.afterObserved
            (by simpa only [hquery] using hinput'))
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    rcases Nat.eq_or_lt_of_le hinputUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_iff.mpr hlt) hselector.input_recent)
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input
      (hselector.result_eq.trans hfixed)
  have hhistorical : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query trace.afterObserved trace.result := by
    simpa only [query, trace] using
      E.completedPrefix_acceptedHistoricalA32PayloadProducerAt
        cfg ext B hT hC hfit hanchor hboundary hv hcall hHn1 hinput hinvariant hselector
  have hhistorical' : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query trace.afterObserved
        (find_latest_confirmed_descendant cfg ext query
          trace.afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hselectedC' : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query trace.afterObserved))
      (get_node_for_root c) = true := by
    rw [← hselector.result_eq]
    simpa only [trace] using hselectedC
  have hselectedKnown' : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      find_latest_confirmed_descendant cfg ext query trace.afterObserved ∈
        (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hstart hm'H
    rw [← hselector.result_eq]
    exact hselectedKnown w' hw' m' hstart hm'H
  have hIH' : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query
            trace.afterObserved)) = true := by
    intro w' hw' m' hstart hm'Lt hm'H
    rw [← hselector.result_eq]
    exact hIH w' hw' m' hstart hm'Lt hm'H
  have hvoteBracket := E.preQueryVoteSelectedSIRBracketAt_of_earlierVotes
    cfg ext hA B hT hC.balance_floor hfit hanchor hboundary hv hHn1
    query hquery trace.afterObserved hinput' hinputEpoch
    (by simpa only [trace] using hbase) hstrict hhistorical'
    hw hslotQM hHm hselectedKnown' hIH'
  have hbracket := E.preQuerySelectedSIRBracketAt_of_voteBracket_strict
    cfg ext hA hanchor hv hHn1 query hquery trace.afterObserved hinput' hstrict
    hw hslotQM hHm hvoteBracket
  have hpre := E.preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket
    cfg ext hA hv hHn1 query hquery trace.afterObserved hinput' hstrict
    hw hslotQM hHm hbracket
  have hout := E.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
    cfg ext hA
    (E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary) hw hHm hslotQM hcM hselectedC'
    hselectedKnown' hIH' hpre
    (CausalPrefixFFGInterpretation.endpointJustificationOriginAt
      cfg ext B hT hanchor hboundary) hnotCovered
  refine ⟨hout.1, ?_⟩
  have hsecond := hout.2
  rw [← hselector.result_eq] at hsecond
  simpa only [trace] using hsecond

end Execution


end FastConfirmation.Spec

end
