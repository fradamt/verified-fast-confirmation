module
public import FastConfirmationProofs.FFG.SelectedSource.EndpointJustifiedOrientation
public import FastConfirmationProofs.FFG.SelectedSource.TrustedEndpointJustifiedOrientationHistorical
public import FastConfirmationProofs.FFG.SelectedSource.TrustedEndpointJustifiedOrientationProducer
public import FastConfirmationProofs.FFG.SelectedSource.TrustedSelectedJustifiedOrientationRest

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
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
  have hhistorical : E.HistoricalCurrentTargetCertificateProducerAt cfg ext
      B.anchor (n + 1) query trace.afterObserved trace.result := by
    simpa only [query, trace] using
      E.trusted_completedPrefix_acceptedHistoricalCertificateProducerAt
        cfg ext B hT hC hfit hdomain hanchor hboundary hv hcall hHn1 hprior hinput
          hselector
  have hhistorical' : E.HistoricalCurrentTargetCertificateProducerAt cfg ext
      B.anchor (n + 1) query trace.afterObserved
        (find_latest_confirmed_descendant cfg ext query
          trace.afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hproducer : E.EndpointOriginOrPinnedProducerAt
      cfg ext B.anchor (n + 1) query := by
    simpa only [query] using
      E.trusted_completedPrefix_endpointOriginOrPinnedProducerAt
        cfg ext B hT hC hfit hanchor hboundary hv hHn1
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
  have hout :=
    E.trusted_strictSelected_result_and_child_ancestor_of_endpointJustified_accepted
      cfg ext hA B hT hanchor hboundary hv hHn1 query hquery
      trace.afterObserved hinput' hinputEpoch
      (by simpa only [trace] using hbase) hstrict
      hhistorical' hproducer hw hHm hslotQM hcM hselectedC'
      hselectedKnown' hIH' hnotCovered
  refine ⟨hout.1, ?_⟩
  have hsecond := hout.2
  rw [← hselector.result_eq] at hsecond
  simpa only [trace] using hsecond

end Execution
end FastConfirmation.Spec
end
