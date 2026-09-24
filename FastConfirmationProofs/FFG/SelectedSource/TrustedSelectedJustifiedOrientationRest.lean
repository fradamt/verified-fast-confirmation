module
public import FastConfirmationProofs.FFG.SelectedSource.TrustedSelectedJustifiedOrientation
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem TrustedCausalPrefixFFGInterpretation.endpointJustified_certificate
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    Nonempty (CertifiedJustified cfg E B.anchor
      store.justified_checkpoint) := by
  rcases B.globalJustified_anchor_or_AUEvidence hgen hanchor hstore with
      hfieldAnchor | hevidence
  · rw [hfieldAnchor]
    exact ⟨CertifiedJustified.anchor⟩
  · obtain ⟨hcarrier⟩ := hevidence
    obtain ⟨hincluded⟩ := hcarrier.formed_evidence.certified
    exact ⟨IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      B.state.includedAttestations.relation hincluded⟩

/-! ## Accepted endpoint origin/pinning at the exact selector call site -/

/-- Accepted replacement for the old call-site pinning dispatcher.

Both live gate arms now hand their executable boolean to
`Execution.EndpointOriginOrPinnedProducerAt`, which returns the three-way
endpoint disjunction of `docs/trunkB-two-case-discharge.md` §7 (**N5**/**N6**)
instead of an unconditional pin.  That is the whole content of the change:
the `currentCrossing` arm no longer needs the accepted live-gate certificate
producer, and neither gate arm carries `HonestVotesSupportTarget`.

The `currentHistorical` arm is unchanged and still produces a pin outright —
it was always proviso-free — and `previousEpochStart` is still the executable
short circuit. -/
theorem trusted_epochStart_or_endpointOriginOrPinned_of_acceptedCallSite
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {q : Nat} {query : FastConfirmationStore Root}
    {input result : Root} {w : ValidatorIndex} {m : Nat}
    (hcall : StrictSelectedHistoricalSIRCallSite cfg ext q query input result)
    (hacc : CertificateAccountability cfg E B.anchor)
    (hhistorical' : E.HistoricalCurrentTargetCertificateProducerAt
      cfg ext B.anchor q query input result)
    (hproducer : E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor q query) :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
      E.EndpointOriginOrPinnedAt cfg ext B.anchor q w m
        (get_current_target cfg query.store) := by
  cases hcall with
  | currentCrossing _resultCurrent _a _c _edge hgate =>
      exact Or.inr (hproducer (Or.inr hgate) w m)
  | currentHistorical hresultCurrent hnone =>
      refine Or.inr (Or.inr (Or.inr ?_))
      intro hepoch
      obtain ⟨hJ⟩ :=
        TrustedCausalPrefixFFGInterpretation.endpointJustified_certificate
          cfg ext B hgen hanchor (E.store_causal cfg ext w m)
      obtain ⟨hT⟩ := hhistorical' hresultCurrent hnone
      exact hacc.justified_unique hJ hT hepoch
  | previousEpochStart _resultPrevious hstart =>
      exact Or.inl hstart
  | previousNoConflict _resultPrevious _notStart hgate =>
      exact Or.inr (hproducer (Or.inl hgate) w m)

/-! ## Pre-query SIR and the final non-covered orientation -/

/-- The pre-query vote bracket for one strict selected call, or the case-α
witness that makes it unnecessary.

This is the shared front half of the two Trunk-B consumers.  Three of the four
call-site outcomes supply the bracket — the epoch-start short circuit and arm
3's pin through `preQueryVoteSelectedSIRBracketAt_of_startOrPin`, arm 1
through the trusted-anchor bracket — and arm 2 hands back the post-query
honest target witness instead, which the two proviso-free post-query consumers
of `docs/trunkB-two-case-discharge.md` §3.1 eliminate directly. -/
theorem trusted_preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_acceptedProducers
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hhistorical : E.HistoricalCurrentTargetCertificateProducerAt cfg ext
      B.anchor q query input
      (find_latest_confirmed_descendant cfg ext query input))
    (hproducer : E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor q query)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    E.PreQueryVoteSelectedSIRBracketAt cfg ext q input
        (find_latest_confirmed_descendant cfg ext query input) w m ∨
      E.CausalHonestTargetAt cfg ext q w m := by
  have hcall := E.strictSelectedHistoricalSIRCallSite cfg ext hA
    hv hqH query hquery input hinput hinputEpoch hstrict
  have hacc : CertificateAccountability cfg E B.anchor :=
    E.certificateAccountability_of_selectedMarginAssumptions cfg ext hA
  rcases E.trusted_epochStart_or_endpointOriginOrPinned_of_acceptedCallSite
      cfg ext B hgen hanchor (w := w) (m := m) hcall hacc hhistorical
      hproducer with hstart | hJanchor | hcausal | hpin
  · exact Or.inl (E.preQueryVoteSelectedSIRBracketAt_of_startOrPin cfg ext hA
      hwalkDomain hv hqH query hquery input hinput hinputEpoch hbase hstrict
      hw hslotQM hHm (Or.inl hstart))
  · exact Or.inl
      (E.preQueryVoteSelectedSIRBracketAt_of_trustedAnchorEndpoint cfg ext hA
        hanchor hv hqH query hquery input hinput hstrict hw hslotQM hHm
        hJanchor)
  · exact Or.inr hcausal
  · exact Or.inl (E.preQueryVoteSelectedSIRBracketAt_of_startOrPin cfg ext hA
      hwalkDomain hv hqH query hquery input hinput hinputEpoch hbase hstrict
      hw hslotQM hHm (Or.inr hpin))

/-- Endpoint justified orientation for a non-covered selected child, using
only accepted FFG producers and the selector's carried input safety.

The result is the exact pair consumed by retained endpoint-filter producers:
both the child and the selected result descend the endpoint justified root. -/
theorem trusted_strictSelected_result_and_child_ancestor_of_endpointJustified_accepted
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hhistorical : E.HistoricalCurrentTargetCertificateProducerAt cfg ext
      B.anchor q query input
      (find_latest_confirmed_descendant cfg ext query input))
    (hproducer : E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor q query)
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query input))
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      find_latest_confirmed_descendant cfg ext query input ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query input)) = true)
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
          (find_latest_confirmed_descendant cfg ext query input))
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.trusted_postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  rcases E.trusted_preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_acceptedProducers
      cfg ext hA hwalkDomain B hgenShort hanchor hv hqH query hquery input
      hinput hinputEpoch hbase hstrict hhistorical hproducer hw hslotQM hHm
      with hvoteBracket | hcausal
  · have hpre := E.preQuerySelectedJustifiedCompatibilityAt_of_voteBracket
      cfg ext hA hanchor hv hqH query hquery input hinput hstrict
        hw hslotQM hHm hvoteBracket
    have horigin : E.EndpointJustificationOriginAt
        cfg ext B.anchor w m :=
      TrustedCausalPrefixFFGInterpretation.endpointJustificationOriginAt
        cfg ext B hT hanchor hboundary
    exact E.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
      cfg ext hA hwalkDomain hw hHm hslotQM hcM hselectedC
        hselectedKnown hIH hpre horigin hnotCovered
  · exact E.selected_result_and_child_ancestor_of_causalHonestTarget
      cfg ext hA hwalkDomain hw hHm hslotQM hcM hselectedC hselectedKnown
        hIH hcausal hnotCovered

end Execution
end FastConfirmation.Spec
end
