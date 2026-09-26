module
public import FastConfirmationInternal.FCRRule.PredictionSupport
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.FFG.Certificates.CurrentTargetCertificateRealization
public import FastConfirmationProofs.Execution.History.HistoricalCurrentTargetTrajectory

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted selected-result / endpoint-justification orientation

This module replaces the two legacy inputs used by the pre-query SIR
consumer:

* endpoint justification is obtained from the accepted global-`J` trajectory,
  rather than from `EndpointFFGPipeline`; and
* the current and historical current-target certificates are supplied by the
  accepted gate and retained-payload producers.

The carried `SafeFrom` premise below is the selector's normative input
invariant.  It is not inferred from the selected-result induction hypothesis:
that hypothesis is strict in the endpoint slot, whereas the below-input SIR
region needs the endpoint's current head to descend the carried input.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

/-! ## Accepted endpoint justification evidence -/

/-- The accepted global justified selector supplies the existing causal
endpoint-origin interface.

The non-anchor arm retains the actual ground vote from the accepted formation
carrier.  Thus downstream SIR code may use the old vote-shaped eliminator,
but callers no longer assume a raw vote/store relation. -/
theorem ScheduledFFGInterpretation.endpointJustificationOriginAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : Nat} :
    E.EndpointJustificationOriginAt cfg ext B.anchor w m := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hslotZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext w 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg hT.whole_seconds]
      at hcurrent0
    exact hcurrent0.symm
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [InitialAnchorAtEpochBoundary, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.ScheduledPrefixStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
      hfieldAnchor | hevidence
  · exact Or.inl hfieldAnchor
  · by_cases hne :
        (E.store cfg ext w m).justified_checkpoint = B.anchor
    · exact Or.inl hne
    · right
      obtain ⟨hcarrier⟩ := hevidence
      have hcausal := hcarrier.formed_evidence.causal.resolve_left hne
      obtain ⟨carrierBlock, hcarrierAt, i, hiHonest, voteSlot,
          groundTime, groundVote, hvoteBeforeCarrier, hvoteSlotH,
          hvoteGround, hgroundSlot, hgroundTarget, hincluded⟩ := hcausal
      obtain ⟨_hincludedCarrier, _hincludedDesc, hincludedAt⟩ := hincluded
      have hincludedEvidence :=
        B.state.includedAttestations.evidence hincludedAt
      obtain ⟨hcertified⟩ := hcarrier.formed_evidence.certified
      have hanchorLt : B.anchor.epoch <
          (E.store cfg ext w m).justified_checkpoint.epoch :=
        CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
          (IncludedCertifiedJustified.toCertifiedJustified
            (cfg := cfg)
            (Execution.AcceptedBlockAttestationInclusion.relation
              cfg ext E B.state.includedAttestations) hcertified) hne
      have htargetEpoch : (E.store cfg ext w m).justified_checkpoint.epoch =
          compute_epoch_at_slot cfg voteSlot := by
        rw [← hgroundTarget, ← hgroundSlot]
        exact hincludedEvidence.target_epoch
      have hstartMono : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
          compute_start_slot_at_epoch cfg
            (E.store cfg ext w m).justified_checkpoint.epoch :=
        Nat.mul_le_mul_right cfg.slots_per_epoch hanchorLt.le
      have hstartVote : compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).justified_checkpoint.epoch ≤ voteSlot := by
        have hmulDiv := Nat.div_mul_le_self voteSlot cfg.slots_per_epoch
        have hdiv : voteSlot / cfg.slots_per_epoch =
            (E.store cfg ext w m).justified_checkpoint.epoch := by
          simpa only [compute_epoch_at_slot] using htargetEpoch.symm
        rw [hdiv] at hmulDiv
        simpa only [compute_start_slot_at_epoch] using hmulDiv
      have hfromZero : E.slot_at cfg 0 ≤ voteSlot := by
        calc
          E.slot_at cfg 0 = ast.slot := hslotZero
          _ = ablk.message.slot := hslot
          _ ≤ compute_start_slot_at_epoch cfg B.anchor.epoch := hboundary'
          _ ≤ compute_start_slot_at_epoch cfg
              (E.store cfg ext w m).justified_checkpoint.epoch := hstartMono
          _ ≤ voteSlot := hstartVote
      have hcarrierRoot : E.ExecutionRoot hcarrier.carrier := by
        obtain ⟨carrierStore, hcarrierStore, hcarrierStoreKnown,
            _hcarrierStoreBlock⟩ := hcarrierAt
        rcases hcarrierStore.blockProvenance cfg ext E hcarrier.carrier
            hcarrierStoreKnown with hgenCarrier |
            ⟨sb, ⟨sw, sn, hsched⟩, hroot, hblock⟩
        · exact ⟨carrierStore.blocks hcarrier.carrier,
            Or.inl ⟨hgenCarrier.1, hgenCarrier.2⟩⟩
        · exact ⟨carrierStore.blocks hcarrier.carrier,
            Or.inr ⟨sw, sn, sb, hsched, hroot, hblock.symm⟩⟩
      have hcarrierKnown : hcarrier.carrier ∈
          (E.store cfg ext w m).block_roots :=
        (E.store_known_ancestor_of_rootDescends_for_storeReflection
          cfg ext hT.wellFormed hT.externals_coherence hgenEq hslot hparent
          hcarrier.tip_carrier.known hcarrierRoot
            hcarrier.tip_descends_carrier).1
      have hcarrierAgreement : carrierBlock =
          (E.store cfg ext w m).blocks hcarrier.carrier :=
        hcarrierAt.unique cfg ext E hT.wellFormed
          (E.acceptedBlockAt_of_causal_known cfg ext hstore hcarrierKnown)
      have hvoteBeforeEndpoint : voteSlot < E.slot_at cfg m := by
        calc
          voteSlot < carrierBlock.slot := hvoteBeforeCarrier
          _ = ((E.store cfg ext w m).blocks hcarrier.carrier).slot :=
            congrArg BeaconBlock.slot hcarrierAgreement
          _ ≤ get_current_slot cfg (E.store cfg ext w m) :=
            E.store_blocks_slot_le_current cfg ext hT.whole_seconds
              hgenShort w m hcarrier.carrier hcarrierKnown
          _ = E.slot_at cfg m := E.store_current_slot cfg ext w m
      exact ⟨i, hiHonest, voteSlot, groundTime, groundVote,
        hfromZero, hvoteBeforeEndpoint, hvoteSlotH, hvoteGround,
        hgroundTarget⟩

/-- Every accepted endpoint justified field has a concrete certificate.

Only the certificate field of the old endpoint pipeline is needed for SIR
pinning, so the broader endpoint geometry record is not reconstructed. -/
theorem ScheduledFFGInterpretation.endpointJustified_certificate
    (B : ScheduledFFGInterpretation cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store) :
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
      (Execution.AcceptedBlockAttestationInclusion.relation
        cfg ext E B.state.includedAttestations) hincluded⟩

/-! ## Accepted certificate pinning at the exact selector call site -/

/-- Accepted replacement for
`epochStart_or_endpointCurrentTargetPinned_of_callSite`.

It consumes only the accepted endpoint certificate, the accepted live-gate
producer, the retained historical payload producer, and concrete no-conflict
pinning.  In particular it has no `EndpointFFGPipeline` premise. -/
theorem epochStart_or_endpointCurrentTargetPinned_of_acceptedCallSite
    (B : ScheduledFFGInterpretation cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {q : Nat} {query : FastConfirmationStore Root}
    {input result : Root} {store : Store Root}
    (hstore : E.ScheduledPrefixStore cfg ext store)
    (hcall : StrictSelectedHistoricalSIRCallSite
      cfg ext E q query input result)
    (hacc : CertificateAccountability cfg E B.anchor)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : E.AcceptedHistoricalA32PayloadProducerAt
      cfg ext B query input result)
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
    (htargetResult : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store →
      E.RootDescends (get_current_target cfg query.store).root result)
    (hguard : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store →
      CurrentTargetLateBoundaryCarrierGuard cfg query.store) :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
      ((get_block_epoch cfg query.store result =
          get_current_store_epoch cfg query.store →
        store.justified_checkpoint.epoch =
            (get_current_target cfg query.store).epoch →
          store.justified_checkpoint.root =
            (get_current_target cfg query.store).root) ∧
       (get_block_epoch cfg query.store result + 1 =
          get_current_store_epoch cfg query.store →
        store.justified_checkpoint.epoch =
            (get_current_target cfg query.store).epoch →
          E.RootDescends store.justified_checkpoint.root result)) := by
  have hcurrent' : E.CurrentTargetCertificateProducerAt
      cfg ext B.anchor q query :=
    E.acceptedCurrentTargetCertificateProducerAt_of_gateProducer
      cfg ext B hcurrent
  have hhistorical' : E.HistoricalCurrentTargetCertificateProducerAt
      cfg ext B.anchor q query input result :=
    E.acceptedHistoricalA32PayloadProducerAt_to_certificateProducer
      cfg ext B hhistorical
  obtain ⟨hJ⟩ :=
    ScheduledFFGInterpretation.endpointJustified_certificate
      cfg ext B hgen hanchor hstore
  cases hcall with
  | currentCrossing resultCurrent _a _c _edge hgate hsupport =>
      right
      constructor
      · intro _ hepoch
        obtain ⟨hT⟩ := hcurrent' hgate hsupport (hguard resultCurrent)
        exact hacc.justified_unique hJ hT hepoch
      · intro hprevious
        rw [resultCurrent] at hprevious
        exact False.elim (Nat.succ_ne_self _ hprevious)
  | currentHistorical hresultCurrent hnone =>
      right
      constructor
      · intro _ hepoch
        obtain ⟨hT⟩ := hhistorical' hresultCurrent hnone
        exact hacc.justified_unique hJ hT hepoch
      · intro hprevious
        rw [hresultCurrent] at hprevious
        exact False.elim (Nat.succ_ne_self _ hprevious)
  | previousEpochStart _resultPrevious hstart =>
      exact Or.inl hstart
  | previousNoConflict resultPrevious _notStart hgate hsupport =>
      right
      constructor
      · intro hcurrent
        rw [hcurrent] at resultPrevious
        exact False.elim (Nat.succ_ne_self _ resultPrevious)
      · intro _ hepoch
        exact hnoConflict result (htargetResult resultPrevious) hgate hsupport
          store.justified_checkpoint hJ hepoch

/-! ## Pre-query SIR and the final non-covered orientation -/

/-- Accepted producer for the non-anchor pre-query SIR bracket.

The pointwise raw vote is bound only by `PreQueryVoteSelectedSIRBracketAt`;
the exported caller obtains that predicate from accepted global-`J` origin.
All certificate production and endpoint certification are accepted-state
facts. -/
theorem preQueryVoteSelectedSIRBracketAt_of_acceptedProducers
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : ScheduledFFGInterpretation cfg ext E)
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
    (hprovisos : SelectedPredictionVoteSupport cfg ext E v q query input)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query input (find_latest_confirmed_descendant cfg ext query input))
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    E.PreQueryVoteSelectedSIRBracketAt cfg ext q input
      (find_latest_confirmed_descendant cfg ext query input) w m := by
  intro i hi s k a hs0 hsq _hsm hsH hvote htarget
  have hcall := E.strictSelectedHistoricalSIRCallSite cfg ext hA
    hv hqH query hquery input hinput hinputEpoch hstrict hprovisos
  have hacc : CertificateAccountability cfg E B.anchor :=
    E.certificateAccountability_of_selectedMarginAssumptions cfg ext hA
  have htargetResult : get_block_epoch cfg query.store
        (find_latest_confirmed_descendant cfg ext query input) + 1 =
      get_current_store_epoch cfg query.store →
      E.RootDescends (get_current_target cfg query.store).root
        (find_latest_confirmed_descendant cfg ext query input) := by
    intro hprevious
    obtain ⟨hwfQ, hwalkQ, _⟩ :=
      E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
        hA.externals_coherence hA.genesis hA.domain v hv q hqH
    rw [← hquery] at hwfQ hwalkQ
    have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
      rw [hquery]
      exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
    have hheadInput : is_ancestor query.store (get_head cfg query.store)
        (get_node_for_root input) = true := by
      rw [hquery]
      exact hbase v hv q
        (E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (Nat.le_refl _)) hqH
    have hheadResult := findLatestSelectedResult_below_head cfg ext query
      hwfQ hwalkQ hheadQ input hinput hheadInput
    have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
      query hquery input hinput hinputEpoch hstrict
    have hboundaryWalk :=
      E.currentEpochBoundaryWalk_of_knownEarlierEpochBlock cfg ext hA hv hqH
        query hquery hfacts.result_known
          (by rw [← hprevious]; exact Nat.lt_succ_self _)
    obtain ⟨hTQ, hdesc⟩ := currentTarget_descends_previousEpochBlock cfg
      hwfQ hwalkQ hheadQ hfacts.result_known hheadResult hboundaryWalk hprevious
    exact E.rootDescends_of_store_ancestor
      (by rw [hquery]; exact E.blockProvenance cfg ext v q) hwfQ
      (hwalkQ _ hfacts.result_known _ hTQ) hdesc
  have hguard : get_block_epoch cfg query.store
        (find_latest_confirmed_descendant cfg ext query input) =
      get_current_store_epoch cfg query.store →
      CurrentTargetLateBoundaryCarrierGuard cfg query.store := by
    intro hcur _
    obtain ⟨hwfQ, hwalkQ, _⟩ :=
      E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
        hA.externals_coherence hA.genesis hA.domain v hv q hqH
    rw [← hquery] at hwfQ hwalkQ
    have hheadQ : (get_head cfg query.store).root ∈ query.store.block_roots := by
      rw [hquery]
      exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
    have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
      query hquery input hinput hinputEpoch hstrict
    exact ⟨_, hfacts.result_known, hcur,
      strictSelectedResult_below_head cfg ext hwfQ hwalkQ hheadQ hinput hstrict⟩
  have hstartOrPin :=
    E.epochStart_or_endpointCurrentTargetPinned_of_acceptedCallSite
      cfg ext B hgen hanchor (E.store_causal cfg ext w m)
      hcall hacc hcurrent hhistorical hnoConflict htargetResult hguard
  exact E.selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning
    cfg ext hA hwalkDomain hv hqH query hquery input hinput hinputEpoch
      hbase hstrict hw hslotQM hHm hi hs0 hsq hsH hvote htarget
      hstartOrPin

/-- Complete accepted pre-query compatibility for one strict selected call.

The trusted-anchor arm is discharged by the executable trajectory; the
non-anchor arm uses the accepted producer above. -/
theorem preQuerySelectedJustifiedCompatibilityAt_of_acceptedProducers
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : ScheduledFFGInterpretation cfg ext E)
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
    (hprovisos : SelectedPredictionVoteSupport cfg ext E v q query input)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query input (find_latest_confirmed_descendant cfg ext query input))
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    E.PreQuerySelectedJustifiedCompatibilityAt cfg ext B.anchor q
      (find_latest_confirmed_descendant cfg ext query input) w m := by
  have hvoteBracket :=
    E.preQueryVoteSelectedSIRBracketAt_of_acceptedProducers cfg ext hA
      hwalkDomain B hgen hanchor hv hqH query hquery input hinput
      hinputEpoch hbase hstrict hprovisos hcurrent hhistorical hnoConflict
      hw hslotQM hHm
  have hbracket := E.preQuerySelectedSIRBracketAt_of_voteBracket_strict
    cfg ext hA hanchor hv hqH query hquery input hinput hstrict
      hw hslotQM hHm hvoteBracket
  exact E.preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket
    cfg ext hA hv hqH query hquery input hinput hstrict hw hslotQM hHm
      hbracket

/-- Endpoint justified orientation for a non-covered selected child, using
only accepted FFG producers and the selector's carried input safety.

The result is the exact pair consumed by retained endpoint-filter producers:
both the child and the selected result descend the endpoint justified root. -/
theorem strictSelected_result_and_child_ancestor_of_endpointJustified_accepted
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
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
    (hprovisos : SelectedPredictionVoteSupport cfg ext E v q query input)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query input (find_latest_confirmed_descendant cfg ext query input))
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
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
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hpre :=
    E.preQuerySelectedJustifiedCompatibilityAt_of_acceptedProducers
      cfg ext hA hwalkDomain B hgenShort hanchor hv hqH query hquery
      input hinput hinputEpoch hbase hstrict hprovisos hcurrent
      hhistorical hnoConflict hw hslotQM hHm
  have horigin : E.EndpointJustificationOriginAt
      cfg ext B.anchor w m :=
    ScheduledFFGInterpretation.endpointJustificationOriginAt
      cfg ext B hT hanchor hboundary
  exact E.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
    cfg ext hA hwalkDomain hw hHm hslotQM hcM hselectedC
      hselectedKnown hIH hpre horigin hnotCovered

end Execution


end FastConfirmation.Spec

end
