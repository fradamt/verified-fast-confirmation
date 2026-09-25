module
public import FastConfirmationProofs.FFG.SelectedSource.EarlyPhaseSource
public import FastConfirmationProofs.FFG.SelectedSource.TrustedPhaseSourceCarriers
public import FastConfirmationProofs.Execution.Delivery.TrustedEarlyPhaseSourceDelivery
public import FastConfirmationProofs.Checkpoints.TrustedProcessedResetCheckpointRealization
public import FastConfirmationProofs.Checkpoints.TrustedDeadlineCarrierAdoption
public import FastConfirmationProofs.FFG.State.TrustedFinalizationTiming

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

private def selectedMarginAssumptions_of_earlyPhaseInputs
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E) :
    SelectedMarginAssumptions cfg ext E :=
  { genesis := hT.genesis_structure
    wellFormed := hT.wellFormed
    whole_seconds := hT.whole_seconds
    honest_behavior := hT.honest_behavior
    synchrony := hsync
    externals_coherence := hT.externals_coherence
    static_validators := hstatic
    byzantine_bound := hbyz
    domain := hdomain }

theorem trusted_recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hgenSlot : ast.slot = ablk.message.slot)
    (hgenParent : ablk.message.parent_root ≠ ablk.root)
    {query : Store Root} {w : ValidatorIndex} {m : Nat}
    {selected seed : Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext (E.store cfg ext w m))
    (hqueryParent : ParentSlotLt query)
    (hqueryProvenance : BlockProvenance E query)
    (hqueryWalk : WalkKnown query (query.blocks selected).slot seed)
    (hselectedQ : selected ∈ query.block_roots)
    (hseedQ : seed ∈ query.block_roots)
    (hseedM : seed ∈ (E.store cfg ext w m).block_roots)
    (hseedSelectedQ : is_ancestor query (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hclock : get_current_store_epoch cfg query ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query)
    (hrecentQ : (get_voting_source cfg query seed).epoch + 2 ≥
      get_current_store_epoch cfg query) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      hqueryWalk hseedSelectedQ
  have hselectedRoot : E.ExecutionRoot selected := by
    refine ⟨query.blocks selected, ?_⟩
    rcases hqueryProvenance selected hselectedQ with hgenesis | hsched
    · exact Or.inl ⟨hgenesis.1, hgenesis.2⟩
    · obtain ⟨sb, ⟨u, k, hscheduled⟩, hroot, hmessage⟩ := hsched
      exact Or.inr ⟨u, k, sb, hscheduled, hroot, hmessage.symm⟩
  obtain ⟨_hselectedM, hseedSelectedM⟩ :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hwf hec hgen hgenSlot hgenParent hseedM hselectedRoot hsemantic
  have hsourceMono := E.trusted_acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hwf hquery hendpoint hseedQ hseedM hclock
  refine ⟨seed, hseedM, hseedSelectedM, ?_⟩
  rw [hsameEpoch]
  exact hrecentQ.trans (Nat.add_le_add_right hsourceMono 2)

theorem StrictSelectedResultMechanicalFacts.trusted_fcrStep_previous_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    {input result : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStoreAtCall cfg ext v n) input result)
    (hprevious : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store result + 1 =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnm : n + 1 ≤ m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) result := by
  let hA := E.selectedMarginAssumptions_of_earlyPhaseInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hnH : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hn1H
  have hslotForward : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    E.slot_at_mono cfg hnm
  have hqueryCausal : E.CausalStore cfg ext
      (E.fcrStoreAtCall cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure hdomain v hv (n + 1) hn1H
  have hqueryParent : ParentSlotLt (E.fcrStoreAtCall cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hqueryProvenance : BlockProvenance E
      (E.fcrStoreAtCall cfg ext v n).store := by
    simpa only [E.fcrStep_store] using E.blockProvenance cfg ext v (n + 1)
  have hqueryWalk : ∀ t ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStoreAtCall cfg ext v n).store
          ((E.fcrStoreAtCall cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hclock : get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store ≤
      get_current_store_epoch cfg (E.store cfg ext w m) :=
    Nat.le_of_eq hsameEpoch.symm
  rcases h.trace_origin with
    ⟨_a, _hedge, _hentry, hrecent, hdesc⟩ |
      ⟨_a, _hedge, _hentry, hfinal⟩
  · have hseedQ := E.fcrStep_previousSlotHead_known cfg ext
      hT.genesis_structure hdomain v hv n hn1H
    have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
      unfold IsScheduledFCRCallAt at hcall
      simpa only [E.store_current_slot cfg ext v (n + 1),
        E.store_current_slot cfg ext v n] using hcall
    have hgenTime : E.genesis_store.genesis_time ≤
        E.genesis_store.time := by
      rw [hgen]
      exact (wellFormedStore_get_forkchoice_store cfg ast ablk
        hgenSlot hgenParent).time_ge_genesis
    obtain ⟨origin, horiginLe, horiginSlot, horiginDeadline,
        hseedOrigin⟩ :=
      E.fcr_currentSlotHead_deadline_origin cfg ext hT.whole_seconds
        hgenTime hT.genesis_structure hdomain v hv n hnH
    have horiginH : E.WithinHorizon cfg origin :=
      E.withinHorizon_mono cfg (horiginLe.trans (Nat.le_succ n)) hn1H
    have hseedOrigin' : (E.fcrStoreAtCall cfg ext v n).previous_slot_head ∈
        (E.store cfg ext v origin).block_roots := by
      rw [E.fcrStep_previousSlotHead_eq_currentSlotHead]
      exact hseedOrigin
    have hstartCall : E.slot_start cfg (E.slot_at cfg (n + 1)) =
        n + 1 :=
      E.scheduled_fcr_call_at_slot_start cfg ext hT.whole_seconds
        hgenTime hcall
    have hstartTarget : E.slot_start cfg (E.slot_at cfg origin + 1) ≤ m := by
      have hslot : E.slot_at cfg origin + 1 ≤ E.slot_at cfg (n + 1) := by
        rw [horiginSlot]
        exact Nat.succ_le_of_lt hslotAdvance
      exact (E.slot_start_mono cfg hslot).trans
        (hstartCall.le.trans hnm)
    have hrelayOutcome :
        (E.fcrStoreAtCall cfg ext v n).previous_slot_head ∈
          (E.store cfg ext w m).block_roots ∨
        PermanentBlockExclusion cfg ext E v origin
          (E.fcrStoreAtCall cfg ext v n).previous_slot_head w
            m :=
      E.deadline_block_relay_at_endpoint cfg ext hsync.deadline_block_relay v hv origin _ horiginH
        hseedOrigin' horiginDeadline w hw m hmH hstartTarget
        (lt_of_le_of_lt horiginLe (Nat.lt_succ_self n) |>.trans_le hnm)
    let target := get_voting_source cfg
      (E.fcrStoreAtCall cfg ext v n).store
      (E.fcrStoreAtCall cfg ext v n).previous_slot_head
    have hsourceAU : B.state.AU cfg ext
        (E.fcrStoreAtCall cfg ext v n).previous_slot_head target := by
      exact hqueryCausal.trusted_getVotingSource_AU cfg ext B hseedQ
    have hreal := E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := w) m
    have hfinalizedKnown : (E.store cfg ext w m).finalized_checkpoint.root ∈
        (E.store cfg ext w m).block_roots := hreal.root_known
    have hanchorLe : B.anchor.epoch ≤
        (E.store cfg ext w m).finalized_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg)
        (Classical.choice hreal.certified)
    have hLag : E.TrustedCausalRealizedFinalizationLag cfg ext B :=
      E.trustedCausalRealizedFinalizationLag_of_acceptedDelay
        cfg ext B hT hanchor hDelay
    have htargetEpoch : (E.store cfg ext w m).finalized_checkpoint.epoch ≤
        target.epoch := by
      rcases hLag hendpointCausal with hFanchor | hFdelay
      · obtain ⟨_carrier, _hdesc, hformed⟩ := hsourceAU
        obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
        have hcert : CertifiedJustified cfg E B.anchor target :=
          IncludedCertifiedJustified.toCertifiedJustified (cfg := cfg)
            B.state.includedAttestations.relation hincluded
        rw [hFanchor]
        exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
      · change target.epoch + 2 ≥ get_current_store_epoch cfg
          (E.fcrStoreAtCall cfg ext v n).store at hrecent
        rw [hsameEpoch] at hFdelay
        exact (Nat.add_le_add_iff_right).mp (hFdelay.trans hrecent)
    have hseedWalk : WalkKnown (E.store cfg ext v origin)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch)
        (E.fcrStoreAtCall cfg ext v n).previous_slot_head :=
      E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
        v origin hanchorLe hseedOrigin'
    have hnotExcluded : ¬ PermanentBlockExclusion cfg ext E v origin
        (E.fcrStoreAtCall cfg ext v n).previous_slot_head w m :=
      E.trusted_acceptedSourceTip_not_permanentlyExcluded_of_AU cfg ext B hT hA
        hanchor hboundary P V hanchorExact hacc hmH hseedOrigin'
        hfinalizedKnown hanchorLe hsourceAU htargetEpoch hseedWalk
    have hseedM : (E.fcrStoreAtCall cfg ext v n).previous_slot_head ∈
        (E.store cfg ext w m).block_roots := by
      rcases hrelayOutcome with hknown | hexcluded
      · exact hknown
      · exact False.elim (hnotExcluded hexcluded)
    exact E.trusted_recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
      cfg ext B hT.wellFormed hT.externals_coherence
      hgen hgenSlot hgenParent hqueryCausal hendpointCausal
      hqueryParent hqueryProvenance
      (hqueryWalk result h.result_known _ hseedQ)
      h.result_known hseedQ hseedM hdesc hclock hsameEpoch hrecent
  · unfold TentativeSelectedResultWitness at hfinal
    rcases hfinal with hcurrent | ⟨hrecent, _houter⟩
    · have hbad : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store result + 1 =
          get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store result :=
        hprevious.trans hcurrent.symm
      exact False.elim ((Nat.ne_of_gt (Nat.lt_succ_self _)) hbad)
    · have hselectedQ : result ∈
          (E.store cfg ext v (n + 1)).block_roots := by
        simpa only [E.fcrStep_store] using h.result_known
      have hparentQ : ((E.store cfg ext v (n + 1)).blocks result).parent_root ∈
          (E.store cfg ext v (n + 1)).block_roots := by
        simpa only [E.fcrStep_store] using h.parent_known
      obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
        E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA
          v hv (n + 1) (E.fcrStoreAtCall cfg ext v n)
          (E.fcrStep_store cfg ext v n) result hn1H
          hselectedQ hparentQ h.confirmed
      obtain ⟨u, nu, d, hu, hHnu, hslot, hdeadline, _hhead,
          hd, hdQuery, hanc⟩ :=
        E.past_descendant_of_honest_supporter_known_minimal cfg ext hA
          v hv (n + 1) result hn1H i hi lm hlm hsupp
      obtain ⟨hselectedOrigin, hrelayOutcome⟩ :=
        E.mem_or_excluded_of_known_honest_past_descendant_minimal
          cfg ext hA v hv (n + 1) result hn1H hselectedQ
          w hw m hslotForward hmH u hu nu hHnu d hslot hdeadline
          hd hdQuery hanc
      let target := get_voting_source cfg
        (E.fcrStoreAtCall cfg ext v n).store result
      have hsourceAU : B.state.AU cfg ext result target :=
        hqueryCausal.trusted_getVotingSource_AU cfg ext B h.result_known
      have hreal := E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
        cfg ext B hT hanchor hboundary (w := w) m
      have hfinalizedKnown : (E.store cfg ext w m).finalized_checkpoint.root ∈
          (E.store cfg ext w m).block_roots := hreal.root_known
      have hanchorLe : B.anchor.epoch ≤
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg)
          (Classical.choice hreal.certified)
      have hLag : E.TrustedCausalRealizedFinalizationLag cfg ext B :=
        E.trustedCausalRealizedFinalizationLag_of_acceptedDelay
          cfg ext B hT hanchor hDelay
      have htargetEpoch : (E.store cfg ext w m).finalized_checkpoint.epoch ≤
          target.epoch := by
        rcases hLag hendpointCausal with hFanchor | hFdelay
        · obtain ⟨_carrier, _hdesc, hformed⟩ := hsourceAU
          obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
          have hcert : CertifiedJustified cfg E B.anchor target :=
            IncludedCertifiedJustified.toCertifiedJustified (cfg := cfg)
              B.state.includedAttestations.relation hincluded
          rw [hFanchor]
          exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
        · change target.epoch + 2 ≥ get_current_store_epoch cfg
            (E.fcrStoreAtCall cfg ext v n).store at hrecent
          rw [hsameEpoch] at hFdelay
          exact (Nat.add_le_add_iff_right).mp (hFdelay.trans hrecent)
      have hselectedWalk : WalkKnown (E.store cfg ext u nu)
          (compute_start_slot_at_epoch cfg
            (E.store cfg ext w m).finalized_checkpoint.epoch) result :=
        E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
          u nu hanchorLe hselectedOrigin
      have hnotExcluded : ¬ PermanentBlockExclusion cfg ext E u nu result w m :=
        E.trusted_acceptedSourceTip_not_permanentlyExcluded_of_AU cfg ext B hT hA
          hanchor hboundary P V hanchorExact hacc hmH hselectedOrigin
          hfinalizedKnown hanchorLe hsourceAU htargetEpoch hselectedWalk
      have hselectedM : result ∈ (E.store cfg ext w m).block_roots := by
        rcases hrelayOutcome with hknown | hexcluded
        · exact hknown
        · exact False.elim (hnotExcluded hexcluded)
      exact E.trusted_recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
        cfg ext B hT.wellFormed hT.externals_coherence
        hgen hgenSlot hgenParent hqueryCausal hendpointCausal
        hqueryParent hqueryProvenance
        (hqueryWalk result h.result_known result h.result_known)
        h.result_known h.result_known hselectedM
        (is_ancestor_refl _ _) hclock hsameEpoch hrecent

/-- Actual `fcrStoreAtCall` current/next cell. Epoch-start exclusion is derived
from the narrow honest past-descendant witness. The one Lemma-13 seed is
transported to the endpoint; its selected ancestor follows from the accepted
parent chain there. -/
theorem StrictSelectedResultMechanicalFacts.trusted_fcrStep_currentNext_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    {input result : Root}
    (hinput : input ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext
      (E.fcrStoreAtCall cfg ext v n) input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStoreAtCall cfg ext v n) input result)
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store result =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store + 1) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) result := by
  let hA := E.selectedMarginAssumptions_of_earlyPhaseInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hqueryCausal : E.CausalStore cfg ext
      (E.fcrStoreAtCall cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure hdomain v hv (n + 1) hn1H
  have hqueryParent : ParentSlotLt (E.fcrStoreAtCall cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hqueryWalk : ∀ t ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStoreAtCall cfg ext v n).store
          ((E.fcrStoreAtCall cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStoreAtCall cfg ext v n).store).root ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
    simpa only [E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hn1H
  have hpast := h.confirmedPastDescendantSlotWitness cfg ext hA hv hn1H
    (E.fcrStep_store cfg ext v n)
  have hnotStart := h.not_epochStart_of_current cfg ext
    (q := n + 1)
    (by rw [E.fcrStep_store, E.store_current_slot cfg ext v (n + 1)])
    hqueryParent hqueryWalk hpast hcurrent
  have hlemma := h.trusted_current_lemma13SourceSeed_of_notStart cfg ext B
    hqueryCausal hqueryParent hqueryWalk hhead hinput hout hstrict hcurrent
      hnotStart
  have hnextSlots : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) + 1 := by
    simpa only [get_current_store_epoch, E.fcrStep_store,
      E.store_current_slot cfg ext w m,
      E.store_current_slot cfg ext v (n + 1)] using hnextEpoch
  have hslotLt : E.slot_at cfg (n + 1) < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg (n + 1) :=
      Nat.le_of_not_gt hnot
    have hepochLe := ce_mono cfg hle
    rw [hnextSlots] at hepochLe
    exact (Nat.not_succ_le_self _) hepochLe
  have hrelayGate : E.slot_at cfg (n + 1) + 1 ≤
      E.slot_at cfg (m + 1) :=
    (Nat.succ_le_iff.mpr hslotLt).trans
      (E.slot_at_mono cfg (Nat.le_succ m))
  obtain ⟨seed, hseedQ, hseedSelectedQ, hguRecent⟩ := hlemma
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk
      hgenSlot hgenParent).time_ge_genesis
  obtain ⟨origin, horiginEq, hcutoff, horiginKnown⟩ :=
    E.scheduled_fcr_call_root_before_deadline cfg ext hT.whole_seconds
      hgenTime hcall (by simpa only [E.fcrStep_store] using hseedQ)
  have hAU : B.state.AU cfg ext seed (B.state.GU seed) :=
    B.state.gu_AU cfg ext (E.acceptedRoot_of_causal_known cfg ext
      hqueryCausal hseedQ)
  obtain ⟨hstart, hbefore⟩ := E.past_slot_deadline_target_gate cfg
    hT.whole_seconds hgenTime (source := origin) (target := m)
      (by simpa only [horiginEq] using hslotLt)
  have hrecent : get_current_store_epoch cfg (E.store cfg ext w m) ≤
      (B.state.GU seed).epoch + 2 := by
    rw [hnextEpoch]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using Nat.add_le_add_right hguRecent 1
  have hseedM : seed ∈ (E.store cfg ext w m).block_roots :=
    E.trusted_deadline_carrier_known_of_recent_au cfg ext B hT hsync.deadline_block_relay
      hanchor hboundary
      (E.trustedCausalRealizedFinalizationLag_of_acceptedDelay cfg ext B hT hanchor hDelay)
      P V hacc (n := origin) (m := m) (tip := seed) (c := B.state.GU seed)
      hv hw (by simpa only [horiginEq] using hn1H) hmH
      horiginKnown hcutoff hstart hbefore hAU hrecent
  have hqueryNonfuture : BlocksSlotLe
      (get_current_slot cfg (E.fcrStoreAtCall cfg ext v n).store)
      (E.fcrStoreAtCall cfg ext v n).store := by
    simpa only [E.fcrStep_store] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hgenSlot⟩ v (n + 1)
  exact E.trusted_recentSourceSeedAt_endpointNext_of_lemma13 cfg ext B
    hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
    hqueryCausal hendpointCausal hqueryParent
    (by simpa only [E.fcrStep_store] using
      E.blockProvenance cfg ext v (n + 1))
    hqueryWalk hqueryNonfuture h.result_known hnextEpoch
    ⟨seed, hseedQ, hseedSelectedQ, hguRecent, hseedM⟩

end Execution
end FastConfirmation.Spec
end
