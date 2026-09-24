module
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem TrustedCausalPrefixFFGInterpretation.endpointJustificationOriginAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : FastConfirmation.Spec.Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
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
    simpa only [FastConfirmation.Spec.Execution.TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
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
      obtain ⟨bodyVote, ⟨_hincludedCarrier, _hincludedDesc, hincludedAt⟩,
        _hbodySigner, hbodyData⟩ := hincluded
      have hincludedEvidence :=
        B.state.includedAttestations.evidence hincludedAt
      obtain ⟨hcertified⟩ := hcarrier.formed_evidence.certified
      have hanchorLt : B.anchor.epoch <
          (E.store cfg ext w m).justified_checkpoint.epoch :=
        CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
          (IncludedCertifiedJustified.toCertifiedJustified
            (cfg := cfg)
            B.state.includedAttestations.relation hcertified) hne
      have htargetEpoch : (E.store cfg ext w m).justified_checkpoint.epoch =
          compute_epoch_at_slot cfg voteSlot := by
        rw [← hgroundTarget, ← hgroundSlot, ← hbodyData]
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

end FastConfirmation.Spec
end
