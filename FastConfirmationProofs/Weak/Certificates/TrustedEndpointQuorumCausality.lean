module
public import FastConfirmationProofs.Weak.Certificates.EndpointQuorumCausality
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

private theorem trustedIncludedCertified_quorum_data
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgenEq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot)
    (hparent : ablk.message.parent_root ≠ ablk.root)
    {w : ValidatorIndex} {m : ℕ} {carrier : Root}
    (hcarrierKnown : carrier ∈ (E.store cfg ext w m).block_roots)
    {c : Checkpoint Root}
    (hcert : IncludedCertifiedJustified cfg E
      B.state.includedAttestations.Included B.anchor carrier c)
    (hne : c ≠ B.anchor) :
    ∃ S : Finset ValidatorIndex,
      S ⊆ E.span_committee (c.epoch * cfg.slots_per_epoch)
        (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) ∧
      2 * E.total_active cfg ≤ 3 * E.weight S ∧
      ∀ i ∈ S, ∃ (u : ValidatorIndex) (n' : ℕ) (a : Attestation Root)
        (fb : Bool),
        Event.attestation a fb ∈ E.schedule u n' ∧
        i ∈ a.attesting_indices ∧
        a.data.target = c ∧
        E.SlotWithinHorizon cfg a.data.slot ∧
        compute_epoch_at_slot cfg a.data.slot = c.epoch ∧
        i ∈ E.committee a.data.slot ∧
        a.data.slot + 1 ≤ E.slot_at cfg m := by
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  cases hcert with
  | anchor => exact absurd rfl hne
  | @link source target _hsource link =>
      refine ⟨link.signers, link.signers_in_epoch, link.supermajority, ?_⟩
      intro i hi
      obtain ⟨a, ⟨block, hdesc, hincluded⟩, hia, _hsource, htarget⟩ :=
        link.signer_attestation i hi
      have hev := B.state.includedAttestations.evidence hincluded
      obtain ⟨u, n', hsched⟩ := hev.received_from_block
      have hblockRoot : E.ExecutionRoot block :=
        ⟨hev.carrier_message, hev.carrier_at⟩
      have hblockKnown : block ∈ (E.store cfg ext w m).block_roots :=
        (E.store_known_ancestor_of_rootDescends_for_storeReflection
          cfg ext hT.wellFormed hT.externals_coherence hgenEq hslot hparent
          hcarrierKnown hblockRoot hdesc).1
      have hblockAgreement : hev.carrier_message =
          (E.store cfg ext w m).blocks block :=
        hev.carrier_accepted.unique cfg ext E hT.wellFormed
          (E.acceptedBlockAt_of_causal_known cfg ext hstore hblockKnown)
      have hslotBound : a.data.slot + 1 ≤ E.slot_at cfg m := by
        have hlt : a.data.slot < E.slot_at cfg m := by
          calc
            a.data.slot < hev.carrier_message.slot := hev.slot_before_carrier
            _ = ((E.store cfg ext w m).blocks block).slot :=
              congrArg BeaconBlock.slot hblockAgreement
            _ ≤ get_current_slot cfg (E.store cfg ext w m) :=
              E.store_blocks_slot_le_current cfg ext hT.whole_seconds
                hgenShort w m block hblockKnown
            _ = E.slot_at cfg m := E.store_current_slot cfg ext w m
        exact Nat.succ_le_of_lt hlt
      have hepoch : compute_epoch_at_slot cfg a.data.slot = c.epoch := by
        rw [← htarget]
        exact hev.target_epoch.symm
      exact ⟨u, n', a, true, hsched, hia, htarget, hev.slot_within_horizon,
        hepoch, hev.attesters_in_committee i hia, hslotBound⟩

/-- **N1** of `docs/trunkB-two-case-discharge.md` §7: a non-anchor endpoint
justification exposes its whole certifying quorum, with per-signer slot data.

The proof is §4 steps 1-10 of that note: the accepted global selector supplies
an AU carrier known in the endpoint store, its formed evidence supplies a
carrier-local certificate, and the certificate's terminal link supplies the
quorum.  Only the post-anchor bound `E.slot_at cfg 0 ≤ a.data.slot` is proved
here rather than in the helper above; it needs `B.anchor.epoch < c.epoch`,
exactly as at `AcceptedSelectedJustifiedOrientation.lean:97-116`. -/
theorem TrustedCausalPrefixFFGInterpretation.endpointJustified_quorumAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : ℕ}
    (hne : (E.store cfg ext w m).justified_checkpoint ≠ B.anchor) :
    Nonempty (E.EndpointJustifiedQuorumAt cfg ext B.anchor w m) := by
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
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
      hfieldAnchor | hevidence
  · exact absurd hfieldAnchor hne
  obtain ⟨hcarrier⟩ := hevidence
  obtain ⟨hcertified⟩ := hcarrier.formed_evidence.certified
  have hcarrierRoot : E.ExecutionRoot hcarrier.carrier := by
    obtain ⟨carrierStore, hcarrierStore, hcarrierStoreKnown⟩ :=
      hcarrier.carrier_accepted
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
  have hanchorLt : B.anchor.epoch <
      (E.store cfg ext w m).justified_checkpoint.epoch :=
    CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
      (IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        B.state.includedAttestations.relation hcertified) hne
  obtain ⟨S, hspan, hsuper, hsigners⟩ :=
    trustedIncludedCertified_quorum_data cfg ext B hT hgenEq hslot hparent
      hcarrierKnown hcertified hne
  refine ⟨⟨S, hspan, hsuper, ?_⟩⟩
  intro i hi
  obtain ⟨u, n', a, fb, hsched, hia, htarget, hsH, hepoch, hcommittee,
    hslotBound⟩ := hsigners i hi
  refine ⟨u, n', a, fb, hsched, hia, htarget, hsH, ?_, hepoch, hcommittee,
    hslotBound⟩
  have hstartMono : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
      compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).justified_checkpoint.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorLt.le
  have hstartVote : compute_start_slot_at_epoch cfg
      (E.store cfg ext w m).justified_checkpoint.epoch ≤ a.data.slot := by
    have hmulDiv := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
    have hdiv : a.data.slot / cfg.slots_per_epoch =
        (E.store cfg ext w m).justified_checkpoint.epoch := by
      simpa only [compute_epoch_at_slot] using hepoch
    rw [hdiv] at hmulDiv
    simpa only [compute_start_slot_at_epoch] using hmulDiv
  calc
    E.slot_at cfg 0 = ast.slot := hslotZero
    _ = ablk.message.slot := hslot
    _ ≤ compute_start_slot_at_epoch cfg B.anchor.epoch := hboundary'
    _ ≤ compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).justified_checkpoint.epoch := hstartMono
    _ ≤ a.data.slot := hstartVote


end Execution
end FastConfirmation.Spec
end
