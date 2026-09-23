module
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedCompatibility

@[expose] public section

/-!
# Spec / Proof / EndpointQuorumCausality: the endpoint justification's quorum

`Execution.ExactPrefixAcceptedFFGSemantics.endpointJustificationOriginAt`
(`AcceptedSelectedJustifiedOrientation.lean:40`) extracts the *single* causal
origin vote of an endpoint justification and bounds its slot below the
endpoint slot.  This module runs the same argument for the **whole terminal
quorum** of that justification, which is what
`docs/trunkB-two-case-discharge.md` §4 shows to be available:

* the endpoint's justified checkpoint is not certified by a bare
  `SupermajorityLink` — it is certified by an `IncludedCertifiedJustified`
  over a carrier known in the endpoint store
  (`AcceptedSelectedJustifiedOrientation.lean:163-172`,
  `AcceptedFFGGlobalCheckpointTrajectory.lean:624-635`);
* every signer's attestation is therefore included in a block of that
  carrier's chain, and `IncludedAttestationEvidence`
  (`Model/FFGStateSemantics.lean:90-115`) supplies `slot_before_carrier`,
  `target_epoch`, `slot_within_horizon` and `attesters_in_committee` for it.

Consequently, for **every** quorum signer:
`a.data.slot + 1 ≤ E.slot_at cfg m`, `compute_epoch_at_slot a.data.slot =
J.epoch`, and `i ∈ E.committee a.data.slot`.  These are the N1/N2 lemmas of
`docs/trunkB-two-case-discharge.md` §7: case α of the two-case discharge reads
off an H2 witness (`Execution.CausalHonestTargetAt`) from an honest signer with
a post-query slot, and case β uses the same facts plus committee-assignment
uniqueness.

Nothing here mentions a selected result, a head, a filter, or a safety
conclusion, and no new assumption is introduced: the causality conjunct
proposed in `docs/justification-causality-contract.md` §1 is *derived*.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## The endpoint justification's quorum, with slot data -/

/-- The terminal quorum certifying the endpoint store's justified checkpoint,
together with the per-signer temporal data derived in
`docs/trunkB-two-case-discharge.md` §4.

`signers_in_epoch` and `supermajority` are the certificate's own fields.  The
four extra conjuncts of `signer_attestation` — horizon, post-anchor, exact
target epoch, and committee assignment at the attested slot — plus the
causality bound `a.data.slot + 1 ≤ E.slot_at cfg m` are what distinguishes
this record from `SupermajorityLink`, which carries no slot data at all. -/
structure EndpointJustifiedQuorumAt (anchor : Checkpoint Root)
    (w : ValidatorIndex) (m : ℕ) : Type where
  signers : Finset ValidatorIndex
  signers_in_epoch : signers ⊆
    E.span_committee
      ((E.store cfg ext w m).justified_checkpoint.epoch * cfg.slots_per_epoch)
      ((E.store cfg ext w m).justified_checkpoint.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1))
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers
  signer_attestation : ∀ i ∈ signers,
    ∃ (u : ValidatorIndex) (n' : ℕ) (a : Attestation Root) (fb : Bool),
      Event.attestation a fb ∈ E.schedule u n' ∧
      i ∈ a.attesting_indices ∧
      a.data.target = (E.store cfg ext w m).justified_checkpoint ∧
      E.SlotWithinHorizon cfg a.data.slot ∧
      E.slot_at cfg 0 ≤ a.data.slot ∧
      compute_epoch_at_slot cfg a.data.slot =
        (E.store cfg ext w m).justified_checkpoint.epoch ∧
      i ∈ E.committee a.data.slot ∧
      a.data.slot + 1 ≤ E.slot_at cfg m

/-- Quorum extraction from a carrier-local certificate, stated over an
arbitrary certified checkpoint so that the certificate's index is a variable.

This is `docs/trunkB-two-case-discharge.md` §4 steps 4-9: the terminal link of
a non-anchor `IncludedCertifiedJustified` is a supermajority whose every
attestation is included in a block on the carrier's chain; that block is known
in the endpoint store, so its slot — and hence, strictly, the attestation slot
— is at most the endpoint's current slot. -/
private theorem includedCertified_quorum_data
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
theorem ExactPrefixAcceptedFFGSemantics.endpointJustified_quorumAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
        (Execution.AcceptedIncludedAttestationRelation.relation
          cfg ext E B.state.includedAttestations) hcertified) hne
  obtain ⟨S, hspan, hsuper, hsigners⟩ :=
    includedCertified_quorum_data cfg ext B hT hgenEq hslot hparent
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

/-! ## Case-α witness extraction -/

/-- The case-α hypothesis of `docs/trunkB-two-case-discharge.md` §3: some
honest quorum signer's own target attestation was cast at or after the query
slot.

The conjuncts are exactly those `EndpointJustifiedQuorumAt.signer_attestation`
supplies, so the negation of this predicate — the case-β hypothesis — is
refuted by any honest signer whose quorum attestation is post-query.  The
upper bound `a.data.slot + 1 ≤ E.slot_at cfg m` is not an extra requirement:
N1 proves it for every signer. -/
def EndpointJustifiedQuorumAt.PostQueryHonestSigner
    {anchor : Checkpoint Root} {w : ValidatorIndex} {m : ℕ}
    (Q : E.EndpointJustifiedQuorumAt cfg ext anchor w m) (q : ℕ) : Prop :=
  ∃ i ∈ Q.signers, i ∈ E.honest ∧
    ∃ (u : ValidatorIndex) (n' : ℕ) (a : Attestation Root) (fb : Bool),
      Event.attestation a fb ∈ E.schedule u n' ∧
      i ∈ a.attesting_indices ∧
      a.data.target = (E.store cfg ext w m).justified_checkpoint ∧
      E.SlotWithinHorizon cfg a.data.slot ∧
      E.slot_at cfg 0 ≤ a.data.slot ∧
      a.data.slot + 1 ≤ E.slot_at cfg m ∧
      E.slot_at cfg q ≤ a.data.slot

/-- Scheduled-attestation packaging of `HonestBehavior.no_forgery`: an
attestation naming an honest validator exposes that validator's own recorded
vote for the attested slot, with the same target.

This is the first half of **N2** of `docs/trunkB-two-case-discharge.md` §7;
the conclusion is the witness shape consumed by
`Execution.endpoint_justified_epoch_le_of_causal_honest_target_minimal`
(`CausalCheckpointEpochBound.lean:87`) and
`Execution.endpoint_justified_ancestor_of_causal_honest_target_minimal`
(`CausalCheckpointCompatibility.lean:37`), together with the post-anchor
conjunct those two derive for themselves. -/
theorem honestTargetVote_of_scheduledAttestation
    {w : ValidatorIndex} {m : ℕ} {q : ℕ}
    (hhb : HonestBehavior cfg ext E)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {u : ValidatorIndex} {n' : ℕ} {a : Attestation Root} {fb : Bool}
    (hsched : Event.attestation a fb ∈ E.schedule u n')
    (hia : i ∈ a.attesting_indices)
    (htarget : a.data.target =
      (E.store cfg ext w m).justified_checkpoint)
    (hsH : E.SlotWithinHorizon cfg a.data.slot)
    (hs0 : E.slot_at cfg 0 ≤ a.data.slot)
    (hslotBound : a.data.slot + 1 ≤ E.slot_at cfg m)
    (hqs : E.slot_at cfg q ≤ a.data.slot) :
    ∃ (s : Slot) (k : ℕ) (a' : Attestation Root),
      E.slot_at cfg 0 ≤ s ∧
      E.slot_at cfg q ≤ s ∧
      s < E.slot_at cfg m ∧
      E.SlotWithinHorizon cfg s ∧
      E.vote i s = some (k, a') ∧
      a'.data.target = (E.store cfg ext w m).justified_checkpoint := by
  obtain ⟨k, a', hvote, hdata⟩ :=
    hhb.no_forgery u n' a fb hsched i hi hia
  refine ⟨a.data.slot, k, a', hs0, hqs, hslotBound, hsH, hvote, ?_⟩
  rw [← hdata]
  exact htarget

/-- **N2** of `docs/trunkB-two-case-discharge.md` §7: case α's hypothesis
yields the H2 witness in the exact shape of
`Execution.CausalHonestTargetAt`, which is what
`Execution.EndpointJustificationCausalityAt`
(`SelectedJustifiedCompatibility.lean:131`) must produce and what the two
proviso-free post-query consumers of §3.1 eliminate. -/
theorem EndpointJustifiedQuorumAt.causalHonestTargetAt_of_postQuerySigner
    {anchor : Checkpoint Root} {w : ValidatorIndex} {m : ℕ} {q : ℕ}
    (hhb : HonestBehavior cfg ext E)
    {Q : E.EndpointJustifiedQuorumAt cfg ext anchor w m}
    (hpost : Q.PostQueryHonestSigner cfg ext q) :
    E.CausalHonestTargetAt cfg ext q w m := by
  obtain ⟨i, _hiQ, hi, u, n', a, fb, hsched, hia, htarget, hsH, hs0,
    hslotBound, hqs⟩ := hpost
  obtain ⟨s, k, a', _hs0, hqs', hsm, hsH', hvote, htarget'⟩ :=
    E.honestTargetVote_of_scheduledAttestation cfg ext hhb hi hsched hia
      htarget hsH hs0 hslotBound hqs
  exact ⟨i, hi, s, k, a', hqs', hsm, hsH', hvote, htarget'⟩

end Execution

end FastConfirmation.Spec

end
