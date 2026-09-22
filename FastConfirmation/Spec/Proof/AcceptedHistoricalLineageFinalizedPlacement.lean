import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedHistoricalFinalizedPlacementAdapters
import FastConfirmation.Spec.Proof.AcceptedPhaseSourceCarriers

/-!
# Historical-lineage finalized placement

This module closes the pre-query finalized-placement branch using the
historical A3.2 payload retained by the accepted candidate trajectory.

The key certificate argument is deliberately mixed.  The endpoint finalized
checkpoint has the ordinary included finalization certificate, while the
historical target is represented by the concrete honest A3.2 quorum retained
in `AcceptedHistoricalA32GatePayloadAt`.  The latter is not silently promoted
to an included certificate.  Instead, its exact accepted source is used as the
split point in the usual Casper finalized-prefix argument, and the one
remaining surround case is contradicted directly from quorum intersection and
honest no-slashing.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Concrete A3.2 quorum versus an included link -/

private def mixedAnchorActive (E : Execution Root) : Finset ValidatorIndex :=
  (get_active_validator_indices E.anchor_state
    (get_current_epoch cfg E.anchor_state)).toFinset

omit [LinearOrder Root] [Inhabited Root] in
private theorem mem_active_of_active_mixed {bs : BeaconState Root}
    {i : ValidatorIndex} {e : Epoch}
    (hact : is_active_validator (bs.validators.getD i default) e = true) :
    i ∈ get_active_validator_indices bs e := by
  simp only [get_active_validator_indices, List.mem_filter, List.mem_range]
  refine ⟨?_, hact⟩
  by_contra hge
  rw [not_lt] at hge
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge,
    Option.getD_none] at hact
  simp only [is_active_validator, decide_eq_true_eq] at hact
  exact (Nat.not_lt_zero e) hact.2

private theorem mixed_anchor_epoch_within
    (hA : FFGAccountabilityAssumptions cfg ext E) :
    get_current_epoch cfg E.anchor_state < E.verification_horizon := by
  have hslot := E.anchor_state_slot_le cfg hA.whole_seconds hA.genesis_store
  have hepoch : get_current_epoch cfg E.anchor_state ≤
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
    simpa only [get_current_epoch] using Nat.div_le_div_right hslot
  exact lt_of_le_of_lt hepoch
    hA.static_validator_set.genesis_within_horizon.2.2

private theorem mixed_span_subset_anchorActive
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {lo hi : Slot} (hhi : E.SlotWithinHorizon cfg hi) :
    E.span_committee lo hi ⊆ E.mixedAnchorActive cfg := by
  have hanchorH := E.mixed_anchor_epoch_within cfg ext hA
  intro i hiSpan
  simp only [Execution.span_committee, Finset.mem_biUnion,
    Finset.mem_Icc] at hiSpan
  obtain ⟨s, hs, hiCommittee⟩ := hiSpan
  have hsH : E.SlotWithinHorizon cfg s :=
    ⟨le_trans hs.2 hhi.1,
      lt_of_le_of_lt (Nat.div_le_div_right hs.2) hhi.2⟩
  have hactiveS := hA.externals_coherence.committee_members_active
    i s hsH hiCommittee
  have hactiveAnchor : is_active_validator (E.registry.getD i default)
      (get_current_epoch cfg E.anchor_state) = true := by
    rw [← hA.static_validator_set.activity_constant i
      (compute_epoch_at_slot cfg s)
      (get_current_epoch cfg E.anchor_state) hsH.2 hanchorH]
    exact hactiveS
  rw [mixedAnchorActive, List.mem_toFinset]
  apply mem_active_of_active_mixed
  simpa only [Execution.registry] using hactiveAnchor

private theorem mixed_quorum_subset_anchorActive
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target) :
    Q.signers ⊆ E.mixedAnchorActive cfg := by
  have hanchorH := E.mixed_anchor_epoch_within cfg ext hA
  intro i hi
  obtain ⟨vote⟩ := Q.votes i hi
  have hactiveVote := hA.externals_coherence.committee_members_active
    i vote.slot vote.slot_within_horizon vote.assigned
  have hactiveAnchor : is_active_validator (E.registry.getD i default)
      (get_current_epoch cfg E.anchor_state) = true := by
    rw [← hA.static_validator_set.activity_constant i
      (compute_epoch_at_slot cfg vote.slot)
      (get_current_epoch cfg E.anchor_state)
      vote.slot_within_horizon.2 hanchorH]
    exact hactiveVote
  rw [mixedAnchorActive, List.mem_toFinset]
  apply mem_active_of_active_mixed
  simpa only [Execution.registry] using hactiveAnchor

private theorem mixed_quorum_subset_honest
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target) :
    Q.signers ⊆ E.honest := by
  intro i hi
  obtain ⟨vote⟩ := Q.votes i hi
  exact vote.honest

omit [LinearOrder Root] [Inhabited Root] in
private theorem mixed_anchorActive_weight_le_total :
    E.weight (E.mixedAnchorActive cfg) ≤ E.total_active cfg := by
  simp only [mixedAnchorActive, Execution.weight, Execution.weight_of,
    Execution.total_active, get_total_active_balance, get_total_balance,
    Execution.registry]
  exact Nat.le_max_right _ _

omit [LinearOrder Root] [Inhabited Root] in
private theorem two_thirds_gt_one_third_mixed {W q : Nat}
    (hW : 0 < W) (hq : 2 * W ≤ 3 * q) : W < 3 * q := by
  omega

/-- A concrete A3.2 honest quorum intersects every ordinary concrete FFG
link.  Unlike the generic two-link theorem, this needs no Byzantine-fraction
subtraction: every signer retained by the A3.2 quorum is already honest. -/
theorem ConcreteA32QuorumBefore.intersects_supermajorityLink_honest
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {deadline : Slot} {target source' target' : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (L : SupermajorityLink cfg E source' target') :
    ∃ i ∈ Q.signers, i ∈ L.signers ∧ i ∈ E.honest := by
  let U := E.mixedAnchorActive cfg
  have hQU : Q.signers ⊆ U := by
    simpa only [U] using E.mixed_quorum_subset_anchorActive cfg ext hA Q
  have hLU : L.signers ⊆ U := by
    intro i hi
    exact E.mixed_span_subset_anchorActive cfg ext hA
      L.target_span_within.2 (L.signers_in_epoch hi)
  have hQlarge : E.total_active cfg < 3 * E.weight Q.signers := by
    exact two_thirds_gt_one_third_mixed
      (E.total_active_pos cfg) Q.supermajority
  exact one_third_honest_intersects_two_thirds E hQU hLU
    (E.mixed_quorum_subset_honest cfg ext Q)
    (by simpa only [U] using E.mixed_anchorActive_weight_le_total cfg)
    hQlarge L.supermajority

/-- The retained honest A3.2 quorum cannot surround an included FFG link.
The A3.2 votes are used in their ground honest form; they are not relabeled as
included attestations. -/
theorem ConcreteA32QuorumBefore.not_surround_includedLink
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : E.IncludedAttestationRelation cfg validity)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    {carrier : Root} {source' target' : Checkpoint Root}
    (L : IncludedSupermajorityLink cfg E I.Included carrier source' target') :
    ¬ (Q.source.epoch < source'.epoch ∧ target'.epoch < target.epoch) := by
  let globalL := IncludedSupermajorityLink.toSupermajorityLink
    (cfg := cfg) I L
  obtain ⟨i, hiQ, hiL, hiHonest⟩ :=
    Q.intersects_supermajorityLink_honest cfg ext hA globalL
  obtain ⟨qvote⟩ := Q.votes i hiQ
  obtain ⟨w', n', a', fromBlock', haSchedule', hiA',
      haSource', haTarget'⟩ := globalL.signer_attestation i hiL
  obtain ⟨k', vote', hvote', hdata'⟩ :=
    hA.honest_behavior.no_forgery w' n' a' fromBlock' haSchedule'
      i hiHonest hiA'
  let qa := honest_attestation cfg ext (E.store cfg ext i qvote.time)
    qvote.slot qvote.index i
  have hqSource : qa.data.source = Q.source := by
    simpa only [qa] using Q.source_agreement i hiQ qvote
  have hqTarget : qa.data.target = target := by
    simpa only [qa] using qvote.target_eq
  have hsource' : vote'.data.source = source' := by
    rw [← hdata']
    exact haSource'
  have htarget' : vote'.data.target = target' := by
    rw [← hdata']
    exact haTarget'
  rintro ⟨hsource, htarget⟩
  have hslash : is_slashable_attestation_data qa.data vote'.data = true := by
    simp [is_slashable_attestation_data, hqSource, hqTarget,
      hsource', htarget', hsource, htarget]
  have hnot := hA.honest_behavior.not_slashable i hiHonest
    qvote.slot a'.data.slot qvote.time k' qa vote'
    (by simpa only [qa] using qvote.vote) hvote'
  rw [hslash] at hnot
  contradiction

/-! ## Mixed exact finalized prefix -/

/-- Exact finalized prefix whose upper link is the historical concrete A3.2
quorum rather than an included-attestation link.

The source is exact at `selected` and has an included certificate because it
is AU there.  The historical target has an ordinary concrete justification
certificate.  Those are exactly the asymmetric facts retained by the accepted
historical payload. -/
theorem AcceptedHistoricalA32QuorumAt.exactFinalizedPrefix_of_included
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {selected : Root} {e : Epoch}
    (hselected : E.AcceptedRoot cfg ext selected)
    (hQ : E.AcceptedHistoricalA32QuorumAt cfg ext B selected e)
    (hsourceAU : B.state.AU cfg ext selected hQ.quorum.source)
    (hsourceExact : hQ.quorum.source =
      B.state.C selected hQ.quorum.source.epoch)
    (htargetCertified : CertifiedJustified cfg E B.anchor hQ.target)
    {finalizedCarrier : Root} {finalized : Checkpoint Root}
    (hfinalized : IncludedCertifiedFinalized cfg E
      B.state.includedAttestations.Included B.anchor
      finalizedCarrier finalized)
    (hepoch : finalized.epoch ≤ hQ.target.epoch) :
    ExactCheckpointPrefix B.state.C finalized hQ.target := by
  let I := Execution.AcceptedIncludedAttestationRelation.relation
    (cfg := cfg) (ext := ext) (E := E) B.state.includedAttestations
  let toGlobalJ := fun {carrier : Root} {c : Checkpoint Root}
      (h : IncludedCertifiedJustified cfg E
        B.state.includedAttestations.Included B.anchor carrier c) =>
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg) I h
  let toGlobalL := fun {carrier : Root} {source target : Checkpoint Root}
      (L : IncludedSupermajorityLink cfg E
        B.state.includedAttestations.Included carrier source target) =>
    IncludedSupermajorityLink.toSupermajorityLink (cfg := cfg) I L
  have hsourceIncluded : Nonempty (IncludedCertifiedJustified cfg E
      B.state.includedAttestations.Included B.anchor selected
        hQ.quorum.source) :=
    B.state.includedJustifiedAtTip_of_AU cfg ext hsourceAU
  obtain ⟨hsourceIncluded⟩ := hsourceIncluded
  have hsourceGlobal : CertifiedJustified cfg E B.anchor hQ.quorum.source :=
    toGlobalJ hsourceIncluded
  have hfinalizedGlobal : CertifiedJustified cfg E B.anchor finalized :=
    toGlobalJ hfinalized.justified
  have hanchorSource : B.anchor.epoch ≤ hQ.quorum.source.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hsourceGlobal
  have hsourceTargetEpoch : hQ.quorum.source.epoch ≤
      hQ.target.epoch := Nat.le_of_lt hQ.quorum.source_before_target
  have hanchorTarget : B.anchor.epoch ≤ hQ.target.epoch :=
    hanchorSource.trans hsourceTargetEpoch
  have htargetEpoch : hQ.target.epoch = e := by
    rw [hQ.target_eq]
    exact B.state.checkpoint_epoch selected e
  have htargetEqEpoch : hQ.target =
      B.state.C selected hQ.target.epoch := by
    calc
      hQ.target = B.state.C selected e := hQ.target_eq
      _ = B.state.C selected hQ.target.epoch := by rw [htargetEpoch]
  have hsourceTarget : ExactCheckpointPrefix B.state.C
      hQ.quorum.source hQ.target := by
    have hcomp := P.checkpoint_comp hselected hanchorSource
      hsourceTargetEpoch
    unfold ExactCheckpointPrefix
    calc
      hQ.quorum.source =
          B.state.C selected hQ.quorum.source.epoch := hsourceExact
      _ = B.state.C (B.state.C selected hQ.target.epoch).root
          hQ.quorum.source.epoch := hcomp.symm
      _ = B.state.C hQ.target.root
          hQ.quorum.source.epoch := by
            rw [congrArg Checkpoint.root htargetEqEpoch]
  have htargetAccepted : E.AcceptedRoot cfg ext hQ.target.root := by
    rw [hQ.target_eq]
    apply P.checkpoint_root_accepted hselected
    simpa only [← htargetEpoch] using hanchorTarget
  have htargetSelf : hQ.target =
      B.state.C hQ.target.root hQ.target.epoch := by
    have hcomp := P.checkpoint_comp hselected
      hanchorTarget (Nat.le_refl hQ.target.epoch)
    calc
      hQ.target = B.state.C selected hQ.target.epoch := htargetEqEpoch
      _ = B.state.C (B.state.C selected hQ.target.epoch).root
          hQ.target.epoch := hcomp.symm
      _ = B.state.C hQ.target.root
          hQ.target.epoch := by
            rw [congrArg Checkpoint.root htargetEqEpoch]
  by_cases hfinalizedSource : finalized.epoch ≤ hQ.quorum.source.epoch
  · have hprefix := B.state.exactFinalizedPrefix_of_accountable cfg P V
      hanchorExact hacc hfinalized hsourceIncluded hfinalizedSource
    exact P.prefix_trans htargetAccepted
      (CertifiedJustified.anchor_epoch_le (cfg := cfg) hfinalizedGlobal)
      hfinalizedSource hprefix hsourceTarget
  · have hsourceLt : hQ.quorum.source.epoch < finalized.epoch :=
      Nat.lt_of_not_ge hfinalizedSource
    by_cases htargetFinalized :
        hQ.target.epoch = finalized.epoch
    · have hroot := hacc.justified_unique htargetCertified
        hfinalizedGlobal htargetFinalized
      have heq : hQ.target = finalized :=
        checkpoint_eq_of_epoch_root_eq htargetFinalized hroot
      unfold ExactCheckpointPrefix
      rw [← heq]
      exact htargetSelf
    · have hfinalizedLt : finalized.epoch < hQ.target.epoch :=
        lt_of_le_of_ne hepoch (Ne.symm htargetFinalized)
      have hchildIncluded : IncludedCertifiedJustified cfg E
          B.state.includedAttestations.Included B.anchor finalizedCarrier
          hfinalized.child :=
        .link hfinalized.justified hfinalized.finalizing_link
      have hchildGlobal : CertifiedJustified cfg E B.anchor hfinalized.child :=
        toGlobalJ hchildIncluded
      by_cases htargetChild :
          hQ.target.epoch = hfinalized.child.epoch
      · have hroot := hacc.justified_unique htargetCertified hchildGlobal
          htargetChild
        have heq : hQ.target = hfinalized.child :=
          checkpoint_eq_of_epoch_root_eq htargetChild hroot
        have hanchorFinalized : B.anchor.epoch ≤ finalized.epoch :=
          CertifiedJustified.anchor_epoch_le (cfg := cfg) hfinalizedGlobal
        have hprefix := V.source_prefix_target (cfg := cfg) P
          hfinalized.finalizing_link hfinalized.justified hanchorFinalized
        simpa only [heq] using hprefix
      · have hchildLt : hfinalized.child.epoch < hQ.target.epoch := by
          have hsuccLe : finalized.epoch + 1 ≤ hQ.target.epoch :=
            Nat.succ_le_iff.mpr hfinalizedLt
          have htargetNeSucc :
              hQ.target.epoch ≠ finalized.epoch + 1 := by
            intro heq
            apply htargetChild
            rw [hfinalized.child_epoch]
            exact heq
          have hsuccLt : finalized.epoch + 1 < hQ.target.epoch :=
            lt_of_le_of_ne hsuccLe htargetNeSucc.symm
          simpa only [hfinalized.child_epoch] using hsuccLt
        exact False.elim
          ((hQ.quorum.not_surround_includedLink cfg ext hA I
            hfinalized.finalizing_link) ⟨hsourceLt, hchildLt⟩)

/-! ## Materialized historical placement at the query -/

private theorem AcceptedBlockAt.executionRoot_mixed
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- A historical current-candidate lineage supplies the exact placement of
an early endpoint's realized finalized checkpoint on that candidate in the
query store.  This is stronger than the old pre-query callback: it is
unconditional on the formation vote's time, because the retained certificate
payload already records the relevant historical target. -/
theorem EarlySelectedEndpointPhase.finalizedRoot_eq_queryCheckpointBlock_of_lineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {q : Nat}
    {w : ValidatorIndex} {m : Nat}
    {selected : Root} {e : Epoch}
    (hphase : EarlySelectedEndpointPhase e
      (get_current_store_epoch cfg (E.store cfg ext v q))
      (get_current_store_epoch cfg (E.store cfg ext w m)))
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e) :
    (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext v q) selected
        (E.store cfg ext w m).finalized_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  let query := E.store cfg ext v q
  let endpoint := E.store cfg ext w m
  have hqueryCausal : E.CausalStore cfg ext query := by
    simpa only [query] using E.store_causal cfg ext v q
  have hendpointCausal : E.CausalStore cfg ext endpoint := by
    simpa only [endpoint] using E.store_causal cfg ext w m
  have hqueryParent : ParentSlotLt query := by
    simpa only [query] using E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure
      hT.wellFormed.anchor_parent_unscheduled v q
  have hselectedQ' : selected ∈ query.block_roots := by
    simpa only [query] using hselectedQ
  have hselectedAccepted : E.AcceptedRoot cfg ext selected :=
    E.acceptedRoot_of_causal_known cfg ext hqueryCausal hselectedQ'
  have horiginRoot : E.ExecutionRoot hlineage.origin :=
    hlineage.payload.origin_at.executionRoot_mixed cfg ext
  have horiginReflection :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      hselectedQ horiginRoot hlineage.descends
  have horiginQ : hlineage.origin ∈ query.block_roots := by
    simpa only [query] using horiginReflection.1
  have hselectedOrigin : is_ancestor query
      (get_node_for_root selected)
      (get_node_for_root hlineage.origin) = true := by
    simpa only [query] using horiginReflection.2
  have horiginAtQ : E.AcceptedBlockAt cfg ext hlineage.origin
      (query.blocks hlineage.origin) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal horiginQ
  have horiginBlocks : hlineage.payload.origin_block =
      query.blocks hlineage.origin :=
    hlineage.payload.origin_at.unique cfg ext E hT.wellFormed horiginAtQ
  have horiginEpoch : get_block_epoch cfg query hlineage.origin = e := by
    simpa only [get_block_epoch, ← horiginBlocks] using
      hlineage.payload.origin_epoch
  have hselectedEpoch' : get_block_epoch cfg query selected = e := by
    simpa only [query] using hselectedEpoch
  have hlineageCertified : CertifiedJustified cfg E B.anchor
      (B.state.C hlineage.origin e) :=
    Classical.choice hlineage.payload.certified
  have hanchorLeE : B.anchor.epoch ≤ e := by
    have := CertifiedJustified.anchor_epoch_le
      (cfg := cfg) hlineageCertified
    simpa only [B.state.checkpoint_epoch] using this
  have hselectedWalk : WalkKnown query
      (compute_start_slot_at_epoch cfg e) selected := by
    simpa only [query] using
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v q hanchorLeE hselectedQ
  let hpayload := hlineage.payloadAtTip cfg ext hphase0 hqueryCausal
    hqueryParent horiginQ hselectedQ' horiginEpoch hselectedEpoch'
      hselectedOrigin hselectedWalk
  have hpayloadCertified : CertifiedJustified cfg E B.anchor
      (B.state.C selected e) := Classical.choice hpayload.certified
  have hfinalizedEvidence :=
    E.acceptedGlobalFinalized_anchor_or_includedCertificate cfg ext B
      hgenShort hanchor hendpointCausal
  have hsemantic : endpoint.finalized_checkpoint =
      B.state.C selected endpoint.finalized_checkpoint.epoch := by
    rcases hfinalizedEvidence with hfinalizedAnchor |
        ⟨finalizedCarrier, _hcarrier, hfinalized⟩
    · rcases hpayload.support_branch with htargetAnchor | hquorum
      · have hepoch : e = B.anchor.epoch := by
          have he := congrArg Checkpoint.epoch htargetAnchor
          simpa only [B.state.checkpoint_epoch] using he
        calc
          endpoint.finalized_checkpoint = B.anchor := hfinalizedAnchor
          _ = B.state.C selected e := htargetAnchor.symm
          _ = B.state.C selected endpoint.finalized_checkpoint.epoch := by
            rw [hfinalizedAnchor, hepoch]
      · obtain ⟨hQ⟩ := hquorum
        have hsourceAU : B.state.AU cfg ext selected hQ.quorum.source := by
          rw [hQ.source_eq]
          exact B.state.gj_AU cfg ext hselectedAccepted
        have hsourceExact : hQ.quorum.source =
            B.state.C selected hQ.quorum.source.epoch := by
          have hAUCheckpoint := B.coherence.au_checkpoint_of_known
            hqueryCausal selected hselectedQ' hQ.quorum.source hsourceAU
          have hcheckpoint := B.coherence.checkpoint_of_known
            hqueryCausal selected hselectedQ' hQ.quorum.source.epoch
          exact hAUCheckpoint.trans hcheckpoint.symm
        obtain ⟨hsourceIncluded⟩ :=
          B.state.includedJustifiedAtTip_of_AU cfg ext hsourceAU
        have hanchorSource : B.anchor.epoch ≤ hQ.quorum.source.epoch :=
          IncludedCertifiedJustified.anchor_epoch_le
            (cfg := cfg) hsourceIncluded
        have hanchorSourcePrefix : ExactCheckpointPrefix B.state.C
            B.anchor hQ.quorum.source :=
          IncludedCertifiedJustified.anchor_prefix cfg P V hanchorExact
            hsourceIncluded
        have hsourceRoot : hQ.quorum.source.root =
            (B.state.C selected hQ.quorum.source.epoch).root :=
          congrArg Checkpoint.root hsourceExact
        have hcomp := P.checkpoint_comp hselectedAccepted
          (Nat.le_refl B.anchor.epoch) hanchorSource
        have hanchorSelected : B.anchor =
            B.state.C selected B.anchor.epoch := by
          calc
            B.anchor = B.state.C hQ.quorum.source.root
                B.anchor.epoch := hanchorSourcePrefix
            _ = B.state.C (B.state.C selected
                  hQ.quorum.source.epoch).root B.anchor.epoch :=
              congrArg (fun r => B.state.C r B.anchor.epoch) hsourceRoot
            _ = B.state.C selected B.anchor.epoch := hcomp
        calc
          endpoint.finalized_checkpoint = B.anchor := hfinalizedAnchor
          _ = B.state.C selected B.anchor.epoch := hanchorSelected
          _ = B.state.C selected endpoint.finalized_checkpoint.epoch := by
            rw [hfinalizedAnchor]
    · obtain ⟨hfinalized⟩ := hfinalized
      have hfinalizedGlobal : CertifiedJustified cfg E B.anchor
          endpoint.finalized_checkpoint :=
        IncludedCertifiedJustified.toCertifiedJustified
          (cfg := cfg)
          (Execution.AcceptedIncludedAttestationRelation.relation
            cfg ext E B.state.includedAttestations)
          hfinalized.justified
      have hfinalizedLeE : endpoint.finalized_checkpoint.epoch ≤ e := by
        by_cases heq : endpoint.finalized_checkpoint = B.anchor
        · rw [heq]
          exact hanchorLeE
        · have hle := hphase.finalizedEpoch_le_selected_of_nonanchor
            cfg ext B hT hanchor hselectedQ hselectedM hselectedEpoch
            (by simpa only [endpoint] using heq)
          have hblocks : (E.store cfg ext v q).blocks selected =
              (E.store cfg ext w m).blocks selected :=
            hT.wellFormed.blocks_agree
              (E.blockProvenance cfg ext v q)
              (E.blockProvenance cfg ext w m)
              hselectedQ hselectedM
          have hselectedEpochM : get_block_epoch cfg
              (E.store cfg ext w m) selected = e := by
            simp only [get_block_epoch]
            rw [← hblocks]
            simpa only [get_block_epoch] using hselectedEpoch
          simpa only [endpoint, hselectedEpochM] using hle
      rcases hpayload.support_branch with htargetAnchor | hquorum
      · have hepoch : e = B.anchor.epoch := by
          have he := congrArg Checkpoint.epoch htargetAnchor
          simpa only [B.state.checkpoint_epoch] using he
        have hfinalizedEpoch : endpoint.finalized_checkpoint.epoch =
            B.anchor.epoch := Nat.le_antisymm
          (by simpa only [hepoch] using hfinalizedLeE)
          (CertifiedJustified.anchor_epoch_le (cfg := cfg) hfinalizedGlobal)
        have hroot := hacc.justified_unique hfinalizedGlobal
          (CertifiedJustified.anchor) hfinalizedEpoch
        have hfinalizedEq : endpoint.finalized_checkpoint = B.anchor :=
          checkpoint_eq_of_epoch_root_eq hfinalizedEpoch hroot
        calc
          endpoint.finalized_checkpoint = B.anchor := hfinalizedEq
          _ = B.state.C selected e := htargetAnchor.symm
          _ = B.state.C selected endpoint.finalized_checkpoint.epoch := by
            rw [hfinalizedEq, hepoch]
      · obtain ⟨hQ⟩ := hquorum
        have hsourceAU : B.state.AU cfg ext selected hQ.quorum.source := by
          rw [hQ.source_eq]
          exact B.state.gj_AU cfg ext hselectedAccepted
        have hsourceExact : hQ.quorum.source =
            B.state.C selected hQ.quorum.source.epoch := by
          have hAUCheckpoint := B.coherence.au_checkpoint_of_known
            hqueryCausal selected hselectedQ' hQ.quorum.source hsourceAU
          have hcheckpoint := B.coherence.checkpoint_of_known
            hqueryCausal selected hselectedQ' hQ.quorum.source.epoch
          exact hAUCheckpoint.trans hcheckpoint.symm
        have htargetCertified : CertifiedJustified cfg E B.anchor hQ.target := by
          rw [hQ.target_eq]
          exact hpayloadCertified
        have htargetEpoch : hQ.target.epoch = e := by
          rw [hQ.target_eq]
          exact B.state.checkpoint_epoch selected e
        have hprefix := hQ.exactFinalizedPrefix_of_included cfg ext B P V
          hanchorExact hacc hA hselectedAccepted hsourceAU hsourceExact
          htargetCertified hfinalized
          (by simpa only [htargetEpoch] using hfinalizedLeE)
        have hanchorFinalized : B.anchor.epoch ≤
            endpoint.finalized_checkpoint.epoch :=
          CertifiedJustified.anchor_epoch_le (cfg := cfg) hfinalizedGlobal
        have hcomp := P.checkpoint_comp hselectedAccepted hanchorFinalized
          hfinalizedLeE
        calc
          endpoint.finalized_checkpoint =
              B.state.C hQ.target.root
                endpoint.finalized_checkpoint.epoch := hprefix
          _ = B.state.C (B.state.C selected e).root
                endpoint.finalized_checkpoint.epoch := by rw [hQ.target_eq]
          _ = B.state.C selected endpoint.finalized_checkpoint.epoch := hcomp
  have hreflect := B.coherence.checkpoint_of_known hqueryCausal selected
    hselectedQ' endpoint.finalized_checkpoint.epoch
  have heq : endpoint.finalized_checkpoint =
      get_checkpoint_for_block cfg query selected
        endpoint.finalized_checkpoint.epoch := hsemantic.trans hreflect
  have hroot := congrArg Checkpoint.root heq
  simpa only [endpoint, query, get_checkpoint_for_block] using hroot

/-- Producer-shaped replacement for `AcceptedFinalizedPlacementBeforeQueryAt`.
The old pre-query target argument is accepted for interface compatibility but
is no longer used: the retained historical lineage is the stronger temporal
base. -/
theorem EarlySelectedEndpointPhase.acceptedFinalizedPlacementBeforeQueryAt_of_lineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {q : Nat}
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {w : ValidatorIndex} {m : Nat}
    {selected : Root} {e : Epoch}
    (hphase : EarlySelectedEndpointPhase e
      (get_current_store_epoch cfg (E.store cfg ext v q))
      (get_current_store_epoch cfg (E.store cfg ext w m)))
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (hselectedQ : selected ∈ query.store.block_roots)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hselectedEpoch : get_block_epoch cfg query.store selected = e) :
    E.AcceptedFinalizedPlacementBeforeQueryAt
      cfg ext B query q selected w m := by
  intro _hpre
  have hselectedQ' : selected ∈
      (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hselectedQ
  have hselectedEpoch' : get_block_epoch cfg
      (E.store cfg ext v q) selected = e := by
    simpa only [← hquery] using hselectedEpoch
  have hplacement := hphase.finalizedRoot_eq_queryCheckpointBlock_of_lineage
    cfg ext B hT hphase0 hanchor hboundary P V hanchorExact hacc hA hlineage
      hselectedQ' hselectedM hselectedEpoch'
  simpa only [← hquery] using hplacement

namespace AcceptedRetainedPhaseSourceCarrierAt

/-- Direct early-phase consumer for the retained historical A3.2 lineage.

The lineage first identifies the endpoint finalized checkpoint on `selected`
in the concrete query store.  Trusted-anchor walks transport that executable
checkpoint computation to the endpoint store, and the retained carrier's
ancestry then extends it to the unchanged source tip.  No finalized-target
formation time or dummy pre-query witness appears in the interface. -/
theorem finalized_check_of_earlyHistoricalLineage
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {q : Nat}
    {w : ValidatorIndex} {m : Nat}
    {selected : Root} {e : Epoch}
    (hphase : EarlySelectedEndpointPhase e
      (get_current_store_epoch cfg (E.store cfg ext v q))
      (get_current_store_epoch cfg (E.store cfg ext w m)))
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B
      (E.store cfg ext w m) selected)
    (hselectedQuery : selected ∈
      (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e) :
    (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext w m) h.tip
        (E.store cfg ext w m).finalized_checkpoint.epoch := by
  have hplacement :=
    hphase.finalizedRoot_eq_queryCheckpointBlock_of_lineage
      cfg ext B hT hphase0 hanchor hboundary P V hanchorExact hacc hA
        hlineage hselectedQuery h.selected_known hselectedEpoch
  have hqueryCausal : E.CausalStore cfg ext (E.store cfg ext v q) :=
    E.store_causal cfg ext v q
  have hqueryParent : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled v q
  have hendpointParent : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled w m
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hanchorLeFinalized : B.anchor.epoch ≤
      (E.store cfg ext w m).finalized_checkpoint.epoch := by
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
        cfg ext B hgenShort hanchor h.store_causal with
      hfinalizedAnchor | ⟨_finalizedCarrier, _hcarrier, hfinalized⟩
    · rw [hfinalizedAnchor]
    · obtain ⟨hfinalized⟩ := hfinalized
      exact IncludedCertifiedJustified.anchor_epoch_le
        (cfg := cfg) hfinalized.justified
  have hlineageCertified : CertifiedJustified cfg E B.anchor
      (B.state.C hlineage.origin e) :=
    Classical.choice hlineage.payload.certified
  have hanchorLeE : B.anchor.epoch ≤ e := by
    have hle := CertifiedJustified.anchor_epoch_le
      (cfg := cfg) hlineageCertified
    simpa only [B.state.checkpoint_epoch] using hle
  have hselectedBlocks : (E.store cfg ext v q).blocks selected =
      (E.store cfg ext w m).blocks selected :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m)
      hselectedQuery h.selected_known
  have hselectedEpochEndpoint : get_block_epoch cfg
      (E.store cfg ext w m) selected = e := by
    simpa only [get_block_epoch, ← hselectedBlocks] using hselectedEpoch
  have hfinalizedLeSelected :
      (E.store cfg ext w m).finalized_checkpoint.epoch ≤
        get_block_epoch cfg (E.store cfg ext w m) selected := by
    by_cases hfinalizedAnchor :
        (E.store cfg ext w m).finalized_checkpoint = B.anchor
    · rw [hfinalizedAnchor, hselectedEpochEndpoint]
      exact hanchorLeE
    · exact hphase.finalizedEpoch_le_selected_of_nonanchor
        cfg ext B hT hanchor hselectedQuery h.selected_known
          hselectedEpoch hfinalizedAnchor
  have hquerySelectedWalk : WalkKnown (E.store cfg ext v q)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) selected :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchor hboundary v q hanchorLeFinalized hselectedQuery
  have hendpointSelectedWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) selected :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchor hboundary w m hanchorLeFinalized h.selected_known
  have hendpointTipWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) h.tip :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchor hboundary w m hanchorLeFinalized h.tip_known
  have hselectedTransport :
      get_checkpoint_block cfg (E.store cfg ext v q) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch =
        get_checkpoint_block cfg (E.store cfg ext w m) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
    hqueryCausal.getCheckpointBlock_eq_of_pairedWalks cfg ext
      hT.wellFormed h.store_causal hqueryParent hendpointParent
        hquerySelectedWalk hendpointSelectedWalk
  have hfinalizedSelected :
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg (E.store cfg ext w m) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
    hplacement.trans hselectedTransport
  have hboundarySelectedEndpoint : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      ((E.store cfg ext w m).blocks selected).slot := by
    calc
      compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch ≤
          compute_start_slot_at_epoch cfg
            (get_block_epoch cfg (E.store cfg ext w m) selected) :=
        Nat.mul_le_mul_right cfg.slots_per_epoch hfinalizedLeSelected
      _ ≤ ((E.store cfg ext w m).blocks selected).slot :=
        start_slot_at_block_epoch_le cfg (E.store cfg ext w m) selected
  exact finalized_check_of_ancestor cfg hendpointParent
    h.tip_descends_selected hboundarySelectedEndpoint hendpointTipWalk
      hfinalizedSelected

end AcceptedRetainedPhaseSourceCarrierAt


end Execution

end FastConfirmation.Spec
