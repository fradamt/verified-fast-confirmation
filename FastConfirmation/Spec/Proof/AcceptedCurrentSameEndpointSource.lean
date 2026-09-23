module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedCurrentSameSourceHistory
public import FastConfirmation.Spec.Proof.AcceptedPhaseSourceCarriers
public import FastConfirmation.Spec.Proof.AcceptedFFGJustifiedMaximality
public import FastConfirmation.Spec.Proof.ExactCheckpointLinks
public import FastConfirmation.Spec.Proof.AcceptedHistoricalFinalizedPlacement
public import FastConfirmation.Spec.Proof.AcceptedRealizedJustifiedOrigin
public import FastConfirmation.Spec.Proof.AcceptedHistoricalFinalizedPlacementAdapters
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section


/-!
# Current-same historical source transport to an endpoint

This module transports the two outcomes of the strict current-same source
history argument to a concrete honest endpoint.  The positive recent-carrier
arm is entirely mechanical: relay the retained historical tip, reflect its
accepted semantic ancestry, transport its fixed-root source epoch, and extend
to an endpoint leaf.

The apparent justified fallback is eliminated locally.  The past covering
justified checkpoint is forced to the selected/current epoch, and the exact
handler trajectory says that every realized justified value comes from
either `GJ` or an old-block `GU`.  Its accepted installer is therefore a
recent executable source seed above the selected result.  No generic
cross-store justified monotonicity, takeover, or safety premise is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Honest formation target for a realized justified field -/

/-- A concrete honest ground vote which targeted a non-anchor accepted
store-global justified checkpoint before the endpoint containing its accepted
formation carrier. -/
structure AcceptedHonestJustifiedTargetAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (w : ValidatorIndex) (m : Nat) (justified : Checkpoint Root) where
  validator : ValidatorIndex
  vote_slot : Slot
  second : Nat
  index : CommitteeIndex
  validator_honest : validator ∈ E.honest
  second_within : E.WithinHorizon cfg second
  second_slot : E.slot_at cfg second = vote_slot
  vote_eq : E.vote validator vote_slot =
    some (second, honest_attestation cfg ext
      (E.store cfg ext validator second) vote_slot index validator)
  post_anchor : E.slot_at cfg 0 ≤ vote_slot
  before_endpoint : vote_slot < E.slot_at cfg m
  anchor_epoch_lt : B.anchor.epoch < justified.epoch
  target_epoch_eq_vote_epoch :
    justified.epoch = compute_epoch_at_slot cfg vote_slot
  target_eq :
    (honest_attestation cfg ext
      (E.store cfg ext validator second) vote_slot index validator
    ).data.target = justified
  target_walk : WalkKnown (E.store cfg ext validator second)
    (compute_start_slot_at_epoch cfg justified.epoch)
    (get_head cfg (E.store cfg ext validator second)).root

/-- A non-anchor accepted global justified selector exposes its exact honest
causal formation vote.  This is the justified analogue of
`globalFinalized_honestTarget`; it keeps the target head and boundary walk and
does not conclude any selected-branch orientation. -/
theorem globalJustified_honestTarget
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : Nat}
    (hne : (E.store cfg ext w m).justified_checkpoint ≠ B.anchor) :
    Nonempty (E.AcceptedHonestJustifiedTargetAt
      cfg ext B w m (E.store cfg ext w m).justified_checkpoint) := by
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
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
  · exact False.elim (hne hfieldAnchor)
  · obtain ⟨hcarrier⟩ := hevidence
    have hcausal := hcarrier.formed_evidence.causal.resolve_left hne
    obtain ⟨carrierBlock, hcarrierAt, i, hiHonest, voteSlot, groundTime,
        groundVote, hvoteBeforeCarrier, hvoteSlotH, hvoteGround,
        hgroundSlot, hgroundTarget, hincluded⟩ := hcausal
    obtain ⟨hincludedCarrier, _hincludedDesc, hincludedAt⟩ := hincluded
    have hincludedEvidence :=
      B.state.includedAttestations.evidence hincludedAt
    obtain ⟨hcertified⟩ := hcarrier.formed_evidence.certified
    have hanchorLt : B.anchor.epoch <
        (E.store cfg ext w m).justified_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
        (IncludedCertifiedJustified.toCertifiedJustified
          (cfg := cfg)
          (Execution.AcceptedIncludedAttestationRelation.relation
            cfg ext E B.state.includedAttestations) hcertified) hne
    have htargetEpoch : (E.store cfg ext w m).justified_checkpoint.epoch =
        compute_epoch_at_slot cfg voteSlot := by
      rw [← hgroundTarget, ← hgroundSlot]
      exact hincludedEvidence.target_epoch
    have hcommittee : i ∈ E.committee voteSlot :=
      hT.honest_behavior.votes_assigned i hiHonest voteSlot
        (by rw [hvoteGround]; exact Option.some_ne_none _)
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
    obtain ⟨k, index, hHk, hkSlot, hvoteHead⟩ :=
      hT.honest_behavior.votes_head i hiHonest voteSlot hcommittee
        hvoteSlotH hfromZero
    have hvoteEq := hvoteGround
    rw [hvoteHead] at hvoteEq
    simp only [Option.some.injEq, Prod.mk.injEq] at hvoteEq
    obtain ⟨_, hgroundVote⟩ := hvoteEq
    have htargetExact :
        (honest_attestation cfg ext (E.store cfg ext i k)
          voteSlot index i).data.target =
            (E.store cfg ext w m).justified_checkpoint := by
      rw [hgroundVote]
      exact hgroundTarget
    have htargetWalk : WalkKnown (E.store cfg ext i k)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).justified_checkpoint.epoch)
        (get_head cfg (E.store cfg ext i k)).root := by
      simpa only [htargetExact] using
        hwalkDomain i hiHonest voteSlot k index hfromZero hHk
          hkSlot hvoteHead
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
    exact ⟨{
      validator := i
      vote_slot := voteSlot
      second := k
      index := index
      validator_honest := hiHonest
      second_within := hHk
      second_slot := hkSlot
      vote_eq := hvoteHead
      post_anchor := hfromZero
      before_endpoint := hvoteBeforeEndpoint
      anchor_epoch_lt := hanchorLt
      target_epoch_eq_vote_epoch := htargetEpoch
      target_eq := htargetExact
      target_walk := htargetWalk
    }⟩

namespace AcceptedRecentCandidateSourceCarrierAt

/-- Relay one historical current-same recent carrier to a later endpoint and
extend it to a childless accepted source tip above the same selected result.

The clock premise is the ordinary query-to-endpoint ordering used by the
selected-edge geometry.  Current-same equality is used only to preserve the
numeric `+2` recency bound. -/
theorem retainedAt_currentSameEndpoint
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    {v : ValidatorIndex} {q : Nat} {selected : Root}
    (h : E.AcceptedRecentCandidateSourceCarrierAt cfg ext B v q selected)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hqueryEndpoint : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcurrentSame : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hselectedEndpoint : selected ∈
      (E.store cfg ext w m).block_roots) :
    Nonempty (E.AcceptedRetainedPhaseSourceCarrierAt
      cfg ext B (E.store cfg ext w m) selected) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hrelayGate : E.slot_at cfg h.second + 1 ≤
      E.slot_at cfg (m + 1) :=
    (Nat.succ_le_of_lt h.strictly_past).trans
      (hqueryEndpoint.trans
        (E.slot_at_mono cfg (Nat.le_succ m)))
  have htipEndpoint : h.tip ∈
      (E.store cfg ext w m).block_roots :=
    hsync.block_relay h.validator h.validator_honest h.second h.tip
      h.second_within h.tip_known w hw m hmH hrelayGate
  have htipSelectedEndpoint : is_ancestor (E.store cfg ext w m)
      (get_node_for_root h.tip) (get_node_for_root selected) = true :=
    E.store_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      htipEndpoint hselectedEndpoint h.tip_semantic_descends_candidate
  have hpastEndpointClock : get_current_store_epoch cfg
      (E.store cfg ext h.validator h.second) ≤
        get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.store_current_slot]
    exact ce_mono cfg (h.strictly_past.le.trans hqueryEndpoint)
  have hrecentEndpoint : get_current_store_epoch cfg
      (E.store cfg ext w m) ≤
        (get_voting_source cfg
          (E.store cfg ext h.validator h.second) h.tip).epoch + 2 := by
    rw [hcurrentSame]
    exact h.source_recent
  have hendpointCausal : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hendpointParent : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled w m
  have hendpointWalk : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ w m
  have hendpointNonfuture : BlocksSlotLe
      (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      hgenShort w m
  exact ⟨E.acceptedRetainedPhaseSourceCarrier_of_queryRecentSeed
    cfg ext B hT.wellFormed
      (E.store_causal cfg ext h.validator h.second) hendpointCausal
      hendpointParent (E.blockProvenance cfg ext w m) hendpointWalk
      hendpointNonfuture hselectedEndpoint h.tip_known htipEndpoint
      htipSelectedEndpoint hpastEndpointClock hrecentEndpoint⟩

end AcceptedRecentCandidateSourceCarrierAt

/-! ## Exact justified-fallback elimination -/

/-- Every accepted store-global justified field has its carrier-local
included certificate, including the trusted-anchor base case. -/
theorem ExactPrefixAcceptedFFGSemantics.acceptedGlobalJustified_includedCertificate
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    ∃ carrier : Root, Nonempty (IncludedCertifiedJustified cfg E
      B.state.includedAttestations.Included B.anchor carrier
        store.justified_checkpoint) := by
  rcases B.globalJustified_anchor_or_AUEvidence hgen hanchor hstore with
      hfieldAnchor | hevidence
  · refine ⟨B.anchor.root, ?_⟩
    rw [hfieldAnchor]
    exact ⟨IncludedCertifiedJustified.anchor⟩
  · obtain ⟨hcarrier⟩ := hevidence
    exact ⟨hcarrier.carrier, hcarrier.formed_evidence.certified⟩

namespace AcceptedPastJustifiedFallbackAt

/-- In the strict current-same fallback, the past covering justified
checkpoint is itself at the selected/current epoch.

The lower bound is geometric: the selected current-epoch block lies below the
past justified root, while certificate exactness places that justified root
at its declared epoch boundary.  The ordinary store checkpoint-epoch bound
gives the reverse inequality. -/
theorem justified_epoch_eq_queryCurrent
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} {q : Nat} {selected : Root}
    (h : E.AcceptedPastJustifiedFallbackAt cfg ext v q selected)
    (hselectedQuery : selected ∈
      (E.store cfg ext v q).block_roots)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v q) selected =
      get_current_store_epoch cfg (E.store cfg ext v q)) :
    (E.store cfg ext h.past.validator h.past.second
      ).justified_checkpoint.epoch =
      get_current_store_epoch cfg (E.store cfg ext v q) := by
  let past := E.store cfg ext h.past.validator h.past.second
  let e := get_current_store_epoch cfg (E.store cfg ext v q)
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hpastCausal : E.CausalStore cfg ext past := by
    simpa only [past] using
      E.store_causal cfg ext h.past.validator h.past.second
  have hpastParent : ParentSlotLt past := by
    simpa only [past] using
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
        hT.wellFormed.anchor_parent_unscheduled
        h.past.validator h.past.second
  have hpastWalk : ∀ t ∈ past.block_roots, ∀ r ∈ past.block_roots,
      WalkKnown past (past.blocks t).slot r := by
    simpa only [past] using
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
        h.past.validator h.past.second
  have hselectedBlocks : (E.store cfg ext v q).blocks selected =
      past.blocks selected := by
    simpa only [past] using hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext h.past.validator h.past.second)
      hselectedQuery h.past.candidate_known
  have hselectedPastEpoch : get_block_epoch cfg past selected = e := by
    simpa only [e, get_block_epoch, ← hselectedBlocks] using hcurrent
  obtain ⟨jCarrier, hjIncluded⟩ :=
    ExactPrefixAcceptedFFGSemantics.acceptedGlobalJustified_includedCertificate
      (E := E) cfg ext B hgenShort hanchor hpastCausal
  obtain ⟨hjIncluded⟩ := hjIncluded
  have hjCertified : CertifiedJustified cfg E B.anchor
      past.justified_checkpoint :=
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.AcceptedIncludedAttestationRelation.relation
        cfg ext E B.state.includedAttestations) hjIncluded
  have hanchorLeJ : B.anchor.epoch ≤ past.justified_checkpoint.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hjCertified
  have hjKnown : past.justified_checkpoint.root ∈ past.block_roots := by
    simpa only [past] using hdomain.justified_root_known
      h.past.validator h.past.validator_honest h.past.second
        h.past.second_within
  have hjWalk : WalkKnown past
      (compute_start_slot_at_epoch cfg past.justified_checkpoint.epoch)
      past.justified_checkpoint.root := by
    simpa only [past] using
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary h.past.validator h.past.second
          hanchorLeJ (by simpa only [past] using hjKnown)
  have hjSelf : past.justified_checkpoint =
      B.state.C past.justified_checkpoint.root
        past.justified_checkpoint.epoch :=
    IncludedCertifiedJustified.exact_self (cfg := cfg) P V
      hanchorExact hjIncluded
  have hjReflect := B.coherence.checkpoint_of_known hpastCausal
    past.justified_checkpoint.root hjKnown
      past.justified_checkpoint.epoch
  have hjExecutable : past.justified_checkpoint =
      get_checkpoint_for_block cfg past past.justified_checkpoint.root
        past.justified_checkpoint.epoch :=
    hjSelf.trans hjReflect
  have hjRoot : past.justified_checkpoint.root =
      get_checkpoint_block cfg past past.justified_checkpoint.root
        past.justified_checkpoint.epoch := by
    have := congrArg Checkpoint.root hjExecutable
    simpa only [get_checkpoint_for_block] using this
  have hjSpec := get_ancestor_spec hpastParent hjWalk
  rw [get_checkpoint_block] at hjRoot
  rw [← hjRoot] at hjSpec
  have hselectedSlotLeJ : (past.blocks selected).slot ≤
      (past.blocks past.justified_checkpoint.root).slot :=
    ancestor_slot_le hpastParent
      (hpastWalk selected h.past.candidate_known
        past.justified_checkpoint.root hjKnown)
      (by simpa only [past] using h.justified_descends_candidate)
  have heLeJScaled : e * cfg.slots_per_epoch ≤
      past.justified_checkpoint.epoch * cfg.slots_per_epoch := by
    calc
      e * cfg.slots_per_epoch = compute_start_slot_at_epoch cfg e := rfl
      _ ≤ (past.blocks selected).slot := by
        rw [← hselectedPastEpoch]
        exact start_slot_at_block_epoch_le cfg past selected
      _ ≤ (past.blocks past.justified_checkpoint.root).slot :=
        hselectedSlotLeJ
      _ ≤ compute_start_slot_at_epoch cfg
          past.justified_checkpoint.epoch := hjSpec.2
      _ = past.justified_checkpoint.epoch * cfg.slots_per_epoch := rfl
  have heLeJ : e ≤ past.justified_checkpoint.epoch :=
    Nat.le_of_mul_le_mul_right heLeJScaled cfg.slots_per_epoch_pos
  have hjLePast : past.justified_checkpoint.epoch ≤
      get_current_store_epoch cfg past := by
    simpa only [past] using E.store_justified_epoch_le cfg ext
      hT.externals_coherence hT.whole_seconds hgenShort
        h.past.validator h.past.second
  have hpastLeQuery : get_current_store_epoch cfg past ≤ e := by
    simp only [past, e, get_current_store_epoch, E.store_current_slot]
    exact ce_mono cfg h.past.strictly_past.le
  exact Nat.le_antisymm (hjLePast.trans hpastLeQuery) heLeJ

/-! ## Elimination of the direct-justified fallback -/

/-- The executable-origin invariant turns the direct justified fallback into
a recent seed on the selected branch.

For a `GJ` origin, the executable source is either that same `GJ` or the
larger `GU`.  For a `GU` origin, the strengthened handler invariant records
the old-block guard, so the executable selector is exactly `GU`.  The anchor
arm uses positive AU/certificate evidence for the anchor-root source. -/
theorem retainedAt_currentSameEndpoint
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} {q : Nat} {selected : Root}
    (h : E.AcceptedPastJustifiedFallbackAt cfg ext v q selected)
    (hselectedQuery : selected ∈
      (E.store cfg ext v q).block_roots)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v q) selected =
      get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hqueryEndpoint : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcurrentSame : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hselectedEndpoint : selected ∈
      (E.store cfg ext w m).block_roots) :
    Nonempty (E.AcceptedRetainedPhaseSourceCarrierAt
      cfg ext B (E.store cfg ext w m) selected) := by
  let past := E.store cfg ext h.past.validator h.past.second
  let endpoint := E.store cfg ext w m
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hpastCausal : E.CausalStore cfg ext past := by
    simpa only [past] using
      E.store_causal cfg ext h.past.validator h.past.second
  have hpastParent : ParentSlotLt past := by
    simpa only [past] using
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
        hT.wellFormed.anchor_parent_unscheduled
        h.past.validator h.past.second
  have hpastWalk : ∀ t ∈ past.block_roots, ∀ r ∈ past.block_roots,
      WalkKnown past (past.blocks t).slot r := by
    simpa only [past] using
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
        h.past.validator h.past.second
  have hjKnown : past.justified_checkpoint.root ∈ past.block_roots := by
    simpa only [past] using hdomain.justified_root_known
      h.past.validator h.past.validator_honest h.past.second
        h.past.second_within
  have hjEpoch : past.justified_checkpoint.epoch =
      get_current_store_epoch cfg (E.store cfg ext v q) := by
    simpa only [past] using h.justified_epoch_eq_queryCurrent cfg ext hT
      hanchor hboundary P V hanchorExact hdomain hselectedQuery hcurrent
  have hjSemantic : E.RootDescends past.justified_checkpoint.root selected :=
    E.rootDescends_of_store_ancestor
      (E.blockProvenance cfg ext h.past.validator h.past.second)
      hpastParent
      (hpastWalk selected h.past.candidate_known
        past.justified_checkpoint.root hjKnown)
      (by simpa only [past] using h.justified_descends_candidate)
  have horigins := E.acceptedRealizedJustifiedOrigins cfg ext B hT hanchor
    h.past.validator h.past.second
  have hseed : ∃ seed : Root,
      seed ∈ past.block_roots ∧
      E.RootDescends seed selected ∧
      get_current_store_epoch cfg (E.store cfg ext v q) ≤
        (get_voting_source cfg past seed).epoch + 2 := by
    rcases horigins.realized with hfieldAnchor |
        ⟨seed, hseedCarrier, hgj | ⟨hgu, hseedOld⟩⟩
    · let seed := past.justified_checkpoint.root
      have hsourceAU := hpastCausal.getVotingSource_AU cfg ext B hjKnown
      obtain ⟨carrier, _hdesc, hformed⟩ := hsourceAU
      obtain ⟨hcertified⟩ :=
        (B.state.formed_evidence hformed).certified
      have hanchorLeSource : B.anchor.epoch ≤
          (get_voting_source cfg past seed).epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg)
          (IncludedCertifiedJustified.toCertifiedJustified
            (cfg := cfg)
            (Execution.AcceptedIncludedAttestationRelation.relation
              cfg ext E B.state.includedAttestations) hcertified)
      refine ⟨seed, hjKnown, hjSemantic, ?_⟩
      rw [← hjEpoch, hfieldAnchor]
      exact hanchorLeSource.trans (Nat.le_add_right _ _)
    · have hseedKnown : seed ∈ past.block_roots := hseedCarrier.known
      have hseedAccepted := hseedCarrier.acceptedRoot
      have hseedJ : E.RootDescends seed past.justified_checkpoint.root := by
        obtain ⟨carrier, hseedCarrierDesc, hformed⟩ :=
          B.state.gj_AU cfg ext hseedAccepted
        have honChain : E.RootDescends carrier
            past.justified_checkpoint.root := by
          simpa only [← hgj] using
            (B.state.formed_evidence hformed).on_chain
        exact Execution.RootDescends.trans E hseedCarrierDesc
          honChain
      have hsourceLower : past.justified_checkpoint.epoch ≤
          (get_voting_source cfg past seed).epoch := by
        rw [hpastCausal.getVotingSource_eq_acceptedSelector cfg ext B
          hseedKnown]
        split_ifs with hold
        · rw [hgj]
          exact B.state.gj_epoch_le_gu cfg ext hseedAccepted
        · rw [hgj]
      refine ⟨seed, hseedKnown,
        Execution.RootDescends.trans E hseedJ hjSemantic, ?_⟩
      rw [← hjEpoch]
      exact hsourceLower.trans (Nat.le_add_right _ _)
    · have hseedKnown : seed ∈ past.block_roots := hseedCarrier.known
      have hseedAccepted := hseedCarrier.acceptedRoot
      have hseedJ : E.RootDescends seed past.justified_checkpoint.root := by
        obtain ⟨carrier, hseedCarrierDesc, hformed⟩ :=
          B.state.gu_AU cfg ext hseedAccepted
        have honChain : E.RootDescends carrier
            past.justified_checkpoint.root := by
          simpa only [← hgu] using
            (B.state.formed_evidence hformed).on_chain
        exact Execution.RootDescends.trans E hseedCarrierDesc
          honChain
      have hsourceEq : get_voting_source cfg past seed = B.state.GU seed := by
        rw [hpastCausal.getVotingSource_eq_acceptedSelector cfg ext B
          hseedKnown]
        exact if_pos hseedOld
      refine ⟨seed, hseedKnown,
        Execution.RootDescends.trans E hseedJ hjSemantic, ?_⟩
      rw [← hjEpoch, hgu, hsourceEq]
      exact Nat.le_add_right _ _
  obtain ⟨seed, hseedPast, hseedSemantic, hrecentPast⟩ := hseed
  have hrelayGate : E.slot_at cfg h.past.second + 1 ≤
      E.slot_at cfg (m + 1) :=
    (Nat.succ_le_of_lt h.past.strictly_past).trans
      (hqueryEndpoint.trans (E.slot_at_mono cfg (Nat.le_succ m)))
  have hseedEndpoint : seed ∈ endpoint.block_roots := by
    simpa only [endpoint] using
      hsync.block_relay h.past.validator h.past.validator_honest
        h.past.second seed h.past.second_within hseedPast w hw m hmH
          hrelayGate
  have hseedSelectedEndpoint : is_ancestor endpoint
      (get_node_for_root seed) (get_node_for_root selected) = true := by
    simpa only [endpoint] using
      E.store_ancestor_of_rootDescends_for_storeReflection cfg ext
        hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
        hseedEndpoint hselectedEndpoint hseedSemantic
  have hpastEndpointClock : get_current_store_epoch cfg past ≤
      get_current_store_epoch cfg endpoint := by
    simp only [past, endpoint, get_current_store_epoch,
      E.store_current_slot]
    exact ce_mono cfg (h.past.strictly_past.le.trans hqueryEndpoint)
  have hrecentEndpointClock : get_current_store_epoch cfg endpoint ≤
      (get_voting_source cfg past seed).epoch + 2 := by
    rw [hcurrentSame]
    exact hrecentPast
  have hendpointCausal : E.CausalStore cfg ext endpoint := by
    simpa only [endpoint] using E.store_causal cfg ext w m
  have hendpointParent : ParentSlotLt endpoint := by
    simpa only [endpoint] using
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
        hT.wellFormed.anchor_parent_unscheduled w m
  have hendpointWalk : ∀ t ∈ endpoint.block_roots,
      ∀ r ∈ endpoint.block_roots,
        WalkKnown endpoint (endpoint.blocks t).slot r := by
    simpa only [endpoint] using
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ w m
  have hendpointNonfuture : BlocksSlotLe
      (get_current_slot cfg endpoint) endpoint := by
    simpa only [endpoint] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        hgenShort w m
  exact ⟨E.acceptedRetainedPhaseSourceCarrier_of_queryRecentSeed
    cfg ext B hT.wellFormed hpastCausal hendpointCausal
      hendpointParent (E.blockProvenance cfg ext w m) hendpointWalk
      hendpointNonfuture hselectedEndpoint hseedPast hseedEndpoint
      hseedSelectedEndpoint hpastEndpointClock hrecentEndpointClock⟩

end AcceptedPastJustifiedFallbackAt

namespace AcceptedCurrentSameSourceHistoryOutcome

/-- Both exact outcomes of the strict current-same history proof now produce
the same retained endpoint carrier.  The former direct-justified arm is
discharged by the executable-origin invariant rather than a cross-store
checkpoint monotonicity premise. -/
theorem retainedAt_currentSameEndpoint
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} {q : Nat} {selected : Root}
    (h : E.AcceptedCurrentSameSourceHistoryOutcome cfg ext B v q selected)
    (hselectedQuery : selected ∈
      (E.store cfg ext v q).block_roots)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v q) selected =
      get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hqueryEndpoint : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcurrentSame : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hselectedEndpoint : selected ∈
      (E.store cfg ext w m).block_roots) :
    Nonempty (E.AcceptedRetainedPhaseSourceCarrierAt
      cfg ext B (E.store cfg ext w m) selected) := by
  rcases h with hjustified | hrecent
  · obtain ⟨hjustified⟩ := hjustified
    exact hjustified.retainedAt_currentSameEndpoint cfg ext hT hsync
      hanchor hboundary P V hanchorExact hdomain hselectedQuery hcurrent
        hw hmH hqueryEndpoint hcurrentSame hselectedEndpoint
  · obtain ⟨hrecent⟩ := hrecent
    exact hrecent.retainedAt_currentSameEndpoint cfg ext hT hsync hw hmH
      hqueryEndpoint hcurrentSame hselectedEndpoint

end AcceptedCurrentSameSourceHistoryOutcome

end Execution

end FastConfirmation.Spec

end
