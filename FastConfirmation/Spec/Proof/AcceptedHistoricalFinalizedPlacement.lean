import FastConfirmation.Spec.Proof.AcceptedPathLocalFinalizedTransport
import FastConfirmation.Spec.Proof.AcceptedResetCheckpointClassification
import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts
import FastConfirmation.Spec.Proof.AcceptedHistoricalA32GlobalTrajectory

/-!
# Historical finalized placement on the retained source tip

The endpoint filter needs its exact finalized checkpoint equation on the
same retained tip which carries source recency.  Global finalized origins do
not themselves identify that tip: their installer can be an unrelated known
block.  This module closes the historically lagging case without making that
invalid identification.

If the endpoint finalized epoch is no later than the query finalized epoch,
accepted global provenance and exact certificate accountability give an
epoch-indexed prefix from `endpoint.F` to `query.F`.  The query's executable
filter witness first realizes `query.F` on the selected result.  Paired causal
walks transport that exact computation to the endpoint selected result, and
checkpoint composition realizes the older `endpoint.F` there.  The retained
source tip is a descendant of the selected result, so one final boundary walk
finishes the executable check.

No ordinary `RootDescends` fact is substituted for an exact checkpoint
prefix.  No global installer is merged with the retained source carrier, and
the statements assume no source visibility, AU for a finalized checkpoint at
the retained tip, filter result, `SafeFrom`, justification interface,
selected-margin bundle, or safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

namespace ExactPrefixAcceptedFFGSemantics

/-- Two accepted store-global finalized checkpoints are related by an exact
checkpoint prefix whenever their epochs are ordered.

The later finalized checkpoint contributes its included *justification*
certificate.  The earlier checkpoint is either the trusted anchor or has its
own included finalization certificate.  Certificate accountability is
cross-carrier, so the two global installer tips need not be equal or
comparable. -/
theorem globalFinalized_exactPrefix_of_epoch_le
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {earlier later : Store Root}
    (hearlier : E.CausalStore cfg ext earlier)
    (hlater : E.CausalStore cfg ext later)
    (hepoch : earlier.finalized_checkpoint.epoch ≤
      later.finalized_checkpoint.epoch) :
    ExactCheckpointPrefix B.state.C earlier.finalized_checkpoint
      later.finalized_checkpoint := by
  rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
      cfg ext B hgen hanchor hlater with hlaterAnchor |
      ⟨laterCarrier, _hlaterCarrier, hlaterFinalized⟩
  · have hlaterJustified : IncludedCertifiedJustified cfg E
        B.state.includedAttestations.Included B.anchor B.anchor.root
        later.finalized_checkpoint := by
      rw [hlaterAnchor]
      exact IncludedCertifiedJustified.anchor
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
        cfg ext B hgen hanchor hearlier with hearlierAnchor |
        ⟨earlierCarrier, _hearlierCarrier, hearlierFinalized⟩
    · rw [hearlierAnchor]
      exact IncludedCertifiedJustified.anchor_prefix
        (cfg := cfg) P V hanchorExact hlaterJustified
    · obtain ⟨hearlierFinalized⟩ := hearlierFinalized
      exact B.state.exactFinalizedPrefix_of_accountable cfg P V
        hanchorExact hacc hearlierFinalized hlaterJustified hepoch
  · obtain ⟨hlaterFinalized⟩ := hlaterFinalized
    have hlaterJustified : IncludedCertifiedJustified cfg E
        B.state.includedAttestations.Included B.anchor laterCarrier
        later.finalized_checkpoint := hlaterFinalized.justified
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
        cfg ext B hgen hanchor hearlier with hearlierAnchor |
        ⟨earlierCarrier, _hearlierCarrier, hearlierFinalized⟩
    · rw [hearlierAnchor]
      exact IncludedCertifiedJustified.anchor_prefix
        (cfg := cfg) P V hanchorExact hlaterJustified
    · obtain ⟨hearlierFinalized⟩ := hearlierFinalized
      exact B.state.exactFinalizedPrefix_of_accountable cfg P V
        hanchorExact hacc hearlierFinalized hlaterJustified hepoch

end ExactPrefixAcceptedFFGSemantics

/-! ## Honest target carried by an accepted finalization -/

/-- A concrete honest vote which targeted an accepted finalized checkpoint
before the store containing its certificate carrier.

This is the useful inner result of the older reset-root-delivery argument.
It retains the voter's actual executable head and target-boundary walk rather
than concluding only that the finalized root was relayed somewhere. -/
structure AcceptedHonestFinalizedTargetAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (w : ValidatorIndex) (m : Nat) (finalized : Checkpoint Root) where
  validator : ValidatorIndex
  vote_slot : Slot
  second : Nat
  index : CommitteeIndex
  validator_honest : validator ∈ E.honest
  second_within : E.WithinHorizon cfg second
  second_slot : E.slot_at cfg second = vote_slot
  post_anchor : E.slot_at cfg 0 ≤ vote_slot
  before_endpoint : vote_slot < E.slot_at cfg m
  anchor_epoch_lt : B.anchor.epoch < finalized.epoch
  target_eq :
    (honest_attestation cfg ext
      (E.store cfg ext validator second) vote_slot index validator
    ).data.target = finalized
  target_walk : WalkKnown (E.store cfg ext validator second)
    (compute_start_slot_at_epoch cfg finalized.epoch)
    (get_head cfg (E.store cfg ext validator second)).root

/-- A non-anchor accepted global finalized selector exposes the honest ground
vote stored in its exact accepted formation evidence.

No quorum is reconstructed here.  The accepted AU trajectory already retains
the causal ground vote, its inclusion before the formed carrier, and that
carrier's exact accepted block.  Honest voting identifies the ground vote
with the executable validator-spec attestation; accepted reflection places
the formed carrier in the endpoint store and hence preserves the strict
before-endpoint bound. -/
theorem globalFinalized_honestTarget
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : Nat}
    (hne : (E.store cfg ext w m).finalized_checkpoint ≠ B.anchor) :
    Nonempty (E.AcceptedHonestFinalizedTargetAt
      cfg ext B w m (E.store cfg ext w m).finalized_checkpoint) := by
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
  have hanchorEpoch : B.anchor.epoch =
      compute_epoch_at_slot cfg ast.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at he
    simpa only [get_forkchoice_store, get_current_epoch] using he
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
  rcases B.globalFinalized_anchor_or_AUEvidence hgenShort hanchor hstore with
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
        (E.store cfg ext w m).finalized_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
        (IncludedCertifiedJustified.toCertifiedJustified
          (cfg := cfg)
          (Execution.AcceptedIncludedAttestationRelation.relation
            cfg ext E B.state.includedAttestations) hcertified) hne
    have htargetEpoch : (E.store cfg ext w m).finalized_checkpoint.epoch =
        compute_epoch_at_slot cfg voteSlot := by
      rw [← hgroundTarget, ← hgroundSlot]
      exact hincludedEvidence.target_epoch
    have hcommittee : i ∈ E.committee voteSlot :=
      hT.honest_behavior.votes_assigned i hiHonest voteSlot
        (by rw [hvoteGround]; exact Option.some_ne_none _)
    have hstartMono : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorLt.le
    have hstartVote : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤ voteSlot := by
      have hmulDiv := Nat.div_mul_le_self voteSlot cfg.slots_per_epoch
      have hdiv : voteSlot / cfg.slots_per_epoch =
          (E.store cfg ext w m).finalized_checkpoint.epoch := by
        simpa only [compute_epoch_at_slot] using htargetEpoch.symm
      rw [hdiv] at hmulDiv
      simpa only [compute_start_slot_at_epoch] using hmulDiv
    have hfromZero : E.slot_at cfg 0 ≤ voteSlot := by
      calc
        E.slot_at cfg 0 = ast.slot := hslotZero
        _ = ablk.message.slot := hslot
        _ ≤ compute_start_slot_at_epoch cfg B.anchor.epoch := hboundary'
        _ ≤ compute_start_slot_at_epoch cfg
            (E.store cfg ext w m).finalized_checkpoint.epoch := hstartMono
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
            (E.store cfg ext w m).finalized_checkpoint := by
      rw [hgroundVote]
      exact hgroundTarget
    have htargetWalk : WalkKnown (E.store cfg ext i k)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch)
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
      post_anchor := hfromZero
      before_endpoint := hvoteBeforeEndpoint
      anchor_epoch_lt := hanchorLt
      target_eq := htargetExact
      target_walk := htargetWalk
    }⟩

/-- The exact historical residue left when the honest formation vote for an
endpoint finalized checkpoint predates the selected query.  The witness keeps
the executable vote head and target walk; it is not weakened to timeless
checkpoint ancestry. -/
def AcceptedFinalizedTargetBeforeQueryAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (q : Nat) (w : ValidatorIndex) (m : Nat) : Prop :=
  ∃ htarget : E.AcceptedHonestFinalizedTargetAt cfg ext B w m
      (E.store cfg ext w m).finalized_checkpoint,
    htarget.vote_slot < E.slot_at cfg q

/-- Consumer-shaped post-query canonicality for finalized formation votes.
It adds selected-root knownness to the ordinary head induction because paired
checkpoint transport needs the concrete selected root in both stores. -/
def SelectedCanonicalForFinalizedTargetsAfterQueryAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (q : Nat) (selected : Root) (w : ValidatorIndex) (m : Nat) : Prop :=
  ∀ htarget : E.AcceptedHonestFinalizedTargetAt cfg ext B w m
      (E.store cfg ext w m).finalized_checkpoint,
    E.slot_at cfg q ≤ htarget.vote_slot →
      selected ∈
          (E.store cfg ext htarget.validator htarget.second).block_roots ∧
        is_ancestor (E.store cfg ext htarget.validator htarget.second)
          (get_head cfg
            (E.store cfg ext htarget.validator htarget.second))
          (get_node_for_root selected) = true

namespace AcceptedRetainedPhaseSourceCarrierAt

/-- An honest finalized-target head on the selected branch realizes the
endpoint finalized checkpoint on the retained source tip.

The vote fixes the exact checkpoint computation on its executable head.
Because the head descends `selected` and `selected` is no earlier than the
finalized boundary, the same computation holds on `selected`.  Paired causal
walks transport only that selected-root computation to the endpoint store;
the retained tip then extends it.  In particular, no global AU installer is
identified with either `selected` or the retained tip. -/
theorem finalized_check_of_honestTargetOnSelected
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : Nat} {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B
      (E.store cfg ext w m) selected)
    (htarget : E.AcceptedHonestFinalizedTargetAt cfg ext B w m
      (E.store cfg ext w m).finalized_checkpoint)
    (hselectedVote : selected ∈
      (E.store cfg ext htarget.validator htarget.second).block_roots)
    (hheadDescendsSelected : is_ancestor
      (E.store cfg ext htarget.validator htarget.second)
      (get_head cfg
        (E.store cfg ext htarget.validator htarget.second))
      (get_node_for_root selected) = true)
    (hboundarySelectedVote : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      ((E.store cfg ext htarget.validator
        htarget.second).blocks selected).slot) :
    (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext w m) h.tip
        (E.store cfg ext w m).finalized_checkpoint.epoch := by
  have hparentVote : ParentSlotLt
      (E.store cfg ext htarget.validator htarget.second) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled
      htarget.validator htarget.second
  have hparentEndpoint : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled w m
  have hselectedVoteWalk : WalkKnown
      (E.store cfg ext htarget.validator htarget.second)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) selected :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchor hboundary htarget.validator htarget.second
        htarget.anchor_epoch_lt.le hselectedVote
  have hselectedEndpointWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) selected :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchor hboundary w m htarget.anchor_epoch_lt.le h.selected_known
  have htipEndpointWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) h.tip :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchor hboundary w m htarget.anchor_epoch_lt.le h.tip_known
  have htargetAtHead :
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg
          (E.store cfg ext htarget.validator htarget.second)
          (get_head cfg
            (E.store cfg ext htarget.validator htarget.second)).root
          (E.store cfg ext w m).finalized_checkpoint.epoch := by
    have htargetData : (honest_attestation_data cfg ext
        (E.store cfg ext htarget.validator htarget.second)
        htarget.vote_slot htarget.index).target =
          (E.store cfg ext w m).finalized_checkpoint := by
      simpa only [honest_attestation_data_eq] using htarget.target_eq
    have hroot := honest_attestation_data_target_root cfg ext
      (E.store cfg ext htarget.validator htarget.second)
      htarget.vote_slot htarget.index
    rw [htargetData] at hroot
    exact hroot
  have htargetAtVoteSelected :
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg
          (E.store cfg ext htarget.validator htarget.second) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
    htargetAtHead.trans
      (get_checkpoint_block_of_ancestor cfg hparentVote
        hheadDescendsSelected hboundarySelectedVote htarget.target_walk)
  have hselectedTransport :
      get_checkpoint_block cfg
          (E.store cfg ext htarget.validator htarget.second) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch =
        get_checkpoint_block cfg (E.store cfg ext w m) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
    (E.store_causal cfg ext htarget.validator htarget.second
      ).getCheckpointBlock_eq_of_pairedWalks cfg ext hT.wellFormed
        (E.store_causal cfg ext w m) hparentVote hparentEndpoint
          hselectedVoteWalk hselectedEndpointWalk
  have htargetAtEndpointSelected :
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg (E.store cfg ext w m) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
    htargetAtVoteSelected.trans hselectedTransport
  have hselectedBlocks :
      (E.store cfg ext htarget.validator htarget.second).blocks selected =
        (E.store cfg ext w m).blocks selected :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext htarget.validator htarget.second)
      (E.blockProvenance cfg ext w m) hselectedVote h.selected_known
  have hboundarySelectedEndpoint : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      ((E.store cfg ext w m).blocks selected).slot := by
    simpa only [← hselectedBlocks] using hboundarySelectedVote
  exact finalized_check_of_ancestor cfg hparentEndpoint
    h.tip_descends_selected hboundarySelectedEndpoint htipEndpointWalk
      htargetAtEndpointSelected

/-- Split a non-anchor endpoint finalization at the selected query time.

If its accepted honest formation vote is post-query, the selected-head
induction places that vote's executable head above `selected`, and the
preceding theorem closes exact finality on the retained tip.  Otherwise the
conclusion is precisely the pre-query formation witness which a historical
base case must consume. -/
theorem finalized_check_or_targetBeforeQuery
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {q : Nat} {w : ValidatorIndex} {m : Nat} {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B
      (E.store cfg ext w m) selected)
    (hne : (E.store cfg ext w m).finalized_checkpoint ≠ B.anchor)
    (hcanonical : E.SelectedCanonicalForFinalizedTargetsAfterQueryAt
      cfg ext B q selected w m)
    (hboundarySelectedEndpoint : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      ((E.store cfg ext w m).blocks selected).slot) :
    E.AcceptedFinalizedTargetBeforeQueryAt cfg ext B q w m ∨
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg (E.store cfg ext w m) h.tip
          (E.store cfg ext w m).finalized_checkpoint.epoch := by
  obtain ⟨htarget⟩ :=
    E.globalFinalized_honestTarget cfg ext B hT hanchor hboundary hne
  by_cases hpre : htarget.vote_slot < E.slot_at cfg q
  · exact Or.inl ⟨htarget, hpre⟩
  · right
    obtain ⟨hselectedVote, hheadSelected⟩ :=
      hcanonical htarget (Nat.le_of_not_gt hpre)
    have hselectedBlocks :
        (E.store cfg ext htarget.validator htarget.second).blocks selected =
          (E.store cfg ext w m).blocks selected :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext htarget.validator htarget.second)
        (E.blockProvenance cfg ext w m) hselectedVote h.selected_known
    have hboundarySelectedVote : compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch ≤
        ((E.store cfg ext htarget.validator htarget.second
          ).blocks selected).slot := by
      simpa only [hselectedBlocks] using hboundarySelectedEndpoint
    exact h.finalized_check_of_honestTargetOnSelected cfg ext hT
      hanchor hboundary htarget hselectedVote hheadSelected
        hboundarySelectedVote

/-- Exact finalized placement when the endpoint finalized checkpoint lags
the query finalized checkpoint.

The query viable leaf is used only to place `query.F` on `selected`.  The raw
query leaf is neither identified with nor required to be known as the
endpoint retained tip.  The only cross-store computation starts at the
common selected root and is justified by paired causal walks. -/
theorem finalized_check_of_laggingQuery
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hwfExecution : WellFormedExecution E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {query endpoint : Store Root}
    (hquery : E.CausalStore cfg ext query)
    (hqueryParent : ParentSlotLt query)
    (hendpointParent : ParentSlotLt endpoint)
    {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B endpoint selected)
    (hselectedQuery : selected ∈ query.block_roots)
    (hviable : PathLocalFilterViableLeafBelow cfg query selected)
    (hepoch : endpoint.finalized_checkpoint.epoch ≤
      query.finalized_checkpoint.epoch)
    (hboundarySelectedQuery : compute_start_slot_at_epoch cfg
      query.finalized_checkpoint.epoch ≤ (query.blocks selected).slot)
    (hquerySelectedBoundaryWalk : WalkKnown query
      (compute_start_slot_at_epoch cfg
        query.finalized_checkpoint.epoch) selected)
    (hendpointSelectedBoundaryWalk : WalkKnown endpoint
      (compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch) selected)
    (hendpointTipBoundaryWalk : WalkKnown endpoint
      (compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch) h.tip) :
    endpoint.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      endpoint.finalized_checkpoint.root =
        get_checkpoint_block cfg endpoint h.tip
          endpoint.finalized_checkpoint.epoch := by
  by_cases hqueryGenesis : query.finalized_checkpoint.epoch = GENESIS_EPOCH
  · left
    exact Nat.le_zero.mp (by simpa only [hqueryGenesis, GENESIS_EPOCH]
      using hepoch)
  · right
    obtain ⟨queryTip, hqueryTipKnown, hqueryTipSelected,
        _hqueryTipLeaf, _hquerySource, hqueryFinalized,
        hqueryTipToSelectedWalk⟩ := hviable
    have hqueryTipFinalized : query.finalized_checkpoint.root =
        get_checkpoint_block cfg query queryTip
          query.finalized_checkpoint.epoch := by
      rcases hqueryFinalized with hgenesis | hfinalized
      · exact False.elim (hqueryGenesis hgenesis)
      · exact hfinalized
    have hqueryTipLandsOnSelected :
        get_ancestor query (get_node_for_root queryTip)
            (query.blocks selected).slot =
          get_node_for_root selected := by
      simpa only [is_ancestor, decide_eq_true_eq] using hqueryTipSelected
    have hqueryTipBoundaryWalk : WalkKnown query
        (compute_start_slot_at_epoch cfg
          query.finalized_checkpoint.epoch) queryTip :=
      WalkKnown.splice_at_ancestor hqueryParent hboundarySelectedQuery
        hqueryTipToSelectedWalk hqueryTipLandsOnSelected
          hquerySelectedBoundaryWalk
    have hqueryTipSelectedCheckpoint :
        get_checkpoint_block cfg query queryTip
            query.finalized_checkpoint.epoch =
          get_checkpoint_block cfg query selected
            query.finalized_checkpoint.epoch :=
      get_checkpoint_block_of_ancestor cfg hqueryParent
        hqueryTipSelected hboundarySelectedQuery hqueryTipBoundaryWalk
    have hqueryFinalizedAtSelected : query.finalized_checkpoint.root =
        get_checkpoint_block cfg query selected
          query.finalized_checkpoint.epoch :=
      hqueryTipFinalized.trans hqueryTipSelectedCheckpoint
    have hboundaryEpochs : compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch ≤
        compute_start_slot_at_epoch cfg
          query.finalized_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hepoch
    have hendpointSelectedQueryBoundaryWalk : WalkKnown endpoint
        (compute_start_slot_at_epoch cfg
          query.finalized_checkpoint.epoch) selected :=
      hendpointSelectedBoundaryWalk.mono hboundaryEpochs
    have hselectedCheckpointTransport :
        get_checkpoint_block cfg query selected
            query.finalized_checkpoint.epoch =
          get_checkpoint_block cfg endpoint selected
            query.finalized_checkpoint.epoch :=
      hquery.getCheckpointBlock_eq_of_pairedWalks cfg ext hwfExecution
        h.store_causal hqueryParent hendpointParent
          hquerySelectedBoundaryWalk hendpointSelectedQueryBoundaryWalk
    have hqueryFinalizedAtEndpointSelected :
        query.finalized_checkpoint = get_checkpoint_for_block cfg endpoint
          selected query.finalized_checkpoint.epoch := by
      apply checkpoint_eq_of_epoch_root_eq
      · rfl
      · simpa only [get_checkpoint_for_block] using
          hqueryFinalizedAtSelected.trans hselectedCheckpointTransport
    have hqueryFinalizedRootKnown :
        query.finalized_checkpoint.root ∈ endpoint.block_roots := by
      rw [congrArg Checkpoint.root hqueryFinalizedAtEndpointSelected]
      exact (get_ancestor_spec hendpointParent
        hendpointSelectedQueryBoundaryWalk).1
    have hprefix :=
      ExactPrefixAcceptedFFGSemantics.globalFinalized_exactPrefix_of_epoch_le
        cfg ext B hgen hanchor P V hanchorExact hacc h.store_causal hquery
          hepoch
    have hsourceAtQueryFinalized : endpoint.finalized_checkpoint =
        get_checkpoint_for_block cfg endpoint
          query.finalized_checkpoint.root
          endpoint.finalized_checkpoint.epoch := by
      calc
        endpoint.finalized_checkpoint =
            B.state.C query.finalized_checkpoint.root
              endpoint.finalized_checkpoint.epoch := hprefix
        _ = get_checkpoint_for_block cfg endpoint
            query.finalized_checkpoint.root
              endpoint.finalized_checkpoint.epoch :=
          B.coherence.checkpoint_of_known h.store_causal
            query.finalized_checkpoint.root hqueryFinalizedRootKnown
              endpoint.finalized_checkpoint.epoch
    have hcomp := get_checkpoint_for_block_comp cfg hendpointParent hepoch
      hendpointSelectedBoundaryWalk
    have hsourceAtSelected : endpoint.finalized_checkpoint =
        get_checkpoint_for_block cfg endpoint selected
          endpoint.finalized_checkpoint.epoch := by
      calc
        endpoint.finalized_checkpoint = get_checkpoint_for_block cfg endpoint
            query.finalized_checkpoint.root
              endpoint.finalized_checkpoint.epoch := hsourceAtQueryFinalized
        _ = get_checkpoint_for_block cfg endpoint
            (get_checkpoint_for_block cfg endpoint selected
              query.finalized_checkpoint.epoch).root
              endpoint.finalized_checkpoint.epoch := by
          rw [← congrArg Checkpoint.root hqueryFinalizedAtEndpointSelected]
        _ = get_checkpoint_for_block cfg endpoint selected
            endpoint.finalized_checkpoint.epoch := hcomp
    have hsourceRootAtSelected : endpoint.finalized_checkpoint.root =
        get_checkpoint_block cfg endpoint selected
          endpoint.finalized_checkpoint.epoch := by
      simpa only [get_checkpoint_for_block] using
        congrArg Checkpoint.root hsourceAtSelected
    have hselectedBlocks : query.blocks selected = endpoint.blocks selected :=
      hwfExecution.blocks_agree hquery.blockProvenance
        h.store_causal.blockProvenance hselectedQuery h.selected_known
    have hboundarySelectedEndpoint : compute_start_slot_at_epoch cfg
        endpoint.finalized_checkpoint.epoch ≤
          (endpoint.blocks selected).slot := by
      calc
        compute_start_slot_at_epoch cfg
            endpoint.finalized_checkpoint.epoch ≤
            compute_start_slot_at_epoch cfg
              query.finalized_checkpoint.epoch := hboundaryEpochs
        _ ≤ (query.blocks selected).slot := hboundarySelectedQuery
        _ = (endpoint.blocks selected).slot :=
          congrArg BeaconBlock.slot hselectedBlocks
    exact finalized_check_of_ancestor cfg hendpointParent
      h.tip_descends_selected hboundarySelectedEndpoint
        hendpointTipBoundaryWalk hsourceRootAtSelected

end AcceptedRetainedPhaseSourceCarrierAt

end Execution


end FastConfirmation.Spec
