import FastConfirmation.Spec.Proof.FFGJustifiedCheckpointCache
import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts

/-!
# Accepted justified-checkpoint cache provenance

This module reconstructs the second field of `SelectedMarginDomain` from the
production accepted-prefix FFG semantics.  The handler-local cache proof is
the existing executable one: an honest target vote is delivered, validated,
inserted into `checkpoint_state_keys`, and the key persists to the endpoint.

The only replacement is the global provenance of the justified checkpoint.
`ExactPrefixAcceptedFFGSemantics.globalJustified_anchor_or_AUEvidence` returns
either the trusted anchor or an `AcceptedSelectorAUCarrier`.  In the latter
case, `formed_evidence.causal` supplies the exact accepted formation block and
an honest target vote strictly before it.  Accepted store reflection places
that carrier below the endpoint's known selector tip, so the vote's next-slot
delivery precedes the endpoint.

No legacy `ChainFFGState`, `FFGTransitionCoherence`, justification interface,
selected-margin bundle, filter fact, or safety conclusion is a premise.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Every reachable honest store has cached its accepted-prefix realized
justified checkpoint. -/
theorem justifiedCheckpoint_cached_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : Nat)
    (hHm : E.WithinHorizon cfg m) :
    (E.store cfg ext w m).justified_checkpoint ∈
      (E.store cfg ext w m).checkpoint_state_keys := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
  have hgenFull : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hslot, hparent⟩
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hgenTime :
      E.genesis_store.genesis_time ≤ E.genesis_store.time :=
    hgws.time_ge_genesis
  have hanchorKey0 :
      B.anchor ∈ E.genesis_store.checkpoint_state_keys := by
    rw [hanchor, hgenEq]
    simp only [get_forkchoice_store, Finset.mem_singleton]
  have hanchorKey :
      B.anchor ∈ (E.store cfg ext w m).checkpoint_state_keys :=
    (E.store_checkpointKeysLE cfg ext w (Nat.zero_le m)) hanchorKey0
  have hslotZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrentZero := E.store_current_slot cfg ext w 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0
      at hcurrentZero
    rw [hgenEq,
      get_current_slot_get_forkchoice_store cfg hT.whole_seconds]
      at hcurrentZero
    exact hcurrentZero.symm
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hroot := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hroot
    simpa only [get_forkchoice_store] using hroot
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  let justified := (E.store cfg ext w m).justified_checkpoint
  change justified ∈ (E.store cfg ext w m).checkpoint_state_keys
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
    hjustifiedAnchor | hevidence
  · have hjustifiedAnchor' : justified = B.anchor := by
      simpa only [justified] using hjustifiedAnchor
    rw [hjustifiedAnchor']
    exact hanchorKey
  · obtain ⟨hcarrier⟩ := hevidence
    by_cases hjustifiedAnchor : justified = B.anchor
    · rw [hjustifiedAnchor]
      exact hanchorKey
    · have hcausal :=
        hcarrier.formed_evidence.causal.resolve_left hjustifiedAnchor
      obtain ⟨carrierBlock, hcarrierAt, voter, hvoter, voteSlot,
          groundTime, groundVote, hvoteBeforeCarrier, hvoteSlotH,
          hgroundVote, hgroundSlot, hgroundTarget, hincluded⟩ := hcausal
      obtain ⟨includedCarrier, _hincludedDesc, hincludedAt⟩ := hincluded
      have hincludedEvidence :=
        B.state.includedAttestations.evidence hincludedAt
      have hgroundTarget' : groundVote.data.target = justified := by
        simpa only [justified] using hgroundTarget
      obtain ⟨hincludedCertificate⟩ :=
        hcarrier.formed_evidence.certified
      have hanchorLtJustified : B.anchor.epoch < justified.epoch := by
        exact CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
          (IncludedCertifiedJustified.toCertifiedJustified
            (cfg := cfg)
            (Execution.AcceptedIncludedAttestationRelation.relation
              cfg ext E B.state.includedAttestations)
            hincludedCertificate)
          hjustifiedAnchor
      have htargetEpoch : justified.epoch =
          compute_epoch_at_slot cfg voteSlot := by
        rw [← hgroundTarget', ← hgroundSlot]
        exact hincludedEvidence.target_epoch
      have hstartMono :
          compute_start_slot_at_epoch cfg B.anchor.epoch ≤
            compute_start_slot_at_epoch cfg justified.epoch :=
        Nat.mul_le_mul_right cfg.slots_per_epoch
          hanchorLtJustified.le
      have hstartVote :
          compute_start_slot_at_epoch cfg justified.epoch ≤ voteSlot := by
        have hmulDiv := Nat.div_mul_le_self
          voteSlot cfg.slots_per_epoch
        have hepochDiv :
            voteSlot / cfg.slots_per_epoch = justified.epoch := by
          simpa only [compute_epoch_at_slot] using htargetEpoch.symm
        rw [hepochDiv] at hmulDiv
        simpa only [compute_start_slot_at_epoch] using hmulDiv
      have hfromZero : E.slot_at cfg 0 ≤ voteSlot := by
        calc
          E.slot_at cfg 0 = ast.slot := hslotZero
          _ = ablk.message.slot := hslot
          _ ≤ compute_start_slot_at_epoch cfg B.anchor.epoch := hboundary'
          _ ≤ compute_start_slot_at_epoch cfg justified.epoch := hstartMono
          _ ≤ voteSlot := hstartVote
      have hcommittee : voter ∈ E.committee voteSlot :=
        hT.honest_behavior.votes_assigned voter hvoter voteSlot
          (by rw [hgroundVote]; exact Option.some_ne_none _)
      obtain ⟨voteTime, index, hHvoteTime, hvoteTimeSlot, hvoteHead⟩ :=
        hT.honest_behavior.votes_head voter hvoter voteSlot hcommittee
          hvoteSlotH hfromZero
      have hgroundEq := hgroundVote
      rw [hvoteHead] at hgroundEq
      simp only [Option.some.injEq, Prod.mk.injEq] at hgroundEq
      obtain ⟨_timeEq, hattestationEq⟩ := hgroundEq
      have htargetExact :
          (honest_attestation cfg ext
            (E.store cfg ext voter voteTime)
            voteSlot index voter).data.target = justified := by
        rw [hattestationEq]
        exact hgroundTarget'
      have hheadKnown :
          (honest_attestation cfg ext
            (E.store cfg ext voter voteTime)
            voteSlot index voter).data.beacon_block_root ∈
              (E.store cfg ext voter voteTime).block_roots := by
        change (get_head cfg
          (E.store cfg ext voter voteTime)).root ∈
            (E.store cfg ext voter voteTime).block_roots
        rcases get_head_root_mem_or cfg
            (E.store cfg ext voter voteTime) with hhead | hfallback
        · exact hhead
        · rw [hfallback]
          exact E.justifiedRootKnown_of_acceptedGlobalTrajectory
            cfg ext B hT hanchor hboundary hvoter voteTime hHvoteTime
      have hheadWalk : WalkKnown
          (E.store cfg ext voter voteTime)
          (compute_start_slot_at_epoch cfg
            (honest_attestation cfg ext
              (E.store cfg ext voter voteTime)
              voteSlot index voter).data.target.epoch)
          (honest_attestation cfg ext
            (E.store cfg ext voter voteTime)
            voteSlot index voter).data.beacon_block_root :=
        hwalkDomain voter hvoter voteSlot voteTime index
          hfromZero hHvoteTime hvoteTimeSlot hvoteHead
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
          cfg ext hT.wellFormed hT.externals_coherence
          hgenEq hslot hparent hcarrier.tip_carrier.known hcarrierRoot
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
      have hdeliveryLe :
          E.slot_start cfg (voteSlot + 1) ≤ m := by
        apply Nat.le_of_not_gt
        intro hmBeforeDelivery
        have hslotBeforeDelivery : E.slot_at cfg m < voteSlot + 1 :=
          (E.slot_at_lt_iff cfg hT.whole_seconds hgenTime).2
            hmBeforeDelivery
        exact (Nat.not_lt_of_ge
          (Nat.succ_le_of_lt hvoteBeforeEndpoint)) hslotBeforeDelivery
      have hcached := E.honestVoteTarget_cached cfg ext
        hT.wellFormed hT.honest_behavior hsync hT.externals_coherence
        hT.whole_seconds hgenFull hvoter hw
        hvoteTimeSlot hHvoteTime hvoteHead hheadKnown hheadWalk
        hdeliveryLe hHm
      rwa [htargetExact] at hcached

/-- Accepted root knownness plus accepted cache provenance construct the
complete two-field domain consumed by strict selected-result geometry. -/
theorem selectedMarginDomain_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    SelectedMarginDomain cfg ext E := by
  constructor
  · intro w hw m hHm
    exact E.justifiedRootKnown_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary hw m hHm
  · intro w hw m hHm
    exact E.justifiedCheckpoint_cached_of_acceptedGlobalTrajectory
      cfg ext B hT hsync hanchor hboundary hw m hHm


end Execution

end FastConfirmation.Spec
