module
public import FastConfirmation.Spec.Proof.HonestVoteTargetCache
public import FastConfirmation.Spec.Proof.FinalizedResetSafety
public import FastConfirmation.Spec.Proof.MinimalSelectedDomain

@[expose] public section

/-!
# Realized justified-checkpoint cache provenance

A non-anchor realized justified checkpoint has a causal honest target vote
before its formation carrier. The delivered-vote cache result then gives
its checkpoint-state key at each later endpoint.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Global realized justified checkpoints -/

/-- Every reachable honest store has cached its realized justified checkpoint.

The anchor is keyed at genesis and persists.  For a non-anchor checkpoint,
`AU.evidence` exposes an honest target vote before a concrete formation
carrier.  Since that carrier is an execution ancestor of a block known at the
endpoint, its concrete slot is at most the endpoint slot.  Thus the vote's
next-slot delivery precedes the endpoint, where `honestVoteTarget_cached`
provides the exact key. -/
theorem justifiedCheckpoint_cached_of_globalTrajectory
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : Nat)
    (hHm : E.WithinHorizon cfg m) :
    (E.store cfg ext w m).justified_checkpoint ∈
      (E.store cfg ext w m).checkpoint_state_keys := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
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
      anchor ∈ E.genesis_store.checkpoint_state_keys := by
    rw [hanchor, hgenEq]
    simp only [get_forkchoice_store, Finset.mem_singleton]
  have hanchorKey :
      anchor ∈ (E.store cfg ext w m).checkpoint_state_keys :=
    (E.store_checkpointKeysLE cfg ext w (Nat.zero_le m)) hanchorKey0
  have hslotZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrentZero := E.store_current_slot cfg ext w 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrentZero
    rw [hgenEq,
      get_current_slot_get_forkchoice_store cfg hdiv] at hcurrentZero
    exact hcurrentZero.symm
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    have hanchorRoot : anchor.root = ablk.root := by
      have hroot := congrArg Checkpoint.root hanchor
      rw [hgenEq] at hroot
      simpa only [get_forkchoice_store] using hroot
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_globalTrajectory cfg ext
      hwf hec hdiv hgenFull hcoh hanchor hboundary
  let justified := (E.store cfg ext w m).justified_checkpoint
  change justified ∈ (E.store cfg ext w m).checkpoint_state_keys
  have hglobal := E.globalJustified_anchor_or_known_AU cfg ext
    hcoh hgenShort hanchor w m
  change justified = anchor ∨
    ∃ tip ∈ (E.store cfg ext w m).block_roots,
      S.AU cfg tip justified at hglobal
  rcases hglobal with hjustifiedAnchor | ⟨tip, htip, hAU⟩
  · rw [hjustifiedAnchor]
    exact hanchorKey
  · by_cases hjustifiedAnchor : justified = anchor
    · rw [hjustifiedAnchor]
      exact hanchorKey
    · obtain ⟨carrier, htipCarrier, hformed⟩ :=
        ChainFFGState.AU.evidence (cfg := cfg) S hAU
      have hcausal := hformed.causal.resolve_left hjustifiedAnchor
      obtain ⟨carrierBlock, hcarrierAt, voter, hvoter, voteSlot,
          groundTime, groundVote, hvoteBeforeCarrier, hvoteSlotH,
          hgroundVote, hgroundSlot, hgroundTarget, hincluded⟩ := hcausal
      obtain ⟨includedCarrier, _hincludedDesc, hincludedAt⟩ := hincluded
      have hincludedEvidence :=
        S.includedAttestations.evidence hincludedAt
      obtain ⟨hincludedCertificate⟩ := hformed.certified
      have hanchorLtJustified : anchor.epoch < justified.epoch := by
        exact CertifiedJustified.anchor_epoch_lt_of_ne (cfg := cfg)
          (IncludedCertifiedJustified.toCertifiedJustified
            (cfg := cfg) S.includedAttestations hincludedCertificate)
          hjustifiedAnchor
      have htargetEpoch : justified.epoch =
          compute_epoch_at_slot cfg voteSlot := by
        rw [← hgroundTarget, ← hgroundSlot]
        exact hincludedEvidence.target_epoch
      have hstartMono :
          compute_start_slot_at_epoch cfg anchor.epoch ≤
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
          _ ≤ compute_start_slot_at_epoch cfg anchor.epoch := hboundary'
          _ ≤ compute_start_slot_at_epoch cfg justified.epoch := hstartMono
          _ ≤ voteSlot := hstartVote
      have hcommittee : voter ∈ E.committee voteSlot :=
        hhb.votes_assigned voter hvoter voteSlot
          (by rw [hgroundVote]; exact Option.some_ne_none _)
      obtain ⟨voteTime, index, hHvoteTime, hvoteTimeSlot, hvoteHead⟩ :=
        hhb.votes_head voter hvoter voteSlot hcommittee
          hvoteSlotH hfromZero
      have hgroundEq := hgroundVote
      rw [hvoteHead] at hgroundEq
      simp only [Option.some.injEq, Prod.mk.injEq] at hgroundEq
      obtain ⟨_htimeEq, hattestationEq⟩ := hgroundEq
      have htargetExact :
          (honest_attestation cfg ext
            (E.store cfg ext voter voteTime)
            voteSlot index voter).data.target = justified := by
        rw [hattestationEq]
        exact hgroundTarget
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
          exact E.justifiedRootKnown_of_globalTrajectory cfg ext
            hwf hec hgenFull hcoh hanchor hboundary
            hvoter voteTime hHvoteTime
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
      have hcarrierRoot : E.ExecutionRoot carrier :=
        ⟨carrierBlock, hcarrierAt⟩
      have hcarrierKnown : carrier ∈
          (E.store cfg ext w m).block_roots :=
        (E.store_known_ancestor_of_rootDescends cfg ext
          hwf hec hgenEq hslot hparent htip hcarrierRoot htipCarrier).1
      have hcarrierAgreement : carrierBlock =
          (E.store cfg ext w m).blocks carrier :=
        E.blockAt_unique hwf hcarrierAt
          (E.blockAt_of_store_known cfg ext hcarrierKnown)
      have hvoteBeforeEndpoint : voteSlot < E.slot_at cfg m := by
        calc
          voteSlot < carrierBlock.slot := hvoteBeforeCarrier
          _ = ((E.store cfg ext w m).blocks carrier).slot :=
            congrArg BeaconBlock.slot hcarrierAgreement
          _ ≤ get_current_slot cfg (E.store cfg ext w m) :=
            E.store_blocks_slot_le_current cfg ext hdiv hgenShort
              w m carrier hcarrierKnown
          _ = E.slot_at cfg m := E.store_current_slot cfg ext w m
      have hdeliveryLe :
          E.slot_start cfg (voteSlot + 1) ≤ m := by
        apply Nat.le_of_not_gt
        intro hmBeforeDelivery
        have hslotBeforeDelivery : E.slot_at cfg m < voteSlot + 1 :=
          (E.slot_at_lt_iff cfg hdiv hgenTime).2 hmBeforeDelivery
        exact (Nat.not_lt_of_ge
          (Nat.succ_le_of_lt hvoteBeforeEndpoint)) hslotBeforeDelivery
      have hcached := E.honestVoteTarget_cached cfg ext
        hwf hhb hsyn hec hdiv hgenFull hvoter hw
        hvoteTimeSlot hHvoteTime hvoteHead hheadKnown hheadWalk
        hdeliveryLe hHm
      rwa [htargetExact] at hcached

/-- The common FFG trajectory realizes the complete local domain consumed by
the selected-margin proof: known justified roots and cached justified
checkpoint states. -/
theorem selectedMarginDomain_of_globalTrajectory
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    SelectedMarginDomain cfg ext E := by
  constructor
  · intro w hw m hHm
    exact E.justifiedRootKnown_of_globalTrajectory cfg ext
      hwf hec hgen hcoh hanchor hboundary hw m hHm
  · intro w hw m hHm
    exact E.justifiedCheckpoint_cached_of_globalTrajectory cfg ext
      hwf hhb hsyn hec hdiv hgen hcoh hanchor hboundary hw m hHm

/-- Direct constructor for the assumption bundle consumed by actual selected
confirmation calls.  The economic fields are passed through unchanged; the
two local domain fields are reconstructed from the common FFG trajectory. -/
theorem selectedMarginAssumptions_of_globalTrajectory
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hwf : WellFormedExecution E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyzantine : ByzantineBound cfg E)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    SelectedMarginAssumptions cfg ext E :=
  ⟨hgen, hwf, hdiv, hhb, hsyn, hec, hstatic, hbyzantine,
    E.selectedMarginDomain_of_globalTrajectory cfg ext
      hwf hhb hsyn hec hdiv hgen hcoh hanchor hboundary⟩

end Execution

end FastConfirmation.Spec

end
