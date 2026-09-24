module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.SelectedSource.CurrentSameEndpointSource
public import FastConfirmationProofs.FCRRule.ObservedRestartAdoption
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionCallInduction
public import FastConfirmationProofs.FFG.SourceHistory.FFGJustifiedCheckpointCache
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.FCRRule.FCRCallInvariants
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant
public import FastConfirmationProofs.Checkpoints.DeadlineBlockAdmissibility
public import FastConfirmationProofs.Discount.SelectedCoveredMarginConstruction

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Dynamic safety of an accepted active-observed restart

This module derives the paper's active-restart checkpoint lock from the actual
accepted execution.  In particular it does not assume the generic
`ObservedRestartJustifiedSourceLockAt` proposition.

The first lemma is the executable counterpart of the active arm in paper
Lemma 32: the restart guard fixes the checkpoint root in the previous block
epoch, while accepted cache provenance bounds the checkpoint epoch from above
by the epoch of the pre-boundary carrier.  Hence the checkpoint itself is
exactly a previous-epoch checkpoint.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- An actual active-observed restart carries a checkpoint whose declared
epoch, not only whose root block epoch, is exactly the previous epoch. -/
theorem ObservedResetCandidateInputAt.observed_checkpoint_previous_epoch
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} {n : ℕ}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    {trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n)}
    (h : ObservedResetCandidateInputAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace) :
    (E.fcrStoreAtCall cfg ext v n
      ).current_epoch_observed_justified_checkpoint.epoch + 1 =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
  let c := (E.fcrStoreAtCall cfg ext v n
    ).current_epoch_observed_justified_checkpoint
  let e := get_current_store_epoch cfg (E.store cfg ext v (n + 1))
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  obtain ⟨hi⟩ :=
    FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.acceptedInstallation
      (E := E) cfg ext B hgenShort hanchor hspe h
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    have hslotAdvanceRaw := hcall
    unfold IsScheduledFCRCallAt at hslotAdvanceRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hslotAdvanceRaw
    exact hslotAdvanceRaw
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.fcrStep_store, E.store_current_slot] using h.epoch_start
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg e := by
    have hraw : E.slot_at cfg (n + 1) =
        compute_start_slot_at_epoch cfg
          (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
      simp only [compute_slots_since_epoch_start,
        compute_start_slot_at_epoch] at hstartZero ⊢
      exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
        (Nat.div_mul_le_self _ cfg.slots_per_epoch)
    simpa only [e, get_current_store_epoch, E.store_current_slot] using hraw
  have hrootPrevious : get_block_epoch cfg (E.store cfg ext v (n + 1))
        c.root + 1 = e := by
    simpa only [c, e, E.fcrStep_store] using h.observed_previous_epoch
  have hreal :=
    E.fcrStep_observed_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary v n
  have hrootEpochLe : get_block_epoch cfg
      (E.store cfg ext v (n + 1)) c.root ≤ c.epoch := by
    have hscaled : get_block_epoch cfg (E.store cfg ext v (n + 1)) c.root *
          cfg.slots_per_epoch ≤ c.epoch * cfg.slots_per_epoch :=
      (start_slot_at_block_epoch_le cfg
        (E.store cfg ext v (n + 1)) c.root).trans (by
          simpa only [c] using hreal.root_slot_le_boundary)
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hcEpochLt : c.epoch < e := by
    rcases hi.accepted_origin with hanchorField | ⟨tip, htip, hguField⟩
    · have hcAnchor : c = B.anchor := hi.field_eq.trans hanchorField
      have htrusted := E.trustedAnchor_checkpointForBlock_of_trajectory
        cfg ext hT hanchor hboundary
      have hanchorEpochGenesis :
          get_block_epoch cfg E.genesis_store B.anchor.root = B.anchor.epoch := by
        have he := congrArg Checkpoint.epoch htrusted
        simpa only [get_checkpoint_for_block] using he
      have hanchorKnown0 : B.anchor.root ∈ E.genesis_store.block_roots := by
        rw [hgen]
        have hroot : B.anchor.root = ablk.root := by
          have hr := congrArg Checkpoint.root hanchor
          rw [hgen] at hr
          simpa only [get_forkchoice_store] using hr
        rw [hroot]
        simp only [get_forkchoice_store, List.mem_singleton]
      have hanchorKnownN : B.anchor.root ∈
          (E.store cfg ext v (n + 1)).block_roots :=
        (E.store_storeLE cfg ext v (Nat.zero_le _)).1 hanchorKnown0
      have hanchorAgree : E.genesis_store.blocks B.anchor.root =
          (E.store cfg ext v (n + 1)).blocks B.anchor.root :=
        hT.wellFormed.blocks_agree
          (E.blockProvenance cfg ext v 0)
          (E.blockProvenance cfg ext v (n + 1))
          (by
            simpa only [show E.store cfg ext v 0 = E.genesis_store from rfl]
              using hanchorKnown0) hanchorKnownN
      have hanchorEpochN : get_block_epoch cfg
          (E.store cfg ext v (n + 1)) B.anchor.root = B.anchor.epoch := by
        simpa only [get_block_epoch, ← hanchorAgree] using hanchorEpochGenesis
      rw [hcAnchor] at hrootPrevious ⊢
      rw [hanchorEpochN] at hrootPrevious
      exact Nat.lt_of_succ_le hrootPrevious.le
    · have hcGU : c = B.state.GU tip := hi.field_eq.trans hguField
      have htipAt : E.AcceptedBlockAt cfg ext tip
          ((E.store cfg ext v hi.originSecond).blocks tip) :=
        E.acceptedBlockAt_of_causal_known cfg ext
          (E.store_causal cfg ext v hi.originSecond) htip.known
      have hAU : B.state.AU cfg ext tip c := by
        rw [hcGU]
        exact B.state.gu_AU cfg ext htip.acceptedRoot
      have hcEpochLeTip : c.epoch ≤ compute_epoch_at_slot cfg
          ((E.store cfg ext v hi.originSecond).blocks tip).slot :=
        B.state.au_epoch_le_block htipAt hAU
      have htipSlotUpper :
          ((E.store cfg ext v hi.originSecond).blocks tip).slot ≤
            E.slot_at cfg hi.originSecond := by
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds
            hgenShort v hi.originSecond tip htip.known
      have htipSlotLtBoundary :
          ((E.store cfg ext v hi.originSecond).blocks tip).slot <
            E.slot_at cfg (n + 1) :=
        (htipSlotUpper.trans (E.slot_at_mono cfg hi.origin_le)).trans_lt
          hslotAdvance
      have htipEpochLt : compute_epoch_at_slot cfg
          ((E.store cfg ext v hi.originSecond).blocks tip).slot < e := by
        rw [hslotBoundary] at htipSlotLtBoundary
        simp only [compute_epoch_at_slot]
        exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
          htipSlotLtBoundary
      exact hcEpochLeTip.trans_lt htipEpochLt
  change c.epoch + 1 = e
  apply Nat.le_antisymm
  · exact Nat.succ_le_of_lt hcEpochLt
  · rw [← hrootPrevious]
    exact Nat.add_le_add_right hrootEpochLe 1

/-- The actual active-observed branch is safe from its call second using only
accepted checkpoint dynamics, honest vote-your-head behavior, synchrony, and
ordinary FFG accountability.  No generic observed source-lock proposition is
an input.

The strong induction is the slot-indexed version of paper Lemma 35.  Equal
checkpoint epochs close by accountable uniqueness.  A strictly newer endpoint
checkpoint has an honest causal formation vote in the current or a later
epoch; the induction hypothesis puts the observed root on that voter's head,
and checkpoint-boundary walk composition puts it below the vote target. -/
theorem ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    {trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n)}
    (h : ObservedResetCandidateInputAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace) :
    E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
  rw [h.input_eq]
  let c := (E.fcrStoreAtCall cfg ext v n
    ).current_epoch_observed_justified_checkpoint
  let e := get_current_store_epoch cfg (E.store cfg ext v (n + 1))
  change E.SafeFrom cfg ext c.root (n + 1)
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hdomain : SelectedMarginDomain cfg ext E :=
    E.selectedMarginDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hsync hpaths hanchor hboundary
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  let hacc : FFGAccountabilityAssumptions cfg ext E :=
    SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext E hA
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    have hslotAdvanceRaw := hcall
    unfold IsScheduledFCRCallAt at hslotAdvanceRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hslotAdvanceRaw
    exact hslotAdvanceRaw
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hcall
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.fcrStep_store, E.store_current_slot] using h.epoch_start
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg e := by
    have hraw : E.slot_at cfg (n + 1) =
        compute_start_slot_at_epoch cfg
          (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
      simp only [compute_slots_since_epoch_start,
        compute_start_slot_at_epoch] at hstartZero ⊢
      exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
        (Nat.div_mul_le_self _ cfg.slots_per_epoch)
    simpa only [e, get_current_store_epoch, E.store_current_slot] using hraw
  have hcEpoch : c.epoch + 1 = e := by
    simpa only [c, e] using
      FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.observed_checkpoint_previous_epoch
        (E := E) cfg ext B hT hanchor hboundary hspe hcall h
  have hrestart : ObservedRestartCompatible cfg (E.fcrStoreAtCall cfg ext v n) :=
    { epoch_start := h.epoch_start
      root_previous_epoch := h.observed_previous_epoch
      observed_eq_head_unrealized := h.observed_eq_head_unrealized }
  have hadoption : E.ActualFCRGuardedObservedAdoption cfg ext v n :=
    FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.actualFCRGuardedObservedAdoption
      (E := E) cfg ext B hT hsync hanchor hboundary hspe
        hA hDelay P V hacc hv hHn1 hcall h (by simpa only [c, e] using hcEpoch)
  have hreal :=
    E.fcrStep_observed_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary v n
  obtain ⟨hcCertified⟩ := hreal.certified
  have hcExecutionRoot : E.ExecutionRoot c.root :=
    ⟨(E.store cfg ext v (n + 1)).blocks c.root,
      E.blockAt_of_store_known cfg ext (by
        simpa only [c] using hreal.root_known)⟩
  obtain ⟨hi⟩ :=
    FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.acceptedInstallation
      (E := E) cfg ext B hgenShort hanchor hspe h
  have horiginH : E.WithinHorizon cfg hi.originSecond :=
    E.withinHorizon_mono cfg (hi.origin_le.trans (Nat.le_succ n)) hHn1
  have horiginDeadline : hi.originSecond ≤
      E.slot_start cfg (E.slot_at cfg hi.originSecond) +
        get_attestation_due_ms cfg / 1000 := by
    have hgenTime :
        E.genesis_store.genesis_time ≤ E.genesis_store.time := by
      rw [hgen]
      simp only [get_forkchoice_store]
      omega
    exact hi.origin_before_deadline cfg ext E hT.whole_seconds hgenTime
  have hrealOrigin : E.ResetCheckpointRealizedAt cfg B.anchor
      (E.store cfg ext v hi.originSecond) c := by
    have hrealField :=
      E.unrealizedJustifiedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
        cfg ext B hT hanchor hboundary (w := v) hi.originSecond
    simpa only [c, hi.field_eq] using hrealField
  have hcIncluded : ∃ carrier : Root,
      Nonempty (IncludedCertifiedJustified cfg E
        B.state.includedAttestations.Included B.anchor carrier c) := by
    have horigin : AcceptedGlobalUnrealizedJustifiedOrigin
        B.state (E.store cfg ext v hi.originSecond) c := by
      simpa only [c, hi.field_eq] using hi.accepted_origin
    rcases horigin with hanchorC | ⟨tip, htip, hcEq⟩
    · refine ⟨B.anchor.root, ?_⟩
      rw [hanchorC]
      exact ⟨IncludedCertifiedJustified.anchor⟩
    · obtain ⟨carrier, _hdesc, hformed⟩ :=
        B.state.gu_mem tip htip.acceptedRoot
      refine ⟨carrier, ?_⟩
      rw [hcEq]
      exact (B.state.formed_evidence hformed).certified
  have hcKnownBoundary : ∀ w ∈ E.honest,
      c.root ∈ (E.store cfg ext w (n + 1)).block_roots := by
    intro w hw
    have horiginNextLe : E.slot_start cfg
        (E.slot_at cfg hi.originSecond + 1) ≤ n + 1 := by
      have hslotLe : E.slot_at cfg hi.originSecond + 1 ≤
          E.slot_at cfg (n + 1) := by
        calc
          E.slot_at cfg hi.originSecond + 1 ≤ E.slot_at cfg n + 1 :=
            Nat.add_le_add_right (E.slot_at_mono cfg hi.origin_le) 1
          _ ≤ E.slot_at cfg (n + 1) :=
            Nat.succ_le_iff.mpr hslotAdvance
      calc
        E.slot_start cfg (E.slot_at cfg hi.originSecond + 1) ≤
            E.slot_start cfg (E.slot_at cfg (n + 1)) :=
          E.slot_start_mono cfg hslotLe
        _ = n + 1 := hstartEq

    have horiginLtM : hi.originSecond < n + 1 :=
      lt_of_le_of_lt hi.origin_le (Nat.lt_succ_self n)
    have hrelayOutcome := hsync.deadline_block_relay v hv
      hi.originSecond c.root horiginH hrealOrigin.root_known
      horiginDeadline w hw (n + 1) hHn1 horiginNextLe horiginLtM
    rcases hrelayOutcome with hknown | hexcluded
    · exact hknown
    by_cases hknown : c.root ∈ (E.store cfg ext w (n + 1)).block_roots
    · exact hknown
    have hexcluded := E.permanentBlockExclusion_mono_of_not_mem cfg ext
      ((Nat.sub_le _ 1).trans horiginNextLe) hknown hexcluded
    have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
      E.causalRealizedFinalizationLag_of_acceptedDelay
        cfg ext B hT hanchor hDelay
    have hendpointLag :
        (E.store cfg ext w (n + 1)).finalized_checkpoint = B.anchor ∨
          (E.store cfg ext w (n + 1)).finalized_checkpoint.epoch + 2 ≤
            get_current_store_epoch cfg (E.store cfg ext w (n + 1)) :=
      hLag (E.store_causal cfg ext w (n + 1))
    have hfinalizedBeforeObservedAtBoundary :
        (E.store cfg ext w (n + 1)).finalized_checkpoint.epoch ≤ c.epoch := by
      have hcurrentEpoch : get_current_store_epoch cfg
          (E.store cfg ext w (n + 1)) = e := by
        simp only [get_current_store_epoch, E.store_current_slot, e]
      rcases hendpointLag with hanchorF | hlag
      · rw [hanchorF]
        exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcCertified
      · rw [hcurrentEpoch] at hlag
        rw [← hcEpoch] at hlag
        exact (Nat.le_succ _).trans (Nat.le_of_succ_le_succ hlag)
    let F := (E.store cfg ext w (n + 1)).finalized_checkpoint
    have hanchorExact : B.anchor =
        B.state.C B.anchor.root B.anchor.epoch :=
      acceptedAnchorExact_of_trajectory cfg ext E B hT hanchor hboundary
    have haccExact : CheckpointCertificateAccountability cfg E B.anchor :=
      CheckpointCertificateAccountability.of_assumptions cfg hacc
    have hFprefixC (hepoch : F.epoch ≤ c.epoch) :
        ExactCheckpointPrefix B.state.C F c := by
      rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
          cfg ext B hgenShort hanchor (E.store_causal cfg ext w (n + 1)) with
        hFanchor | ⟨carrier, _hcarrier, hFcert⟩
      · dsimp only [F]
        rw [hFanchor]
        obtain ⟨carrierC, ⟨hCcert⟩⟩ := hcIncluded
        exact IncludedCertifiedJustified.anchor_prefix
          (cfg := cfg) P V hanchorExact hCcert
      · obtain ⟨hFcert⟩ := hFcert
        obtain ⟨carrierC, ⟨hCcert⟩⟩ := hcIncluded
        exact B.state.exactFinalizedPrefix_of_accountable cfg P V
          hanchorExact haccExact hFcert hCcert hepoch
    have hFprefixC' := hFprefixC hfinalizedBeforeObservedAtBoundary
    have hFrealized :=
      E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
        cfg ext B hT hanchor hboundary (w := w) (n + 1)
    have hFknown : F.root ∈
        (E.store cfg ext w (n + 1)).block_roots := by
      simpa only [F] using hFrealized.root_known
    have hFanchorEpochLe : B.anchor.epoch ≤ F.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg)
        (Classical.choice hFrealized.certified)
    let source := E.store cfg ext v hi.originSecond
    have hsourceCheckpoint : F.root =
        get_checkpoint_block cfg source c.root F.epoch := by
      have hprefix := hFprefixC'
      unfold ExactCheckpointPrefix at hprefix
      rw [B.coherence.checkpoint_of_known
        (E.store_causal cfg ext v hi.originSecond)
        c.root hrealOrigin.root_known F.epoch] at hprefix
      have hr := congrArg Checkpoint.root hprefix
      simpa only [get_checkpoint_for_block] using hr
    exact False.elim
      (E.checkpointCompatible_not_permanentlyExcluded cfg ext
        B hT hanchor hboundary hHn1 hrealOrigin.root_known
        hFknown hFanchorEpochLe hsourceCheckpoint hexcluded)
  have hcKnown : ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      c.root ∈ (E.store cfg ext w m).block_roots := by
    intro w hw m hnm _hHm
    exact (E.store_storeLE cfg ext w hnm).1 (hcKnownBoundary w hw)
  apply E.safeFrom_of_headStep_at cfg ext
  intro w hw m hnm hHm hIH
  let J := (E.store cfg ext w m).justified_checkpoint
  obtain ⟨hwfM, hwalkM, hjustM⟩ := hdomainK w hw m hHm
  have hcKnownM : c.root ∈ (E.store cfg ext w m).block_roots :=
    hcKnown w hw m hnm hHm
  have hcJ : c.epoch ≤ J.epoch := by
    have hboundaryAdoption : c.epoch ≤
        (E.store cfg ext w (n + 1)).justified_checkpoint.epoch := by
      simpa only [c] using hadoption hrestart w hw hHn1
    exact hboundaryAdoption.trans
      (E.store_justified_epoch_mono cfg ext w hnm)
  obtain ⟨hJCertified⟩ :=
    CausalPrefixFFGInterpretation.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  have hJc : is_ancestor (E.store cfg ext w m)
      (get_node_for_root J.root) (get_node_for_root c.root) = true := by
    rcases Nat.eq_or_lt_of_le hcJ with heq | hlt
    · have hrootEq : c.root = J.root :=
        E.certified_justified_unique cfg ext hacc hcCertified hJCertified heq
      rw [hrootEq]
      exact is_ancestor_refl _ _
    · have hanchorLeC : B.anchor.epoch ≤ c.epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg) hcCertified
      have hJne : J ≠ B.anchor := by
        intro hEq
        have hEpochEq := congrArg Checkpoint.epoch hEq
        exact (Nat.ne_of_lt (hanchorLeC.trans_lt hlt)) hEpochEq.symm
      obtain ⟨htarget⟩ :=
        FastConfirmation.Spec.Execution.globalJustified_honestTarget
          (E := E) cfg ext B hT hanchor hboundary hJne
      have heLeJ : e ≤ J.epoch := by
        rw [← hcEpoch]
        exact Nat.succ_le_of_lt hlt
      have hstartJLeVote : compute_start_slot_at_epoch cfg J.epoch ≤
          htarget.vote_slot := by
        have hmulDiv := Nat.div_mul_le_self htarget.vote_slot
          cfg.slots_per_epoch
        have hdiv : htarget.vote_slot / cfg.slots_per_epoch = J.epoch := by
          simpa only [compute_epoch_at_slot] using
            htarget.target_epoch_eq_vote_epoch.symm
        rw [hdiv] at hmulDiv
        simpa only [compute_start_slot_at_epoch] using hmulDiv
      have hboundaryLeVote : E.slot_at cfg (n + 1) ≤ htarget.vote_slot := by
        calc
          E.slot_at cfg (n + 1) = compute_start_slot_at_epoch cfg e :=
            hslotBoundary
          _ ≤ compute_start_slot_at_epoch cfg J.epoch :=
            Nat.mul_le_mul_right cfg.slots_per_epoch heLeJ
          _ ≤ htarget.vote_slot := hstartJLeVote
      have hnSecond : n + 1 ≤ htarget.second := by
        have hslotStartLe := E.query_slot_start_le_of_slot_ge_minimal
          cfg ext hA (q := n + 1) (ni := htarget.second) (by
            rw [htarget.second_slot]
            exact hboundaryLeVote)
        simpa only [hstartEq] using hslotStartLe
      have hsecondLt : E.slot_at cfg htarget.second < E.slot_at cfg m := by
        rw [htarget.second_slot]
        exact htarget.before_endpoint
      have hheadC : is_ancestor
          (E.store cfg ext htarget.validator htarget.second)
          (get_head cfg (E.store cfg ext htarget.validator htarget.second))
          (get_node_for_root c.root) = true :=
        hIH htarget.validator htarget.validator_honest htarget.second
          hnSecond hsecondLt htarget.second_within
      obtain ⟨hwfK, hwalkK, _hjustK⟩ :=
        hdomainK htarget.validator htarget.validator_honest
          htarget.second htarget.second_within
      have hheadK : (get_head cfg
          (E.store cfg ext htarget.validator htarget.second)).root ∈
          (E.store cfg ext htarget.validator htarget.second).block_roots :=
        E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT hanchor
          hboundary htarget.validator_honest htarget.second
            htarget.second_within
      have hcKnownK : c.root ∈
          (E.store cfg ext htarget.validator htarget.second).block_roots :=
        hcKnown htarget.validator htarget.validator_honest htarget.second
          hnSecond htarget.second_within
      have hcAgree : (E.store cfg ext v (n + 1)).blocks c.root =
          (E.store cfg ext htarget.validator htarget.second).blocks c.root :=
        hT.wellFormed.blocks_agree
          (E.blockProvenance cfg ext v (n + 1))
          (E.blockProvenance cfg ext htarget.validator htarget.second)
          (by simpa only [c] using hreal.root_known) hcKnownK
      have hcSlotLeTarget :
          ((E.store cfg ext htarget.validator htarget.second).blocks c.root).slot ≤
            compute_start_slot_at_epoch cfg J.epoch := by
        rw [← hcAgree]
        have hcSlotLeC :
            ((E.store cfg ext v (n + 1)).blocks c.root).slot ≤
              compute_start_slot_at_epoch cfg c.epoch := by
          simpa only [c] using hreal.root_slot_le_boundary
        exact hcSlotLeC.trans
          (Nat.mul_le_mul_right cfg.slots_per_epoch hcJ)
      have htargetRoot : get_checkpoint_block cfg
          (E.store cfg ext htarget.validator htarget.second)
          (get_head cfg
            (E.store cfg ext htarget.validator htarget.second)).root J.epoch =
          J.root := by
        have htargetData : (honest_attestation_data cfg ext
            (E.store cfg ext htarget.validator htarget.second)
            htarget.vote_slot htarget.index).target = J := by
          simpa only [honest_attestation_data_eq] using htarget.target_eq
        have hroot := honest_attestation_data_target_root cfg ext
          (E.store cfg ext htarget.validator htarget.second)
          htarget.vote_slot htarget.index
        rw [htargetData] at hroot
        exact hroot.symm
      have heta : (get_ancestor
          (E.store cfg ext htarget.validator htarget.second)
          (get_node_for_root (get_head cfg
            (E.store cfg ext htarget.validator htarget.second)).root)
          (compute_start_slot_at_epoch cfg J.epoch)).root = J.root := by
        simpa only [get_checkpoint_block, get_node_for_root] using htargetRoot
      have htargetSpec := get_ancestor_spec hwfK htarget.target_walk
      simp only [get_node_for_root] at heta
      rw [heta] at htargetSpec
      have hJK : J.root ∈
          (E.store cfg ext htarget.validator htarget.second).block_roots :=
        htargetSpec.1
      have hJcK : is_ancestor
          (E.store cfg ext htarget.validator htarget.second)
          (get_node_for_root J.root) (get_node_for_root c.root) = true := by
        have hcomp := get_ancestor_comp_root hwfK hcSlotLeTarget
          (hwalkK c.root hcKnownK _ hheadK)
        rw [is_ancestor_node_root] at hheadC
        simp only [is_ancestor_get_node_for_root, decide_eq_true_eq] at hheadC ⊢
        simp only [get_node_for_root] at hheadC hcomp
        rw [heta, hheadC] at hcomp
        exact hcomp
      have hsemantic : E.RootDescends J.root c.root :=
        E.rootDescends_of_store_ancestor
          (E.blockProvenance cfg ext htarget.validator htarget.second)
          hwfK (hwalkK c.root hcKnownK J.root hJK) hJcK
      exact (E.store_known_ancestor_of_rootDescends_for_storeReflection
        cfg ext hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
        hjustM hcExecutionRoot hsemantic).2
  exact head_ge_of_justified_ge_K cfg hwfM hwalkM hjustM hcKnownM hJc

end Execution

end FastConfirmation.Spec

end
