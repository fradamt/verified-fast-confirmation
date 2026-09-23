module
public import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts
public import FastConfirmation.Spec.Proof.ActualResetCheckpointRealization
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Accepted realization of the executable FCR reset checkpoints

This file realizes the finalized and observed-reset inputs in the
accepted-prefix FFG semantics. The only reset-specific state is the exact
ordered field rotation already proved for `update_fast_confirmation_variables`.
Checkpoint origins, certificates, and causal-store reflection all come from
one `ExactPrefixAcceptedFFGSemantics` selected before the execution store.

No legacy `ChainFFGState`, `BlockStateTransitionHistory`, justification
interface, confirmation conclusion, filter conclusion, or safety premise is
used by the declarations below.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Narrow trajectory transport -/

/-- A realized reset checkpoint persists along one node's store trajectory.
The proof needs only root-list monotonicity, accepted block-message uniqueness,
and clock monotonicity; it does not use any FFG or safety interface. -/
theorem ResetCheckpointRealizedAt.mono_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor c : Checkpoint Root} {v : ValidatorIndex} {n m : ℕ}
    (hnm : n ≤ m)
    (h : E.ResetCheckpointRealizedAt cfg anchor
      (E.store cfg ext v n) c) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext v m) c := by
  have hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext v m).block_roots :=
    (E.store_storeLE cfg ext v hnm).1
  have hknownM : c.root ∈ (E.store cfg ext v m).block_roots :=
    hsub h.root_known
  have hagree : (E.store cfg ext v n).blocks c.root =
      (E.store cfg ext v m).blocks c.root :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v m) h.root_known hknownM
  have hcurrentMono :
      get_current_store_epoch cfg (E.store cfg ext v n) ≤
        get_current_store_epoch cfg (E.store cfg ext v m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (E.slot_at_mono cfg hnm)
  exact {
    root_known := hknownM
    root_slot_le_boundary := by
      rw [← hagree]
      exact h.root_slot_le_boundary
    epoch_le_current := h.epoch_le_current.trans hcurrentMono
    certified := h.certified
  }

/-! ## Accepted selector realization -/

/-- The boundary-aligned trusted anchor is a realized reset checkpoint in
every execution store under the safety-free trajectory assumptions. -/
theorem resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext v n) anchor := by
  obtain ⟨ast, ablk, hgenEq, _hanchorSlot, _hanchorParent⟩ := hT.genesis_structure
  have hanchorRoot : anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hknown0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hknownN : anchor.root ∈ (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hknown0
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq v n
      (hanchorRoot ▸ hknownN)
  have hslotUpper : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hslot0 : get_current_slot cfg E.genesis_store = ast.slot := by
    rw [hgenEq]
    exact get_current_slot_get_forkchoice_store cfg hT.whole_seconds ast ablk
  have hslotAtZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext v 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    exact hcurrent0.symm.trans hslot0
  have hanchorEpoch : anchor.epoch = compute_epoch_at_slot cfg ast.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at he
    simpa only [get_forkchoice_store, get_current_epoch] using he
  have hcurrentMono : get_current_store_epoch cfg E.genesis_store ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      hslot0, compute_epoch_at_slot]
    rw [← hslotAtZero]
    exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.zero_le n))
  exact {
    root_known := hknownN
    root_slot_le_boundary := by
      rw [hanchorBlock]
      exact hslotUpper
    epoch_le_current := by
      rw [hanchorEpoch]
      simpa only [get_current_store_epoch, hslot0] using hcurrentMono
    certified := ⟨CertifiedJustified.anchor⟩
  }

/-- Accepted AU carrier evidence realizes its checkpoint in the same concrete
execution store.  The boundary walk identifies the root and its boundary-slot
upper bound; accepted AU formation supplies the included certificate and the
checkpoint epoch bound. -/
theorem AcceptedSelectorAUCarrier.resetCheckpointRealizedAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : ℕ} {c : Checkpoint Root}
    (h : AcceptedSelectorAUCarrier B.state (E.store cfg ext w m) c) :
    E.ResetCheckpointRealizedAt cfg B.anchor
      (E.store cfg ext w m) c := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorKnown0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnown : B.anchor.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorKnown0
  have hanchorBlock :
      (E.store cfg ext w m).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq w m
      (hanchorRoot ▸ hanchorKnown)
  have hanchorBoundary : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  obtain ⟨hincluded⟩ := h.formed_evidence.certified
  have hcertified : CertifiedJustified cfg E B.anchor c :=
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.AcceptedIncludedAttestationRelation.relation
        cfg ext E B.state.includedAttestations) hincluded
  have hanchorEpochLe : B.anchor.epoch ≤ c.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
  have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
      compute_start_slot_at_epoch cfg c.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hwalkAnchor : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks B.anchor.root).slot h.tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ w m
      B.anchor.root hanchorKnown h.tip h.tip_carrier.known
  have hwalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg c.epoch) h.tip := by
    apply hwalkAnchor.mono
    rw [hanchorBlock]
    exact hanchorBoundary.trans hstartLe
  have hparentSlots : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled w m
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hcheckpoint : c = get_checkpoint_for_block cfg
      (E.store cfg ext w m) h.tip c.epoch :=
    B.coherence.au_checkpoint_of_known hstore h.tip
      h.tip_carrier.known c h.au
  have hroot : c.root = get_checkpoint_block cfg
      (E.store cfg ext w m) h.tip c.epoch := by
    have hr := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block] using hr
  have hspec := get_ancestor_spec hparentSlots hwalk
  have htipAt : E.AcceptedBlockAt cfg ext h.tip
      ((E.store cfg ext w m).blocks h.tip) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore h.tip_carrier.known
  have hcEpochLeTip : c.epoch ≤ compute_epoch_at_slot cfg
      ((E.store cfg ext w m).blocks h.tip).slot :=
    B.state.au_epoch_le_block htipAt h.au
  have htipSlotUpper : ((E.store cfg ext w m).blocks h.tip).slot ≤
      get_current_slot cfg (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
      w m h.tip h.tip_carrier.known
  exact {
    root_known := by rw [hroot]; exact hspec.1
    root_slot_le_boundary := by rw [hroot]; exact hspec.2
    epoch_le_current :=
      hcEpochLeTip.trans (ce_mono cfg htipSlotUpper)
    certified := ⟨hcertified⟩
  }

/-! ## Global finalized and unrealized-justified fields -/

/-- The exact accepted global finalized selector realizes the concrete store
field without passing through the legacy global FFG trajectory. -/
theorem finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} (m : ℕ) :
    E.ResetCheckpointRealizedAt cfg B.anchor (E.store cfg ext w m)
      (E.store cfg ext w m).finalized_checkpoint := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  rcases B.globalFinalized_anchor_or_AUEvidence hgenShort hanchor hstore with
    hanchorField | hevidence
  · rw [hanchorField]
    exact E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
      cfg ext hT hanchor hboundary w m
  · obtain ⟨hcarrier⟩ := hevidence
    exact Execution.AcceptedSelectorAUCarrier.resetCheckpointRealizedAt
      (E := E) cfg ext B hT hanchor hboundary hcarrier

/-- The exact accepted global unrealized-justified selector realizes the
fresh checkpoint which the ordered FCR rotation may cache. -/
theorem unrealizedJustifiedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} (m : ℕ) :
    E.ResetCheckpointRealizedAt cfg B.anchor (E.store cfg ext w m)
      (E.store cfg ext w m).unrealized_justified_checkpoint := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have horigins :=
    (B.causalStoreGlobalProjection hgenShort hanchor hstore).storeGlobal
  rcases horigins.unrealized_justified with
    hanchorField | ⟨tip, htip, hfield⟩
  · rw [hanchorField]
    exact E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
      cfg ext hT hanchor hboundary w m
  · have hAU : B.state.AU cfg ext tip
        (E.store cfg ext w m).unrealized_justified_checkpoint := by
      rw [hfield]
      exact B.state.gu_AU cfg ext htip.acceptedRoot
    obtain ⟨hcarrier⟩ : AcceptedSelectorAUEvidence B.state
        (E.store cfg ext w m)
          (E.store cfg ext w m).unrealized_justified_checkpoint :=
      AcceptedSelectorAUEvidence.of_AU htip hAU
    exact Execution.AcceptedSelectorAUCarrier.resetCheckpointRealizedAt
      (E := E) cfg ext B hT hanchor hboundary hcarrier

/-! ## Exact FCR checkpoint history and public reset producer -/

/-- Both retained FCR reset fields stay realized under the accepted global
trajectory.  The induction follows the executable write order exactly. -/
theorem resetCheckpointHistoryAt_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) :
    ∀ n : ℕ, E.ResetCheckpointHistoryAt cfg ext B.anchor v n := by
  intro n
  induction n with
  | zero =>
      have hfinal :=
        E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
          cfg ext B hT hanchor hboundary (w := v) 0
      constructor <;>
        simpa only [Execution.fcr, get_fast_confirmation_store] using hfinal
  | succ n ih =>
      have hobserved := ih.observed.mono_of_trajectory cfg ext E hT
        (Nat.le_succ n)
      have hprevious := ih.previous_greatest.mono_of_trajectory cfg ext E hT
        (Nat.le_succ n)
      have huj :=
        E.unrealizedJustifiedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
          cfg ext B hT hanchor hboundary (w := v) (n + 1)
      by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)
      · constructor
        · rw [E.fcr_observed_succ_of_advance cfg ext v n hadv]
          split_ifs <;> assumption
        · rw [E.fcr_previous_greatest_succ_of_advance cfg ext v n hadv]
          split_ifs <;> assumption
      · constructor
        · simpa only [Execution.fcr, if_neg hadv] using hobserved
        · simpa only [Execution.fcr, if_neg hadv] using hprevious

/-- The observed checkpoint read by the actual speculative query is realized
in that query's store, independently of whether the speculative query becomes
a real slot call. -/
theorem fcrStep_observed_resetRealizedAt_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ) :
    E.ResetCheckpointRealizedAt cfg B.anchor (E.store cfg ext v (n + 1))
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint := by
  have hhistory :=
    E.resetCheckpointHistoryAt_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary v n
  have hobserved := hhistory.observed.mono_of_trajectory cfg ext E hT
    (Nat.le_succ n)
  have hprevious := hhistory.previous_greatest.mono_of_trajectory
    cfg ext E hT (Nat.le_succ n)
  have huj :=
    E.unrealizedJustifiedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  rw [E.fcrStep_observed_exact cfg ext v n]
  split_ifs <;> assumption


end Execution


end FastConfirmation.Spec

end
