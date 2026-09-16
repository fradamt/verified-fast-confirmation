import FastConfirmation.Spec.Proof.AcceptedSameEpochSegmentRealization
import FastConfirmation.Spec.Proof.AcceptedCurrentTargetPrefixVoteRealization

/-!
# Accepted current-target lower contracts

This module discharges the two concrete walk/knownness contracts used below
the accepted current-target gate.  Store-global justified origins come from one
preselected `ExactPrefixAcceptedFFGSemantics`; the only additional geometry is
the retained trusted-anchor walk in each concrete store.

No legacy `ChainFFGState`, `JustificationInterface`, quorum, target-agreement,
source-coherence, or safety premise is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Accepted global justified-root realization -/

/-- Accepted store-global origins make the justified root known at every
honest boundary store.  In the non-anchor case, the accepted selector's
included certificate puts its epoch no earlier than the anchor epoch.  The
ordinary retained-anchor walk can therefore be weakened to the selected
checkpoint boundary, where accepted checkpoint reflection identifies its
root.

`hboundary` is the genuine checkpoint-sync condition: an anchor block after
the start of its declared epoch cannot support this downward walk. -/
theorem justifiedRootKnown_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {w : ValidatorIndex} (_hw : w ∈ E.honest) (m : ℕ)
    (_hHm : E.WithinHorizon cfg m) :
    (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext w m).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq w m
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hparentSlots : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled w m
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
    hjustAnchor | hevidence
  · rw [hjustAnchor]
    exact hanchorMem
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hincluded⟩ := carrier.formed_evidence.certified
    have hcertified : CertifiedJustified cfg E B.anchor
        (E.store cfg ext w m).justified_checkpoint :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedIncludedAttestationRelation.relation cfg ext E
          B.state.includedAttestations) hincluded
    have hanchorEpochLe : B.anchor.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
    have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).justified_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks B.anchor.root).slot carrier.tip :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩ w m
        B.anchor.root hanchorMem carrier.tip carrier.tip_carrier.known
    have hwalk : WalkKnown (E.store cfg ext w m)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).justified_checkpoint.epoch) carrier.tip := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots hwalk

/-- The exact target-known fork-choice domain follows from accepted global
justified origins plus the ordinary execution trajectory.  Parent-slot
strictness and retained-anchor walks are mechanical; the final component is
`justifiedRootKnown_of_acceptedGlobalTrajectory` above.

This is the accepted replacement for routing action-facing proofs through
`SelectedMarginDomain` merely to obtain store geometry. -/
theorem storeDomainK_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.StoreDomainK cfg ext := by
  intro w hw m hHm
  exact
    ⟨E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        hT.genesis hT.wellFormed.anchor_parent_unscheduled w m,
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        hT.genesis w m,
      E.justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
        hanchor hboundary hw m hHm⟩

/-- `get_head` is a known block at every accepted honest boundary store.
The executable fallback is the store's justified root, whose knownness is
now derived from accepted global semantics rather than a selected-margin or
legacy justification premise. -/
theorem headRootKnown_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ)
    (hHm : E.WithinHorizon cfg m) :
    (get_head cfg (E.store cfg ext w m)).root ∈
      (E.store cfg ext w m).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext w m) with hhead | hfallback
  · exact hhead
  · rw [hfallback]
    exact E.justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hw m hHm

/-- The handler-local well-formed core over every exact causal prefix is a
pure consequence of scheduled-prefix trajectory data. -/
theorem exactCausalStoreWellFormedCore_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext) :
    E.ExactCausalStoreWellFormedCore cfg ext := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis
  have hbase : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent).core
  intro store hstore
  exact E.exactCausalStoreWellFormedCore
    hT.externals_coherence.state_transition_slot hbase hstore

/-- Build the exact narrow assumption record consumed by prefix vote
realization from accepted global semantics and lower trajectory geometry. -/
def CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.CurrentTargetPrefixVoteAssumptions cfg ext where
  trajectory := hT
  justified_root_known := by
    intro w hw m hHm
    exact E.justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hw m hHm

/-! ## Honest vote-target walks -/

/-- Once justified-root knownness is available for the totalized `get_head`
fallback, the honest vote-target walk is pure retained-anchor geometry.  This
factorization records the exact lower interface independently of how
justified-root knownness was obtained. -/
theorem postAnchorHonestVoteTargetWalkDomain_of_prefixVoteAssumptions
    (hV : E.CurrentTargetPrefixVoteAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := anchor)) :
    E.PostAnchorHonestVoteTargetWalkDomain cfg ext := by
  obtain ⟨hdiv, hwf, hec, _hhb, hgen⟩ := hV.trajectory
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hanchorRoot : anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorEpoch : anchor.epoch = compute_epoch_at_slot cfg ast.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at he
    simpa only [get_forkchoice_store, get_current_epoch] using he
  have hanchorMem0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  intro i hi s n index hs0 hnH hnSlot _hvote
  have hanchorMem : anchor.root ∈
      (E.store cfg ext i n).block_roots :=
    (E.store_storeLE cfg ext i (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext i n).blocks anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hwf hgenEq i n
      (hanchorRoot ▸ hanchorMem)
  have hheadKnown : (get_head cfg (E.store cfg ext i n)).root ∈
      (E.store cfg ext i n).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i n) with hhead | hfallback
    · exact hhead
    · rw [hfallback]
      exact hV.justified_root_known i hi n hnH
  have hheadStateSlot :
      ((E.store cfg ext i n).block_states
        (get_head cfg (E.store cfg ext i n)).root).slot ≤ s := by
    have hcore := E.store_wellFormedStoreCore cfg ext
      hec.state_transition_slot hgws.core i n
    rw [hcore.2 _ hheadKnown]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext hdiv
      hgenShort i n _ hheadKnown
    rwa [E.store_current_slot cfg ext i n, hnSlot] at hblockSlot
  have htargetEpoch :
      (honest_attestation cfg ext
        (E.store cfg ext i n) s index i).data.target.epoch =
        compute_epoch_at_slot cfg s :=
    honest_attestation_data_target_epoch cfg ext
      (E.store cfg ext i n) s index hec.process_slots_slot hheadStateSlot
  have hslotAtZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext i 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg hdiv] at hcurrent0
    exact hcurrent0.symm
  have hanchorEpochLeTarget : anchor.epoch ≤
      (honest_attestation cfg ext
        (E.store cfg ext i n) s index i).data.target.epoch := by
    calc
      anchor.epoch = compute_epoch_at_slot cfg ast.slot := hanchorEpoch
      _ ≤ compute_epoch_at_slot cfg s :=
        Nat.div_le_div_right (by rwa [hslotAtZero] at hs0)
      _ = (honest_attestation cfg ext
          (E.store cfg ext i n) s index i).data.target.epoch :=
        htargetEpoch.symm
  have hstartLe : compute_start_slot_at_epoch cfg anchor.epoch ≤
      compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext i n) s index i).data.target.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLeTarget
  have hwalkAnchor : WalkKnown (E.store cfg ext i n)
      ((E.store cfg ext i n).blocks anchor.root).slot
      (get_head cfg (E.store cfg ext i n)).root :=
    E.store_walkKnownK cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ i n
      anchor.root hanchorMem _ hheadKnown
  apply hwalkAnchor.mono
  rw [hanchorBlock]
  exact hboundary'.trans hstartLe

/-- Accepted-semantics producer for the full post-anchor honest vote-target
walk domain used by the current-target gate. -/
theorem postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.PostAnchorHonestVoteTargetWalkDomain cfg ext := by
  let hV := CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
    cfg ext E B hT hanchor hboundary
  exact E.postAnchorHonestVoteTargetWalkDomain_of_prefixVoteAssumptions
    cfg ext hV hanchor hboundary

/-- **The honest vote-target walk domain is derived, not assumed.**

For every actual post-anchor honest vote, the walk from the voter's own head
down to the boundary slot of the vote's target epoch stays inside that store's
block domain.  Nothing here is new assumption content:

* the voter's head is a known block — either `get_head` returns a block of the
  store (`get_head_root_mem_or`), or it falls back to the justified root, which
  `SelectedMarginDomain.justified_root_known` keeps known at every in-horizon
  honest store;
* every known block walks down to the retained trusted anchor's slot —
  `Execution.store_walkKnownK`, the store-closure family proved for arbitrary
  nodes out of the handler contract that `on_block` admits only parent-known
  blocks (`Model/Handlers.lean:354` ← fork-choice.md:908
  `assert block.parent_root in store.block_states`);
* the anchor's own block sits at or before the start slot of its epoch
  (`TrustedAnchorBoundaryAligned`), and the vote's target epoch is at or above
  the anchor epoch because the vote is post-anchor (`E.slot_at cfg 0 ≤ s`, the
  predicate's own hypothesis), so `WalkKnown.mono` lifts the anchor-slot walk
  to the target boundary slot.

The last bullet is where the post-anchor hypothesis is spent: a vote whose
target epoch preceded the anchor epoch would demand a walk *below* the retained
anchor, which no store can support.  `hboundary` is likewise irreducible — a
mid-epoch checkpoint-sync anchor cannot support the walk to the earlier
boundary of its own epoch — and it is exactly the premise the weak headlines
already carry for global justified/finalized root knownness.

This is the weakest producer in the file: it consumes neither
`ExactPrefixAcceptedFFGSemantics` nor `JustificationInterface`, only the
selected-margin floor plus the anchor identification and its boundary
alignment. -/
theorem postAnchorHonestVoteTargetWalkDomain_of_selectedMarginAssumptions
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := anchor)) :
    E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
  E.postAnchorHonestVoteTargetWalkDomain_of_prefixVoteAssumptions cfg ext
    (CurrentTargetPrefixVoteAssumptions.of_selectedMarginAssumptions cfg ext E hA)
    hanchor hboundary


end Execution

end FastConfirmation.Spec
