module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem trusted_justifiedRootKnown_of_acceptedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {w : ValidatorIndex} (_hw : w ∈ E.honest) (m : ℕ)
    (_hHm : E.WithinHorizon cfg m) :
    (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
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
        B.state.includedAttestations.relation hincluded
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
`trusted_justifiedRootKnown_of_acceptedGlobalTrajectory` above.

This is the accepted replacement for routing action-facing proofs through
`SelectedMarginDomain` merely to obtain store geometry. -/
theorem trusted_storeDomainK_of_acceptedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.StoreDomainK cfg ext := by
  intro w hw m hHm
  exact
    ⟨E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled w m,
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        hT.genesis_structure w m,
      E.trusted_justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
        hanchor hboundary hw m hHm⟩

/-- `get_head` is a known block at every accepted honest boundary store.
The executable fallback is the store's justified root, whose knownness is
now derived from accepted global semantics rather than a selected-margin or
legacy justification premise. -/
theorem trusted_headRootKnown_of_acceptedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
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
    exact E.trusted_justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hw m hHm

/-- The handler-local well-formed core over every exact causal prefix is a
pure consequence of scheduled-prefix trajectory data. -/
theorem trusted_exactCausalStoreWellFormedCore_of_trajectory
    (hT : E.ScheduledPrefixPremises cfg ext) :
    E.ExactCausalStoreWellFormedCore cfg ext := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hbase : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent).core
  intro store hstore
  exact E.exactCausalStoreWellFormedCore
    hT.externals_coherence.state_transition_slot hbase hstore

/-- Build the exact narrow assumption record consumed by prefix vote
realization from accepted global semantics and lower trajectory geometry. -/
def CurrentTargetPrefixVoteAssumptions.of_trustedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.CurrentTargetPrefixVoteAssumptions cfg ext where
  trajectory := hT
  justified_root_known := by
    intro w hw m hHm
    exact E.trusted_justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hw m hHm

/-! ## Honest vote-target walks -/


theorem trusted_postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.PostAnchorHonestVoteTargetWalkDomain cfg ext := by
  let hV := CurrentTargetPrefixVoteAssumptions.of_trustedGlobalTrajectory
    cfg ext E B hT hanchor hboundary
  exact E.postAnchorHonestVoteTargetWalkDomain_of_prefixVoteAssumptions
    cfg ext hV hanchor hboundary

end Execution
end FastConfirmation.Spec
end
