module
public import FastConfirmationProofs.Execution.Calls.ScheduledPrefixGeometry
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem ScheduledEventPrefix.trusted_justifiedRootKnown_of_acceptedGlobalTrajectory
    (p : E.ScheduledEventPrefix)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    (p.store cfg ext).justified_checkpoint.root ∈
      (p.store cfg ext).block_roots := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ ast ablk,
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgen, hslot⟩
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgen] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchor0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnown : B.anchor.root ∈ (p.store cfg ext).block_roots :=
    (p.genesisStoreLE cfg ext).1 hanchor0
  have hanchorBlock :
      (p.store cfg ext).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact p.anchorBlock cfg ext hT.wellFormed hgen
      (hanchorRoot ▸ hanchorKnown)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgen, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (p.store cfg ext) := .scheduledPrefix p
  have hparentSlots : ParentSlotLt (p.store cfg ext) :=
    p.parentSlotLt cfg ext E hT
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
    hjustAnchor | hevidence
  · rw [hjustAnchor]
    exact hanchorKnown
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hincluded⟩ := carrier.formed_evidence.certified
    have hcertified : CertifiedJustified cfg E B.anchor
        (p.store cfg ext).justified_checkpoint :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        B.state.includedAttestations.relation hincluded
    have hanchorEpochLe : B.anchor.epoch ≤
        (p.store cfg ext).justified_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
    have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (p.store cfg ext).justified_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (p.store cfg ext)
        ((p.store cfg ext).blocks B.anchor.root).slot carrier.tip :=
      p.walkKnownK cfg ext hT B.anchor.root hanchorKnown
        carrier.tip carrier.tip_carrier.known
    have hwalk : WalkKnown (p.store cfg ext)
        (compute_start_slot_at_epoch cfg
          (p.store cfg ext).justified_checkpoint.epoch) carrier.tip := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots hwalk

/-- The totalized `get_head` fallback is in-domain at every exact scheduled
prefix under accepted global semantics. -/
theorem ScheduledEventPrefix.trusted_headRootKnown_of_acceptedGlobalTrajectory
    (p : E.ScheduledEventPrefix)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    (get_head cfg (p.store cfg ext)).root ∈
      (p.store cfg ext).block_roots := by
  rcases get_head_root_mem_or cfg (p.store cfg ext) with hhead | hfallback
  · exact hhead
  · rw [hfallback]
    exact p.trusted_justifiedRootKnown_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary

/-- The exact executable current target lands on a known block no later than
the start of its checkpoint epoch.  In particular its block epoch is either
the target epoch or strictly older; this is the exhaustive split used by the
accepted GJ/GU gate facade. -/
theorem ScheduledEventPrefix.trusted_currentTargetKnown_and_blockEpoch_le
    (p : E.ScheduledEventPrefix)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    let target := get_current_target cfg (p.store cfg ext)
    target.root ∈ (p.store cfg ext).block_roots ∧
      get_block_epoch cfg (p.store cfg ext) target.root ≤ target.epoch := by
  let store := p.store cfg ext
  let target := get_current_target cfg store
  let head := (get_head cfg store).root
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgen] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchor0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnown : B.anchor.root ∈ store.block_roots := by
    exact (p.genesisStoreLE cfg ext).1 hanchor0
  have hanchorBlock : store.blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact p.anchorBlock cfg ext hT.wellFormed hgen
      (hanchorRoot ▸ hanchorKnown)
  have hanchorEpoch : B.anchor.epoch =
      compute_epoch_at_slot cfg ablk.message.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgen] at he
    simpa only [get_forkchoice_store, get_current_epoch, hslot] using he
  have hanchorSlotLeCurrent : ablk.message.slot ≤
      get_current_slot cfg store := by
    rw [← hanchorBlock]
    exact p.blocksSlotLeCurrent cfg ext E hT B.anchor.root hanchorKnown
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg store := by
    rw [hanchorEpoch]
    exact ce_mono cfg hanchorSlotLeCurrent
  have hheadKnown : head ∈ store.block_roots := by
    exact p.trusted_headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary
  have hwalkAnchor : WalkKnown store
      (store.blocks B.anchor.root).slot head :=
    p.walkKnownK cfg ext hT B.anchor.root hanchorKnown head hheadKnown
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgen, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
      head := by
    apply hwalkAnchor.mono
    rw [hanchorBlock]
    exact hboundary'.trans
      (Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLeCurrent)
  have hspec := get_ancestor_spec
    (p.parentSlotLt cfg ext E hT) hwalk
  have htargetKnown : target.root ∈ store.block_roots := by
    simpa only [target, head, get_current_target, get_checkpoint_for_block]
      using hspec.1
  have htargetSlotLe : (store.blocks target.root).slot ≤
      compute_start_slot_at_epoch cfg target.epoch := by
    simpa only [target, head, get_current_target, get_checkpoint_for_block]
      using hspec.2
  refine ⟨htargetKnown, ?_⟩
  have hepoch := ce_mono cfg htargetSlotLe
  simpa only [get_block_epoch, compute_epoch_at_slot,
    compute_start_slot_at_epoch,
    Nat.mul_div_cancel _ cfg.slots_per_epoch_pos] using hepoch

/-- The exact current target cannot precede the retained trusted-anchor epoch.
This is clock/retention geometry, not an FFG-safety assumption. -/
theorem ScheduledEventPrefix.trusted_currentTarget_anchor_epoch_le
    (p : E.ScheduledEventPrefix)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    B.anchor.epoch ≤
      (get_current_target cfg (p.store cfg ext)).epoch := by
  let store := p.store cfg ext
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgen] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchor0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnown : B.anchor.root ∈ store.block_roots :=
    (p.genesisStoreLE cfg ext).1 hanchor0
  have hanchorBlock : store.blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact p.anchorBlock cfg ext hT.wellFormed hgen
      (hanchorRoot ▸ hanchorKnown)
  have hanchorEpoch : B.anchor.epoch =
      compute_epoch_at_slot cfg ablk.message.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgen] at he
    simpa only [get_forkchoice_store, get_current_epoch, hslot] using he
  have hanchorSlotLeCurrent : ablk.message.slot ≤
      get_current_slot cfg store := by
    rw [← hanchorBlock]
    exact p.blocksSlotLeCurrent cfg ext E hT B.anchor.root hanchorKnown
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg store := by
    rw [hanchorEpoch]
    exact ce_mono cfg hanchorSlotLeCurrent
  change B.anchor.epoch ≤ get_current_store_epoch cfg store
  exact hanchorEpochLeCurrent

/-- At the aligned trusted-anchor boundary, an exact current target in the
anchor epoch is the anchor itself.  Therefore every distinct current target
has a strictly later epoch. -/
theorem ScheduledEventPrefix.trusted_currentTarget_anchor_epoch_lt_of_ne
    (p : E.ScheduledEventPrefix)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hne : get_current_target cfg (p.store cfg ext) ≠ B.anchor) :
    B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch := by
  let store := p.store cfg ext
  let target := get_current_target cfg store
  have hanchorLe := p.trusted_currentTarget_anchor_epoch_le cfg ext B hT
    hanchor hboundary
  change B.anchor.epoch ≤ target.epoch at hanchorLe
  rcases lt_or_eq_of_le hanchorLe with hlt | hepoch
  · exact hlt
  · obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
    have hanchorRoot : B.anchor.root = ablk.root := by
      have hr := congrArg Checkpoint.root hanchor
      rw [hgen] at hr
      simpa only [get_forkchoice_store] using hr
    have hanchor0 : B.anchor.root ∈ E.genesis_store.block_roots := by
      rw [hgen, hanchorRoot]
      simp only [get_forkchoice_store, List.mem_singleton]
    have hanchorKnown : B.anchor.root ∈ store.block_roots :=
      (p.genesisStoreLE cfg ext).1 hanchor0
    have hanchorBlock : store.blocks B.anchor.root = ablk.message := by
      rw [hanchorRoot]
      exact p.anchorBlock cfg ext hT.wellFormed hgen
        (hanchorRoot ▸ hanchorKnown)
    have hanchorEpoch : B.anchor.epoch =
        compute_epoch_at_slot cfg ablk.message.slot := by
      have he := congrArg Checkpoint.epoch hanchor
      rw [hgen] at he
      simpa only [get_forkchoice_store, get_current_epoch, hslot] using he
    have hboundary' : ablk.message.slot ≤
        compute_start_slot_at_epoch cfg B.anchor.epoch := by
      simpa only [TrustedAnchorBoundaryAligned, hgen, hanchorRoot,
        get_forkchoice_store, Function.update_self] using hboundary
    have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        ablk.message.slot := by
      have hdiv := Nat.div_mul_le_self ablk.message.slot
        cfg.slots_per_epoch
      have hdivEpoch : ablk.message.slot / cfg.slots_per_epoch =
          B.anchor.epoch := by
        simpa only [compute_epoch_at_slot] using hanchorEpoch.symm
      rw [hdivEpoch] at hdiv
      simpa only [compute_start_slot_at_epoch] using hdiv
    have hboundaryEq : ablk.message.slot =
        compute_start_slot_at_epoch cfg B.anchor.epoch :=
      Nat.le_antisymm hboundary' hstartLe
    have htargetKnown : target.root ∈ store.block_roots := by
      have hlanding := p.trusted_currentTargetKnown_and_blockEpoch_le cfg ext B hT
        hanchor hboundary
      simpa only [store, target] using hlanding.1
    let head := (get_head cfg store).root
    have hheadKnown : head ∈ store.block_roots := by
      exact p.trusted_headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
        hanchor hboundary
    have hwalkAnchor : WalkKnown store
        (store.blocks B.anchor.root).slot head :=
      p.walkKnownK cfg ext hT B.anchor.root hanchorKnown head hheadKnown
    have hwalk : WalkKnown store
        (compute_start_slot_at_epoch cfg target.epoch) head := by
      apply hwalkAnchor.mono
      rw [hanchorBlock, hboundaryEq]
      exact Nat.mul_le_mul_right cfg.slots_per_epoch hanchorLe
    have hspec := get_ancestor_spec
      (p.parentSlotLt cfg ext E hT) hwalk
    have htargetSlotLe : (store.blocks target.root).slot ≤
        compute_start_slot_at_epoch cfg target.epoch := by
      simpa only [target, head, get_current_target, get_checkpoint_for_block]
        using hspec.2
    have hanchorLeTarget : ablk.message.slot ≤
        (store.blocks target.root).slot :=
      p.anchorMinSlot cfg ext hT hgen target.root htargetKnown
    have htargetLeAnchor : (store.blocks target.root).slot ≤
        ablk.message.slot := by
      rw [hboundaryEq, hepoch]
      exact htargetSlotLe
    have htargetSlotEq : (store.blocks target.root).slot =
        ablk.message.slot :=
      Nat.le_antisymm htargetLeAnchor hanchorLeTarget
    have htargetRoot : target.root = B.anchor.root := by
      rcases p.nonAnchorParentKnown cfg ext hgen target.root htargetKnown with
        hroot | hparentKnown
      · exact hroot.trans hanchorRoot.symm
      · have hparentLt :=
          p.parentSlotLt cfg ext E hT target.root htargetKnown hparentKnown
        rw [htargetSlotEq] at hparentLt
        have hanchorLeParent := p.anchorMinSlot cfg ext hT hgen
          (store.blocks target.root).parent_root hparentKnown
        exact absurd hparentLt (Nat.not_lt_of_ge hanchorLeParent)
    have htargetAnchor : target = B.anchor := by
      generalize ht : target = t at hepoch htargetRoot ⊢
      generalize ha : B.anchor = a at hepoch htargetRoot ⊢
      cases t
      cases a
      simp only at hepoch htargetRoot ⊢
      subst_vars
      rfl
    exfalso
    apply hne
    simpa only [store, target] using htargetAnchor


end Execution
end FastConfirmation.Spec
end
