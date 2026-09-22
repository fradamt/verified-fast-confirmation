import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts

/-!
# Accepted geometry at exact scheduled-event prefixes

The action interpreter queries stores in the middle of one scheduled event
fold, not only the completed `Execution.store` boundary.  This module lifts
the retained-anchor fork-choice geometry to that exact prefix domain and then
derives the executable `get_current_target` landing bound.

No selected-margin domain, legacy justification interface, FFG safety result,
or target-epoch premise is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Prefix provenance and retained-anchor geometry -/

/-- Every exact scheduled prefix extends the trusted genesis store. -/
theorem ScheduledEventPrefix.genesisStoreLE
    (p : E.ScheduledEventPrefix) :
    StoreLE E.genesis_store (p.store cfg ext) := by
  rw [ScheduledEventPrefix.store]
  exact (E.store_storeLE cfg ext p.node
      (Nat.zero_le p.previousSecond)).trans
    ((on_tick_storeLE cfg _ _).trans
      (foldl_storeLE cfg ext _ _))

/-- Block provenance survives an arbitrary exact prefix of the scheduled
event list. -/
theorem ScheduledEventPrefix.blockProvenance
    (p : E.ScheduledEventPrefix) :
    BlockProvenance E (p.store cfg ext) := by
  rw [ScheduledEventPrefix.store]
  refine blockProvenance_foldl cfg ext _ _ ?_ ?_
  · intro b hb
    exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hb⟩
  · exact on_tick_blockProvenance cfg _ _
      (E.blockProvenance cfg ext p.node p.previousSecond)

/-- Every non-anchor root in an exact prefix has a known parent. -/
theorem ScheduledEventPrefix.nonAnchorParentKnown
    (p : E.ScheduledEventPrefix)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk) :
    NonAnchorParentKnown ablk.root (p.store cfg ext) := by
  rw [ScheduledEventPrefix.store]
  exact nonAnchorParentKnown_foldl cfg ext ablk.root _ _
    (on_tick_nonAnchorParentKnown cfg ablk.root _ _
      (E.store_nonAnchorParentKnown cfg ext hgen p.node
        p.previousSecond))

/-- The trusted anchor's message is unchanged in every exact prefix. -/
theorem ScheduledEventPrefix.anchorBlock
    (p : E.ScheduledEventPrefix)
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hr : ablk.root ∈ (p.store cfg ext).block_roots) :
    (p.store cfg ext).blocks ablk.root = ablk.message := by
  have hmem0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgen]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hblock0 : E.genesis_store.blocks ablk.root = ablk.message := by
    rw [hgen]
    simp only [get_forkchoice_store, Function.update_self]
  rcases p.blockProvenance cfg ext ablk.root hr with
    ⟨_hgenRoot, hblock⟩ | ⟨b, hsched, hroot, hblock⟩
  · rw [hblock, hblock0]
  · obtain ⟨w, n, hb⟩ := hsched
    have hmessage : b.message = E.genesis_store.blocks b.root :=
      hwf.genesis_blocks_agree w n b hb (hroot ▸ hmem0)
    rw [hblock, hmessage, hroot, hblock0]

/-- The anchor's dangling parent is not a known root at an exact prefix. -/
theorem ScheduledEventPrefix.danglingParentUnknown
    (p : E.ScheduledEventPrefix)
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root) :
    ablk.message.parent_root ∉ (p.store cfg ext).block_roots := by
  intro hmem
  have hanchor0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgen]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hparent0 :
      (E.genesis_store.blocks ablk.root).parent_root =
        ablk.message.parent_root := by
    rw [hgen]
    simp only [get_forkchoice_store, Function.update_self]
  rcases p.blockProvenance cfg ext ablk.message.parent_root hmem with
    ⟨hgenRoot, _hblock⟩ | ⟨b, hsched, hroot, _hblock⟩
  · rw [hgen] at hgenRoot
    simp only [get_forkchoice_store, List.mem_singleton] at hgenRoot
    exact hparent hgenRoot
  · obtain ⟨w, n, hb⟩ := hsched
    exact hwf.anchor_parent_unscheduled ablk.root hanchor0 w n b hb
      (hroot.trans hparent0.symm)

/-- Every exact-prefix block naming the dangling parent is the anchor block
and therefore lies at the anchor slot. -/
theorem ScheduledEventPrefix.anchorGuard
    (p : E.ScheduledEventPrefix)
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root) :
    ∀ r ∈ (p.store cfg ext).block_roots,
      ((p.store cfg ext).blocks r).parent_root =
          ablk.message.parent_root →
        ((p.store cfg ext).blocks r).slot ≤ ablk.message.slot := by
  intro r hr hpar
  rcases p.nonAnchorParentKnown cfg ext hgen r hr with heq | hknown
  · subst r
    rw [p.anchorBlock cfg ext hwf hgen hr]
  · rw [hpar] at hknown
    exact absurd hknown
      (p.danglingParentUnknown cfg ext hwf hgen hparent)

/-- The anchor slot is a lower bound on every block known at an exact prefix. -/
theorem ScheduledEventPrefix.anchorMinSlot
    (p : E.ScheduledEventPrefix)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk) :
    ∀ r ∈ (p.store cfg ext).block_roots,
      ablk.message.slot ≤ ((p.store cfg ext).blocks r).slot := by
  have hparentSlots : ParentSlotLt (p.store cfg ext) :=
    p.parentSlotLt cfg ext E hT
  have hnonAnchor := p.nonAnchorParentKnown cfg ext hgen
  have hanchor : ∀ hr : ablk.root ∈ (p.store cfg ext).block_roots,
      (p.store cfg ext).blocks ablk.root = ablk.message :=
    fun hr => p.anchorBlock cfg ext hT.wellFormed hgen hr
  have key : ∀ N r,
      ((p.store cfg ext).blocks r).slot = N →
      r ∈ (p.store cfg ext).block_roots →
      ablk.message.slot ≤ ((p.store cfg ext).blocks r).slot := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro r hslot hr
      rcases hnonAnchor r hr with heq | hparentKnown
      · subst r
        rw [hanchor hr]
      · have hlt := hparentSlots r hr hparentKnown
        have hle := ih _ (hslot ▸ hlt) _ rfl hparentKnown
        exact hle.trans hlt.le
  intro r hr
  exact key _ r rfl hr

/-- Target-known walk geometry at an exact scheduled prefix. -/
theorem ScheduledEventPrefix.walkKnownK
    (p : E.ScheduledEventPrefix)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext) :
    ∀ t ∈ (p.store cfg ext).block_roots,
      ∀ r ∈ (p.store cfg ext).block_roots,
        WalkKnown (p.store cfg ext) ((p.store cfg ext).blocks t).slot r := by
  obtain ⟨ast, ablk, hgen, _hslot, hparent⟩ := hT.genesis_structure
  have hQ : ParentInRootsOr ablk.message.parent_root (p.store cfg ext) := by
    intro r hr
    rcases p.nonAnchorParentKnown cfg ext hgen r hr with heq | hknown
    · right
      subst r
      rw [p.anchorBlock cfg ext hT.wellFormed hgen hr]
    · exact Or.inl hknown
  intro t ht r hr
  exact walkKnown_of_anchorSlot
    (p.parentSlotLt cfg ext E hT) hQ
    (p.anchorGuard cfg ext hT.wellFormed hgen hparent)
    (p.anchorMinSlot cfg ext hT hgen t ht) r hr

/-! ## Accepted justified/head and current-target landing -/

/-- Accepted global origins make the justified root known at an exact
scheduled prefix, including in the middle of its event fold. -/
theorem ScheduledEventPrefix.justifiedRootKnown_of_acceptedGlobalTrajectory
    (p : E.ScheduledEventPrefix)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
        (Execution.AcceptedIncludedAttestationRelation.relation
          cfg ext E B.state.includedAttestations) hincluded
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
theorem ScheduledEventPrefix.headRootKnown_of_acceptedGlobalTrajectory
    (p : E.ScheduledEventPrefix)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    (get_head cfg (p.store cfg ext)).root ∈
      (p.store cfg ext).block_roots := by
  rcases get_head_root_mem_or cfg (p.store cfg ext) with hhead | hfallback
  · exact hhead
  · rw [hfallback]
    exact p.justifiedRootKnown_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary

/-- The exact executable current target lands on a known block no later than
the start of its checkpoint epoch.  In particular its block epoch is either
the target epoch or strictly older; this is the exhaustive split used by the
accepted GJ/GU gate facade. -/
theorem ScheduledEventPrefix.currentTargetKnown_and_blockEpoch_le
    (p : E.ScheduledEventPrefix)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    exact p.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
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
theorem ScheduledEventPrefix.currentTarget_anchor_epoch_le
    (p : E.ScheduledEventPrefix)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
theorem ScheduledEventPrefix.currentTarget_anchor_epoch_lt_of_ne
    (p : E.ScheduledEventPrefix)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hne : get_current_target cfg (p.store cfg ext) ≠ B.anchor) :
    B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch := by
  let store := p.store cfg ext
  let target := get_current_target cfg store
  have hanchorLe := p.currentTarget_anchor_epoch_le cfg ext B hT
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
      have hlanding := p.currentTargetKnown_and_blockEpoch_le cfg ext B hT
        hanchor hboundary
      simpa only [store, target] using hlanding.1
    let head := (get_head cfg store).root
    have hheadKnown : head ∈ store.block_roots := by
      exact p.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
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
