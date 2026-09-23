module
public import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Crossing

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Historical A3.2 evaluator branches over accepted global trajectory data

These are the preferred action-facing wrappers for the carried current-epoch
branches.  They use one accepted-prefix FFG semantics and the narrow scheduled
trajectory assumptions.  Store geometry, head knownness, and exact causal
well-formedness come from the accepted global lower contracts; no
`SelectedMarginAssumptions`, selected-margin domain, or legacy justification
interface is reconstructed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Narrow trusted-anchor geometry from scheduled trajectory data -/

/-- Boundary alignment identifies the trusted anchor block slot using only
the scheduled trajectory's genesis facts. -/
theorem trustedAnchor_slot_eq_start_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    (E.genesis_store.blocks anchor.root).slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hepoch : get_block_epoch cfg E.genesis_store anchor.root =
      anchor.epoch := by
    rw [hgen, hroot]
    have h := congrArg Checkpoint.epoch hanchor
    rw [hgen] at h
    simp only [get_block_epoch, get_forkchoice_store,
      Function.update_self, get_current_epoch, hslot] at h ⊢
    exact h.symm
  apply Nat.le_antisymm hboundary
  rw [← hepoch]
  exact start_slot_at_block_epoch_le cfg E.genesis_store anchor.root

/-- The trusted anchor epoch is no later than a concrete execution store's
clock epoch, using only trajectory timing and accepted-message provenance. -/
theorem trustedAnchor_epoch_le_currentEpoch_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) :
    anchor.epoch ≤ get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hanchor0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorN : anchor.root ∈
      (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchor0
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hroot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgen v n
      (hroot ▸ hanchorN)
  have hslot0 := E.trustedAnchor_slot_eq_start_of_trajectory cfg ext hT
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgen, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  have hslotUpper : ((E.store cfg ext v n).blocks anchor.root).slot ≤
      get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v n anchor.root hanchorN
  simp only [get_current_store_epoch, compute_epoch_at_slot]
  apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
  change compute_start_slot_at_epoch cfg anchor.epoch ≤
    get_current_slot cfg (E.store cfg ext v n)
  rw [← hanchorStart, ← hanchorBlock]
  exact hslotUpper

/-- The trusted anchor supplies a walk to every later epoch boundary under
the narrow scheduled trajectory assumptions. -/
theorem trustedAnchor_boundaryWalkAtEpoch_of_trajectory
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) {e : Epoch}
    (hae : anchor.epoch ≤ e)
    {r : Root} (hr : r ∈ (E.store cfg ext v n).block_roots) :
    WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg e) r := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hanchor0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorN : anchor.root ∈
      (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchor0
  have hwalkAnchor : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks anchor.root).slot r :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgen, hslot, hparent⟩ v n
        anchor.root hanchorN r hr
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hroot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgen v n
      (hroot ▸ hanchorN)
  have hslot0 := E.trustedAnchor_slot_eq_start_of_trajectory cfg ext hT
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgen, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  apply hwalkAnchor.mono
  rw [hanchorBlock, hanchorStart]
  simpa only [compute_start_slot_at_epoch] using
    Nat.mul_le_mul_right cfg.slots_per_epoch hae

/-! ## Accepted-global carried/no-crossing wrapper -/

/-- Preferred no-crossing action wrapper.  The accepted global semantics
supplies the only fallback-root fact needed by the evaluator geometry. -/
noncomputable def carriedCurrentNoCrossingLineageAt_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext
      (E.fcrStep cfg ext v n))
    (hobserved : getLatestObservedRestartGuard cfg
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
        (E.fcrStep cfg ext v n).confirmed_root a c)
    {e : Epoch}
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.confirmed cfg ext v n) e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result e := by
  let ast : BeaconState Root := Classical.choose hT.genesis_structure
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis_structure)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis_structure)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hslot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hanchorParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT
  have hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hdomain := E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hv (n + 1) hHn1
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hinputKnown : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact hknownN1
  have hinputSlotUpper :
      ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot ≤
        get_current_slot cfg (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v (n + 1) _ hknownN1
  have hstrictNonGenesis : ∀ r ∈
      (E.fcrStep cfg ext v n).store.block_roots,
      ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot <
          ((E.fcrStep cfg ext v n).store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hr
    have hanchorBlock :
        (E.fcrStep cfg ext v n).store.blocks ablk.root = ablk.message := by
      rw [E.fcrStep_store]
      exact E.store_anchor_block cfg ext hT.wellFormed hgen v (n + 1)
        hanchorKnown
    have hanchorLeInput : ablk.message.slot ≤
        ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot := by
      rw [E.fcrStep_confirmed_root, E.fcrStep_store]
      exact E.store_anchor_min_slot cfg ext hT.wellFormed
        hT.externals_coherence hgen hslot hanchorParent v (n + 1)
          (E.confirmed cfg ext v n) hknownN1
    have hbad :
        ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot <
            ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeInput) hbad
  have hpreviousQ : E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.fcrStep cfg ext v n).confirmed_root e := by
    simpa only [E.fcrStep_confirmed_root] using hprevious
  exact E.carriedCurrentNoCrossingLineage_of_trace cfg ext B hT.wellFormed
    hcore hstore hparent hwalk hhead hinputKnown hinputSlotUpper
      (E.getLatestConfirmedTraceAt cfg ext v n) hfinalized hobserved
        hselector hresultCurrent hnoCrossing hstrictNonGenesis hpreviousQ

/-! ## Accepted-global current-target crossing wrapper -/

/-- Preferred crossing action wrapper over accepted global trajectory data.

The target-local accepted gate producer is the exact upstream interface.  The
selected result's source is not assumed: its accepted same-epoch path from the
current-target root is reconstructed from the evaluator trace, then used to
retie the concrete quorum without changing any vote or deadline. -/
noncomputable def
    carriedCurrentCrossingLineageAt_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext
      (E.fcrStep cfg ext v n))
    (hobserved : getLatestObservedRestartGuard cfg
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (htargetEpoch : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (get_current_target cfg (E.fcrStep cfg ext v n).store).root =
      (get_current_target cfg (E.fcrStep cfg ext v n).store).epoch)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v (n + 1)
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root a c)
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result
      (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) := by
  let ast : BeaconState Root := Classical.choose hT.genesis_structure
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis_structure)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis_structure)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hslot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hanchorParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT
  have hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hdomain := E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hv (n + 1) hHn1
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hinputKnown : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact hknownN1
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    E.trustedAnchor_epoch_le_currentEpoch_of_trajectory cfg ext hT
      hanchor hboundary v (n + 1)
  have hcurrentWalk : WalkKnown (E.fcrStep cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store))
      (get_head cfg (E.fcrStep cfg ext v n).store).root := by
    have hheadStore : (get_head cfg
        (E.fcrStep cfg ext v n).store).root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hhead
    have hboundaryWalk :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v (n + 1) hanchorEpochLeCurrent hheadStore
    simpa only [E.fcrStep_store] using hboundaryWalk
  let target := get_current_target cfg (E.fcrStep cfg ext v n).store
  have htargetKnown : target.root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    simpa only [target, get_current_target, get_checkpoint_for_block,
      get_checkpoint_block] using (get_ancestor_spec hparent hcurrentWalk).1
  have hstrictNonGenesis : ∀ r ∈
      (E.fcrStep cfg ext v n).store.block_roots,
      ((E.fcrStep cfg ext v n).store.blocks target.root).slot <
          ((E.fcrStep cfg ext v n).store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hr
    have hanchorBlock :
        (E.fcrStep cfg ext v n).store.blocks ablk.root = ablk.message := by
      rw [E.fcrStep_store]
      exact E.store_anchor_block cfg ext hT.wellFormed hgen v (n + 1)
        hanchorKnown
    have htargetKnownStore : target.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [target, E.fcrStep_store] using htargetKnown
    have hanchorLeTarget : ablk.message.slot ≤
        ((E.fcrStep cfg ext v n).store.blocks target.root).slot := by
      rw [E.fcrStep_store]
      exact E.store_anchor_min_slot cfg ext hT.wellFormed
        hT.externals_coherence hgen hslot hanchorParent v (n + 1)
          target.root htargetKnownStore
    have hbad : ((E.fcrStep cfg ext v n).store.blocks target.root).slot <
        ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeTarget) hbad
  have hsegment := E.carriedCurrentCrossingAcceptedTargetSegment cfg ext B
    hT.wellFormed hcore hstore hparent hwalk hhead hcurrentWalk hinputKnown
      (E.getLatestConfirmedTraceAt cfg ext v n) hfinalized hobserved
        hselector hresultCurrent htargetEpoch hedge
          (by simpa only [target] using hstrictNonGenesis)
  have hgateAndSupport :=
    E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
  have htargetGate := hproducer hgateAndSupport.1 hgateAndSupport.2
  have htargetCurrent :
      (get_current_target cfg (E.fcrStep cfg ext v n).store).epoch =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := rfl
  have hresultTargetEpoch : get_block_epoch cfg
      (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      (get_current_target cfg (E.fcrStep cfg ext v n).store).epoch :=
    hresultCurrent.trans htargetCurrent.symm
  have hfixed :=
    AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedSameEpochSegment
      cfg ext B hphase htargetEpoch hresultTargetEpoch hsegment htargetGate
  have hfixedProducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt cfg ext
        B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).result := by
    intro _hgate _hsupport
    exact hfixed
  exact E.carriedCurrentCrossingLineage cfg ext B hstore hparent hwalk
    hhead hcurrentWalk hinputKnown
      (E.getLatestConfirmedTraceAt cfg ext v n) hfinalized hobserved
        hselector hresultCurrent hprovisos hedge hfixedProducer

end Execution


end FastConfirmation.Spec

end
