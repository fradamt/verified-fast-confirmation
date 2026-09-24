module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetGateGeometry
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.Checkpoints.TrustedSameEpochSegmentRealization
public import FastConfirmationProofs.FFG.SourceHistory.TrustedFFGSourceCoherence
public import FastConfirmationProofs.ModelFacts.TrustedFFGState
public import FastConfirmationProofs.FFG.Certificates.TrustedCurrentTargetCertificateRealization
public import FastConfirmationProofs.Execution.Calls.TrustedCurrentTargetPrefixVoteRealization
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

private theorem epoch_eq_of_start_le_lt_next
    {e : Epoch} {slot : Slot}
    (hlo : compute_start_slot_at_epoch cfg e ≤ slot)
    (hhi : slot < compute_start_slot_at_epoch cfg (e + 1)) :
    compute_epoch_at_slot cfg slot = e := by
  simp only [compute_epoch_at_slot]
  apply Nat.div_eq_of_lt_le
    (by simpa only [compute_start_slot_at_epoch] using hlo)
  simpa only [compute_start_slot_at_epoch, Nat.add_mul, one_mul] using hhi

omit [LinearOrder Root] [Inhabited Root] in
private theorem slot_lt_next_epoch_start_of_epoch
    {slot : Slot} {e : Epoch}
    (hepoch : compute_epoch_at_slot cfg slot = e) :
    slot < compute_start_slot_at_epoch cfg (e + 1) := by
  rw [← hepoch]
  simp only [compute_start_slot_at_epoch, compute_epoch_at_slot]
  simpa only [Nat.mul_comm] using
    (Nat.lt_mul_div_succ (b := cfg.slots_per_epoch) slot
      cfg.slots_per_epoch_pos)

omit [LinearOrder Root] [Inhabited Root] in
private theorem slot_lt_epoch_start_of_epoch_lt_accepted
    {slot : Slot} {e : Epoch}
    (h : compute_epoch_at_slot cfg slot < e) :
    slot < compute_start_slot_at_epoch cfg e := by
  have hnext : compute_epoch_at_slot cfg slot + 1 ≤ e :=
    Nat.succ_le_of_lt h
  have hlt := Nat.lt_mul_div_succ slot cfg.slots_per_epoch_pos
  calc
    slot < cfg.slots_per_epoch *
        (slot / cfg.slots_per_epoch + 1) := hlt
    _ ≤ cfg.slots_per_epoch * e :=
      Nat.mul_le_mul_left cfg.slots_per_epoch hnext
    _ = compute_start_slot_at_epoch cfg e := by
      simp only [compute_start_slot_at_epoch, Nat.mul_comm]

namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem trusted_acceptedCrossEpochParentGJEqGU_of_known_parent
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwf : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {parent child : Root}
    (hparentKnown : parent ∈ store.block_roots)
    (hchildKnown : child ∈ store.block_roots)
    (hchildNonGenesis : child ∉ E.genesis_store.block_roots)
    (hparent : (store.blocks child).parent_root = parent)
    (hcross : compute_epoch_at_slot cfg (store.blocks parent).slot <
      compute_epoch_at_slot cfg (store.blocks child).slot) :
    B.state.GJ child = B.state.GU parent := by
  obtain ⟨writer⟩ :=
    hstore.acceptedBlockLastWriterProvenance child hchildKnown
      hchildNonGenesis
  let t := writer.transition
  have htRoot : t.signedBlock.root = child := writer.root_eq
  have htMessage : t.signedBlock.message = store.blocks child :=
    writer.message_eq
  have htParent : t.signedBlock.message.parent_root = parent :=
    (congrArg BeaconBlock.parent_root htMessage).trans hparent
  have htParentKnown : t.signedBlock.message.parent_root ∈
      (t.atPrefix.store cfg ext).block_roots :=
    t.parent_known writer.fresh
  have hprefixParentKnown : parent ∈
      (t.atPrefix.store cfg ext).block_roots := by
    rw [← htParent]
    exact htParentKnown
  have hprefixParentAt : E.AcceptedBlockAt cfg ext parent
      ((t.atPrefix.store cfg ext).blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext
      (.scheduledPrefix t.atPrefix) hprefixParentKnown
  have hstoreParentAt : E.AcceptedBlockAt cfg ext parent
      (store.blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hparentKnown
  have hparentMessage : (t.atPrefix.store cfg ext).blocks parent =
      store.blocks parent :=
    hprefixParentAt.unique cfg ext E hwf hstoreParentAt
  have hprefixCore : WellFormedStoreCore
      (t.atPrefix.store cfg ext) :=
    hcore (.scheduledPrefix t.atPrefix)
  have hinsertionCross : compute_epoch_at_slot cfg
        ((t.atPrefix.store cfg ext).block_states
          t.signedBlock.message.parent_root).slot <
      compute_epoch_at_slot cfg t.signedBlock.message.slot := by
    calc
      compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).block_states
            t.signedBlock.message.parent_root).slot =
          compute_epoch_at_slot cfg
            ((t.atPrefix.store cfg ext).block_states parent).slot := by
        rw [htParent]
      _ = compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).blocks parent).slot :=
        congrArg (compute_epoch_at_slot cfg)
          (hprefixCore.2 parent hprefixParentKnown)
      _ = compute_epoch_at_slot cfg (store.blocks parent).slot :=
        congrArg (fun b => compute_epoch_at_slot cfg b.slot) hparentMessage
      _ < compute_epoch_at_slot cfg (store.blocks child).slot := hcross
      _ = compute_epoch_at_slot cfg t.signedBlock.message.slot :=
        (congrArg (fun b => compute_epoch_at_slot cfg b.slot)
          htMessage).symm
  obtain ⟨post, htransition, hpost⟩ :=
    Execution.AcceptedBlockTransition.on_block_inserted_state_fresh
      cfg ext writer.fresh t.accepted
  have hprojection : TrustedAcceptedFFGStoreProjection B.state
      (t.atPrefix.store cfg ext) :=
    Execution.TrustedCausalPrefixFFGInterpretation.causalStoreProjection B
      (.scheduledPrefix t.atPrefix)
  calc
    B.state.GJ child = B.state.GJ t.signedBlock.root :=
      congrArg B.state.GJ htRoot.symm
    _ = (t.postStore.block_states
          t.signedBlock.root).current_justified_checkpoint :=
      (B.coherence.transition_gj t).symm
    _ = post.current_justified_checkpoint :=
      congrArg BeaconState.current_justified_checkpoint hpost
    _ = (ext.process_justification_and_finalization
          ((t.atPrefix.store cfg ext).block_states parent)
        ).current_justified_checkpoint := by
      rw [← htParent]
      exact hboundaryPhase.state_transition_current_justified _ _ _
        htransition hinsertionCross
    _ = B.state.GU parent := hprojection.pulled_up_gu parent
      hprefixParentKnown

/-- Accepted, last-writer version of the target-boundary walk source lemma.
Same-epoch suffix edges preserve `GJ`; if the boundary landing is older, the
first edge above it is realized by an actual accepted cross-epoch transition
and changes the source to `GU` of the landing block. -/
theorem trusted_acceptedGJEqVSAt_of_target_walk_root
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwf : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparentSlots : ParentSlotLt store)
    {e : Epoch} {targetRoot head : Root}
    (hcurrentNonGenesis : ∀ r ∈ store.block_roots,
      get_block_epoch cfg store r = e →
        r ∉ E.genesis_store.block_roots)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) head)
    (hlands : (get_ancestor store (ForkChoiceNode.mk head .pending)
      (compute_start_slot_at_epoch cfg e)).root = targetRoot)
    (hheadEpoch : get_block_epoch cfg store head = e) :
    B.state.GJ head = B.state.VSAt cfg ext store targetRoot e := by
  induction hwalk generalizing targetRoot with
  | @stop r hr hle =>
      rw [get_ancestor_stop hle] at hlands
      have hre : r = targetRoot := hlands
      subst targetRoot
      simp only [TrustedCausalCarrierFFGState.VSAt, hheadEpoch, if_pos]
  | @step r hr hgt hp ih =>
      have hparentKnown := hp.root_mem
      have hparentSlotLt := hparentSlots r hr hparentKnown
      have hlandsParent : (get_ancestor store
          (ForkChoiceNode.mk (store.blocks r).parent_root .pending)
          (compute_start_slot_at_epoch cfg e)).root = targetRoot := by
        rw [get_ancestor_step hparentSlots hr hgt hp] at hlands
        exact hlands
      have hparentEpochLe :
          get_block_epoch cfg store (store.blocks r).parent_root ≤ e := by
        rw [← hheadEpoch]
        exact Nat.div_le_div_right hparentSlotLt.le
      by_cases hparentCurrent :
          get_block_epoch cfg store (store.blocks r).parent_root = e
      · have hsame : compute_epoch_at_slot cfg
            (store.blocks (store.blocks r).parent_root).slot =
            compute_epoch_at_slot cfg (store.blocks r).slot := by
          simpa only [get_block_epoch] using
            hparentCurrent.trans hheadEpoch.symm
        have hedge := E.trusted_acceptedProjectedSameEpochTransition_of_known_parent
          cfg ext (S := B.state) hwf hcore hstore hparentKnown hr
            (hcurrentNonGenesis r hr hheadEpoch) rfl hsame
        exact (hedge.gj_eq_parent hphase
          B.coherence.toTrustedFFGSelectorsMatchBeaconStates).trans
            (ih hlandsParent hparentCurrent)
      · have hparentOld :
            get_block_epoch cfg store (store.blocks r).parent_root < e :=
          Nat.lt_of_le_of_ne hparentEpochLe hparentCurrent
        have hparentBelow :
            (store.blocks (store.blocks r).parent_root).slot <
              compute_start_slot_at_epoch cfg e :=
          slot_lt_epoch_start_of_epoch_lt_accepted cfg hparentOld
        rw [get_ancestor_stop hparentBelow.le] at hlandsParent
        have hparentEq : (store.blocks r).parent_root = targetRoot :=
          hlandsParent
        have hcross : compute_epoch_at_slot cfg
            (store.blocks (store.blocks r).parent_root).slot <
            compute_epoch_at_slot cfg (store.blocks r).slot := by
          simpa only [get_block_epoch] using
            hparentOld.trans_eq hheadEpoch.symm
        have hedge := E.trusted_acceptedCrossEpochParentGJEqGU_of_known_parent
          cfg ext B hwf hcore hboundaryPhase hstore hparentKnown hr
            (hcurrentNonGenesis r hr hheadEpoch) rfl hcross
        have htargetOld : get_block_epoch cfg store targetRoot ≠ e := by
          rw [← hparentEq]
          exact Nat.ne_of_lt hparentOld
        rw [hparentEq] at hedge
        simp only [TrustedCausalCarrierFFGState.VSAt, if_neg htargetOld]
        exact hedge


namespace TrustedAcceptedCurrentTargetA32GateRealization
def fixedSource_of_acceptedTargetWalk_root
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwf : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparentSlots : ParentSlotLt store)
    {carrier : Root}
    (hcarrierEpoch : get_block_epoch cfg store carrier =
      (get_current_target cfg store).epoch)
    (hcurrentNonGenesis : ∀ r ∈ store.block_roots,
      get_block_epoch cfg store r = (get_current_target cfg store).epoch →
        r ∉ E.genesis_store.block_roots)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg
        (get_current_target cfg store).epoch) carrier)
    (hlands : (get_ancestor store (ForkChoiceNode.mk carrier .pending)
      (compute_start_slot_at_epoch cfg
        (get_current_target cfg store).epoch)).root =
      (get_current_target cfg store).root)
    (hgate : TrustedAcceptedCurrentTargetA32GateRealization cfg ext
      B.anchor B.state store) :
    TrustedAcceptedFixedSourceCurrentTargetA32GateRealization cfg ext
      B.anchor B.state store carrier := by
  refine ⟨hgate.certified, ?_⟩
  rcases hgate.support_branch with hanchor | ⟨hne, Q, hsource⟩
  · exact Or.inl hanchor
  · refine Or.inr ⟨hne, Q, ?_⟩
    have hgj : B.state.GJ carrier = B.state.VSAt cfg ext store
        (get_current_target cfg store).root
        (get_current_target cfg store).epoch :=
      E.trusted_acceptedGJEqVSAt_of_target_walk_root cfg ext B hwf hcore hphase
        hboundaryPhase hstore hparentSlots hcurrentNonGenesis hwalk hlands
        hcarrierEpoch
    calc
      Q.source = B.state.VSAt cfg ext store
          (get_current_target cfg store).root
          (get_current_target cfg store).epoch := hsource
      _ = B.state.GJ carrier := hgj.symm
      _ = B.state.VSAt cfg ext store carrier
          (get_current_target cfg store).epoch := by
        simp only [TrustedCausalCarrierFFGState.VSAt, hcarrierEpoch, if_pos]


end TrustedAcceptedCurrentTargetA32GateRealization
theorem trusted_acceptedHonestAttestationDataSourceEqVSAtTarget
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwf : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparentSlots : ParentSlotLt store)
    {slot : Slot} {index : CommitteeIndex} {target : Checkpoint Root}
    (hslotEpoch : compute_epoch_at_slot cfg slot = target.epoch)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg target.epoch)
      (get_head cfg store).root)
    (htarget : (honest_attestation_data cfg ext store slot index).target =
      target)
    (hheadStateSlotLe :
      (store.block_states (get_head cfg store).root).slot ≤ slot)
    (hcurrentNonGenesis : ∀ r ∈ store.block_roots,
      get_block_epoch cfg store r = target.epoch →
        r ∉ E.genesis_store.block_roots) :
    (honest_attestation_data cfg ext store slot index).source =
      B.state.VSAt cfg ext store target.root target.epoch := by
  let head := (get_head cfg store).root
  have hheadKnown : head ∈ store.block_roots := hwalk.root_mem
  have hroot := honest_attestation_data_target_root cfg ext store slot index
  rw [htarget] at hroot
  have hcheckpoint : get_checkpoint_block cfg store head target.epoch =
      target.root := hroot.symm
  have hlands : (get_ancestor store (ForkChoiceNode.mk head .pending)
      (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
    simpa only [get_checkpoint_block] using hcheckpoint
  have hheadEpochLe : get_block_epoch cfg store head ≤ target.epoch := by
    simp only [get_block_epoch, compute_epoch_at_slot]
    calc
      (store.blocks head).slot / cfg.slots_per_epoch =
          (store.block_states head).slot / cfg.slots_per_epoch := by
        rw [(hcore hstore).2 head hheadKnown]
      _ ≤ slot / cfg.slots_per_epoch :=
        Nat.div_le_div_right hheadStateSlotLe
      _ = target.epoch := by
        simpa only [compute_epoch_at_slot] using hslotEpoch
  have hprojection : TrustedAcceptedFFGStoreProjection B.state store :=
    Execution.TrustedCausalPrefixFFGInterpretation.causalStoreProjection B hstore
  by_cases hheadCurrent : get_block_epoch cfg store head = target.epoch
  · have hsame : compute_epoch_at_slot cfg
        (store.block_states head).slot = compute_epoch_at_slot cfg slot := by
      rw [(hcore hstore).2 head hheadKnown]
      exact hheadCurrent.trans hslotEpoch.symm
    have hsourceGJ :
        (honest_attestation_data cfg ext store slot index).source =
          B.state.GJ head := by
      rw [honest_attestation_data_source_eq_head_state hphase
        store slot index hsame]
      exact hprojection.block_state_gj head hheadKnown
    rw [hsourceGJ]
    exact E.trusted_acceptedGJEqVSAt_of_target_walk_root cfg ext B hwf hcore hphase
      hboundaryPhase hstore hparentSlots hcurrentNonGenesis hwalk hlands
      hheadCurrent
  · have hheadOld : get_block_epoch cfg store head < target.epoch :=
      Nat.lt_of_le_of_ne hheadEpochLe hheadCurrent
    have hstateEpochOld : compute_epoch_at_slot cfg
        (store.block_states head).slot < target.epoch := by
      rw [(hcore hstore).2 head hheadKnown]
      exact hheadOld
    have hstateBelow : (store.block_states head).slot <
        compute_start_slot_at_epoch cfg target.epoch :=
      slot_lt_epoch_start_of_epoch_lt_accepted cfg hstateEpochOld
    have hvoteStartLe : compute_start_slot_at_epoch cfg target.epoch ≤
        slot := by
      have hlo := Nat.div_mul_le_self slot cfg.slots_per_epoch
      have heq : slot / cfg.slots_per_epoch = target.epoch := by
        simpa only [compute_epoch_at_slot] using hslotEpoch
      rw [heq] at hlo
      simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlo
    have hstateSlotLt : (store.block_states head).slot < slot :=
      hstateBelow.trans_le hvoteStartLe
    have hheadBelow : (store.blocks head).slot <
        compute_start_slot_at_epoch cfg target.epoch :=
      slot_lt_epoch_start_of_epoch_lt_accepted cfg hheadOld
    rw [get_ancestor_stop hheadBelow.le] at hlands
    have hheadEq : head = target.root := hlands
    have hboundaryEpoch : compute_epoch_at_slot cfg
        (store.block_states head).slot < compute_epoch_at_slot cfg slot :=
      hstateEpochOld.trans_eq hslotEpoch.symm
    change (if (store.block_states head).slot < slot then
        ext.process_slots (store.block_states head) slot
      else store.block_states head).current_justified_checkpoint = _
    rw [if_pos hstateSlotLt]
    calc
      (ext.process_slots (store.block_states head) slot
          ).current_justified_checkpoint =
          (ext.process_justification_and_finalization
            (store.block_states head)).current_justified_checkpoint :=
        hboundaryPhase.process_slots_current_justified _ _
          hstateSlotLt hboundaryEpoch
      _ = B.state.GU head := hprojection.pulled_up_gu head hheadKnown
      _ = B.state.VSAt cfg ext store target.root target.epoch := by
        have htargetOld :
            get_block_epoch cfg store target.root ≠ target.epoch := by
          rw [← hheadEq]
          exact Nat.ne_of_lt hheadOld
        simp only [TrustedCausalCarrierFFGState.VSAt, if_neg htargetOld, hheadEq]

/-- Accepted/global carrier for one honest old-target vote.  Unlike
`AcceptedHonestSourceCarrier`, this record is deliberately tied to the
target block's eager `GU`: an old head may obtain its source through
`process_slots`, so the source need not equal `GJ(head)`. -/
structure TrustedAcceptedHonestOldTargetSourceCarrier
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex)
    (targetRoot : Root) where
  global_projection : TrustedAcceptedFFGGlobalStoreProjection B.state store
  target_block : BeaconBlock Root
  target_block_at : E.AcceptedBlockAt cfg ext targetRoot target_block
  target_block_eq : target_block = store.blocks targetRoot
  target_gu_carrier : TrustedAcceptedSelectorAUCarrier B.state store
    (B.state.GU targetRoot)
  target_gu_tip : target_gu_carrier.tip = targetRoot
  source_eq : (honest_attestation_data cfg ext store slot index).source =
    B.state.GU targetRoot

def TrustedAcceptedHonestOldTargetSourceEvidence
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex)
    (targetRoot : Root) : Prop :=
  Nonempty (TrustedAcceptedHonestOldTargetSourceCarrier cfg ext E B store slot index
    targetRoot)

namespace TrustedAcceptedHonestOldTargetSourceEvidence

theorem source_eq
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    {targetRoot : Root}
    (h : E.TrustedAcceptedHonestOldTargetSourceEvidence cfg ext B store slot index
      targetRoot) :
    (honest_attestation_data cfg ext store slot index).source =
      B.state.GU targetRoot := by
  obtain ⟨carrier⟩ := h
  exact carrier.source_eq

end TrustedAcceptedHonestOldTargetSourceEvidence

/-- A concrete vote for an old checkpoint landing carries accepted/global
source evidence for `GU(target.root)`.  The target block is identified between
the query prefix and the voter's causal store through `AcceptedBlockAt`
uniqueness.  Head-current and head-old cases are both discharged by
`trusted_acceptedHonestAttestationDataSourceEqVSAtTarget`. -/
theorem trusted_concreteHonestTargetVote_acceptedOldTargetSourceEvidence
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.CausalStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetOld : get_block_epoch cfg queryStore target.root < target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    E.TrustedAcceptedHonestOldTargetSourceEvidence cfg ext B
      (E.store cfg ext i vote.time) vote.slot vote.index target.root := by
  let voteStore := E.store cfg ext i vote.time
  let head := (get_head cfg voteStore).root
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenTrajectory :
      ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk ∧
          ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hcausalCore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore
      hT.externals_coherence.state_transition_slot hgenCore
  have hvoteCausal : E.CausalStore cfg ext voteStore := by
    simpa only [voteStore] using E.store_causal cfg ext i vote.time
  have hslot0 : E.slot_at cfg 0 ≤ vote.slot := by
    rw [← vote.slot_at_time]
    exact E.slot_at_mono cfg (Nat.zero_le vote.time)
  have hwalk : WalkKnown voteStore
      (compute_start_slot_at_epoch cfg target.epoch) head := by
    have hwalkVote := hwalkDomain i vote.honest vote.slot vote.time
      vote.index hslot0 vote.time_within_horizon vote.slot_at_time vote.vote
    simpa only [voteStore, head, vote.target_eq] using hwalkVote
  have hparentSlots : ParentSlotLt voteStore := by
    simpa only [voteStore] using
      E.store_parentSlotLt cfg ext hT.wellFormed
        hT.externals_coherence hT.genesis_structure
        hT.wellFormed.anchor_parent_unscheduled i vote.time
  have htargetData : (honest_attestation_data cfg ext voteStore
      vote.slot vote.index).target = target := by
    simpa only [voteStore, honest_attestation_data_eq] using vote.target_eq
  have hcheckpoint : get_checkpoint_block cfg voteStore head target.epoch =
      target.root := by
    have hroot := honest_attestation_data_target_root cfg ext voteStore
      vote.slot vote.index
    rw [htargetData] at hroot
    exact hroot.symm
  have hlands : (get_ancestor voteStore (ForkChoiceNode.mk head .pending)
      (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
    simpa only [get_checkpoint_block] using hcheckpoint
  have htargetSpec : target.root ∈ voteStore.block_roots ∧
      (voteStore.blocks target.root).slot ≤
        compute_start_slot_at_epoch cfg target.epoch := by
    have hspec := get_ancestor_spec hparentSlots hwalk
    rw [hlands] at hspec
    exact hspec
  have hqueryAt : E.AcceptedBlockAt cfg ext target.root
      (queryStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hvoteAt : E.AcceptedBlockAt cfg ext target.root
      (voteStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hvoteCausal htargetSpec.1
  have htargetBlocks : voteStore.blocks target.root =
      queryStore.blocks target.root :=
    hvoteAt.unique cfg ext E hT.wellFormed hqueryAt
  have hvoteTargetOld : get_block_epoch cfg voteStore target.root <
      target.epoch := by
    simpa only [get_block_epoch, htargetBlocks] using htargetOld
  have hheadKnown : head ∈ voteStore.block_roots := hwalk.root_mem
  have hvoteCore : WellFormedStoreCore voteStore := hcausalCore hvoteCausal
  have hheadBlockSlotLe : (voteStore.blocks head).slot ≤ vote.slot := by
    calc
      (voteStore.blocks head).slot ≤ get_current_slot cfg voteStore := by
        simpa only [voteStore, head] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds
            hgenTrajectory i vote.time
            (get_head cfg (E.store cfg ext i vote.time)).root
            (by simpa only [voteStore, head] using hheadKnown)
      _ = E.slot_at cfg vote.time := by
        simpa only [voteStore] using E.store_current_slot cfg ext i vote.time
      _ = vote.slot := vote.slot_at_time
  have hheadStateSlotLe : (voteStore.block_states head).slot ≤ vote.slot := by
    rw [hvoteCore.2 head hheadKnown]
    exact hheadBlockSlotLe
  have hanchorEpoch : B.anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgen]
    rfl
  have hcurrentNonGenesis : ∀ r ∈ voteStore.block_roots,
      get_block_epoch cfg voteStore r = target.epoch →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hcurrent hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorBlock : voteStore.blocks ablk.root = ablk.message := by
      simpa only [voteStore] using
        E.store_anchor_block cfg ext hT.wellFormed hgen i vote.time hr
    have hrootEpoch : get_block_epoch cfg voteStore ablk.root =
        B.anchor.epoch := by
      simp only [get_block_epoch]
      rw [hanchorBlock, ← hgenSlot]
      simpa only [get_current_epoch] using hanchorEpoch.symm
    exact (Nat.ne_of_lt hanchorBefore) (hrootEpoch.symm.trans hcurrent)
  have hsourceVSAt := E.trusted_acceptedHonestAttestationDataSourceEqVSAtTarget
    cfg ext B hT.wellFormed hcausalCore hphase hboundaryPhase hvoteCausal
    hparentSlots vote.slot_epoch hwalk htargetData hheadStateSlotLe
    hcurrentNonGenesis
  have hsource : (honest_attestation_data cfg ext voteStore
      vote.slot vote.index).source = B.state.GU target.root := by
    simpa only [TrustedCausalCarrierFFGState.VSAt, if_neg
      (Nat.ne_of_lt hvoteTargetOld)] using hsourceVSAt
  have hglobal : TrustedAcceptedFFGGlobalStoreProjection B.state voteStore :=
    B.causalStoreGlobalProjection hgenTrajectory hanchor hvoteCausal
  let htip : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) voteStore target.root :=
    Execution.AcceptedCarrierIn.of_causal_known hvoteCausal htargetSpec.1
  obtain ⟨carrier, hdesc, hformed⟩ :=
    B.state.gu_mem target.root htip.acceptedRoot
  let hguCarrier : TrustedAcceptedSelectorAUCarrier B.state voteStore
      (B.state.GU target.root) :=
    { tip := target.root
      carrier := carrier
      tip_carrier := htip
      au := ⟨carrier, hdesc, hformed⟩
      tip_descends_carrier := hdesc
      carrier_accepted := B.state.formed_carrier_accepted hformed
      formed_evidence := B.state.formed_evidence hformed }
  exact ⟨
    { global_projection := hglobal
      target_block := voteStore.blocks target.root
      target_block_at := hvoteAt
      target_block_eq := rfl
      target_gu_carrier := hguCarrier
      target_gu_tip := rfl
      source_eq := hsource }⟩

/-- Prefix-store specialization of the future-seat vote constructor.  The
query store need not be a completed `Execution.store`; the exact global
action adapter only has to identify its clock slot with `querySecond`.

This is the future half of the concrete signer set.  Its target agreement is
obtained from the action-derived whole-slot `HonestVotesSupportTarget`
property, not from a target certificate or a safety conclusion. -/
theorem trusted_currentTargetFutureHonestSeat_vote_of_currentSlot
    (hhb : HonestBehavior cfg ext E)
    {queryStore : Store Root} {querySecond : ℕ}
    (hcurrentSlot : get_current_slot cfg queryStore =
      E.slot_at cfg querySecond)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg queryStore))
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg queryStore) querySecond)
    {i : ValidatorIndex}
    (hiFuture : i ∈
      (E.currentTargetFutureSpan cfg queryStore).filter
        (fun j => j ∈ E.honest)) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg queryStore).epoch + 1))
      (get_current_target cfg queryStore)) := by
  simp only [Finset.mem_filter, Execution.currentTargetFutureSpan,
    Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiFuture
  obtain ⟨⟨s, hs, hiCommittee⟩, hi⟩ := hiFuture
  let e := get_current_store_epoch cfg queryStore
  have hloCurrent : compute_start_slot_at_epoch cfg e ≤
      get_current_slot cfg queryStore := by
    have h := Nat.div_mul_le_self (get_current_slot cfg queryStore)
      cfg.slots_per_epoch
    simpa only [e, get_current_store_epoch, compute_start_slot_at_epoch,
      Nat.mul_comm] using h
  have hendLt : currentTargetEpochEnd cfg queryStore <
      compute_start_slot_at_epoch cfg (e + 1) := by
    simp only [currentTargetEpochEnd, currentTargetEpochStart,
      compute_start_slot_at_epoch, e, Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left
      (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
  have hsEpoch : compute_epoch_at_slot cfg s = e :=
    epoch_eq_of_start_le_lt_next cfg (hloCurrent.trans hs.1)
      (hs.2.trans_lt hendLt)
  have htargetEpoch : (get_current_target cfg queryStore).epoch = e := rfl
  have hsTargetEpoch : compute_epoch_at_slot cfg s =
      (get_current_target cfg queryStore).epoch :=
    hsEpoch.trans htargetEpoch.symm
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_mono cfg hs.2 hendH
  have hquerySlot : E.slot_at cfg querySecond ≤ s := by
    rw [← hcurrentSlot]
    exact hs.1
  have hs0 : E.slot_at cfg 0 ≤ s :=
    (E.slot_at_mono cfg (Nat.zero_le querySecond)).trans hquerySlot
  obtain ⟨k, index, hkH, hkSlot, hvote⟩ :=
    hhb.votes_head i hi s hiCommittee hsH hs0
  have htarget :
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data.target =
        get_current_target cfg queryStore :=
    hsupport.2 i hi s hsH hsTargetEpoch hquerySlot k
      (honest_attestation cfg ext (E.store cfg ext i k) s index i) hvote
  refine ⟨⟨s, k, index, hi, hkH, hkSlot, hsH, hiCommittee, hvote,
    (hhb.vote_deadline i hi s k _ hvote).2,
    hsTargetEpoch, ?_, htarget⟩⟩
  exact slot_lt_next_epoch_start_of_epoch cfg hsTargetEpoch

/-- One concrete honest vote for a target that is current-epoch in the exact
query store yields an accepted same-epoch segment from the target checkpoint
root to that vote's actual head.

No ancestry segment or transition history is assumed.  The target equation
of `vote` fixes the boundary landing in the vote store.  Accepted block-message
uniqueness transports the query store's current-epoch fact to that landing,
and the ordinary walk is then lifted using last-writer provenance.
-/
theorem trusted_concreteHonestTargetVote_knownCurrentEpochSegment
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.CausalStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetEpoch : get_block_epoch cfg queryStore target.root = target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      (E.store cfg ext i vote.time) target.root
      (get_head cfg (E.store cfg ext i vote.time)).root := by
  let voteStore := E.store cfg ext i vote.time
  let head := (get_head cfg voteStore).root
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenTrajectory :
      ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk ∧
          ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hslot0 : E.slot_at cfg 0 ≤ vote.slot := by
    rw [← vote.slot_at_time]
    exact E.slot_at_mono cfg (Nat.zero_le vote.time)
  have hwalk : WalkKnown voteStore
      (compute_start_slot_at_epoch cfg target.epoch) head := by
    have hwalkVote := hwalkDomain i vote.honest vote.slot vote.time
      vote.index hslot0 vote.time_within_horizon vote.slot_at_time vote.vote
    simpa only [voteStore, head, vote.target_eq] using hwalkVote
  have hparentSlots : ParentSlotLt voteStore := by
    simpa only [voteStore] using
      E.store_parentSlotLt cfg ext hT.wellFormed
        hT.externals_coherence hT.genesis_structure
        hT.wellFormed.anchor_parent_unscheduled i vote.time
  have htargetData :
      (honest_attestation_data cfg ext voteStore vote.slot vote.index).target =
        target := by
    simpa only [voteStore, honest_attestation_data_eq] using vote.target_eq
  have hcheckpoint : get_checkpoint_block cfg voteStore head target.epoch =
      target.root := by
    have hroot := honest_attestation_data_target_root cfg ext voteStore
      vote.slot vote.index
    rw [htargetData] at hroot
    exact hroot.symm
  have hlands : (get_ancestor voteStore (ForkChoiceNode.mk head .pending)
      (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
    simpa only [get_checkpoint_block] using hcheckpoint
  have htargetSpec : target.root ∈ voteStore.block_roots ∧
      (voteStore.blocks target.root).slot ≤
        compute_start_slot_at_epoch cfg target.epoch := by
    have hspec := get_ancestor_spec hparentSlots hwalk
    rw [hlands] at hspec
    exact hspec
  have hqueryAt : E.AcceptedBlockAt cfg ext target.root
      (queryStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hvoteCausal : E.CausalStore cfg ext voteStore := by
    simpa only [voteStore] using E.store_causal cfg ext i vote.time
  have hvoteAt : E.AcceptedBlockAt cfg ext target.root
      (voteStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hvoteCausal htargetSpec.1
  have htargetBlocks : voteStore.blocks target.root =
      queryStore.blocks target.root :=
    hvoteAt.unique cfg ext E hT.wellFormed hqueryAt
  have hvoteTargetEpoch : get_block_epoch cfg voteStore target.root =
      target.epoch := by
    simp only [get_block_epoch]
    rw [htargetBlocks]
    exact htargetEpoch
  have htargetStartLe : compute_start_slot_at_epoch cfg target.epoch ≤
      (voteStore.blocks target.root).slot := by
    have hstart := start_slot_at_block_epoch_le cfg voteStore target.root
    rwa [hvoteTargetEpoch] at hstart
  have htargetSlot : (voteStore.blocks target.root).slot =
      compute_start_slot_at_epoch cfg target.epoch :=
    le_antisymm htargetSpec.2 htargetStartLe
  have hheadKnown : head ∈ voteStore.block_roots := hwalk.root_mem
  have hheadLeVote : (voteStore.blocks head).slot ≤ vote.slot := by
    calc
      (voteStore.blocks head).slot ≤ get_current_slot cfg voteStore := by
        simpa only [voteStore, head] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds
            hgenTrajectory i vote.time
            (get_head cfg (E.store cfg ext i vote.time)).root
            (by simpa only [voteStore, head] using hheadKnown)
      _ = E.slot_at cfg vote.time := by
        simpa only [voteStore] using E.store_current_slot cfg ext i vote.time
      _ = vote.slot := vote.slot_at_time
  have hheadBefore : (voteStore.blocks head).slot <
      compute_start_slot_at_epoch cfg (target.epoch + 1) :=
    hheadLeVote.trans_lt
      (slot_lt_next_epoch_start_of_epoch cfg vote.slot_epoch)
  have hanchorEpoch : B.anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgen]
    rfl
  have hcurrentNonGenesis : ∀ r ∈ voteStore.block_roots,
      compute_epoch_at_slot cfg (voteStore.blocks r).slot = target.epoch →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hcurrent hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorBlock : voteStore.blocks ablk.root = ablk.message := by
      simpa only [voteStore] using
        E.store_anchor_block cfg ext hT.wellFormed hgen i vote.time hr
    have hrootEpoch : compute_epoch_at_slot cfg
        (voteStore.blocks ablk.root).slot = B.anchor.epoch := by
      rw [hanchorBlock, ← hgenSlot]
      simpa only [get_current_epoch] using hanchorEpoch.symm
    exact (Nat.ne_of_lt hanchorBefore) (hrootEpoch.symm.trans hcurrent)
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots voteStore target.root head :=
    knownSameEpochAncestrySegment_of_boundary_walk_root cfg hparentSlots hwalk
      hlands htargetSlot hheadBefore hcurrentNonGenesis
  simpa only [voteStore, head] using hknownSegment

theorem trusted_concreteHonestTargetVote_acceptedCurrentEpochSegment
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.CausalStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetEpoch : get_block_epoch cfg queryStore target.root = target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state target.root
      (get_head cfg (E.store cfg ext i vote.time)).root := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hvoteCausal : E.CausalStore cfg ext
      (E.store cfg ext i vote.time) :=
    E.store_causal cfg ext i vote.time
  have hknown := E.trusted_concreteHonestTargetVote_knownCurrentEpochSegment cfg ext B
    hT hwalkDomain hanchor hqueryCausal htargetKnown htargetEpoch
    hanchorBefore vote
  exact E.trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment_of_core
    cfg ext hT.wellFormed hT.externals_coherence.state_transition_slot hgenCore
    hvoteCausal hknown

/-- One concrete current-epoch target vote carries both ingredients required
by `TrustedAcceptedConcreteA32QuorumSourceGeometry`: its source is read from the
accepted/global state at the exact causal vote store, and its head is joined
to the target root by accepted same-epoch transitions.

This remains an internal geometry edge.  It consumes only the scheduled-prefix
trajectory, not the broader selected-margin bundle. -/
theorem trusted_concreteHonestTargetVote_acceptedCurrentEpochSourceGeometry
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.CausalStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetEpoch : get_block_epoch cfg queryStore target.root = target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    TrustedAcceptedHonestSourceEvidence B.state
        (E.store cfg ext i vote.time) vote.slot vote.index ∧
      TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state target.root
        (get_head cfg (E.store cfg ext i vote.time)).root := by
  let voteStore := E.store cfg ext i vote.time
  let head := (get_head cfg voteStore).root
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenTrajectory :
      ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk ∧
          ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hvoteCausal : E.CausalStore cfg ext voteStore := by
    simpa only [voteStore] using E.store_causal cfg ext i vote.time
  have hknown : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots voteStore target.root head := by
    simpa only [voteStore, head] using
      E.trusted_concreteHonestTargetVote_knownCurrentEpochSegment cfg ext B hT
        hwalkDomain hanchor hqueryCausal htargetKnown htargetEpoch
        hanchorBefore vote
  have haccepted : TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state
      target.root head := by
    simpa only [voteStore, head] using
      E.trusted_concreteHonestTargetVote_acceptedCurrentEpochSegment cfg ext B hT
        hwalkDomain hanchor hqueryCausal htargetKnown htargetEpoch
        hanchorBefore vote
  have hheadKnown : head ∈ voteStore.block_roots := hknown.last_known
  have htargetVoteKnown : target.root ∈ voteStore.block_roots :=
    hknown.first_known cfg
  have hqueryAt : E.AcceptedBlockAt cfg ext target.root
      (queryStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hvoteAt : E.AcceptedBlockAt cfg ext target.root
      (voteStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hvoteCausal htargetVoteKnown
  have htargetBlocks : voteStore.blocks target.root =
      queryStore.blocks target.root :=
    hvoteAt.unique cfg ext E hT.wellFormed hqueryAt
  have hvoteTargetEpoch : get_block_epoch cfg voteStore target.root =
      target.epoch := by
    simp only [get_block_epoch]
    rw [htargetBlocks]
    exact htargetEpoch
  have hvoteCore : WellFormedStoreCore voteStore := by
    simpa only [voteStore] using
      E.store_wellFormedStoreCore cfg ext
        hT.externals_coherence.state_transition_slot hgenCore i vote.time
  have hsame : compute_epoch_at_slot cfg
      (voteStore.block_states head).slot =
        compute_epoch_at_slot cfg vote.slot := by
    rw [hvoteCore.2 head hheadKnown]
    exact (hknown.last_epoch_eq_first cfg).trans
      (hvoteTargetEpoch.trans vote.slot_epoch.symm)
  have hsource : TrustedAcceptedHonestSourceEvidence B.state voteStore
      vote.slot vote.index :=
    B.causalStoreHonestSourceEvidence hphase hgenTrajectory hanchor
      hvoteCausal hheadKnown hsame
  exact ⟨by simpa only [voteStore] using hsource,
    by simpa only [head] using haccepted⟩

/-- The exact signer set computed by a successful current-target gate at a
scheduled prefix realizes an accepted concrete A3.2 quorum.  `Q` is an output:
its signers are definitionally the observed/future union from the executable
helper, its votes come from exact prefix provenance and the normative
whole-slot support property, and every source/segment pair is reconstructed
at the vote's causal store.

No arbitrary signer set, supplied quorum, source agreement, ancestry segment,
transition history, target certificate, or safety conclusion is assumed. -/
theorem trusted_scheduledEventPrefix_acceptedConcreteCurrentTargetQuorum_of_operationalEvidence
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (p : E.ScheduledEventPrefix)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1))
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext (p.store cfg ext))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)))
    (hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1))
    (htargetKnown : (get_current_target cfg
      (p.store cfg ext)).root ∈ (p.store cfg ext).block_roots)
    (htargetEpoch : get_block_epoch cfg (p.store cfg ext)
      (get_current_target cfg (p.store cfg ext)).root =
        (get_current_target cfg (p.store cfg ext)).epoch)
    (hanchorBefore : B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch) :
    ∃ Q : ConcreteA32QuorumBefore cfg ext E
        (compute_start_slot_at_epoch cfg
          ((get_current_target cfg (p.store cfg ext)).epoch + 1))
        (get_current_target cfg (p.store cfg ext)),
      TrustedAcceptedConcreteA32QuorumSourceGeometry cfg ext B Q
        (get_current_target cfg (p.store cfg ext)).root := by
  classical
  let store := p.store cfg ext
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  let hV := CurrentTargetPrefixVoteAssumptions.of_trustedGlobalTrajectory
    cfg ext E B hT hanchor hboundary
  let hwalkDomain :=
    E.trusted_postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hboundary0 : TrustedAnchorBoundaryAligned
      (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint) := by
    simpa only [← hanchor] using hboundary
  change E.CurrentTargetPrefixAccountingEvidence cfg ext store
    (p.previousSecond + 1) at hevidence
  change state = get_pulled_up_head_state cfg ext store at hstate
  change E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store) at hendH
  change will_current_target_be_justified cfg ext store = true at hgate
  change HonestVotesSupportTarget cfg E target
    (p.previousSecond + 1) at hsupport
  change target.root ∈ store.block_roots at htargetKnown
  change get_block_epoch cfg store target.root = target.epoch at htargetEpoch
  change B.anchor.epoch < target.epoch at hanchorBefore
  have hvotes : ∀ i ∈ signers,
      Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i deadline target) := by
    intro i hiSigner
    simp only [signers, Execution.currentTargetA32Signers,
      Finset.mem_union] at hiSigner
    rcases hiSigner with hiObserved | hiFuture
    · simpa only [store, target, deadline] using
        E.trusted_currentTargetObservedHonestSupporter_vote_of_prefix_of_provenance
          cfg ext B hV hboundary0 p
            hevidence.operational.latest_message_provenance hqH hiObserved
    · simpa only [store, target, deadline] using
        E.trusted_currentTargetFutureHonestSeat_vote_of_currentSlot cfg ext
          hT.honest_behavior hevidence.operational.current_slot hendH
          hsupport hiFuture
  have hsupermajority :
      2 * E.total_active cfg ≤ 3 * E.weight signers := by
    simpa only [signers, store] using
      E.will_current_target_be_justified_honest_quorum_of_prefix cfg ext
        hT.externals_coherence hsv hbb
        hevidence hqH hstate hval htab hendH hanchorH hfloor hgate
  have htargetSpan :
      E.SlotWithinHorizon cfg (target.epoch * cfg.slots_per_epoch) ∧
        E.SlotWithinHorizon cfg
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
    have hstartLe : target.epoch * cfg.slots_per_epoch ≤
        target.epoch * cfg.slots_per_epoch +
          (cfg.slots_per_epoch - 1) := Nat.le_add_right _ _
    have hstartH := E.slotWithinHorizon_mono cfg hstartLe
      (by simpa only [target, store, currentTargetEpochEnd,
        currentTargetEpochStart, compute_start_slot_at_epoch,
        get_current_target, get_checkpoint_for_block] using hendH)
    refine ⟨hstartH, ?_⟩
    simpa only [target, store, currentTargetEpochEnd,
      currentTargetEpochStart, compute_start_slot_at_epoch,
      get_current_target, get_checkpoint_for_block] using hendH
  have htargetEpochWithin : target.epoch < E.verification_horizon := by
    have h := htargetSpan.1.2
    calc
      target.epoch = target.epoch * cfg.slots_per_epoch /
          cfg.slots_per_epoch :=
        (Nat.mul_div_left target.epoch cfg.slots_per_epoch_pos).symm
      _ < E.verification_horizon := by
        simpa only [compute_epoch_at_slot] using h
  have hqueryCausal : E.CausalStore cfg ext store := by
    simpa only [store] using (Execution.CausalStore.scheduledPrefix p)
  have htargetAt : E.AcceptedBlockAt cfg ext target.root
      (store.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have htargetBlockEpoch : compute_epoch_at_slot cfg
      (store.blocks target.root).slot = target.epoch := by
    simpa only [get_block_epoch] using htargetEpoch
  have hsourceBefore : (B.state.GJ target.root).epoch < target.epoch := by
    rcases B.state.gj_anchor_or_before htargetAt with hsourceAnchor | hbefore
    · rw [hsourceAnchor]
      exact hanchorBefore
    · exact hbefore.trans_eq htargetBlockEpoch
  have hgeometryVote : ∀ i ∈ signers,
      ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
        TrustedAcceptedHonestSourceEvidence B.state
            (E.store cfg ext i vote.time) vote.slot vote.index ∧
          TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state target.root
            (get_head cfg (E.store cfg ext i vote.time)).root := by
    intro i hi vote
    exact E.trusted_concreteHonestTargetVote_acceptedCurrentEpochSourceGeometry
      cfg ext B hT hwalkDomain hphase hanchor hqueryCausal htargetKnown
      htargetEpoch hanchorBefore vote
  have hsourceAgreement : CurrentTargetSourceAgreement cfg ext E signers
      deadline (B.state.GJ target.root) target := by
    intro i hi vote
    obtain ⟨hsourceEvidence, hsegment⟩ := hgeometryVote i hi vote
    simpa only [honest_attestation_data_eq] using
      hsourceEvidence.source_eq.trans
        (hsegment.gj_eq_first hphase
          B.coherence.toTrustedFFGSelectorsMatchBeaconStates)
  let Q : ConcreteA32QuorumBefore cfg ext E deadline target :=
    { source := B.state.GJ target.root
      signers := signers
      votes := hvotes
      source_agreement := hsourceAgreement
      supermajority := hsupermajority
      source_before_target := hsourceBefore
      target_epoch_within := htargetEpochWithin }
  refine ⟨Q, ?_⟩
  intro i hi vote
  exact hgeometryVote i hi vote

/-- Accepted per-vote geometry for a concrete quorum whose target checkpoint
block is older than the checkpoint epoch.  Each vote retains a named accepted
`GU(target.root)` carrier and exact source readback. -/
def TrustedAcceptedConcreteA32QuorumOldSourceGeometry
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (common : Root) : Prop :=
  ∀ i ∈ Q.signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      E.TrustedAcceptedHonestOldTargetSourceEvidence cfg ext B
        (E.store cfg ext i vote.time) vote.slot vote.index common

theorem trusted_scheduledEventPrefix_acceptedConcreteCurrentTargetQuorum
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (p : E.ScheduledEventPrefix)
    (hp : p.node ∈ E.honest)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1))
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext (p.store cfg ext))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)))
    (hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1))
    (htargetKnown : (get_current_target cfg
      (p.store cfg ext)).root ∈ (p.store cfg ext).block_roots)
    (htargetEpoch : get_block_epoch cfg (p.store cfg ext)
      (get_current_target cfg (p.store cfg ext)).root =
        (get_current_target cfg (p.store cfg ext)).epoch)
    (hanchorBefore : B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch) :
    ∃ Q : ConcreteA32QuorumBefore cfg ext E
        (compute_start_slot_at_epoch cfg
          ((get_current_target cfg (p.store cfg ext)).epoch + 1))
        (get_current_target cfg (p.store cfg ext)),
      TrustedAcceptedConcreteA32QuorumSourceGeometry cfg ext B Q
        (get_current_target cfg (p.store cfg ext)).root := by
  exact E.trusted_scheduledEventPrefix_acceptedConcreteCurrentTargetQuorum_of_operationalEvidence cfg ext
    B hT hsv hbb hphase hanchor hboundary p hqH hevidence hstate hval htab hendH hanchorH hfloor hgate hsupport htargetKnown htargetEpoch hanchorBefore

/-- Old-checkpoint counterpart of the current-boundary quorum constructor.
The executable signer union and weight arithmetic are unchanged; every
concrete vote is instead tied to the accepted target block's eager `GU`.
The quorum and its source are outputs. -/
theorem trusted_scheduledEventPrefix_acceptedConcreteOldTargetQuorum_of_operationalEvidence
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (p : E.ScheduledEventPrefix)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1))
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext (p.store cfg ext))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)))
    (hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1))
    (htargetKnown : (get_current_target cfg
      (p.store cfg ext)).root ∈ (p.store cfg ext).block_roots)
    (htargetOld : get_block_epoch cfg (p.store cfg ext)
      (get_current_target cfg (p.store cfg ext)).root <
        (get_current_target cfg (p.store cfg ext)).epoch)
    (hanchorBefore : B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch) :
    ∃ Q : ConcreteA32QuorumBefore cfg ext E
        (compute_start_slot_at_epoch cfg
          ((get_current_target cfg (p.store cfg ext)).epoch + 1))
        (get_current_target cfg (p.store cfg ext)),
      E.TrustedAcceptedConcreteA32QuorumOldSourceGeometry cfg ext B Q
        (get_current_target cfg (p.store cfg ext)).root := by
  classical
  let store := p.store cfg ext
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  let hV := CurrentTargetPrefixVoteAssumptions.of_trustedGlobalTrajectory
    cfg ext E B hT hanchor hboundary
  let hwalkDomain :=
    E.trusted_postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hboundary0 : TrustedAnchorBoundaryAligned
      (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint) := by
    simpa only [← hanchor] using hboundary
  change E.CurrentTargetPrefixAccountingEvidence cfg ext store
    (p.previousSecond + 1) at hevidence
  change state = get_pulled_up_head_state cfg ext store at hstate
  change E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store) at hendH
  change will_current_target_be_justified cfg ext store = true at hgate
  change HonestVotesSupportTarget cfg E target
    (p.previousSecond + 1) at hsupport
  change target.root ∈ store.block_roots at htargetKnown
  change get_block_epoch cfg store target.root < target.epoch at htargetOld
  change B.anchor.epoch < target.epoch at hanchorBefore
  have hvotes : ∀ i ∈ signers,
      Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i deadline target) := by
    intro i hiSigner
    simp only [signers, Execution.currentTargetA32Signers,
      Finset.mem_union] at hiSigner
    rcases hiSigner with hiObserved | hiFuture
    · simpa only [store, target, deadline] using
        E.trusted_currentTargetObservedHonestSupporter_vote_of_prefix_of_provenance
          cfg ext B hV hboundary0 p
            hevidence.operational.latest_message_provenance hqH hiObserved
    · simpa only [store, target, deadline] using
        E.trusted_currentTargetFutureHonestSeat_vote_of_currentSlot cfg ext
          hT.honest_behavior hevidence.operational.current_slot hendH
          hsupport hiFuture
  have hsupermajority :
      2 * E.total_active cfg ≤ 3 * E.weight signers := by
    simpa only [signers, store] using
      E.will_current_target_be_justified_honest_quorum_of_prefix cfg ext
        hT.externals_coherence hsv hbb
        hevidence hqH hstate hval htab hendH hanchorH hfloor hgate
  have htargetSpan :
      E.SlotWithinHorizon cfg (target.epoch * cfg.slots_per_epoch) ∧
        E.SlotWithinHorizon cfg
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
    have hstartLe : target.epoch * cfg.slots_per_epoch ≤
        target.epoch * cfg.slots_per_epoch +
          (cfg.slots_per_epoch - 1) := Nat.le_add_right _ _
    have hstartH := E.slotWithinHorizon_mono cfg hstartLe
      (by simpa only [target, store, currentTargetEpochEnd,
        currentTargetEpochStart, compute_start_slot_at_epoch,
        get_current_target, get_checkpoint_for_block] using hendH)
    refine ⟨hstartH, ?_⟩
    simpa only [target, store, currentTargetEpochEnd,
      currentTargetEpochStart, compute_start_slot_at_epoch,
      get_current_target, get_checkpoint_for_block] using hendH
  have htargetEpochWithin : target.epoch < E.verification_horizon := by
    have h := htargetSpan.1.2
    calc
      target.epoch = target.epoch * cfg.slots_per_epoch /
          cfg.slots_per_epoch :=
        (Nat.mul_div_left target.epoch cfg.slots_per_epoch_pos).symm
      _ < E.verification_horizon := by
        simpa only [compute_epoch_at_slot] using h
  have hqueryCausal : E.CausalStore cfg ext store := by
    simpa only [store] using (Execution.CausalStore.scheduledPrefix p)
  have htargetAt : E.AcceptedBlockAt cfg ext target.root
      (store.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hsourceBefore : (B.state.GU target.root).epoch < target.epoch :=
    (B.state.au_epoch_le_block htargetAt
      (B.state.gu_mem target.root htargetAt.acceptedRoot)).trans_lt
        (by simpa only [get_block_epoch] using htargetOld)
  have hgeometryVote : ∀ i ∈ signers,
      ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
        E.TrustedAcceptedHonestOldTargetSourceEvidence cfg ext B
          (E.store cfg ext i vote.time) vote.slot vote.index target.root := by
    intro i hi vote
    exact E.trusted_concreteHonestTargetVote_acceptedOldTargetSourceEvidence
      cfg ext B hT hwalkDomain hphase hboundaryPhase hanchor hqueryCausal
      htargetKnown htargetOld hanchorBefore vote
  have hsourceAgreement : CurrentTargetSourceAgreement cfg ext E signers
      deadline (B.state.GU target.root) target := by
    intro i hi vote
    simpa only [honest_attestation_data_eq] using
      (hgeometryVote i hi vote).source_eq
  let Q : ConcreteA32QuorumBefore cfg ext E deadline target :=
    { source := B.state.GU target.root
      signers := signers
      votes := hvotes
      source_agreement := hsourceAgreement
      supermajority := hsupermajority
      source_before_target := hsourceBefore
      target_epoch_within := htargetEpochWithin }
  refine ⟨Q, ?_⟩
  intro i hi vote
  exact hgeometryVote i hi vote

theorem trusted_scheduledEventPrefix_acceptedConcreteOldTargetQuorum
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (p : E.ScheduledEventPrefix)
    (hp : p.node ∈ E.honest)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    (hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1))
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext (p.store cfg ext))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)))
    (hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1))
    (htargetKnown : (get_current_target cfg
      (p.store cfg ext)).root ∈ (p.store cfg ext).block_roots)
    (htargetOld : get_block_epoch cfg (p.store cfg ext)
      (get_current_target cfg (p.store cfg ext)).root <
        (get_current_target cfg (p.store cfg ext)).epoch)
    (hanchorBefore : B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch) :
    ∃ Q : ConcreteA32QuorumBefore cfg ext E
        (compute_start_slot_at_epoch cfg
          ((get_current_target cfg (p.store cfg ext)).epoch + 1))
        (get_current_target cfg (p.store cfg ext)),
      E.TrustedAcceptedConcreteA32QuorumOldSourceGeometry cfg ext B Q
        (get_current_target cfg (p.store cfg ext)).root := by
  exact E.trusted_scheduledEventPrefix_acceptedConcreteOldTargetQuorum_of_operationalEvidence cfg ext
    B hT hsv hbb hphase hboundaryPhase hanchor hboundary p hqH hevidence hstate hval htab hendH hanchorH hfloor hgate hsupport htargetKnown htargetOld hanchorBefore

end Execution
end FastConfirmation.Spec
end
