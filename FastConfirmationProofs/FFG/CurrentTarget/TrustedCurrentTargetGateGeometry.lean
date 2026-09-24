module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetGateGeometry
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.Checkpoints.TrustedSameEpochSegmentRealization

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
end Execution
end FastConfirmation.Spec
end
