module
public import FastConfirmationProofs.Checkpoints.SameEpochSegmentRealization
public import FastConfirmationProofs.Execution.Calls.CurrentTargetPrefixVoteRealization
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness
public import FastConfirmationProofs.Execution.Calls.ScheduledPrefixGeometry
public import FastConfirmationProofs.Execution.Calls.CurrentTargetPrefixAccounting
public import FastConfirmationProofs.FFG.Certificates.CurrentTargetCertificateRealization
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted current-target gate bridge

This file closes the dependency-independent current-epoch geometry between a
concrete honest target vote and the accepted source-coherence carrier.  In
particular, a `KnownSameEpochAncestrySegment` is not a premise of the public
vote bridge: it is reconstructed from the vote's checkpoint equation and its
ordinary known parent walk, then lifted through exact last-writer provenance.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

omit [LinearOrder Root] [Inhabited Root] in
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

/-- A known walk whose exact boundary landing is `first` reconstructs the
same-epoch ancestry segment from `first` to `last`.  Every nontrivial child is
proved current-epoch before the supplied non-genesis classifier is used.
-/
theorem knownSameEpochAncestrySegment_of_boundary_walk_root
    {E : Execution Root} {store : Store Root}
    (hparentSlots : ParentSlotLt store)
    {e : Epoch} {first last : Root}
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) last)
    (hlands : (get_ancestor store (ForkChoiceNode.mk last .pending)
      (compute_start_slot_at_epoch cfg e)).root = first)
    (hfirstSlot : (store.blocks first).slot =
      compute_start_slot_at_epoch cfg e)
    (hlastBefore : (store.blocks last).slot <
      compute_start_slot_at_epoch cfg (e + 1))
    (hcurrentNonGenesis : ∀ r ∈ store.block_roots,
      compute_epoch_at_slot cfg (store.blocks r).slot = e →
        r ∉ E.genesis_store.block_roots) :
    KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      store first last := by
  induction hwalk with
  | @stop r hr hle =>
      have hrEq : r = first := by
        rw [get_ancestor_stop hle] at hlands
        exact hlands
      subst r
      exact .refl first hr
  | @step r hr hgt hp ih =>
      have hlandsParent :
          (get_ancestor store
              (ForkChoiceNode.mk (store.blocks r).parent_root .pending)
              (compute_start_slot_at_epoch cfg e)).root = first := by
        rw [get_ancestor_step hparentSlots hr hgt hp] at hlands
        exact hlands
      have hparentLt :
          (store.blocks (store.blocks r).parent_root).slot <
            (store.blocks r).slot :=
        hparentSlots r hr hp.root_mem
      have hparentStart : compute_start_slot_at_epoch cfg e ≤
          (store.blocks (store.blocks r).parent_root).slot := by
        by_contra hnot
        have hbelow :
            (store.blocks (store.blocks r).parent_root).slot ≤
              compute_start_slot_at_epoch cfg e :=
          Nat.le_of_lt (Nat.lt_of_not_ge hnot)
        rw [get_ancestor_stop hbelow] at hlandsParent
        have hpEq : (store.blocks r).parent_root = first :=
          hlandsParent
        rw [hpEq, hfirstSlot] at hnot
        exact hnot (le_refl _)
      have hparentBefore :
          (store.blocks (store.blocks r).parent_root).slot <
            compute_start_slot_at_epoch cfg (e + 1) :=
        hparentLt.trans hlastBefore
      have hprefix := ih hlandsParent hparentBefore
      have hparentEpoch : compute_epoch_at_slot cfg
          (store.blocks (store.blocks r).parent_root).slot = e :=
        epoch_eq_of_start_le_lt_next cfg hparentStart hparentBefore
      have hchildStart : compute_start_slot_at_epoch cfg e ≤
          (store.blocks r).slot := hgt.le
      have hchildEpoch :
          compute_epoch_at_slot cfg (store.blocks r).slot = e :=
        epoch_eq_of_start_le_lt_next cfg hchildStart hlastBefore
      exact .tail hprefix hr (hcurrentNonGenesis r hr hchildEpoch) rfl
        (hparentEpoch.trans hchildEpoch.symm)


namespace KnownSameEpochAncestrySegment

omit [LinearOrder Root] [Inhabited Root] in
theorem first_known
    {E : Execution Root} {store : Store Root} {first last : Root}
    (h : KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      store first last) :
    first ∈ store.block_roots := by
  induction h with
  | refl known => exact known
  | @tail parent child hprefix hchild hnongenesis hparent hsame ih =>
      exact ih

omit [LinearOrder Root] [Inhabited Root] in
theorem last_epoch_eq_first
    {E : Execution Root} {store : Store Root} {first last : Root}
    (h : KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      store first last) :
    compute_epoch_at_slot cfg (store.blocks last).slot =
      compute_epoch_at_slot cfg (store.blocks first).slot := by
  induction h with
  | refl => rfl
  | @tail parent child hprefix hchild hnongenesis hparent hsame ih =>
      exact hsame.symm.trans ih

end KnownSameEpochAncestrySegment

namespace Execution

variable (E : Execution Root)

/-! ## Accepted cross-boundary source transport -/

/-- A concrete known parent/child edge which crosses an epoch boundary is
realized by the child's actual last successful writer.  The Phase0 boundary
laws are applied at that writer's exact insertion prefix, after accepted block
uniqueness and prefix-core preservation transport the later-store epoch
inequality back to the transition inputs.  The child's `GJ` is the boundary
source of the parent state at the child epoch.  It is the parent's `GU` only
for one boundary; after two or more boundaries it can be newer.

This is the accepted replacement for the legacy history-replay lemma: no
`BlockStateTransitionHistory` appears. -/
theorem acceptedCrossEpochParentGJEqBoundarySource_of_known_parent
    (B : ScheduledFFGInterpretation cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    {parent child : Root}
    (hparentKnown : parent ∈ store.block_roots)
    (hchildKnown : child ∈ store.block_roots)
    (hchildNonGenesis : child ∉ E.genesis_store.block_roots)
    (hparent : (store.blocks child).parent_root = parent)
    (hcross : compute_epoch_at_slot cfg (store.blocks parent).slot <
      compute_epoch_at_slot cfg (store.blocks child).slot) :
    B.state.realized_justified child =
      phase0BoundarySource cfg ext (store.block_states parent)
        (compute_epoch_at_slot cfg (store.blocks child).slot) := by
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
  have hprefixParentAt : E.BlockKnownInScheduledPrefix cfg ext parent
      ((t.atPrefix.store cfg ext).blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext
      (.scheduledPrefix t.atPrefix) hprefixParentKnown
  have hstoreParentAt : E.BlockKnownInScheduledPrefix cfg ext parent
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
    Execution.SuccessfulScheduledBlockImport.on_block_inserted_state_fresh
      cfg ext writer.fresh t.accepted
  have hstateAgree : (t.atPrefix.store cfg ext).block_states parent =
      store.block_states parent :=
    E.causal_block_states_agree cfg ext hwf hec (.scheduledPrefix t.atPrefix)
      hstore hprefixParentKnown hparentKnown
  calc
    B.state.realized_justified child = B.state.realized_justified t.signedBlock.root :=
      congrArg B.state.realized_justified htRoot.symm
    _ = (t.postStore.block_states
          t.signedBlock.root).current_justified_checkpoint :=
      (B.coherence.transition_gj t).symm
    _ = post.current_justified_checkpoint :=
      congrArg BeaconState.current_justified_checkpoint hpost
    _ = phase0BoundarySource cfg ext
          ((t.atPrefix.store cfg ext).block_states
            t.signedBlock.message.parent_root)
          (compute_epoch_at_slot cfg t.signedBlock.message.slot) :=
      hboundaryPhase.state_transition_eq_boundarySource htransition
        hinsertionCross
    _ = phase0BoundarySource cfg ext (store.block_states parent)
          (compute_epoch_at_slot cfg (store.blocks child).slot) := by
      rw [htParent, hstateAgree, htMessage]

/-- Accepted, last-writer version of the target-boundary walk source lemma.
Same-epoch suffix edges preserve `GJ`; if the boundary landing is older, the
first edge above it is realized by an actual accepted cross-epoch transition
and changes the source to the boundary source of the landing block. -/
theorem acceptedGJEqHonestSourceAt_of_target_walk_root
    (B : ScheduledFFGInterpretation cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    (hparentSlots : ParentSlotLt store)
    {e : Epoch} {targetRoot head : Root}
    (hcurrentNonGenesis : ∀ r ∈ store.block_roots,
      get_block_epoch cfg store r = e →
        r ∉ E.genesis_store.block_roots)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) head)
    (hlands : (get_ancestor store (ForkChoiceNode.mk head .pending)
      (compute_start_slot_at_epoch cfg e)).root = targetRoot)
    (hheadEpoch : get_block_epoch cfg store head = e) :
    B.state.realized_justified head =
      phase0HonestSourceAt cfg ext store targetRoot e := by
  induction hwalk generalizing targetRoot with
  | @stop r hr hle =>
      rw [get_ancestor_stop hle] at hlands
      have hre : r = targetRoot := hlands
      subst targetRoot
      simp only [phase0HonestSourceAt, hheadEpoch, if_pos]
      exact ((Execution.ScheduledFFGInterpretation.causalStoreProjection B
        hstore).block_state_gj r hr).symm
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
        have hedge := E.acceptedProjectedSameEpochTransition_of_known_parent
          (S := B.state) hwf hcore hstore hparentKnown hr
            (hcurrentNonGenesis r hr hheadEpoch) rfl hsame
        exact (hedge.gj_eq_parent hphase
          B.coherence.toFFGStateReadAgreement).trans
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
        have hedge := E.acceptedCrossEpochParentGJEqBoundarySource_of_known_parent
          cfg ext B hwf hec hcore hboundaryPhase hstore hparentKnown hr
            (hcurrentNonGenesis r hr hheadEpoch) rfl hcross
        have htargetOld : get_block_epoch cfg store targetRoot ≠ e := by
          rw [← hparentEq]
          exact Nat.ne_of_lt hparentOld
        have hrEpoch : compute_epoch_at_slot cfg (store.blocks r).slot = e :=
          hheadEpoch
        rw [hparentEq, hrEpoch] at hedge
        simp only [phase0HonestSourceAt, if_neg htargetOld]
        exact hedge


namespace AcceptedCurrentTargetA32GateRealization

/-- Retie an accepted target-local gate realization to a concrete
current-epoch carrier whose exact boundary walk lands on that target.

Unlike the same-epoch-segment specialization, this theorem also handles a
skipped-boundary target: when the target block itself is old, the gate source
is the boundary source of the target block, while
`acceptedGJEqHonestSourceAt_of_target_walk_root` identifies that same
checkpoint with `GJ(carrier)` across the actual accepted boundary edge.
The concrete quorum, votes, deadline, weight bound, and certificate are left
unchanged.

No source-visibility, filter, safety, or historical-induction premise is
used. -/
def fixedSource_of_acceptedTargetWalk_root
    (B : ScheduledFFGInterpretation cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
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
    (hgate : AcceptedCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store) :
    AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store carrier := by
  refine ⟨hgate.certified, ?_⟩
  rcases hgate.support_branch with hanchor | ⟨hne, Q, hsource⟩
  · exact Or.inl hanchor
  · refine Or.inr ⟨hne, Q, ?_⟩
    have hgj : B.state.realized_justified carrier = phase0HonestSourceAt cfg ext store
        (get_current_target cfg store).root
        (get_current_target cfg store).epoch :=
      E.acceptedGJEqHonestSourceAt_of_target_walk_root cfg ext B hwf hec hcore
        hphase hboundaryPhase hstore hparentSlots hcurrentNonGenesis hwalk
        hlands hcarrierEpoch
    calc
      Q.source = phase0HonestSourceAt cfg ext store
          (get_current_target cfg store).root
          (get_current_target cfg store).epoch := hsource
      _ = B.state.realized_justified carrier := hgj.symm
      _ = B.state.voting_source_at cfg ext store carrier
          (get_current_target cfg store).epoch := by
        simp only [AcceptedBlockFFGState.voting_source_at, hcarrierEpoch, if_pos]


end AcceptedCurrentTargetA32GateRealization

/-- Read an honest attestation's source as the Phase0 honest source at the
actual target-boundary landing.  If the head is in the voting epoch, source
readback uses `GJ` plus the accepted walk theorem above.  If the head itself
is older, `process_slots` crosses the empty boundaries and reads the boundary
source of the head state directly. -/
theorem acceptedHonestAttestationDataSourceEqHonestSourceAtTarget
    (B : ScheduledFFGInterpretation cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
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
      phase0HonestSourceAt cfg ext store target.root target.epoch := by
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
  have hprojection : AcceptedFFGStoreProjection B.state store :=
    Execution.ScheduledFFGInterpretation.causalStoreProjection B hstore
  by_cases hheadCurrent : get_block_epoch cfg store head = target.epoch
  · have hsame : compute_epoch_at_slot cfg
        (store.block_states head).slot = compute_epoch_at_slot cfg slot := by
      rw [(hcore hstore).2 head hheadKnown]
      exact hheadCurrent.trans hslotEpoch.symm
    have hsourceGJ :
        (honest_attestation_data cfg ext store slot index).source =
          B.state.realized_justified head := by
      rw [honest_attestation_data_source_eq_head_state hphase
        store slot index hsame]
      exact hprojection.block_state_gj head hheadKnown
    rw [hsourceGJ]
    exact E.acceptedGJEqHonestSourceAt_of_target_walk_root cfg ext B hwf hec
      hcore hphase hboundaryPhase hstore hparentSlots hcurrentNonGenesis hwalk
      hlands hheadCurrent
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
    have htargetOld :
        get_block_epoch cfg store target.root ≠ target.epoch := by
      rw [← hheadEq]
      exact Nat.ne_of_lt hheadOld
    rw [hboundaryPhase.process_slots_eq_boundarySource hboundaryEpoch,
      hslotEpoch]
    simp only [phase0HonestSourceAt, if_neg htargetOld, hheadEq]

/-- Accepted carrier for one honest old-target vote.  An old head obtains
its source through `process_slots`, and a current-epoch head obtains it
through the first cross-epoch block transition.  Both read the boundary source
of the target block state at the target epoch.  After two or more boundaries
this source can be newer than the target block's eager `GU`. -/
structure AcceptedHonestOldTargetSourceCarrier
    (_B : ScheduledFFGInterpretation cfg ext E)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex)
    (targetRoot : Root) (targetEpoch : Epoch) where
  target_known : targetRoot ∈ store.block_roots
  source_eq : (honest_attestation_data cfg ext store slot index).source =
    phase0BoundarySource cfg ext (store.block_states targetRoot) targetEpoch

def AcceptedHonestOldTargetSourceEvidence
    (B : ScheduledFFGInterpretation cfg ext E)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex)
    (targetRoot : Root) (targetEpoch : Epoch) : Prop :=
  Nonempty (AcceptedHonestOldTargetSourceCarrier cfg ext E B store slot index
    targetRoot targetEpoch)

namespace AcceptedHonestOldTargetSourceEvidence

theorem source_eq
    {B : ScheduledFFGInterpretation cfg ext E}
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    {targetRoot : Root} {targetEpoch : Epoch}
    (h : E.AcceptedHonestOldTargetSourceEvidence cfg ext B store slot index
      targetRoot targetEpoch) :
    (honest_attestation_data cfg ext store slot index).source =
      phase0BoundarySource cfg ext (store.block_states targetRoot) targetEpoch := by
  obtain ⟨carrier⟩ := h
  exact carrier.source_eq

theorem target_known
    {B : ScheduledFFGInterpretation cfg ext E}
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    {targetRoot : Root} {targetEpoch : Epoch}
    (h : E.AcceptedHonestOldTargetSourceEvidence cfg ext B store slot index
      targetRoot targetEpoch) :
    targetRoot ∈ store.block_roots := by
  obtain ⟨carrier⟩ := h
  exact carrier.target_known

end AcceptedHonestOldTargetSourceEvidence

/-- A concrete vote for an old checkpoint landing carries source evidence for
the boundary source of the target block.  The target block is identified
between the query prefix and the voter's causal store through
`BlockKnownInScheduledPrefix` uniqueness.  Head-current and head-old cases
are both discharged by
`acceptedHonestAttestationDataSourceEqHonestSourceAtTarget`. -/
theorem concreteHonestTargetVote_acceptedOldTargetSourceEvidence
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.ScheduledPrefixStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetOld : get_block_epoch cfg queryStore target.root < target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    E.AcceptedHonestOldTargetSourceEvidence cfg ext B
      (E.store cfg ext i vote.time) vote.slot vote.index target.root
        target.epoch := by
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
  have hvoteCausal : E.ScheduledPrefixStore cfg ext voteStore := by
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
  have hqueryAt : E.BlockKnownInScheduledPrefix cfg ext target.root
      (queryStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hvoteAt : E.BlockKnownInScheduledPrefix cfg ext target.root
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
  have hsourceHonest :=
    E.acceptedHonestAttestationDataSourceEqHonestSourceAtTarget cfg ext B
      hT.wellFormed hT.externals_coherence hcausalCore hphase hboundaryPhase
      hvoteCausal hparentSlots vote.slot_epoch hwalk htargetData
      hheadStateSlotLe hcurrentNonGenesis
  have hsource : (honest_attestation_data cfg ext voteStore
      vote.slot vote.index).source =
        phase0BoundarySource cfg ext (voteStore.block_states target.root)
          target.epoch := by
    simpa only [phase0HonestSourceAt, if_neg
      (Nat.ne_of_lt hvoteTargetOld)] using hsourceHonest
  exact ⟨{ target_known := htargetSpec.1, source_eq := hsource }⟩

/-- Prefix-store specialization of the future-seat vote constructor.  The
query store need not be a completed `Execution.store`; the exact global
action adapter only has to identify its clock slot with `querySecond`.

This is the future half of the concrete signer set.  Its target agreement is
obtained from the action-derived whole-slot `HonestVotesSupportTarget`
property, not from a target certificate or a safety conclusion. -/
theorem currentTargetFutureHonestSeat_vote_of_currentSlot
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
theorem concreteHonestTargetVote_knownCurrentEpochSegment
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.ScheduledPrefixStore cfg ext queryStore)
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
  have hqueryAt : E.BlockKnownInScheduledPrefix cfg ext target.root
      (queryStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hvoteCausal : E.ScheduledPrefixStore cfg ext voteStore := by
    simpa only [voteStore] using E.store_causal cfg ext i vote.time
  have hvoteAt : E.BlockKnownInScheduledPrefix cfg ext target.root
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

/-- Last-writer lifting specialization of
`concreteHonestTargetVote_knownCurrentEpochSegment`. -/
theorem concreteHonestTargetVote_acceptedCurrentEpochSegment
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.ScheduledPrefixStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetEpoch : get_block_epoch cfg queryStore target.root = target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    AcceptedProjectedSameEpochSegment cfg ext E B.state target.root
      (get_head cfg (E.store cfg ext i vote.time)).root := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hvoteCausal : E.ScheduledPrefixStore cfg ext
      (E.store cfg ext i vote.time) :=
    E.store_causal cfg ext i vote.time
  have hknown := E.concreteHonestTargetVote_knownCurrentEpochSegment cfg ext B
    hT hwalkDomain hanchor hqueryCausal htargetKnown htargetEpoch
    hanchorBefore vote
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment_of_core
    hT.wellFormed hT.externals_coherence.state_transition_slot hgenCore
    hvoteCausal hknown

/-- One concrete current-epoch target vote carries both ingredients required
by `AcceptedConcreteA32QuorumSourceGeometry`: its source is read from the
accepted/global state at the exact causal vote store, and its head is joined
to the target root by accepted same-epoch transitions.

This remains an internal geometry edge.  It consumes only the scheduled-prefix
trajectory, not the broader selected-margin bundle. -/
theorem concreteHonestTargetVote_acceptedCurrentEpochSourceGeometry
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {queryStore : Store Root}
    (hqueryCausal : E.ScheduledPrefixStore cfg ext queryStore)
    {target : Checkpoint Root}
    (htargetKnown : target.root ∈ queryStore.block_roots)
    (htargetEpoch : get_block_epoch cfg queryStore target.root = target.epoch)
    (hanchorBefore : B.anchor.epoch < target.epoch)
    {i : ValidatorIndex} {deadline : Slot}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    AcceptedHonestSourceEvidence B.state
        (E.store cfg ext i vote.time) vote.slot vote.index ∧
      AcceptedProjectedSameEpochSegment cfg ext E B.state target.root
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
  have hvoteCausal : E.ScheduledPrefixStore cfg ext voteStore := by
    simpa only [voteStore] using E.store_causal cfg ext i vote.time
  have hknown : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots voteStore target.root head := by
    simpa only [voteStore, head] using
      E.concreteHonestTargetVote_knownCurrentEpochSegment cfg ext B hT
        hwalkDomain hanchor hqueryCausal htargetKnown htargetEpoch
        hanchorBefore vote
  have haccepted : AcceptedProjectedSameEpochSegment cfg ext E B.state
      target.root head := by
    simpa only [voteStore, head] using
      E.concreteHonestTargetVote_acceptedCurrentEpochSegment cfg ext B hT
        hwalkDomain hanchor hqueryCausal htargetKnown htargetEpoch
        hanchorBefore vote
  have hheadKnown : head ∈ voteStore.block_roots := hknown.last_known
  have htargetVoteKnown : target.root ∈ voteStore.block_roots :=
    hknown.first_known cfg
  have hqueryAt : E.BlockKnownInScheduledPrefix cfg ext target.root
      (queryStore.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have hvoteAt : E.BlockKnownInScheduledPrefix cfg ext target.root
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
  have hsource : AcceptedHonestSourceEvidence B.state voteStore
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
theorem scheduledEventPrefix_acceptedConcreteCurrentTargetQuorum
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
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
      AcceptedConcreteA32QuorumSourceGeometry cfg ext E B Q
        (get_current_target cfg (p.store cfg ext)).root := by
  classical
  let store := p.store cfg ext
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  let hV := CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
    cfg ext E B hT hanchor hboundary
  let hwalkDomain :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hboundary0 : InitialAnchorAtEpochBoundary
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
        E.currentTargetObservedHonestSupporter_vote_of_prefix
          cfg ext B hV hboundary0 p hp hqH hiObserved
    · simpa only [store, target, deadline] using
        E.currentTargetFutureHonestSeat_vote_of_currentSlot cfg ext
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
  have hqueryCausal : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using (Execution.ScheduledPrefixStore.scheduledPrefix p)
  have htargetAt : E.BlockKnownInScheduledPrefix cfg ext target.root
      (store.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  have htargetBlockEpoch : compute_epoch_at_slot cfg
      (store.blocks target.root).slot = target.epoch := by
    simpa only [get_block_epoch] using htargetEpoch
  have hsourceBefore : (B.state.realized_justified target.root).epoch < target.epoch := by
    rcases B.state.realized_justified_anchor_or_before htargetAt with hsourceAnchor | hbefore
    · rw [hsourceAnchor]
      exact hanchorBefore
    · exact hbefore.trans_eq htargetBlockEpoch
  have hgeometryVote : ∀ i ∈ signers,
      ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
        AcceptedHonestSourceEvidence B.state
            (E.store cfg ext i vote.time) vote.slot vote.index ∧
          AcceptedProjectedSameEpochSegment cfg ext E B.state target.root
            (get_head cfg (E.store cfg ext i vote.time)).root := by
    intro i hi vote
    exact E.concreteHonestTargetVote_acceptedCurrentEpochSourceGeometry
      cfg ext B hT hwalkDomain hphase hanchor hqueryCausal htargetKnown
      htargetEpoch hanchorBefore vote
  have hsourceAgreement : CurrentTargetSourceAgreement cfg ext E signers
      deadline (B.state.realized_justified target.root) target := by
    intro i hi vote
    obtain ⟨hsourceEvidence, hsegment⟩ := hgeometryVote i hi vote
    simpa only [honest_attestation_data_eq] using
      hsourceEvidence.source_eq.trans
        (hsegment.gj_eq_first hphase
          B.coherence.toFFGStateReadAgreement)
  let Q : ConcreteA32QuorumBefore cfg ext E deadline target :=
    { source := B.state.realized_justified target.root
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
block is older than the checkpoint epoch.  Each vote retains exact source
readback to the boundary source of the target block state. -/
def AcceptedConcreteA32QuorumOldSourceGeometry
    (B : ScheduledFFGInterpretation cfg ext E)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (common : Root) : Prop :=
  ∀ i ∈ Q.signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      E.AcceptedHonestOldTargetSourceEvidence cfg ext B
        (E.store cfg ext i vote.time) vote.slot vote.index common target.epoch

/-- Old-checkpoint counterpart of the current-boundary quorum constructor.
The executable signer union and weight arithmetic are unchanged; every
concrete vote is instead tied to the boundary source of the target block
state, which the voter and the query store read identically.
The source epoch bound comes from the source certificate.  The quorum and its
source are outputs. -/
theorem scheduledEventPrefix_acceptedConcreteOldTargetQuorum
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
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
      (get_current_target cfg (p.store cfg ext)).epoch)
    (hsourceBeforeIn : (phase0BoundarySource cfg ext
      ((p.store cfg ext).block_states
        (get_current_target cfg (p.store cfg ext)).root)
      (get_current_target cfg (p.store cfg ext)).epoch).epoch <
        (get_current_target cfg (p.store cfg ext)).epoch) :
    ∃ Q : ConcreteA32QuorumBefore cfg ext E
        (compute_start_slot_at_epoch cfg
          ((get_current_target cfg (p.store cfg ext)).epoch + 1))
        (get_current_target cfg (p.store cfg ext)),
      Q.source = phase0BoundarySource cfg ext
        ((p.store cfg ext).block_states
          (get_current_target cfg (p.store cfg ext)).root)
        (get_current_target cfg (p.store cfg ext)).epoch ∧
      E.AcceptedConcreteA32QuorumOldSourceGeometry cfg ext B Q
        (get_current_target cfg (p.store cfg ext)).root := by
  classical
  let store := p.store cfg ext
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  let hV := CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
    cfg ext E B hT hanchor hboundary
  let hwalkDomain :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hboundary0 : InitialAnchorAtEpochBoundary
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
        E.currentTargetObservedHonestSupporter_vote_of_prefix
          cfg ext B hV hboundary0 p hp hqH hiObserved
    · simpa only [store, target, deadline] using
        E.currentTargetFutureHonestSeat_vote_of_currentSlot cfg ext
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
  have hqueryCausal : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using (Execution.ScheduledPrefixStore.scheduledPrefix p)
  have htargetAt : E.BlockKnownInScheduledPrefix cfg ext target.root
      (store.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal htargetKnown
  let source := phase0BoundarySource cfg ext (store.block_states target.root)
    target.epoch
  have hsourceBefore : source.epoch < target.epoch := hsourceBeforeIn
  have hgeometryVote : ∀ i ∈ signers,
      ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
        E.AcceptedHonestOldTargetSourceEvidence cfg ext B
          (E.store cfg ext i vote.time) vote.slot vote.index target.root
            target.epoch := by
    intro i hi vote
    exact E.concreteHonestTargetVote_acceptedOldTargetSourceEvidence
      cfg ext B hT hwalkDomain hphase hboundaryPhase hanchor hqueryCausal
      htargetKnown htargetOld hanchorBefore vote
  have hsourceAgreement : CurrentTargetSourceAgreement cfg ext E signers
      deadline source target := by
    intro i hi vote
    have hevidence := hgeometryVote i hi vote
    have hstates : (E.store cfg ext i vote.time).block_states target.root =
        store.block_states target.root :=
      E.causal_block_states_agree cfg ext hT.wellFormed hT.externals_coherence
        (E.store_causal cfg ext i vote.time) hqueryCausal
        hevidence.target_known htargetKnown
    have hsource := hevidence.source_eq
    rw [hstates] at hsource
    simpa only [honest_attestation_data_eq] using hsource
  let Q : ConcreteA32QuorumBefore cfg ext E deadline target :=
    { source := source
      signers := signers
      votes := hvotes
      source_agreement := hsourceAgreement
      supermajority := hsupermajority
      source_before_target := hsourceBefore
      target_epoch_within := htargetEpochWithin }
  refine ⟨Q, rfl, ?_⟩
  intro i hi vote
  exact hgeometryVote i hi vote

/-- Close the current-epoch accepted gate branch at an exact scheduled query
prefix.  The intermediate quorum and all of its accepted source geometry are
constructed by `scheduledEventPrefix_acceptedConcreteCurrentTargetQuorum` and
immediately consumed by the existing certificate constructor. -/
theorem scheduledEventPrefix_acceptedCurrentTargetA32GateRealization_core
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
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
    (hdelivery : ∀ Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (p.store cfg ext)).epoch + 1))
      (get_current_target cfg (p.store cfg ext)),
        ConcreteA32QuorumScheduledDelivery cfg ext E Q)
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
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      (p.store cfg ext) := by
  let store := p.store cfg ext
  let target := get_current_target cfg store
  change E.CurrentTargetPrefixAccountingEvidence cfg ext store
    (p.previousSecond + 1) at hevidence
  change state = get_pulled_up_head_state cfg ext store at hstate
  change E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store) at hendH
  change (∀ Q : ConcreteA32QuorumBefore cfg ext E
    (compute_start_slot_at_epoch cfg (target.epoch + 1)) target,
      ConcreteA32QuorumScheduledDelivery cfg ext E Q) at hdelivery
  change will_current_target_be_justified cfg ext store = true at hgate
  change HonestVotesSupportTarget cfg E target
    (p.previousSecond + 1) at hsupport
  change target.root ∈ store.block_roots at htargetKnown
  change get_block_epoch cfg store target.root = target.epoch at htargetEpoch
  change B.anchor.epoch < target.epoch at hanchorBefore
  obtain ⟨Q, hgeometry⟩ :=
    E.scheduledEventPrefix_acceptedConcreteCurrentTargetQuorum cfg ext B hT
      hsv hbb hphase hanchor hboundary p hp hqH hevidence hstate hval htab
      hendH hanchorH hfloor hgate hsupport htargetKnown htargetEpoch
      hanchorBefore
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
  have htargetNotAnchor : target ≠ B.anchor := by
    intro heq
    have hepoch := congrArg Checkpoint.epoch heq
    exact (Nat.ne_of_lt hanchorBefore) hepoch.symm
  have hstore : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using (Execution.ScheduledPrefixStore.scheduledPrefix p)
  exact
    E.acceptedCurrentTargetA32GateRealization_of_currentEpochConcreteQuorum_core
      cfg ext B hphase hstore htargetKnown htargetEpoch htargetNotAnchor
        hanchorBefore htargetSpan Q (hdelivery Q) hgeometry



/-- Internal accepted certificate constructor for the old-checkpoint branch.
The selected source is the boundary source of the target block state.  The
caller supplies its certificate and target-to-source descent; the concrete
quorum supplies the new link.

`Q` remains an intermediate object consumed by the prefix/action wrappers,
never an input to the final actual-call interface. -/
theorem acceptedCurrentTargetA32GateRealization_of_oldEpochConcreteQuorum_core
    (B : ScheduledFFGInterpretation cfg ext E)
    {store : Store Root}
    (htargetOld : get_block_epoch cfg store
      (get_current_target cfg store).root <
        (get_current_target cfg store).epoch)
    (htargetNotAnchor : get_current_target cfg store ≠ B.anchor)
    (htargetSpan :
      E.SlotWithinHorizon cfg
          ((get_current_target cfg store).epoch * cfg.slots_per_epoch) ∧
        E.SlotWithinHorizon cfg
          ((get_current_target cfg store).epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)))
    (Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg store).epoch + 1))
      (get_current_target cfg store))
    (hdelivery : ConcreteA32QuorumScheduledDelivery cfg ext E Q)
    (hQSource : Q.source = phase0BoundarySource cfg ext
      (store.block_states (get_current_target cfg store).root)
      (get_current_target cfg store).epoch)
    (hsourceCertified : Nonempty (CertifiedJustified cfg E B.anchor Q.source))
    (htargetDescendsSource :
      E.RootDescends (get_current_target cfg store).root Q.source.root) :
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      store := by
  classical
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  change get_block_epoch cfg store target.root < target.epoch at htargetOld
  change target ≠ B.anchor at htargetNotAnchor
  change ConcreteA32QuorumBefore cfg ext E deadline target at Q
  change ConcreteA32QuorumScheduledDelivery cfg ext E Q at hdelivery
  have hsourceBefore : Q.source.epoch < target.epoch := Q.source_before_target
  have hsignersEpoch : Q.signers ⊆
      E.span_committee (target.epoch * cfg.slots_per_epoch)
        (target.epoch * cfg.slots_per_epoch +
          (cfg.slots_per_epoch - 1)) := by
    intro j hj
    obtain ⟨vj⟩ := Q.votes j hj
    have hdivEpoch : vj.slot / cfg.slots_per_epoch = target.epoch := by
      simpa only [compute_epoch_at_slot] using vj.slot_epoch
    have hlo : target.epoch * cfg.slots_per_epoch ≤ vj.slot := by
      have h := Nat.div_mul_le_self vj.slot cfg.slots_per_epoch
      rwa [hdivEpoch] at h
    have hlt : vj.slot <
        target.epoch * cfg.slots_per_epoch + cfg.slots_per_epoch := by
      have h := Nat.lt_mul_div_succ vj.slot cfg.slots_per_epoch_pos
      rw [hdivEpoch, Nat.mul_add] at h
      simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
    have hhi : vj.slot ≤ target.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1) := by
      have hpred := Nat.le_pred_of_lt hlt
      rw [Nat.pred_eq_sub_one,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
      exact hpred
    simp only [Execution.span_committee, Finset.mem_biUnion]
    exact ⟨vj.slot, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, vj.assigned⟩
  have hlink : SupermajorityLink cfg E Q.source target := {
    signers := Q.signers
    source_before_target := hsourceBefore
    target_descends_source := htargetDescendsSource
    target_epoch_within := Q.target_epoch_within
    target_span_within := by simpa only [target] using htargetSpan
    signers_in_epoch := hsignersEpoch
    signer_attestation := by
      intro j hj
      obtain ⟨vj⟩ := Q.votes j hj
      let a := honest_attestation cfg ext
        (E.store cfg ext j vj.time) vj.slot vj.index j
      refine ⟨j, E.slot_start cfg (vj.slot + 1), a, false, ?_, ?_, ?_, ?_⟩
      · simpa only [a] using hdelivery j hj vj
      · simp only [a, honest_attestation_attesting_indices,
          List.mem_singleton]
      · simpa only [a] using Q.source_agreement j hj vj
      · simpa only [a] using vj.target_eq
    supermajority := Q.supermajority }
  obtain ⟨hsourceCertificate⟩ := hsourceCertified
  have htargetCertificate : Nonempty
      (CertifiedJustified cfg E B.anchor target) :=
    ⟨CertifiedJustified.link hsourceCertificate hlink⟩
  refine ⟨htargetCertificate, Or.inr ⟨htargetNotAnchor, Q, ?_⟩⟩
  change Q.source = phase0HonestSourceAt cfg ext store target.root target.epoch
  simpa only [phase0HonestSourceAt, if_neg (Nat.ne_of_lt htargetOld)]
    using hQSource



/-- A fork-choice checkpoint block is an execution ancestor of its query
root on a known walk domain. -/
theorem rootDescends_checkpointBlock_of_walks
    {store : Store Root} (hprovenance : BlockProvenance E store)
    (hparentSlots : ParentSlotLt store)
    {r : Root} {e : Epoch}
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) r)
    (hwalkAt : ∀ a ∈ store.block_roots,
      WalkKnown store (store.blocks a).slot r) :
    E.RootDescends r (get_checkpoint_block cfg store r e) := by
  have hspec := get_ancestor_spec hparentSlots hwalk
  have hwalkA := hwalkAt _ hspec.1
  apply E.rootDescends_of_getAncestor hprovenance hparentSlots hwalkA
  have hcomp := get_ancestor_comp_root hparentSlots hspec.2 hwalkA
  rw [get_ancestor_stop le_rfl] at hcomp
  exact hcomp.symm

/-- Certificate and descent for the old-target boundary source.  For one
boundary it is the target block's eager `GU`, with its formed carrier.  For
two or more boundaries the late-boundary guard gives a known current-epoch
block below the head; that block's `GJ` is the same checkpoint, with its
formed carrier on the block's chain. -/
theorem scheduledEventPrefix_oldTargetBoundarySource_certificate
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (p : E.ScheduledEventPrefix)
    (hguard : CurrentTargetLateBoundaryCarrierGuard cfg (p.store cfg ext))
    (htargetKnown : (get_current_target cfg
      (p.store cfg ext)).root ∈ (p.store cfg ext).block_roots)
    (htargetOld : get_block_epoch cfg (p.store cfg ext)
      (get_current_target cfg (p.store cfg ext)).root <
        (get_current_target cfg (p.store cfg ext)).epoch)
    (hanchorBefore : B.anchor.epoch <
      (get_current_target cfg (p.store cfg ext)).epoch) :
    let source := phase0BoundarySource cfg ext
      ((p.store cfg ext).block_states
        (get_current_target cfg (p.store cfg ext)).root)
      (get_current_target cfg (p.store cfg ext)).epoch
    Nonempty (CertifiedJustified cfg E B.anchor source) ∧
      E.RootDescends (get_current_target cfg (p.store cfg ext)).root
        source.root ∧
      source.epoch < (get_current_target cfg (p.store cfg ext)).epoch := by
  intro source
  let store := p.store cfg ext
  let target := get_current_target cfg store
  change target.root ∈ store.block_roots at htargetKnown
  change get_block_epoch cfg store target.root < target.epoch at htargetOld
  change B.anchor.epoch < target.epoch at hanchorBefore
  change Nonempty (CertifiedJustified cfg E B.anchor source) ∧
    E.RootDescends target.root source.root ∧ source.epoch < target.epoch
  have hstore : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using (Execution.ScheduledPrefixStore.scheduledPrefix p)
  have hprojection : AcceptedFFGStoreProjection B.state store :=
    Execution.ScheduledFFGInterpretation.causalStoreProjection B hstore
  have hqueryCore : WellFormedStoreCore store :=
    E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT hstore
  have hstateEpoch : compute_epoch_at_slot cfg
      (store.block_states target.root).slot =
        get_block_epoch cfg store target.root := by
    simp only [get_block_epoch]
    rw [hqueryCore.2 target.root htargetKnown]
  by_cases hone : get_block_epoch cfg store target.root + 1 = target.epoch
  · -- One boundary: the eager `GU` of the target block.
    have hGU : source = B.state.unrealized_justified target.root := by
      change phase0BoundarySource cfg ext (store.block_states target.root)
        target.epoch = _
      rw [hboundaryPhase.boundarySource_eq_pjf
        (by rw [hstateEpoch]; exact hone.symm)]
      exact hprojection.pulled_up_gu target.root htargetKnown
    have htargetCarrier : E.AcceptedCarrierIn
        (cfg := cfg) (ext := ext) store target.root :=
      Execution.AcceptedCarrierIn.of_causal_known hstore htargetKnown
    obtain ⟨formedCarrier, htargetDescendsCarrier, hformed⟩ :=
      B.state.unrealized_justified_mem target.root htargetCarrier.acceptedRoot
    have hevidence := B.state.formed_evidence hformed
    have htargetAt : E.BlockKnownInScheduledPrefix cfg ext target.root
        (store.blocks target.root) :=
      E.acceptedBlockAt_of_causal_known cfg ext hstore htargetKnown
    have hGUEpoch : (B.state.unrealized_justified target.root).epoch <
        target.epoch :=
      lt_of_le_of_lt (B.state.available_checkpoint_epoch_le_block htargetAt
        ⟨formedCarrier, htargetDescendsCarrier, hformed⟩) htargetOld
    rw [hGU]
    obtain ⟨hincluded⟩ := hevidence.certified
    exact ⟨⟨IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg) B.state.includedAttestations.relation hincluded⟩,
      Execution.RootDescends.trans E htargetDescendsCarrier hevidence.on_chain,
      hGUEpoch⟩
  · -- Two or more boundaries: the `GJ` of a current-epoch carrier.
    have hlate : get_block_epoch cfg store target.root + 1 < target.epoch :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt htargetOld) hone
    obtain ⟨c, hcKnown, hcEpoch, hheadC⟩ := hguard hlate
    obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
    have hgenCore : WellFormedStoreCore E.genesis_store := by
      rw [hgen]
      exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
        hgenParent).core
    have hcausalCore : E.ExactCausalStoreWellFormedCore cfg ext :=
      E.exactCausalStoreWellFormedCore
        hT.externals_coherence.state_transition_slot hgenCore
    have hparentSlots : ParentSlotLt store := p.parentSlotLt cfg ext E hT
    have hheadKnown : (get_head cfg store).root ∈ store.block_roots :=
      p.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT hanchor hboundary
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
      simpa only [get_forkchoice_store, get_current_epoch, hgenSlot] using he
    have hboundary' : ablk.message.slot ≤
        compute_start_slot_at_epoch cfg B.anchor.epoch := by
      simpa only [InitialAnchorAtEpochBoundary, hgen, hanchorRoot,
        get_forkchoice_store, Function.update_self] using hboundary
    have hwalkFromAnchor : ∀ e, B.anchor.epoch ≤ e → ∀ r ∈ store.block_roots,
        WalkKnown store (compute_start_slot_at_epoch cfg e) r := by
      intro e he r hr
      apply (p.walkKnownK cfg ext hT B.anchor.root hanchorKnown r hr).mono
      rw [hanchorBlock]
      exact hboundary'.trans (Nat.mul_le_mul_right cfg.slots_per_epoch he)
    have htargetEq : target = get_checkpoint_for_block cfg store c
        (get_block_epoch cfg store c) :=
      current_target_eq_checkpoint_of_current_epoch_ancestor cfg hparentSlots
        hheadC hcEpoch
        (hwalkFromAnchor _ hanchorBefore.le _ hheadKnown)
    have hcTargetEpoch : get_block_epoch cfg store c = target.epoch := hcEpoch
    have htargetAtC : target = get_checkpoint_for_block cfg store c
        target.epoch := by
      rw [← hcTargetEpoch]
      exact htargetEq
    have hwalk : WalkKnown store (compute_start_slot_at_epoch cfg target.epoch)
        c := hwalkFromAnchor _ hanchorBefore.le c hcKnown
    have hlands : (get_ancestor store (ForkChoiceNode.mk c .pending)
        (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
      have h := congrArg Checkpoint.root htargetAtC
      simpa only [get_checkpoint_for_block, get_checkpoint_block] using h.symm
    have hcurrentNonGenesis : ∀ r ∈ store.block_roots,
        get_block_epoch cfg store r = target.epoch →
          r ∉ E.genesis_store.block_roots := by
      intro r hr hcurrent hrGenesis
      have hrEq : r = ablk.root := by
        rw [hgen] at hrGenesis
        simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
      subst r
      have hrootEpoch : get_block_epoch cfg store ablk.root =
          B.anchor.epoch := by
        simp only [get_block_epoch]
        rw [← hanchorRoot, hanchorBlock, hanchorEpoch]
      exact (Nat.ne_of_lt hanchorBefore) (hrootEpoch.symm.trans hcurrent)
    have hgj := E.acceptedGJEqHonestSourceAt_of_target_walk_root cfg ext B
      hT.wellFormed hT.externals_coherence hcausalCore hphase hboundaryPhase
      hstore hparentSlots hcurrentNonGenesis hwalk hlands hcTargetEpoch
    have hsource : B.state.realized_justified c = source := by
      simpa only [phase0HonestSourceAt, if_neg (Nat.ne_of_lt htargetOld)]
        using hgj
    have hcCarrier : E.AcceptedCarrierIn
        (cfg := cfg) (ext := ext) store c :=
      Execution.AcceptedCarrierIn.of_causal_known hstore hcKnown
    obtain ⟨formedCarrier, hcDescendsCarrier, hformed⟩ :=
      B.state.realized_justified_mem c hcCarrier.acceptedRoot
    have hevidence := B.state.formed_evidence hformed
    obtain ⟨hincluded⟩ := hevidence.certified
    have hcertified : CertifiedJustified cfg E B.anchor
        (B.state.realized_justified c) :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg) B.state.includedAttestations.relation hincluded
    have hcAt : E.BlockKnownInScheduledPrefix cfg ext c (store.blocks c) :=
      E.acceptedBlockAt_of_causal_known cfg ext hstore hcKnown
    have hsourceLt : (B.state.realized_justified c).epoch < target.epoch := by
      rcases B.state.realized_justified_anchor_or_before hcAt with hanc | hbefore
      · rw [hanc]
        exact hanchorBefore
      · exact lt_of_lt_of_eq hbefore hcTargetEpoch
    rw [← hsource]
    refine ⟨⟨hcertified⟩, ?_, hsourceLt⟩
    have hanchorLe : B.anchor.epoch ≤ (B.state.realized_justified c).epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
    have hepochLe : (B.state.realized_justified c).epoch ≤ target.epoch :=
      hsourceLt.le
    have hcheckpoint : B.state.realized_justified c =
        get_checkpoint_for_block cfg store c
          (B.state.realized_justified c).epoch :=
      B.coherence.available_checkpoint_checkpoint_of_known hstore c
        hcKnown _ ⟨formedCarrier, hcDescendsCarrier, hformed⟩
    have hcomp := get_checkpoint_for_block_comp cfg hparentSlots hepochLe
      (hwalkFromAnchor _ hanchorLe c hcKnown)
    rw [← htargetAtC] at hcomp
    have hroot : (B.state.realized_justified c).root =
        get_checkpoint_block cfg store target.root
          (B.state.realized_justified c).epoch := by
      have h := congrArg Checkpoint.root (hcheckpoint.trans hcomp.symm)
      simpa only [get_checkpoint_for_block] using h
    rw [hroot]
    exact E.rootDescends_checkpointBlock_of_walks cfg
      (p.blockProvenance cfg ext) hparentSlots
      (hwalkFromAnchor _ hanchorLe target.root htargetKnown)
      (fun a ha => p.walkKnownK cfg ext hT a ha target.root htargetKnown)

/-- Close the old-checkpoint accepted gate branch at an exact scheduled
prefix.  The boundary-source quorum, its certificate, and its descent are
constructed internally and immediately consumed by the old-epoch certificate
constructor. -/
theorem scheduledEventPrefix_acceptedOldTargetA32GateRealization_core
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
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
    (hdelivery : ∀ Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (p.store cfg ext)).epoch + 1))
      (get_current_target cfg (p.store cfg ext)),
        ConcreteA32QuorumScheduledDelivery cfg ext E Q)
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
      (get_current_target cfg (p.store cfg ext)).epoch)
    (hguard : CurrentTargetLateBoundaryCarrierGuard cfg (p.store cfg ext)) :
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      (p.store cfg ext) := by
  let store := p.store cfg ext
  let target := get_current_target cfg store
  change E.CurrentTargetPrefixAccountingEvidence cfg ext store
    (p.previousSecond + 1) at hevidence
  change state = get_pulled_up_head_state cfg ext store at hstate
  change E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store) at hendH
  change (∀ Q : ConcreteA32QuorumBefore cfg ext E
    (compute_start_slot_at_epoch cfg (target.epoch + 1)) target,
      ConcreteA32QuorumScheduledDelivery cfg ext E Q) at hdelivery
  change will_current_target_be_justified cfg ext store = true at hgate
  change HonestVotesSupportTarget cfg E target
    (p.previousSecond + 1) at hsupport
  change target.root ∈ store.block_roots at htargetKnown
  change get_block_epoch cfg store target.root < target.epoch at htargetOld
  change B.anchor.epoch < target.epoch at hanchorBefore
  obtain ⟨hsourceCertified, htargetDescendsSource, hsourceBefore⟩ :=
    E.scheduledEventPrefix_oldTargetBoundarySource_certificate cfg ext B hT
      hphase hboundaryPhase hanchor hboundary p hguard htargetKnown htargetOld
      hanchorBefore
  obtain ⟨Q, hQSource, _hgeometry⟩ :=
    E.scheduledEventPrefix_acceptedConcreteOldTargetQuorum cfg ext B hT
      hsv hbb hphase hboundaryPhase hanchor hboundary p hp hqH hevidence
      hstate hval htab hendH hanchorH hfloor hgate hsupport htargetKnown
      htargetOld hanchorBefore hsourceBefore
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
  have htargetNotAnchor : target ≠ B.anchor := by
    intro heq
    have hepoch := congrArg Checkpoint.epoch heq
    exact (Nat.ne_of_lt hanchorBefore) hepoch.symm
  have hstore : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using (Execution.ScheduledPrefixStore.scheduledPrefix p)
  exact E.acceptedCurrentTargetA32GateRealization_of_oldEpochConcreteQuorum_core
    cfg ext B htargetOld htargetNotAnchor htargetSpan Q (hdelivery Q) hQSource
      (hQSource ▸ hsourceCertified) (hQSource ▸ htargetDescendsSource)



/-- Preferred accepted gate facade at an exact scheduled prefix.

The executable current target is first handled by the trusted-anchor base
case.  Otherwise retained-anchor prefix geometry derives both target
knownness and strict progress after the anchor.  The checkpoint landing bound
then gives the exhaustive current/old split used to select the accepted `GJ`
or `GU` construction internally.

No selected-margin bundle, walk/domain premise, target-epoch premise, quorum,
source, segment, certificate, transition history, or safety conclusion is an
input. -/
theorem scheduledEventPrefix_acceptedTargetA32GateRealization_core
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
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
    (hdelivery : ∀ Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (p.store cfg ext)).epoch + 1))
      (get_current_target cfg (p.store cfg ext)),
        ConcreteA32QuorumScheduledDelivery cfg ext E Q)
    (hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1))
    (hguard : CurrentTargetLateBoundaryCarrierGuard cfg (p.store cfg ext)) :
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      (p.store cfg ext) := by
  let store := p.store cfg ext
  let target := get_current_target cfg store
  change E.CurrentTargetPrefixAccountingEvidence cfg ext store
    (p.previousSecond + 1) at hevidence
  change state = get_pulled_up_head_state cfg ext store at hstate
  change E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store) at hendH
  change (∀ Q : ConcreteA32QuorumBefore cfg ext E
    (compute_start_slot_at_epoch cfg (target.epoch + 1)) target,
      ConcreteA32QuorumScheduledDelivery cfg ext E Q) at hdelivery
  change will_current_target_be_justified cfg ext store = true at hgate
  change HonestVotesSupportTarget cfg E target
    (p.previousSecond + 1) at hsupport
  by_cases htargetAnchor : target = B.anchor
  · refine ⟨⟨?_⟩, Or.inl htargetAnchor⟩
    change CertifiedJustified cfg E B.anchor target
    rw [htargetAnchor]
    exact CertifiedJustified.anchor
  · have htargetFacts :=
      p.currentTargetKnown_and_blockEpoch_le cfg ext B hT hanchor hboundary
    have htargetKnown : target.root ∈ store.block_roots := by
      simpa only [store, target] using htargetFacts.1
    have htargetEpochLe : get_block_epoch cfg store target.root ≤
        target.epoch := by
      simpa only [store, target] using htargetFacts.2
    have hanchorBefore : B.anchor.epoch < target.epoch := by
      simpa only [store, target] using
        p.currentTarget_anchor_epoch_lt_of_ne cfg ext B hT hanchor hboundary
          (by simpa only [store, target] using htargetAnchor)
    by_cases htargetEpoch :
        get_block_epoch cfg store target.root = target.epoch
    · exact E.scheduledEventPrefix_acceptedCurrentTargetA32GateRealization_core
        cfg ext B hT hsv hbb hphase hanchor hboundary p hp hqH hevidence
        hstate hval htab hendH hdelivery hanchorH hfloor hgate hsupport
        htargetKnown htargetEpoch hanchorBefore
    · have htargetOld : get_block_epoch cfg store target.root <
          target.epoch := lt_of_le_of_ne htargetEpochLe htargetEpoch
      exact E.scheduledEventPrefix_acceptedOldTargetA32GateRealization_core
        cfg ext B hT hsv hbb hphase hboundaryPhase hanchor hboundary p hp hqH
        hevidence hstate hval htab hendH hdelivery hanchorH hfloor hgate
        hsupport htargetKnown htargetOld hanchorBefore hguard


/-- Preferred finite-prefix facade. Votes are created inside the public
horizon; only their one-slot-later scheduled receipt may cross its exclusive
endpoint. -/
theorem scheduledEventPrefix_acceptedTargetA32GateRealization_withLookahead
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hdelivery : HorizonVoteDeliveryLookahead cfg E)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E)
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
    (hguard : CurrentTargetLateBoundaryCarrierGuard cfg (p.store cfg ext)) :
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      (p.store cfg ext) := by
  apply E.scheduledEventPrefix_acceptedTargetA32GateRealization_core
    cfg ext B hT hsv hbb hphase hboundaryPhase hanchor hboundary p hp hqH
      hevidence hstate hval htab hendH ?_ hanchorH hfloor hgate hsupport hguard
  intro Q
  exact Q.scheduledDelivery_of_lookahead cfg ext E hdelivery

end Execution

namespace AllowedFCRCalls

open Execution




end AllowedFCRCalls


end FastConfirmation.Spec

end
