module
public import FastConfirmationProofs.FFG.Certificates.NoConflictCertificatePinning
public import FastConfirmationProofs.Execution.History.SelectedPreQueryHistoricalSIR
public import FastConfirmationProofs.FFG.SelectedSource.FFGSelectedDomainRealization
public import FastConfirmationProofs.ModelFacts

public import FastConfirmationStatements.Premises.FFG
@[expose] public section

/-!
# Realizing the current-target certificate

The executable current-target helper counts exact-target votes, whereas a
`CertifiedJustified` object needs one source-specific, scheduled
`SupermajorityLink`.  This module reconstructs the source information which
the target-only accounting intentionally forgets and constructs that link.

The construction uses no certificate producer, target certificate, arbitrary
source certificate, or target/source descent premise.  Instead:

* the gate supplies concrete canonical honest votes and their two-thirds
  weight;
* the global FFG trajectory supplies each vote's actual target-boundary walk;
* same-epoch and boundary phase0 laws identify its source with the paper's
  `VSAt` selector, and cross-store block agreement makes that selector common;
* `GJ`/`GU` AU evidence supplies the source certificate and puts source and
  target on one checkpoint chain, from which execution descent is derived; and
* a scheduled-delivery law turns each retained ground vote into the witness
  stored by `SupermajorityLink`.

The last step exposes one genuine finite-horizon seam.  A vote in the last
slot of epoch `e` is first processable at the start of `e+1`.  Therefore the
core constructor accepts the needed local delivery law.  The legacy synchrony
adapter keeps that exact delivery second within the verified horizon, while
the accepted finite-horizon path uses the boundary case of the single
synchrony premise (`PaperSafetySynchrony.toDeliveryLookahead`, formerly the
separate `HorizonVoteDeliveryLookahead` assumption): vote creation remains
inside the public horizon, and receipt may occur at the first second beyond
its exclusive cutoff.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The epoch-boundary source law -/

omit [LinearOrder Root] [Inhabited Root] in
/-- A slot whose epoch precedes `e` is strictly before `e`'s boundary. -/
private theorem slot_lt_epoch_start_of_epoch_lt
    {slot : Slot} {e : Epoch}
    (h : compute_epoch_at_slot cfg slot < e) :
    slot < compute_start_slot_at_epoch cfg e := by
  have hnext : compute_epoch_at_slot cfg slot + 1 ≤ e :=
    Nat.succ_le_of_lt h
  have hlt := Nat.lt_mul_div_succ slot cfg.slots_per_epoch_pos
  calc
    slot < cfg.slots_per_epoch * (slot / cfg.slots_per_epoch + 1) := hlt
    _ ≤ cfg.slots_per_epoch * e :=
      Nat.mul_le_mul_left cfg.slots_per_epoch hnext
    _ = compute_start_slot_at_epoch cfg e := by
      simp only [compute_start_slot_at_epoch, Nat.mul_comm]

namespace Execution

variable (E : Execution Root)

/-- A known block edge which crosses an epoch boundary installs the eager
`GU` value of its parent as the child's realized `GJ` value.  The transition
equation comes from handler history; the checkpoint equation itself comes
only from the state-only boundary law. -/
theorem known_cross_epoch_parent_gj_eq_gu
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    {child : Root}
    (hchild : child ∈ (E.store cfg ext w n).block_roots)
    (hnongenesis : child ∉ E.genesis_store.block_roots)
    (hcross : compute_epoch_at_slot cfg
        ((E.store cfg ext w n).blocks
          ((E.store cfg ext w n).blocks child).parent_root).slot <
      compute_epoch_at_slot cfg
        ((E.store cfg ext w n).blocks child).slot) :
    S.GJ child =
      S.GU ((E.store cfg ext w n).blocks child).parent_root := by
  let store := E.store cfg ext w n
  let parent := (store.blocks child).parent_root
  have hreplay := hhistory.replay w hw n hH child hchild hnongenesis
  change parent ∈ store.block_roots ∧
    ext.state_transition (store.block_states parent)
      (storedSignedBlock store child) = some (store.block_states child)
    at hreplay
  have hstateCross : compute_epoch_at_slot cfg
      (store.block_states parent).slot <
      compute_epoch_at_slot cfg
        (storedSignedBlock store child).message.slot := by
    rw [hcore.2 parent hreplay.1]
    simpa only [store, parent, storedSignedBlock] using hcross
  have hprojection := E.ffgStoreProjection hcoh w n
  calc
    S.GJ child = (store.block_states child).current_justified_checkpoint :=
      (hprojection.block_state_gj child hchild).symm
    _ = (ext.process_justification_and_finalization
          (store.block_states parent)).current_justified_checkpoint :=
      hboundaryPhase.state_transition_current_justified _ _ _
        hreplay.2 hstateCross
    _ = S.GU parent := hprojection.pulled_up_gu parent hreplay.1

/-- Follow the actual target-boundary walk of a current-epoch head.

Same-epoch edges preserve `GJ`.  If the checkpoint block at the boundary is
older, the first edge above it is the unique cross-boundary edge and changes
the value to `GU` of that checkpoint block.  Thus the head's realized source
is exactly paper Definition 7's `VSAt` selector, without postulating a common
ancestor or a source equality. -/
theorem gj_eq_vSAt_of_target_walk_root
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    (hwf : ParentSlotLt (E.store cfg ext w n))
    {e : Epoch} {targetRoot head : Root}
    (hcurrentNonGenesis : ∀ r ∈ (E.store cfg ext w n).block_roots,
      get_block_epoch cfg (E.store cfg ext w n) r = e →
      r ∉ E.genesis_store.block_roots)
    (hwalk : WalkKnown (E.store cfg ext w n)
      (compute_start_slot_at_epoch cfg e) head)
    (hlands : (get_ancestor (E.store cfg ext w n)
      (ForkChoiceNode.mk head .pending) (compute_start_slot_at_epoch cfg e)).root = targetRoot)
    (hheadEpoch : get_block_epoch cfg (E.store cfg ext w n) head = e) :
    S.GJ head = S.VSAt cfg (E.store cfg ext w n) targetRoot e := by
  let store := E.store cfg ext w n
  change WalkKnown store (compute_start_slot_at_epoch cfg e) head at hwalk
  change (get_ancestor store (ForkChoiceNode.mk head .pending)
    (compute_start_slot_at_epoch cfg e)).root = targetRoot at hlands
  change get_block_epoch cfg store head = e at hheadEpoch
  change (∀ r ∈ store.block_roots, get_block_epoch cfg store r = e →
    r ∉ E.genesis_store.block_roots) at hcurrentNonGenesis
  change S.GJ head = S.VSAt cfg store targetRoot e
  induction hwalk generalizing targetRoot with
  | @stop r hr hle =>
      rw [get_ancestor_stop hle] at hlands
      have hre : r = targetRoot := hlands
      subst targetRoot
      simp only [ChainFFGState.VSAt, hheadEpoch, if_pos]
  | @step r hr hgt hp ih =>
      have hparentKnown := hp.root_mem
      have hparentSlotLt := hwf r hr hparentKnown
      have hlandsParent : (get_ancestor store
          (ForkChoiceNode.mk (store.blocks r).parent_root .pending)
          (compute_start_slot_at_epoch cfg e)).root = targetRoot := by
        rw [get_ancestor_step hwf hr hgt hp] at hlands
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
          simpa only [get_block_epoch] using hparentCurrent.trans hheadEpoch.symm
        have hedge := E.known_same_epoch_parent_gj_eq
          (cfg := cfg) (ext := ext) (S := S) hhistory hphase hcoh
          hw hH hr (hcurrentNonGenesis r hr hheadEpoch) hcore hsame
        exact hedge.trans (ih hlandsParent hparentCurrent)
      · have hparentOld :
            get_block_epoch cfg store (store.blocks r).parent_root < e :=
          Nat.lt_of_le_of_ne hparentEpochLe hparentCurrent
        have hparentBelow :
            (store.blocks (store.blocks r).parent_root).slot <
              compute_start_slot_at_epoch cfg e :=
          slot_lt_epoch_start_of_epoch_lt cfg hparentOld
        rw [get_ancestor_stop hparentBelow.le] at hlandsParent
        have hparentEq : (store.blocks r).parent_root = targetRoot :=
          hlandsParent
        have hcross : compute_epoch_at_slot cfg
            (store.blocks (store.blocks r).parent_root).slot <
            compute_epoch_at_slot cfg (store.blocks r).slot := by
          simpa only [get_block_epoch] using
            hparentOld.trans_eq hheadEpoch.symm
        have hedge := E.known_cross_epoch_parent_gj_eq_gu
          (cfg := cfg) (ext := ext) (S := S) hhistory hboundaryPhase hcoh
          hw hH hcore hr (hcurrentNonGenesis r hr hheadEpoch) hcross
        have htargetOld : get_block_epoch cfg store targetRoot ≠ e := by
          rw [← hparentEq]
          exact Nat.ne_of_lt hparentOld
        rw [hparentEq] at hedge
        simp only [ChainFFGState.VSAt, if_neg htargetOld]
        exact hedge


/-- Definition 7's selector is invariant under replacing a current-epoch
carrier by its epoch checkpoint block.

This is the fixed-source bridge needed by paper Assumption 3.2.  The left
side is the selector naturally reconstructed from the gate's target votes;
the right side is `VSAt(b,e)` for the original selected block `b`.  The proof
uses only the actual checkpoint equation and phase0 source semantics. -/
theorem vSAt_checkpoint_eq_vSAt_current_carrier
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    (hwf : ParentSlotLt (E.store cfg ext w n))
    {e : Epoch} {b : Root} {target : Checkpoint Root}
    (hcurrentNonGenesis : ∀ r ∈ (E.store cfg ext w n).block_roots,
      get_block_epoch cfg (E.store cfg ext w n) r = e →
      r ∉ E.genesis_store.block_roots)
    (hwalk : WalkKnown (E.store cfg ext w n)
      (compute_start_slot_at_epoch cfg e) b)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w n) b = e)
    (htarget : get_checkpoint_for_block cfg (E.store cfg ext w n) b e =
      target) :
    S.VSAt cfg (E.store cfg ext w n) target.root e =
      S.VSAt cfg (E.store cfg ext w n) b e := by
  let store := E.store cfg ext w n
  have htargetRoot : get_checkpoint_block cfg store b e = target.root := by
    have hroot := congrArg Checkpoint.root htarget
    simpa only [store, get_checkpoint_for_block] using hroot
  have hlands : (get_ancestor store (ForkChoiceNode.mk b .pending)
      (compute_start_slot_at_epoch cfg e)).root = target.root := by
    simpa only [get_checkpoint_block] using htargetRoot
  have hgj := E.gj_eq_vSAt_of_target_walk_root cfg ext hhistory hphase
    hboundaryPhase hcoh hw hH hcore hwf hcurrentNonGenesis hwalk hlands
    hbEpoch
  have hbEpoch' : get_block_epoch cfg store b = e := by
    simpa only [store] using hbEpoch
  calc
    S.VSAt cfg store target.root e = S.GJ b := hgj.symm
    _ = S.VSAt cfg store b e := by
      simp only [ChainFFGState.VSAt, hbEpoch', if_pos]

/-- Read an actual honest vote's source as the paper selector at its concrete
target checkpoint block.  The only geometry premise is the target-boundary
`WalkKnown` fact derived globally in `FFGSelectedDomainRealization`. -/
theorem honest_attestation_data_source_eq_vSAt_target
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    (hwf : ParentSlotLt (E.store cfg ext w n))
    {slot : Slot} {index : CommitteeIndex} {target : Checkpoint Root}
    (hslotEpoch : compute_epoch_at_slot cfg slot = target.epoch)
    (hwalk : WalkKnown (E.store cfg ext w n)
      (compute_start_slot_at_epoch cfg target.epoch)
      (get_head cfg (E.store cfg ext w n)).root)
    (htarget : (honest_attestation_data cfg ext
      (E.store cfg ext w n) slot index).target = target)
    (hheadStateSlotLe : ((E.store cfg ext w n).block_states
      (get_head cfg (E.store cfg ext w n)).root).slot ≤ slot)
    (hcurrentNonGenesis : ∀ r ∈ (E.store cfg ext w n).block_roots,
      get_block_epoch cfg (E.store cfg ext w n) r = target.epoch →
      r ∉ E.genesis_store.block_roots) :
    (honest_attestation_data cfg ext
      (E.store cfg ext w n) slot index).source =
      S.VSAt cfg (E.store cfg ext w n) target.root target.epoch := by
  let store := E.store cfg ext w n
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
        rw [hcore.2 head hheadKnown]
      _ ≤ slot / cfg.slots_per_epoch :=
        Nat.div_le_div_right hheadStateSlotLe
      _ = target.epoch := by
        simpa only [compute_epoch_at_slot] using hslotEpoch
  by_cases hheadCurrent : get_block_epoch cfg store head = target.epoch
  · have hsame : compute_epoch_at_slot cfg (store.block_states head).slot =
        compute_epoch_at_slot cfg slot := by
      rw [hcore.2 head hheadKnown]
      exact hheadCurrent.trans hslotEpoch.symm
    rw [honest_attestation_data_source_eq_gj hphase
      (E.ffgStoreProjection hcoh w n) hheadKnown hsame]
    exact E.gj_eq_vSAt_of_target_walk_root cfg ext hhistory hphase
      hboundaryPhase hcoh hw hH hcore hwf hcurrentNonGenesis hwalk
      hlands hheadCurrent
  · have hheadOld : get_block_epoch cfg store head < target.epoch :=
      Nat.lt_of_le_of_ne hheadEpochLe hheadCurrent
    have hstateEpochOld : compute_epoch_at_slot cfg
        (store.block_states head).slot < target.epoch := by
      rw [hcore.2 head hheadKnown]
      exact hheadOld
    have hstateBelow : (store.block_states head).slot <
        compute_start_slot_at_epoch cfg target.epoch :=
      slot_lt_epoch_start_of_epoch_lt cfg hstateEpochOld
    have hvoteStartLe : compute_start_slot_at_epoch cfg target.epoch ≤ slot := by
      have hlo := Nat.div_mul_le_self slot cfg.slots_per_epoch
      have heq : slot / cfg.slots_per_epoch = target.epoch := by
        simpa only [compute_epoch_at_slot] using hslotEpoch
      rw [heq] at hlo
      simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlo
    have hstateSlotLt : (store.block_states head).slot < slot :=
      hstateBelow.trans_le hvoteStartLe
    have hheadBelow : (store.blocks head).slot <
        compute_start_slot_at_epoch cfg target.epoch :=
      slot_lt_epoch_start_of_epoch_lt cfg hheadOld
    rw [get_ancestor_stop hheadBelow.le] at hlands
    have hheadEq : head = target.root := hlands
    have hboundaryEpoch : compute_epoch_at_slot cfg
        (store.block_states head).slot < compute_epoch_at_slot cfg slot := by
      exact hstateEpochOld.trans_eq hslotEpoch.symm
    change (if (store.block_states head).slot < slot then
        ext.process_slots (store.block_states head) slot
      else store.block_states head).current_justified_checkpoint = _
    rw [if_pos hstateSlotLt]
    calc
      (ext.process_slots (store.block_states head) slot).current_justified_checkpoint =
          (ext.process_justification_and_finalization
            (store.block_states head)).current_justified_checkpoint :=
        hboundaryPhase.process_slots_current_justified _ _
          hstateSlotLt hboundaryEpoch
      _ = S.GU head :=
        (E.ffgStoreProjection hcoh w n).pulled_up_gu head hheadKnown
      _ = S.VSAt cfg store target.root target.epoch := by
        have htargetOld : get_block_epoch cfg store target.root ≠ target.epoch := by
          rw [← hheadEq]
          exact Nat.ne_of_lt hheadOld
        simp only [ChainFFGState.VSAt, if_neg htargetOld, hheadEq]

omit [LinearOrder Root] [Inhabited Root] in
/-- `slot_start` is monotone.  This is used only to inherit the horizon of the
next-epoch delivery boundary for earlier votes in the target epoch. -/
private theorem slot_start_mono {a b : Slot} (hab : a ≤ b) :
    E.slot_start cfg a ≤ E.slot_start cfg b := by
  simp only [Execution.slot_start]
  apply Nat.sub_le_sub_right
  apply Nat.add_le_add_left
  exact Nat.div_le_div_right (Nat.mul_le_mul_right cfg.slot_duration_ms hab)

/-- A trusted-boundary execution has a known walk from any known carrier down
to every epoch boundary at or after the trusted anchor epoch. -/
theorem walkKnown_epochBoundary_of_anchor_le
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {w : ValidatorIndex} {m : ℕ} {carrier : Root} {e : Epoch}
    (hcarrier : carrier ∈ (E.store cfg ext w m).block_roots)
    (hae : anchor.epoch ≤ e) :
    WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg e) carrier := by
  obtain ⟨hgen, hwf, _hdiv, _hhb, hec, _hsv, _hbb, _hknown⟩ := hA
  obtain ⟨ast, ablk, hgeq, hgenSlot, hparent⟩ := hgen
  have hgenFull : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hgenSlot, hparent⟩
  have hanchorRoot : anchor.root = ablk.root := by
    rw [hanchor, hgeq]
    rfl
  have hanchorEpoch : anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgeq]
    rfl
  have hanchorKnown0 : ablk.root ∈ (E.store cfg ext w 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnown : ablk.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorKnown0
  have hanchorBlock :
      (E.store cfg ext w m).blocks ablk.root = ablk.message :=
    E.store_anchor_block cfg ext hwf hgeq w m hanchorKnown
  have hwalkAnchor : WalkKnown (E.store cfg ext w m)
      ablk.message.slot carrier := by
    have hwalk := E.store_walkKnownK cfg ext hwf hec hgenFull w m
      ablk.root hanchorKnown carrier hcarrier
    rwa [hanchorBlock] at hwalk
  have hanchorBoundary : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgeq, get_forkchoice_store,
      Function.update_self, hanchorEpoch] using hboundary
  apply hwalkAnchor.mono
  exact hanchorBoundary.trans
    (Nat.mul_le_mul_right cfg.slots_per_epoch hae)

/-- Two epoch checkpoint blocks of one known carrier inherit their ordering
in the concrete execution parent graph.  Both checkpoint equations and all
walk-domain facts are premises; the desired `RootDescends` fact is derived. -/
theorem checkpointBlock_rootDescends
    (hA : NoConflictPinningAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {carrier : Root}
    {sourceEpoch targetEpoch : Epoch}
    (hsourceTarget : sourceEpoch < targetEpoch)
    (hsourceWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg sourceEpoch) carrier)
    (htargetWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg targetEpoch) carrier) :
    E.RootDescends
      (get_checkpoint_block cfg (E.store cfg ext w m) carrier targetEpoch)
      (get_checkpoint_block cfg (E.store cfg ext w m) carrier sourceEpoch) := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hec, _hsv, _hbb, _hknown⟩ := hA
  let store := E.store cfg ext w m
  let source := get_checkpoint_block cfg store carrier sourceEpoch
  let target := get_checkpoint_block cfg store carrier targetEpoch
  have hwf : ParentSlotLt store :=
    E.store_parentSlotLt cfg ext hwfE hec hgen
      hwfE.anchor_parent_unscheduled w m
  have hsourceSpec := get_ancestor_spec hwf hsourceWalk
  have htargetSpec := get_ancestor_spec hwf htargetWalk
  have hboundaryLe : compute_start_slot_at_epoch cfg sourceEpoch ≤
      compute_start_slot_at_epoch cfg targetEpoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hsourceTarget.le
  have htargetToSourceBoundary :
      (get_ancestor store (ForkChoiceNode.mk target .pending)
          (compute_start_slot_at_epoch cfg sourceEpoch)).root = source := by
    have hcomp := get_ancestor_comp_root hwf hboundaryLe hsourceWalk
    simpa only [target, source, get_checkpoint_block, store] using hcomp
  have hwalkTargetSource : WalkKnown store (store.blocks source).slot target :=
    E.store_walkKnownK cfg ext hwfE hec hgen w m
      source hsourceSpec.1 target htargetSpec.1
  have hlands : (get_ancestor store (ForkChoiceNode.mk target .pending)
      (store.blocks source).slot).root = source := by
    have hsourceSlotLe : (store.blocks source).slot ≤
        compute_start_slot_at_epoch cfg sourceEpoch := by
      simpa only [source] using hsourceSpec.2
    have hcomp := get_ancestor_comp_root hwf hsourceSlotLe hwalkTargetSource
    rw [htargetToSourceBoundary] at hcomp
    rw [get_ancestor_stop (Nat.le_refl _)] at hcomp
    exact hcomp.symm
  exact E.rootDescends_of_getAncestor
    (E.blockProvenance cfg ext w m) hwf hwalkTargetSource hlands

/-! ## Gate-to-certificate constructor -/

/-- The current-target gate produces both a concrete `CertifiedJustified`
target and the paper-facing branch from which it was obtained.

The target-boundary walk domain is derived from the global handler-driven FFG
trajectory.  The walk plus the two state-only phase0 source laws proves every
vote's source to be `VSAt(target.root, target.epoch)`; cross-store block
agreement makes that selector common.  Its AU evidence, certificate, and
descent to the target are all then derived from `ChainFFGState`.

`hnextH` is not a protocol-strength assumption: it is the exact finite-model
buffer needed to materialize the scheduled receipt of a possible last-slot
vote.  A model in which honest ground votes are also explicit broadcast
events could replace this premise with that local broadcast fact. -/
theorem certifiedCurrentTarget_of_gate_and_stateSemantics
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hstate : state =
      get_pulled_up_head_state cfg ext (E.store cfg ext v n))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hnextH : E.WithinHorizon cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (E.store cfg ext v n)).epoch + 1))))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hgate : will_current_target_be_justified cfg ext
      (E.store cfg ext v n) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v n)) n) :
    CurrentTargetA32GateRealization cfg ext E anchor S
      (E.store cfg ext v n) := by
  classical
  have hA0 := hA
  obtain ⟨hgen, _hwf, hdiv, hhb, hec, hsv, hbb, hknown⟩ := hA
  obtain ⟨ast, ablk, hgeq, hgenSlot, hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  have hgenTrajectory :
      ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk ∧
          ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgeq, hgenSlot⟩
  have hgenFull :
      ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk ∧
          ast.slot = ablk.message.slot ∧
          ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hgenSlot, hparent⟩
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot hparent
  have hboundaryAnchor : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := anchor) := by
    rw [hanchor]
    exact hboundary
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_globalTrajectory cfg ext
      hA0.wellFormed hec hdiv hgenFull hcoh hanchor hboundaryAnchor
  have hslot0 : E.slot_at cfg 0 = ast.slot := by
    have hcur := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at hcur
    exact hcur.symm
  have hanchorEpoch : anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgeq]
    rfl
  have hanchorEpoch0 : anchor.epoch =
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
    simpa only [get_current_epoch, hslot0] using hanchorEpoch
  let store := E.store cfg ext v n
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  change HonestVotesSupportTarget cfg E target n at hsupport
  change E.WithinHorizon cfg (E.slot_start cfg deadline) at hnextH
  change CurrentTargetA32GateRealization cfg ext E anchor S store
  have horigins := E.globalCheckpointOrigins cfg ext hcoh
    hgenTrajectory hanchor v n
  have hcertifiedUJ : Nonempty (CertifiedJustified cfg E anchor
      store.unrealized_justified_checkpoint) := by
    rcases horigins.unrealized_justified with hanchorUJ |
      ⟨r, hr, hgu⟩
    · refine ⟨?_⟩
      rw [hanchorUJ]
      exact CertifiedJustified.anchor
    · obtain ⟨hcertified⟩ := S.gu_certified cfg r
        ⟨_, E.blockAt_of_store_known cfg ext hr⟩
      refine ⟨?_⟩
      rwa [hgu]
  by_cases htargetAnchor : target = anchor
  · refine ⟨?_, Or.inl htargetAnchor⟩
    change Nonempty (CertifiedJustified cfg E anchor target)
    rw [htargetAnchor]
    exact ⟨CertifiedJustified.anchor⟩
  · have hvotes : ∀ i ∈ signers,
        Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i deadline target) := by
      intro i hiSigner
      simp only [signers, Execution.currentTargetA32Signers,
        Finset.mem_union] at hiSigner
      rcases hiSigner with hiObserved | hiFuture
      · simpa only [store, target, deadline] using
          E.currentTargetObservedHonestSupporter_vote_of_ffgState
            cfg ext hA0 hboundary hcoh hv hnH hiObserved
      · simpa only [store, target, deadline] using
          E.currentTargetFutureHonestSeat_vote cfg ext hhb hendH
            hsupport hiFuture
    have hsignersHonest : signers ⊆ E.honest := by
      intro i hi
      obtain ⟨vote⟩ := hvotes i hi
      exact vote.honest
    have hsignersEpoch : signers ⊆
        E.span_committee (target.epoch * cfg.slots_per_epoch)
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
      intro i hi
      obtain ⟨vote⟩ := hvotes i hi
      have hdivEpoch : vote.slot / cfg.slots_per_epoch = target.epoch := by
        simpa only [compute_epoch_at_slot] using vote.slot_epoch
      have hlo : target.epoch * cfg.slots_per_epoch ≤ vote.slot := by
        have h := Nat.div_mul_le_self vote.slot cfg.slots_per_epoch
        rwa [hdivEpoch] at h
      have hlt : vote.slot <
          target.epoch * cfg.slots_per_epoch + cfg.slots_per_epoch := by
        have h := Nat.lt_mul_div_succ vote.slot cfg.slots_per_epoch_pos
        rw [hdivEpoch, Nat.mul_add] at h
        simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
      have hhi : vote.slot ≤ target.epoch * cfg.slots_per_epoch +
          (cfg.slots_per_epoch - 1) := by
        have hpred := Nat.le_pred_of_lt hlt
        rw [Nat.pred_eq_sub_one,
          Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
        exact hpred
      simp only [Execution.span_committee, Finset.mem_biUnion]
      exact ⟨vote.slot, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, vote.assigned⟩
    have hprov := E.latestMessageProvenance cfg ext hA0.wellFormed hec
      hgen0 v n (by assumption) (by assumption)
    rw [← E.store_current_slot cfg ext v n] at hprov
    have hquorum : 2 * E.total_active cfg ≤ 3 * E.weight signers := by
      simpa only [signers, Execution.currentTargetA32Signers, store] using
        E.will_current_target_be_justified_honest_quorum cfg ext hhb hec hsv
          hbb hgen0 hv hnH hstate hval htab hendH hanchorH hfloor hprov hgate
    have hsignersNonempty : signers.Nonempty := by
      by_contra hnone
      have hempty : signers = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      have hzero : 2 * E.total_active cfg ≤ 0 := by
        simpa only [hempty, Execution.weight, Finset.sum_empty,
          Nat.mul_zero] using hquorum
      exact (Nat.not_lt_of_ge hzero)
        (Nat.mul_pos (by omega) (E.total_active_pos cfg))
    have hanchorBefore : anchor.epoch < target.epoch := by
      by_cases heqUJ : target = store.unrealized_justified_checkpoint
      · obtain ⟨hcertified⟩ := hcertifiedUJ
        have htargetCertified : CertifiedJustified cfg E anchor target := by
          rwa [heqUJ]
        exact CertifiedJustified.anchor_epoch_lt_of_ne
          (cfg := cfg) htargetCertified htargetAnchor
      · simpa only [target, store] using
          E.currentTarget_anchor_epoch_lt_of_ne_unrealized cfg ext hA0
            hboundary hcoh hanchor hv hnH heqUJ
    have hqueryHeadKnown : (get_head cfg store).root ∈ store.block_roots := by
      rcases get_head_root_mem_or cfg store with hhead | hhead
      · exact hhead
      · rw [hhead]
        exact hknown v hv n hnH
    have hqueryBoundaryWalk : WalkKnown store
        (compute_start_slot_at_epoch cfg target.epoch)
        (get_head cfg store).root := by
      simpa only [store] using
        E.walkKnown_epochBoundary_of_anchor_le cfg ext hA0 hboundary hanchor
          hqueryHeadKnown hanchorBefore.le
    have hqueryParentSlots : ParentSlotLt store := by
      simpa only [store] using
        E.store_parentSlotLt cfg ext hA0.wellFormed hec hA0.genesis
          hA0.wellFormed.anchor_parent_unscheduled v n
    have hqueryTargetSpec : target.root ∈ store.block_roots ∧
        (store.blocks target.root).slot ≤
          compute_start_slot_at_epoch cfg target.epoch := by
      have hspec := get_ancestor_spec hqueryParentSlots hqueryBoundaryWalk
      simpa only [target, store, get_current_target, get_checkpoint_for_block,
        get_checkpoint_block] using hspec
    have hvoteCore : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          WellFormedStoreCore (E.store cfg ext j vj.time) := by
      intro j _hj vj
      exact E.store_wellFormedStoreCore cfg ext
        hec.state_transition_slot hgws.core j vj.time
    have hvoteParentSlots : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          ParentSlotLt (E.store cfg ext j vj.time) := by
      intro j _hj vj
      exact E.store_parentSlotLt cfg ext hA0.wellFormed hec hA0.genesis
        hA0.wellFormed.anchor_parent_unscheduled j vj.time
    have hvoteStartLe : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          E.slot_at cfg 0 ≤ vj.slot := by
      intro j _hj vj
      have hzeroEpochLt : compute_epoch_at_slot cfg (E.slot_at cfg 0) <
          target.epoch := by
        rw [← hanchorEpoch0]
        exact hanchorBefore
      have hzeroBelow : E.slot_at cfg 0 <
          compute_start_slot_at_epoch cfg target.epoch :=
        slot_lt_epoch_start_of_epoch_lt cfg hzeroEpochLt
      have hvoteBoundaryLe : compute_start_slot_at_epoch cfg target.epoch ≤
          vj.slot := by
        have hlo := Nat.div_mul_le_self vj.slot cfg.slots_per_epoch
        have hepoch : vj.slot / cfg.slots_per_epoch = target.epoch := by
          simpa only [compute_epoch_at_slot] using vj.slot_epoch
        rw [hepoch] at hlo
        simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlo
      exact hzeroBelow.le.trans hvoteBoundaryLe
    have hvoteWalk : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          WalkKnown (E.store cfg ext j vj.time)
            (compute_start_slot_at_epoch cfg target.epoch)
            (get_head cfg (E.store cfg ext j vj.time)).root := by
      intro j hj vj
      simpa only [vj.target_eq] using
        hwalkDomain j vj.honest vj.slot vj.time vj.index
          (hvoteStartLe j hj vj) vj.time_within_horizon
          vj.slot_at_time vj.vote
    have hvoteTargetSpec : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          target.root ∈ (E.store cfg ext j vj.time).block_roots ∧
            ((E.store cfg ext j vj.time).blocks target.root).slot ≤
              compute_start_slot_at_epoch cfg target.epoch := by
      intro j hj vj
      let voteStore := E.store cfg ext j vj.time
      let head := (get_head cfg voteStore).root
      have htargetData : (honest_attestation_data cfg ext voteStore
          vj.slot vj.index).target = target := by
        simpa only [honest_attestation_data_eq] using vj.target_eq
      have hroot : target.root =
          get_checkpoint_block cfg voteStore head target.epoch := by
        calc
          target.root =
              (honest_attestation_data cfg ext voteStore
                vj.slot vj.index).target.root :=
            congrArg Checkpoint.root htargetData.symm
          _ = get_checkpoint_block cfg voteStore head target.epoch := by
            rw [honest_attestation_data_target_root]
            exact congrArg (get_checkpoint_block cfg voteStore head)
              (congrArg Checkpoint.epoch htargetData)
      have hancestorRoot :
          (get_ancestor voteStore (ForkChoiceNode.mk head .pending)
            (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
        simpa only [get_checkpoint_block] using hroot.symm
      have hspec := get_ancestor_spec (hvoteParentSlots j hj vj)
        (hvoteWalk j hj vj)
      rw [hancestorRoot] at hspec
      exact hspec
    have hvoteCurrentNonGenesis : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          ∀ r ∈ (E.store cfg ext j vj.time).block_roots,
            get_block_epoch cfg (E.store cfg ext j vj.time) r = target.epoch →
              r ∉ E.genesis_store.block_roots := by
      intro j _hj vj r hr hcurrent hrGenesis
      have hrEq : r = ablk.root := by
        rw [hgeq] at hrGenesis
        simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
      subst r
      have hanchorBlock :
          (E.store cfg ext j vj.time).blocks ablk.root = ablk.message :=
        E.store_anchor_block cfg ext hA0.wellFormed hgeq j vj.time hr
      have hrootEpoch : get_block_epoch cfg
          (E.store cfg ext j vj.time) ablk.root = anchor.epoch := by
        simp only [get_block_epoch]
        rw [hanchorBlock, ← hgenSlot]
        simpa only [get_current_epoch] using hanchorEpoch.symm
      exact (Nat.ne_of_lt hanchorBefore) (hrootEpoch.symm.trans hcurrent)
    have hvoteHeadStateSlotLe : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          ((E.store cfg ext j vj.time).block_states
            (get_head cfg (E.store cfg ext j vj.time)).root).slot ≤
            vj.slot := by
      intro j hj vj
      have hheadKnown := (hvoteWalk j hj vj).root_mem
      calc
        ((E.store cfg ext j vj.time).block_states
            (get_head cfg (E.store cfg ext j vj.time)).root).slot =
            ((E.store cfg ext j vj.time).blocks
              (get_head cfg (E.store cfg ext j vj.time)).root).slot :=
          (hvoteCore j hj vj).2 _ hheadKnown
        _ ≤ get_current_slot cfg (E.store cfg ext j vj.time) :=
          E.store_blocks_slot_le_current cfg ext hdiv hgenTrajectory
            j vj.time _ hheadKnown
        _ = E.slot_at cfg vj.time := E.store_current_slot cfg ext j vj.time
        _ = vj.slot := vj.slot_at_time
    have hvoteSourceSelector : ∀ j ∈ signers,
        ∀ vj : ConcreteHonestTargetVoteBefore cfg ext E j deadline target,
          (honest_attestation_data cfg ext (E.store cfg ext j vj.time)
            vj.slot vj.index).source =
            S.VSAt cfg (E.store cfg ext j vj.time)
              target.root target.epoch := by
      intro j hj vj
      have htargetData : (honest_attestation_data cfg ext
          (E.store cfg ext j vj.time) vj.slot vj.index).target = target := by
        simpa only [honest_attestation_data_eq] using vj.target_eq
      exact E.honest_attestation_data_source_eq_vSAt_target cfg ext
        hhistory hphase hboundaryPhase hcoh vj.honest
        vj.time_within_horizon (hvoteCore j hj vj)
        (hvoteParentSlots j hj vj) vj.slot_epoch (hvoteWalk j hj vj)
        htargetData (hvoteHeadStateSlotLe j hj vj)
        (hvoteCurrentNonGenesis j hj vj)
    obtain ⟨i, hiSigner⟩ := hsignersNonempty
    obtain ⟨vote⟩ := hvotes i hiSigner
    let refStore := E.store cfg ext i vote.time
    let source := S.VSAt cfg refStore target.root target.epoch
    have hrefTargetSpec := hvoteTargetSpec i hiSigner vote
    have hrefQueryBlocks : refStore.blocks target.root =
        store.blocks target.root :=
      hA0.wellFormed.blocks_agree
        (E.blockProvenance cfg ext i vote.time)
        (E.blockProvenance cfg ext v n)
        hrefTargetSpec.1 hqueryTargetSpec.1
    have hrefQueryEpoch : get_block_epoch cfg refStore target.root =
        get_block_epoch cfg store target.root := by
      simp only [get_block_epoch]
      rw [hrefQueryBlocks]
    have hsourceQuerySelector : source =
        S.VSAt cfg store target.root target.epoch := by
      change S.VSAt cfg refStore target.root target.epoch =
        S.VSAt cfg store target.root target.epoch
      simp only [ChainFFGState.VSAt]
      rw [hrefQueryEpoch]
    have hrefTargetRoot : E.ExecutionRoot target.root :=
      ⟨_, E.blockAt_of_store_known cfg ext hrefTargetSpec.1⟩
    have hsourceAU : S.AU cfg target.root source := by
      by_cases hcurrent : get_block_epoch cfg refStore target.root = target.epoch
      · simpa only [source, ChainFFGState.VSAt, hcurrent, if_pos] using
          S.gj_AU cfg target.root hrefTargetRoot
      · simpa only [source, ChainFFGState.VSAt, hcurrent, if_neg] using
          S.gu_AU cfg target.root hrefTargetRoot
    have hsourceCertified : Nonempty
        (CertifiedJustified cfg E anchor source) := by
      by_cases hcurrent : get_block_epoch cfg refStore target.root = target.epoch
      · simpa only [source, ChainFFGState.VSAt, hcurrent, if_pos] using
          S.gj_certified cfg target.root hrefTargetRoot
      · simpa only [source, ChainFFGState.VSAt, hcurrent, if_neg] using
          S.gu_certified cfg target.root hrefTargetRoot
    have htargetBlockEpochLe : get_block_epoch cfg refStore target.root ≤
        target.epoch := by
      simp only [get_block_epoch, compute_epoch_at_slot]
      calc
        (refStore.blocks target.root).slot / cfg.slots_per_epoch ≤
            (compute_start_slot_at_epoch cfg target.epoch) /
              cfg.slots_per_epoch :=
          Nat.div_le_div_right hrefTargetSpec.2
        _ = target.epoch := by
          simp only [compute_start_slot_at_epoch,
            Nat.mul_div_left target.epoch cfg.slots_per_epoch_pos]
    have hsourceBefore : source.epoch < target.epoch := by
      by_cases hcurrent : get_block_epoch cfg refStore target.root = target.epoch
      · have hsourceEq : source = S.GJ target.root := by
          simp only [source, hcurrent, if_pos]
        rw [hsourceEq]
        rcases S.gj_anchor_or_before
            (E.blockAt_of_store_known cfg ext hrefTargetSpec.1) with
          hsourceAnchor | hbefore
        · rw [hsourceAnchor]
          exact hanchorBefore
        · exact hbefore.trans_eq hcurrent
      · have htargetOld : get_block_epoch cfg refStore target.root <
            target.epoch := Nat.lt_of_le_of_ne htargetBlockEpochLe hcurrent
        have hsourceEq : source = S.GU target.root := by
          simp [source, ChainFFGState.VSAt, hcurrent]
        rw [hsourceEq]
        exact (S.au_epoch_le_block
          (E.blockAt_of_store_known cfg ext hrefTargetSpec.1)
          (S.gu_mem target.root hrefTargetRoot)).trans_lt htargetOld
    have hanchorLeSource : anchor.epoch ≤ source.epoch := by
      obtain ⟨hcert⟩ := hsourceCertified
      exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
    have hsourceWalk := E.walkKnown_epochBoundary_of_anchor_le cfg ext hA0
      hboundary hanchor hrefTargetSpec.1 hanchorLeSource
    have htargetWalk : WalkKnown refStore
        (compute_start_slot_at_epoch cfg target.epoch) target.root :=
      .stop hrefTargetSpec.1 hrefTargetSpec.2
    have hsourceCheckpoint := hcoh.au_checkpoint_of_known i vote.honest
      vote.time vote.time_within_horizon target.root hrefTargetSpec.1
      source hsourceAU
    have htargetCheckpoint : target = get_checkpoint_for_block cfg
        refStore target.root target.epoch := by
      refine checkpoint_eq_of_epoch_root_eq
        (a := target)
        (b := get_checkpoint_for_block cfg refStore target.root target.epoch)
        rfl ?_
      simp only [get_checkpoint_for_block, get_checkpoint_block]
      rw [get_ancestor_stop hrefTargetSpec.2]
    have htargetDescendsSource : E.RootDescends target.root source.root := by
      have hdesc := E.checkpointBlock_rootDescends cfg ext hA0
        hsourceBefore hsourceWalk htargetWalk
      have hsourceRoot : source.root = get_checkpoint_block cfg
          refStore target.root source.epoch := by
        simpa only [get_checkpoint_for_block] using
          congrArg Checkpoint.root hsourceCheckpoint
      have htargetRoot : target.root = get_checkpoint_block cfg
          refStore target.root target.epoch := by
        simpa only [get_checkpoint_for_block] using
          congrArg Checkpoint.root htargetCheckpoint
      rw [← hsourceRoot, ← htargetRoot] at hdesc
      exact hdesc
    have hsourceAgreement : CurrentTargetSourceAgreement cfg ext E signers
        deadline source target := by
      intro j hj vj
      have hjTargetSpec := hvoteTargetSpec j hj vj
      have hblocks : refStore.blocks target.root =
          (E.store cfg ext j vj.time).blocks target.root :=
        hA0.wellFormed.blocks_agree
          (E.blockProvenance cfg ext i vote.time)
          (E.blockProvenance cfg ext j vj.time)
          hrefTargetSpec.1 hjTargetSpec.1
      have hepochs : get_block_epoch cfg refStore target.root =
          get_block_epoch cfg (E.store cfg ext j vj.time) target.root := by
        simp only [get_block_epoch]
        rw [hblocks]
      have hselector : S.VSAt cfg (E.store cfg ext j vj.time)
          target.root target.epoch = source := by
        change S.VSAt cfg (E.store cfg ext j vj.time)
            target.root target.epoch =
          S.VSAt cfg refStore target.root target.epoch
        simp only [ChainFFGState.VSAt]
        rw [← hepochs]
      simpa only [honest_attestation_data_eq] using
        (hvoteSourceSelector j hj vj).trans hselector
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
    have hlink : SupermajorityLink cfg E source target := {
      signers := signers
      source_before_target := hsourceBefore
      target_descends_source := htargetDescendsSource
      target_epoch_within := htargetEpochWithin
      target_span_within := htargetSpan
      signers_in_epoch := hsignersEpoch
      signer_attestation := by
        intro j hj
        obtain ⟨vj⟩ := hvotes j hj
        let a := honest_attestation cfg ext
          (E.store cfg ext j vj.time) vj.slot vj.index j
        have hdeliveryLe : E.slot_start cfg (vj.slot + 1) ≤
            E.slot_start cfg deadline :=
          E.slot_start_mono cfg (Nat.succ_le_of_lt vj.before_deadline)
        have hdeliveryH : E.WithinHorizon cfg
            (E.slot_start cfg (vj.slot + 1)) :=
          E.withinHorizon_mono cfg hdeliveryLe hnextH
        refine ⟨j, E.slot_start cfg (vj.slot + 1), a, false, ?_, ?_, ?_, ?_⟩
        · exact hsync.toHorizonScopedDelivery cfg ext j vj.honest vj.slot vj.time a
            vj.slot_within_horizon vj.time_within_horizon
            (by simpa only [a] using vj.vote) hdeliveryH j vj.honest
        · simp only [a, honest_attestation_attesting_indices,
            List.mem_singleton]
        · simpa only [a] using hsourceAgreement j hj vj
        · simpa only [a] using vj.target_eq
      supermajority := hquorum }
    let Q : ConcreteA32QuorumBefore cfg ext E deadline target := {
      source := source
      signers := signers
      votes := hvotes
      source_agreement := hsourceAgreement
      supermajority := hquorum
      source_before_target := hsourceBefore
      target_epoch_within := htargetEpochWithin }
    obtain ⟨hsourceCert⟩ := hsourceCertified
    refine ⟨⟨CertifiedJustified.link hsourceCert hlink⟩,
      Or.inr ⟨htargetAnchor, ?_⟩⟩
    refine ⟨Q, ?_⟩
    simpa only [Q] using hsourceQuerySelector

/-- Retie the gate's target-local selector to the original current-epoch
carrier.  Knownness, head ancestry, and the carrier's current-epoch equation
are ordinary selected-call geometry; the concrete votes and their common
source remain entirely internal to `hgateRealization`. -/
theorem CurrentTargetA32GateRealization.fixedSource_of_currentEpochAncestor
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    {b : Root}
    (hbKnown : b ∈ (E.store cfg ext v n).block_roots)
    (hheadB : is_ancestor (E.store cfg ext v n)
      (get_head cfg (E.store cfg ext v n)) (get_node_for_root b) = true)
    (hbEpoch : get_block_epoch cfg (E.store cfg ext v n) b =
      get_current_store_epoch cfg (E.store cfg ext v n))
    (hgateRealization : CurrentTargetA32GateRealization cfg ext E anchor S
      (E.store cfg ext v n)) :
    FixedSourceCurrentTargetA32GateRealization cfg ext E anchor S
      (E.store cfg ext v n) b := by
  classical
  let store := E.store cfg ext v n
  let target := get_current_target cfg store
  have hA0 := hA
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hec, _hsv, _hbb, hknown⟩ := hA
  obtain ⟨ast, ablk, hgeq, hgenSlot, hparent⟩ := hgen
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot hparent
  refine ⟨hgateRealization.certified, ?_⟩
  rcases hgateRealization.support_branch with htargetAnchor |
      ⟨htargetNotAnchor, Q, hQSource⟩
  · exact Or.inl htargetAnchor
  · refine Or.inr ⟨htargetNotAnchor, Q, ?_⟩
    have hanchorBefore : anchor.epoch < target.epoch := by
      obtain ⟨hcertified⟩ := hgateRealization.certified
      exact CertifiedJustified.anchor_epoch_lt_of_ne
        (cfg := cfg) hcertified htargetNotAnchor
    have hheadKnown : (get_head cfg store).root ∈ store.block_roots := by
      rcases get_head_root_mem_or cfg store with hhead | hhead
      · exact hhead
      · rw [hhead]
        exact hknown v hv n hnH
    have hparentSlots : ParentSlotLt store := by
      simpa only [store] using
        E.store_parentSlotLt cfg ext hwfE hec hA0.genesis
          hwfE.anchor_parent_unscheduled v n
    have hheadBoundaryWalk : WalkKnown store
        (compute_start_slot_at_epoch cfg target.epoch)
        (get_head cfg store).root := by
      simpa only [store] using
        E.walkKnown_epochBoundary_of_anchor_le cfg ext hA0 hboundary hanchor
          hheadKnown hanchorBefore.le
    have hbTargetEpoch : get_block_epoch cfg store b = target.epoch := by
      simpa only [store, target, get_current_target,
        get_checkpoint_for_block] using hbEpoch
    have hbBoundaryWalk : WalkKnown store
        (compute_start_slot_at_epoch cfg target.epoch) b := by
      simpa only [store] using
        E.walkKnown_epochBoundary_of_anchor_le cfg ext hA0 hboundary hanchor
          hbKnown hanchorBefore.le
    have htargetEq : target =
        get_checkpoint_for_block cfg store b
          (get_block_epoch cfg store b) := by
      simpa only [target, store] using
        current_target_eq_checkpoint_of_current_epoch_ancestor cfg
          hparentSlots hheadB hbEpoch hheadBoundaryWalk
    have htargetCheckpoint : get_checkpoint_for_block cfg store b
        target.epoch = target := by
      rw [← hbTargetEpoch]
      exact htargetEq.symm
    have hcore : WellFormedStoreCore store := by
      simpa only [store] using
        E.store_wellFormedStoreCore cfg ext
          hec.state_transition_slot hgws.core v n
    have hanchorEpoch : anchor.epoch = get_current_epoch cfg ast := by
      rw [hanchor, hgeq]
      rfl
    have hcurrentNonGenesis : ∀ r ∈ store.block_roots,
        get_block_epoch cfg store r = target.epoch →
        r ∉ E.genesis_store.block_roots := by
      intro r hr hcurrent hrGenesis
      have hrEq : r = ablk.root := by
        rw [hgeq] at hrGenesis
        simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
      subst r
      have hanchorBlock : store.blocks ablk.root = ablk.message := by
        simpa only [store] using
          E.store_anchor_block cfg ext hwfE hgeq v n hr
      have hrootEpoch : get_block_epoch cfg store ablk.root = anchor.epoch := by
        simp only [get_block_epoch]
        rw [hanchorBlock, ← hgenSlot]
        simpa only [get_current_epoch] using hanchorEpoch.symm
      exact (Nat.ne_of_lt hanchorBefore) (hrootEpoch.symm.trans hcurrent)
    have hselector :=
      E.vSAt_checkpoint_eq_vSAt_current_carrier cfg ext hhistory hphase
        hboundaryPhase hcoh hv hnH hcore hparentSlots hcurrentNonGenesis
        hbBoundaryWalk hbTargetEpoch htargetCheckpoint
    exact hQSource.trans hselector

/-- Package the state-semantics constructor without erasing its paper-facing
branch.  This is the public actual-call producer: the executable gate and its
normative support proviso produce either the trusted anchor or a concrete
quorum whose common source is proved to be the query-store `VSAt` selector.
In particular, equality with a non-anchor unrealized checkpoint remains in the
quorum arm. -/
theorem currentTargetA32GateRealizationProducerAt_of_stateSemantics
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {q : ℕ}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext query.store)
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg query.store))
    (hnextH : E.WithinHorizon cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg
        ((get_current_target cfg query.store).epoch + 1))))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg)) :
    E.CurrentTargetA32GateRealizationProducerAt cfg ext anchor S q query := by
  intro hgate hsupport
  rw [hquery] at hstate hendH hnextH hgate hsupport ⊢
  exact E.certifiedCurrentTarget_of_gate_and_stateSemantics cfg ext hA hsync
    hboundary hcoh hhistory hphase hboundaryPhase hanchor hv hqH hstate hval
    htab hendH hnextH hanchorH hfloor hgate hsupport

/-- Public actual-call producer at the fixed source required by paper A3.2.
The three carrier premises are the exact executable geometry of an original
selected current-epoch block.  All committee votes, signer weight, and source
agreement are constructed behind this interface. -/
theorem fixedSourceCurrentTargetA32GateRealizationProducerAt_of_stateSemantics
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {q : ℕ}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext query.store)
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg query.store))
    (hnextH : E.WithinHorizon cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg
        ((get_current_target cfg query.store).epoch + 1))))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    {b : Root}
    (hbKnown : b ∈ query.store.block_roots)
    (hheadB : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root b) = true)
    (hbEpoch : get_block_epoch cfg query.store b =
      get_current_store_epoch cfg query.store) :
    E.FixedSourceCurrentTargetA32GateRealizationProducerAt cfg ext
      anchor S q query b := by
  intro hgate hsupport
  have hrealization :=
    E.currentTargetA32GateRealizationProducerAt_of_stateSemantics cfg ext hA
      hsync hboundary hcoh hhistory hphase hboundaryPhase hanchor hv hqH
      hquery hstate hval htab hendH hnextH hanchorH hfloor hgate hsupport
  rw [hquery] at hbKnown hheadB hbEpoch hrealization ⊢
  exact CurrentTargetA32GateRealization.fixedSource_of_currentEpochAncestor
    cfg ext E hA hboundary hcoh hhistory hphase hboundaryPhase hanchor
    hv hqH hbKnown hheadB hbEpoch hrealization


/-! ## Accepted causal-store current-epoch constructor -/

/-- Actual accepted source evidence for every concrete vote in an intermediate
current-target quorum.  Each vote retains its causal/global source carrier,
and its head is connected to the target root only through accepted
same-epoch transitions.  This is an intermediate proof object, not an input to
the final actual-call producer. -/
def AcceptedConcreteA32QuorumSourceGeometry
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (common : Root) : Prop :=
  ∀ i ∈ Q.signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      AcceptedHonestSourceEvidence B.state
          (E.store cfg ext i vote.time) vote.slot vote.index ∧
        AcceptedProjectedSameEpochSegment cfg ext E B.state common
          (get_head cfg (E.store cfg ext i vote.time)).root

/-- Internal accepted constructor for the current-epoch branch of the
current-target gate.

The target certificate is an output: the theorem obtains the certified source
and target-to-source descent from the target's named accepted `GJ` formed
carrier, turns the concrete quorum's ground votes into one scheduled
supermajority link, and extends the source certificate by that link.  The
old-head/cross-epoch `GU` branch is deliberately absent; it requires
`Phase0BoundarySourceCoherence` and a separate accepted boundary-source
trajectory.

`Q` and `hgeometry` are intentionally intermediate.  Reverse exact-prefix
transition provenance is the remaining prerequisite for constructing them
from `hgate` and `HonestVotesSupportTarget`; they are not advertised as final
actual-call inputs. -/
theorem acceptedCurrentTargetA32GateRealization_of_currentEpochConcreteQuorum_core
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (htargetKnown : (get_current_target cfg store).root ∈ store.block_roots)
    (htargetEpoch : get_block_epoch cfg store
      (get_current_target cfg store).root =
        (get_current_target cfg store).epoch)
    (htargetNotAnchor : get_current_target cfg store ≠ B.anchor)
    (hanchorBefore : B.anchor.epoch < (get_current_target cfg store).epoch)
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
    (hgeometry : AcceptedConcreteA32QuorumSourceGeometry cfg ext E B Q
      (get_current_target cfg store).root) :
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      store := by
  classical
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  change get_block_epoch cfg store target.root = target.epoch at htargetEpoch
  change target ≠ B.anchor at htargetNotAnchor
  change B.anchor.epoch < target.epoch at hanchorBefore
  change ConcreteA32QuorumBefore cfg ext E deadline target at Q
  change ConcreteA32QuorumScheduledDelivery cfg ext E Q at hdelivery
  change AcceptedConcreteA32QuorumSourceGeometry cfg ext E B Q target.root
    at hgeometry
  have htargetAt : E.AcceptedBlockAt cfg ext target.root
      (store.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore htargetKnown
  have htargetCarrier : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) store target.root :=
    Execution.AcceptedCarrierIn.of_causal_known hstore htargetKnown
  obtain ⟨formedCarrier, htargetDescendsCarrier, hformed⟩ :=
    B.state.gj_mem target.root htargetCarrier.acceptedRoot
  let hsourceCarrier : AcceptedSelectorAUCarrier B.state store
      (B.state.GJ target.root) :=
    { tip := target.root
      carrier := formedCarrier
      tip_carrier := htargetCarrier
      au := ⟨formedCarrier, htargetDescendsCarrier, hformed⟩
      tip_descends_carrier := htargetDescendsCarrier
      carrier_accepted := B.state.formed_carrier_accepted hformed
      formed_evidence := B.state.formed_evidence hformed }
  have hsignersNonempty : Q.signers.Nonempty := by
    by_contra hnone
    have hempty : Q.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * E.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using Q.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega) (E.total_active_pos cfg))
  obtain ⟨i, hi⟩ := hsignersNonempty
  obtain ⟨vote⟩ := Q.votes i hi
  obtain ⟨hsourceEvidence, hsegment⟩ := hgeometry i hi vote
  have hvoteSource :
      (honest_attestation_data cfg ext (E.store cfg ext i vote.time)
        vote.slot vote.index).source = Q.source := by
    simpa only [honest_attestation_data_eq] using
      Q.source_agreement i hi vote
  have hQSource : Q.source = B.state.GJ target.root := by
    exact hvoteSource.symm.trans
      (hsourceEvidence.source_eq.trans
        (hsegment.gj_eq_first hphase
          B.coherence.toAcceptedFFGSelectorCoherence))
  have hsourceCertifiedGJ : Nonempty
      (CertifiedJustified cfg E B.anchor (B.state.GJ target.root)) := by
    obtain ⟨hincluded⟩ := hsourceCarrier.formed_evidence.certified
    exact ⟨IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg) B.state.includedAttestations.relation hincluded⟩
  have hsourceCertified : Nonempty
      (CertifiedJustified cfg E B.anchor Q.source) := by
    rw [hQSource]
    exact hsourceCertifiedGJ
  have htargetDescendsSource : E.RootDescends target.root Q.source.root := by
    rw [hQSource]
    exact Execution.RootDescends.trans E hsourceCarrier.tip_descends_carrier
      hsourceCarrier.formed_evidence.on_chain
  have htargetBlockEpoch : compute_epoch_at_slot cfg
      (store.blocks target.root).slot = target.epoch := by
    simpa only [get_block_epoch] using htargetEpoch
  have hsourceBeforeGJ :
      (B.state.GJ target.root).epoch < target.epoch := by
    rcases B.state.gj_anchor_or_before htargetAt with hsourceAnchor | hbefore
    · rw [hsourceAnchor]
      exact hanchorBefore
    · exact hbefore.trans_eq htargetBlockEpoch
  have hsourceBefore : Q.source.epoch < target.epoch := by
    rw [hQSource]
    exact hsourceBeforeGJ
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
  change Q.source = B.state.VSAt cfg ext store target.root target.epoch
  simpa only [AcceptedChainFFGState.VSAt, PaperA32StateView.VSAt,
    htargetEpoch, if_pos] using hQSource



/-- Explicitly labeled erasure consumer.  Once the remaining gate-to-Q
obligation supplies an accepted gate producer, the existing crossing pipeline
receives exactly the target certificate and no migration state. -/
theorem acceptedCurrentTargetCertificateProducerAt_of_gateProducer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {q : ℕ} {query : FastConfirmationStore Root}
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query) :
    E.CurrentTargetCertificateProducerAt cfg ext B.anchor q query := by
  intro hgate hsupport
  exact (hproducer hgate hsupport).certified

end Execution

/-! ## Joint non-vacuity of the two phase0 source laws -/

namespace CurrentTargetCertificateRealizationNonvacuity





















end CurrentTargetCertificateRealizationNonvacuity

end FastConfirmation.Spec

end
