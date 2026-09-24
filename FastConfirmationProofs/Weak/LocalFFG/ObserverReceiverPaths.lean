module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFinalizedSafety
public import FastConfirmationProofs.Checkpoints.HonestVotePathAdmissibility

/-! Checkpoint-compatible paths use concrete stores and their common walks.
These operational adapters do not require a global FFG interpretation.
-/

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root}

/-- Concrete checkpoint agreement rules out permanent exclusion. -/
theorem checkpointCompatible_not_permanentlyExcluded_of_trajectory
    {anchor : Checkpoint Root}
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v w : ValidatorIndex} {n m : ℕ} {r : Root}
    (hHm : E.WithinHorizon cfg m)
    (hsourceKnown : r ∈ (E.store cfg ext v n).block_roots)
    (hfinalizedKnown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : anchor.epoch ≤
      (E.store cfg ext w m).finalized_checkpoint.epoch)
    (hcheckpoint : (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext v n) r
        (E.store cfg ext w m).finalized_checkpoint.epoch)
    (hexcluded : PermanentBlockExclusion cfg ext E v n r w m) : False := by
  let source := E.store cfg ext v n
  let receiver := E.store cfg ext w m
  let F := receiver.finalized_checkpoint
  let parent := (source.blocks r).parent_root
  by_cases hbefore : (source.blocks r).slot ≤
      compute_start_slot_at_epoch cfg F.epoch
  · have hroot : F.root = r := by
      rw [hcheckpoint]
      simp only [get_checkpoint_block]
      rw [get_ancestor_stop hbefore]
    exact hexcluded.1 (by rw [← hroot]; exact hfinalizedKnown)
  have hafter : compute_start_slot_at_epoch cfg F.epoch <
      (source.blocks r).slot := Nat.lt_of_not_ge hbefore
  obtain ⟨ast, ablk, hgen, hgenSlot, _hcommit, hgenParent⟩ := hT.genesis
  have hsourceParent : parent ∈ source.block_roots := by
    have hnonAnchor := E.store_nonAnchorParentKnown cfg ext hgen v n r
      hsourceKnown
    rcases hnonAnchor with hanchorRoot | hparentKnown
    · have hanchorKnown0 : ablk.root ∈ E.genesis_store.block_roots := by
        rw [hgen]
        simp only [get_forkchoice_store, List.mem_singleton]
      have hanchorKnownReceiver : ablk.root ∈ receiver.block_roots :=
        (E.store_storeLE cfg ext w (Nat.zero_le m)).1
          (by simpa only [show E.store cfg ext w 0 = E.genesis_store from rfl]
              using hanchorKnown0)
      exact False.elim (hexcluded.1 (by
        rw [hanchorRoot]
        exact hanchorKnownReceiver))
    · exact hparentKnown
  have hreceiverParent : parent ∈ receiver.block_roots := hexcluded.2.1
  have hparentSlotSource : ParentSlotLt source :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled v n
  have hparentWalk : WalkKnown source
      (compute_start_slot_at_epoch cfg F.epoch) parent :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT hanchor hboundary
      v n hanchorLe hsourceParent
  have hparentCheckpoint : F.root =
      get_checkpoint_block cfg receiver parent F.epoch := by
    calc
      F.root = get_checkpoint_block cfg source r F.epoch := hcheckpoint
      _ = get_checkpoint_block cfg source parent F.epoch := by
        simpa only [source, parent, get_checkpoint_block] using
          get_ancestor_step hparentSlotSource hsourceKnown hafter hparentWalk
      _ = get_checkpoint_block cfg receiver parent F.epoch := by
        have hagree : ∀ x, x ∈ source.block_roots → x ∈ receiver.block_roots →
            source.blocks x = receiver.blocks x := fun x hs hr =>
          hT.wellFormed.blocks_agree (E.blockProvenance cfg ext v n)
            (E.blockProvenance cfg ext w m) hs hr
        have hreceiverWalk := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory
          cfg ext hT hanchor hboundary w m hanchorLe hreceiverParent
        exact congrArg ForkChoiceNode.root
          (get_ancestor_congr_common_walk hagree hparentWalk hreceiverWalk)
  exact (E.permanentBlockExclusion_false_of_finalized_guards cfg ext
    hHm hafter hparentCheckpoint) hexcluded


theorem votePathAdmissible_of_checkpointCompatible_of_trajectory
    {anchor : Checkpoint Root}
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v w : ValidatorIndex} {n m : ℕ} {slot : Slot} {r : Root}
    (hHm : E.WithinHorizon cfg m)
    (hFknown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : anchor.epoch ≤
      (E.store cfg ext w m).finalized_checkpoint.epoch)
    (hwalk : WalkKnown (E.store cfg ext v n) slot r)
    (hcheckpoint : (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext v n) r
        (E.store cfg ext w m).finalized_checkpoint.epoch) :
    VotePathAdmissible cfg ext E v n w m slot r := by
  have hparent : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled v n
  induction hwalk with
  | stop hr hle =>
      exact .stop hr
        (E.checkpointCompatible_not_permanentlyExcluded_of_trajectory cfg ext hT
          hanchor hboundary hHm hr hFknown hanchorLe hcheckpoint) hle
  | @step r hr hgt hp ih =>
      by_cases hbefore : ((E.store cfg ext v n).blocks r).slot ≤
          compute_start_slot_at_epoch cfg
            (E.store cfg ext w m).finalized_checkpoint.epoch
      · have hroot : (E.store cfg ext w m).finalized_checkpoint.root = r := by
          simpa only [get_checkpoint_block, get_ancestor_stop hbefore] using hcheckpoint
        exact E.votePathAdmissible_of_receiver_known cfg ext hT
          (.step hr hgt hp) (hroot ▸ hFknown)
      · have hparentWalk := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
          hanchor hboundary v n hanchorLe hp.root_mem
        have hstep : get_checkpoint_block cfg (E.store cfg ext v n) r
            (E.store cfg ext w m).finalized_checkpoint.epoch =
            get_checkpoint_block cfg (E.store cfg ext v n)
              ((E.store cfg ext v n).blocks r).parent_root
              (E.store cfg ext w m).finalized_checkpoint.epoch := by
          exact get_ancestor_step hparent hr
            (Nat.lt_of_not_ge hbefore) hparentWalk
        exact .step hr
          (E.checkpointCompatible_not_permanentlyExcluded_of_trajectory cfg ext hT
            hanchor hboundary hHm hr hFknown hanchorLe hcheckpoint)
          hgt (ih (hcheckpoint.trans hstep))

/-- A path below a checkpoint-compatible tip is admissible. If its head is
older than the checkpoint boundary, it is an ancestor of the finalized root
and is already known at the receiver. This covers reused checkpoint roots. -/
theorem votePathAdmissible_of_checkpointCompatible_descendant_of_trajectory
    {anchor : Checkpoint Root}
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v w : ValidatorIndex} {n m : ℕ} {slot : Slot} {r tip : Root}
    (hHm : E.WithinHorizon cfg m)
    (hFknown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : anchor.epoch ≤
      (E.store cfg ext w m).finalized_checkpoint.epoch)
    (hwalk : WalkKnown (E.store cfg ext v n) slot r)
    (htip : tip ∈ (E.store cfg ext v n).block_roots)
    (hdesc : is_ancestor (E.store cfg ext v n)
      (get_node_for_root tip) (get_node_for_root r) = true)
    (hcheckpoint : (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext v n) tip
        (E.store cfg ext w m).finalized_checkpoint.epoch) :
    VotePathAdmissible cfg ext E v n w m slot r := by
  let source := E.store cfg ext v n
  let F := (E.store cfg ext w m).finalized_checkpoint
  have hp : ParentSlotLt source := E.store_parentSlotLt cfg ext hT.wellFormed
    hT.externals_coherence hT.genesis_structure
    hT.wellFormed.anchor_parent_unscheduled v n
  have htipF := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT hanchor hboundary
    v n hanchorLe htip
  by_cases hafter : compute_start_slot_at_epoch cfg F.epoch ≤ (source.blocks r).slot
  · apply E.votePathAdmissible_of_checkpointCompatible_of_trajectory cfg ext hT hanchor
      hboundary hHm hFknown hanchorLe hwalk
    exact hcheckpoint.trans (get_checkpoint_block_of_ancestor cfg hp hdesc hafter htipF)
  · have htipR : WalkKnown source (source.blocks r).slot tip :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        hT.genesis_structure v n r hwalk.root_mem tip htip
    have hlands : (get_ancestor source (get_node_for_root tip)
        (source.blocks r).slot).root = r := by
      simpa only [is_ancestor_pending, get_node_for_root, decide_eq_true_eq] using hdesc
    have hFsource : F.root ∈ source.block_roots := by
      rw [hcheckpoint]
      exact (get_ancestor_spec hp htipF).1
    have hFlands : (get_ancestor source (get_node_for_root F.root)
        (source.blocks r).slot).root = r := by
      rw [hcheckpoint]
      exact (get_ancestor_comp_root hp (Nat.le_of_lt (Nat.lt_of_not_ge hafter)) htipR).trans hlands
    have hFdesc : E.RootDescends F.root r :=
      E.rootDescends_of_getAncestor (E.blockProvenance cfg ext v n) hp
        (E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
          hT.genesis_structure v n r hwalk.root_mem F.root hFsource) hFlands
    obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
    have hrRoot : E.ExecutionRoot r :=
      ⟨source.blocks r, E.blockAt_of_store_known cfg ext hwalk.root_mem⟩
    have hrKnown := (E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hT.wellFormed hT.externals_coherence hgen hslot hparent
      hFknown hrRoot hFdesc).1
    exact E.votePathAdmissible_of_receiver_known cfg ext hT hwalk hrKnown

end Execution
end FastConfirmation.Spec
end
