module
public import FastConfirmationProofs.Checkpoints.DeadlineCheckpointRelay
public import FastConfirmationProofs.Checkpoints.DeadlineBlockAdmissibility
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_checkpointCompatible_not_permanentlyExcluded
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v w : ValidatorIndex} {n m : ℕ} {r : Root}
    (hHm : E.WithinHorizon cfg m)
    (hsourceKnown : r ∈ (E.store cfg ext v n).block_roots)
    (hfinalizedKnown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : B.anchor.epoch ≤
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
      _ = (B.state.C parent F.epoch).root := by
        rw [B.coherence.checkpoint_of_known
          (E.store_causal cfg ext v n) parent hsourceParent F.epoch]
        rfl
      _ = get_checkpoint_block cfg receiver parent F.epoch := by
        rw [B.coherence.checkpoint_of_known
          (E.store_causal cfg ext w m) parent hreceiverParent F.epoch]
        rfl
  exact (E.permanentBlockExclusion_false_of_finalized_guards cfg ext
    hHm hafter hparentCheckpoint) hexcluded

theorem trusted_deadline_root_known_of_checkpointCompatible
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v w : ValidatorIndex} {n m : ℕ} {r : Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (hr : r ∈ (E.store cfg ext v n).block_roots)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (hnext : E.slot_start cfg (E.slot_at cfg n + 1) ≤ m)
    (hlt : n < m)
    (hFknown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : B.anchor.epoch ≤
      (E.store cfg ext w m).finalized_checkpoint.epoch)
    (hcheckpoint : (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext v n) r
        (E.store cfg ext w m).finalized_checkpoint.epoch) :
    r ∈ (E.store cfg ext w m).block_roots := by
  rcases hrelay v hv n r hHn hr hdue
      w hw m hHm hnext hlt with hknown | hexcluded
  · exact hknown
  · by_cases hm : r ∈ (E.store cfg ext w m).block_roots
    · exact hm
    have hexcluded := E.permanentBlockExclusion_mono_of_not_mem cfg ext
      ((Nat.sub_le _ 1).trans hnext) hm hexcluded
    exact False.elim (E.trusted_checkpointCompatible_not_permanentlyExcluded
      cfg ext B hT hanchor hboundary hHm hr hFknown hanchorLe
      hcheckpoint hexcluded)

end Execution
end FastConfirmation.Spec
end
