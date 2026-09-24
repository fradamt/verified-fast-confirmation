module
public import FastConfirmationProofs.Checkpoints.TrustedAnchorGeometry
public import FastConfirmationProofs.Execution.Delivery.VoteDeadlineOrigin

@[expose] public section

/-!
# Finalized-guard admissibility of a checkpoint-compatible block

This module proves that a block on the receiver's exact finalized checkpoint
chain cannot satisfy the permanent `on_block` exclusion. The block may be
unknown to the receiver, but its parent is known in the excluded case, so
causal checkpoint reflection compares the parent in both stores.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- A source block whose checkpoint at the receiver's finalized epoch is the
receiver's finalized root cannot be permanently excluded. The at-boundary
case is already stored as the finalized root; after the boundary, the known
parent has the same exact checkpoint in both causal stores. -/
theorem checkpointCompatible_not_permanentlyExcluded
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
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
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hA.genesis
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
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled v n
  have hparentWalk : WalkKnown source
      (compute_start_slot_at_epoch cfg F.epoch) parent :=
    E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
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

end Execution
end FastConfirmation.Spec

end
