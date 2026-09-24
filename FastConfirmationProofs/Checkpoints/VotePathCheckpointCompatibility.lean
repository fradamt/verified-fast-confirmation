module
public import FastConfirmationProofs.Checkpoints.DeadlineCheckpointRelay
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationProofs.FFG.SelectedSource.FFGEndpointRealization
public import FastConfirmationProofs.Checkpoints.FinalizedBeforeVoteJustification

@[expose] public section

/-! Known or checkpoint-compatible roots have admissible vote ancestor paths. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- Every source-known ancestor of a root already known at the receiver is
also known there. The proof follows concrete parent edges, including paths
below the receiver's finalized checkpoint. -/
theorem votePathAdmissible_of_receiver_known
    (hT : E.ScheduledPrefixPremises cfg ext)
    {v w : ValidatorIndex} {n m : ℕ} {slot : Slot} {r : Root}
    (hwalk : WalkKnown (E.store cfg ext v n) slot r)
    (hknown : r ∈ (E.store cfg ext w m).block_roots) :
    VotePathAdmissible cfg ext E v n w m slot r := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  induction hwalk with
  | stop hr hle =>
      exact .stop hr (fun hex => hex.1 hknown) hle
  | @step r hr hgt hp ih =>
      apply VotePathAdmissible.step hr (fun hex => hex.1 hknown) hgt
      apply ih
      have hparentRoot : E.ExecutionRoot ((E.store cfg ext v n).blocks r).parent_root :=
        ⟨(E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root,
          E.blockAt_of_store_known cfg ext hp.root_mem⟩
      have hdesc : E.RootDescends r ((E.store cfg ext v n).blocks r).parent_root :=
        .step (E.parentEdge_of_store_known (E.blockProvenance cfg ext v n) hr)
          (.refl _)
      exact (E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
        hT.wellFormed hT.externals_coherence hgen hslot hparent
        hknown hparentRoot hdesc).1

/-- Exact checkpoint compatibility propagates down a vote path until the
walk reaches the receiver's finalized root. Its remaining ancestors are
already known at the receiver. This includes walks below the finalized epoch. -/
theorem votePathAdmissible_of_checkpointCompatible
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v w : ValidatorIndex} {n m : ℕ} {slot : Slot} {r : Root}
    (hHm : E.WithinHorizon cfg m)
    (hFknown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : B.anchor.epoch ≤
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
        (E.checkpointCompatible_not_permanentlyExcluded cfg ext B hA
          hanchor hboundary hHm hr hFknown hanchorLe hcheckpoint) hle
  | @step r hr hgt hp ih =>
      by_cases hbefore : ((E.store cfg ext v n).blocks r).slot ≤
          compute_start_slot_at_epoch cfg
            (E.store cfg ext w m).finalized_checkpoint.epoch
      · have hroot : (E.store cfg ext w m).finalized_checkpoint.root = r := by
          simpa only [get_checkpoint_block, get_ancestor_stop hbefore] using hcheckpoint
        exact E.votePathAdmissible_of_receiver_known cfg ext hT
          (.step hr hgt hp) (hroot ▸ hFknown)
      · have hparentWalk := E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA
          hanchor hboundary v n hanchorLe hp.root_mem
        have hstep : get_checkpoint_block cfg (E.store cfg ext v n) r
            (E.store cfg ext w m).finalized_checkpoint.epoch =
            get_checkpoint_block cfg (E.store cfg ext v n)
              ((E.store cfg ext v n).blocks r).parent_root
              (E.store cfg ext w m).finalized_checkpoint.epoch := by
          exact get_ancestor_step hparent hr
            (Nat.lt_of_not_ge hbefore) hparentWalk
        exact .step hr
          (E.checkpointCompatible_not_permanentlyExcluded cfg ext B hA
            hanchor hboundary hHm hr hFknown hanchorLe hcheckpoint)
          hgt (ih (hcheckpoint.trans hstep))

end Execution
end FastConfirmation.Spec

end
