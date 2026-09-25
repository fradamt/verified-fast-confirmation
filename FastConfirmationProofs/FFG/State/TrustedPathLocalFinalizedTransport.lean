module
public import FastConfirmationProofs.Checkpoints.GuardedExactCheckpointLinks
public import FastConfirmationProofs.FFG.State.PathLocalFinalizedTransport
public import FastConfirmationProofs.FFG.SelectedSource.TrustedPhaseSourceCarriers
public import FastConfirmationProofs.FFG.State.TrustedFinalizedSameTip

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
namespace TrustedAcceptedRetainedPhaseSourceCarrierAt
variable {trusted : Store Root → Prop}

theorem finalizedRoot_eq_checkpointBlock_of_anchor
    {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {store : Store Root} (hparent : ParentSlotLt store)
    {selected : Root}
    (h : E.TrustedAcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hfinalizedAnchor : store.finalized_checkpoint = B.anchor)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg
        store.finalized_checkpoint.epoch) h.tip) :
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store h.tip
        store.finalized_checkpoint.epoch := by
  obtain ⟨hsourceJustified⟩ :=
    B.state.includedJustifiedAtTip_of_AU cfg ext h.source_au
  have hprefix : ExactCheckpointPrefix B.state.C B.anchor
      (get_voting_source cfg store h.tip) :=
    IncludedCertifiedJustified.guarded_anchor_prefix
      (cfg := cfg) P V hanchorExact ⟨store, h.store_causal, h.tip_known⟩ hsourceJustified
  have hepoch : B.anchor.epoch ≤
      (get_voting_source cfg store h.tip).epoch :=
    IncludedCertifiedJustified.anchor_epoch_le
      (cfg := cfg) hsourceJustified
  have hwalkAnchor : WalkKnown store
      (compute_start_slot_at_epoch cfg B.anchor.epoch) h.tip := by
    simpa only [hfinalizedAnchor] using hwalk
  have hreflect : B.anchor.root =
      get_checkpoint_block cfg store h.tip B.anchor.epoch :=
    trusted_exactCheckpointPrefix_root_eq_at_sameTip cfg ext B.coherence
      h.store_causal hparent h.tip_known hprefix h.source_au hepoch
        hwalkAnchor
  simpa only [hfinalizedAnchor] using hreflect

end TrustedAcceptedRetainedPhaseSourceCarrierAt
end Execution
end FastConfirmation.Spec
end
