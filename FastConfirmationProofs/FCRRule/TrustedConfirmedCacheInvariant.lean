module
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem acceptedAnchorExact_of_trustedTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    B.anchor = B.state.C B.anchor.root B.anchor.epoch := by
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary 0 0
  have hreflect : B.state.C B.anchor.root B.anchor.epoch =
      get_checkpoint_for_block cfg E.genesis_store
        B.anchor.root B.anchor.epoch :=
    B.coherence.checkpoint_of_known (.genesis)
      B.anchor.root hreal.root_known B.anchor.epoch
  have htrusted := E.trustedAnchor_checkpointForBlock_of_trajectory
    cfg ext hT hanchor hboundary
  have hepoch : get_block_epoch cfg E.genesis_store B.anchor.root =
      B.anchor.epoch := by
    have := congrArg Checkpoint.epoch htrusted
    simpa only [get_checkpoint_for_block] using this
  symm
  calc
    B.state.C B.anchor.root B.anchor.epoch =
        get_checkpoint_for_block cfg E.genesis_store
          B.anchor.root B.anchor.epoch := hreflect
    _ = get_checkpoint_for_block cfg E.genesis_store B.anchor.root
          (get_block_epoch cfg E.genesis_store B.anchor.root) := by rw [hepoch]
    _ = B.anchor := htrusted


end Execution
end FastConfirmation.Spec
end
