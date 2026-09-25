module
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation
public import FastConfirmationProofs.FFG.SelectedSource.TrustedSelectedJustifiedOrientationRest
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness

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


theorem trustedAnchor_safeFrom_of_trustedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    E.SafeFrom cfg ext B.anchor.root 0 := by
  have hdomainK := E.trusted_storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  apply E.safeFrom_of_justified_dom_K cfg ext hdomainK
  intro w hw m _h0m hHm
  obtain ⟨_hparent, _hwalk, hjustifiedKnown⟩ := hdomainK w hw m hHm
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  obtain ⟨hjustified⟩ :=
    TrustedCausalPrefixFFGInterpretation.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  have hanchorRealized :=
    E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
      cfg ext hT hanchor hboundary w m
  have hanchorRoot : E.ExecutionRoot B.anchor.root :=
    ⟨(E.store cfg ext w m).blocks B.anchor.root,
      E.blockAt_of_store_known cfg ext hanchorRealized.root_known⟩
  exact E.store_known_ancestor_of_rootDescends_for_storeReflection
    cfg ext hT.wellFormed hT.externals_coherence hgen hslot hparent
      hjustifiedKnown hanchorRoot (hjustified.descends_anchor cfg)

end Execution
end FastConfirmation.Spec
end
