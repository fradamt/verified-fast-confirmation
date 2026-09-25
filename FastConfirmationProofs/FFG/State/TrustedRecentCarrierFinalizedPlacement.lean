module
public import FastConfirmationProofs.FFG.State.RecentCarrierFinalizedPlacement
public import FastConfirmationProofs.FFG.State.TrustedDynamicFinalizedPlacement
public import FastConfirmationProofs.FFG.State.TrustedPathLocalFinalizedTransport
public import FastConfirmationProofs.FFG.State.TrustedFinalizationTiming

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
namespace TrustedAcceptedRetainedPhaseSourceCarrierAt
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem finalizedRoot_eq_checkpointBlock_of_causalLag
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hLag : E.TrustedCausalRealizedFinalizationLag cfg ext B)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {store : Store Root} {selected : Root}
    (h : E.TrustedAcceptedRetainedPhaseSourceCarrierAt
      cfg ext B store selected)
    (hfinalized : FinalizedBoundaryRealization cfg store)
    (hparent : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store h.tip
        store.finalized_checkpoint.epoch := by
  have hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg
        store.finalized_checkpoint.epoch) h.tip :=
    hfinalized.finalizedWalkKnown cfg hwalkK h.tip_known
  by_cases hfinalizedAnchor : store.finalized_checkpoint = B.anchor
  · exact h.finalizedRoot_eq_checkpointBlock_of_anchor cfg ext B P V
      hanchorExact hparent hfinalizedAnchor hwalk
  · have hfinalizedLag : store.finalized_checkpoint.epoch + 2 ≤
        get_current_store_epoch cfg store :=
      E.trustedFinalizedCheckpoint_twoEpochLag_of_causalLag cfg ext hLag
        h.store_causal hfinalizedAnchor
    have hfinalizedLeSource : store.finalized_checkpoint.epoch ≤
        (get_voting_source cfg store h.tip).epoch := by
      exact Nat.le_of_add_le_add_right
        (hfinalizedLag.trans h.source_recent)
    have htipAccepted : E.AcceptedRoot cfg ext h.tip :=
      E.acceptedRoot_of_causal_known cfg ext h.store_causal h.tip_known
    have hprojection :=
      (B.causalStoreGlobalProjection hgen hanchor h.store_causal).blockLocal
    have hselector : get_voting_source cfg store h.tip = B.state.GJ h.tip ∨
        get_voting_source cfg store h.tip = B.state.GU h.tip :=
      hprojection.getVotingSource_eq_gj_or_gu cfg ext h.tip_known
    let hdynamic : TrustedAcceptedDynamicFinalizedPlacementAt
        cfg ext B.state store h.tip :=
      { tip_known := h.tip_known
        tip_accepted := htipAccepted
        target := ⟨get_voting_source cfg store h.tip,
          hselector, h.source_au,
          B.state.includedJustifiedAtTip_of_AU cfg ext h.source_au,
          hfinalizedLeSource⟩ }
    exact hdynamic.finalizedRoot_eq_checkpointBlock_at_tip cfg ext B hgen
      hanchor P V hanchorExact hacc h.store_causal hparent hwalk

end TrustedAcceptedRetainedPhaseSourceCarrierAt
end Execution
end FastConfirmation.Spec
end
