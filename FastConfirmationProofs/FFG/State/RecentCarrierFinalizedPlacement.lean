module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.State.DynamicFinalizedPlacement
public import FastConfirmationProofs.FFG.State.PathLocalFinalizedTransport
public import FastConfirmationProofs.FFG.State.FinalizationTiming
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Finalized placement for an early recent-source carrier

The early selected-result cells retain a source whose epoch is at most two
epochs behind the endpoint clock.  The accepted state-transition boundary
independently gives the same two-epoch upper bound for every non-anchor
realized finalized checkpoint.  Combining those two inequalities places the
finalized epoch below the retained source epoch.  Exact accepted checkpoint
accountability can then reflect finality on the retained tip itself.

This is deliberately separate from the historical A3.2 lineage.  In
particular, an epoch-boundary previous result need not manufacture a
historical payload merely to discharge the early endpoint's finalized filter
check.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

namespace AcceptedRetainedPhaseSourceCarrierAt

/-- A recent accepted source carrier satisfies the exact finalized-tip check
under the faithful causal two-epoch finalization lag.

The anchor branch is the ordinary exact-prefix base.  In the non-anchor
branch, `F + 2 <= current <= source + 2` gives `F <= source`; the carrier's
positive AU evidence then supplies the included upper checkpoint required by
cross-certificate accountability.  No lineage, source visibility, filter
membership, selected safety, or finalized-placement premise occurs. -/
theorem finalizedRoot_eq_checkpointBlock_of_causalLag
    {B : CausalPrefixFFGInterpretation cfg ext E}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {store : Store Root} {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt
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
      E.finalizedCheckpoint_twoEpochLag_of_causalLag cfg ext hLag
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
    let hdynamic : AcceptedDynamicFinalizedPlacementAt
        cfg ext B.state store h.tip :=
      { tip_known := h.tip_known
        tip_accepted := htipAccepted
        target := ⟨get_voting_source cfg store h.tip,
          hselector, h.source_au,
          B.state.includedJustifiedAtTip_of_AU cfg ext h.source_au,
          hfinalizedLeSource⟩ }
    exact hdynamic.finalizedRoot_eq_checkpointBlock_at_tip cfg ext B hgen
      hanchor P V hanchorExact hacc h.store_causal hparent hwalk

end AcceptedRetainedPhaseSourceCarrierAt

end Execution


end FastConfirmation.Spec

end
