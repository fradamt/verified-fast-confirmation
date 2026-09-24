module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionEvaluatorStep
public import FastConfirmationProofs.Checkpoints.TrustedResetCheckpointClassification
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

noncomputable def trusted_actualFinalizedResetCurrentAnchorLineage_core
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e') :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
      Cert Supp := by
  have hrealized :=
    E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hknown : (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
    simpa only [E.fcrStep_store] using hrealized.root_known
  have hstore : E.CausalStore cfg ext (E.fcrStoreAtCall cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  let root := (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root
  have hat : E.AcceptedBlockAt cfg ext root
      ((E.fcrStoreAtCall cfg ext v n).store.blocks root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hknown
  have hcheckpointStore : B.state.C root
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) =
      get_checkpoint_for_block cfg (E.fcrStoreAtCall cfg ext v n).store root
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :=
    B.coherence.checkpoint_of_known hstore root hknown _
  have hcheckpointAnchor :=
    E.trusted_actualFinalizedReset_currentCheckpoint_eq_anchor cfg ext B hT hanchor
      hboundary v n hcurrent
  have hpayload := TrustedAcceptedHistoricalA32GatePayloadCoreAt.of_anchor cfg ext B
    hat (by simpa only [root, get_block_epoch] using hcurrent)
    (hcheckpointStore.trans (by simpa only [root] using hcheckpointAnchor))
    hanchorCert hanchorSupp
  exact TrustedAcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload

/-- Eager instantiation, unchanged for the weak trunk. -/
noncomputable def trusted_actualFinalizedResetCurrentAnchorLineage
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    E.TrustedAcceptedHistoricalA32LineageAt cfg ext B
      (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :=
  E.trusted_actualFinalizedResetCurrentAnchorLineage_core cfg ext B hT hanchor
    hboundary v n hcurrent ⟨CertifiedJustified.anchor⟩
    (fun _ _ h _ _ _ _ _ => Or.inl h)

end Execution
end FastConfirmation.Spec
end
