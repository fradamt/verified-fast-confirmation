module
public import FastConfirmationProofs.FFG.State.FinalizationTiming
public import FastConfirmationProofs.Checkpoints.DeadlineCheckpointRelay
public import FastConfirmationProofs.Checkpoints.ResetCheckpointClassification
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks
public import FastConfirmationProofs.FFG.State.FinalizedSameTip
public import FastConfirmationProofs.FFG.State.FFGCheckpointEpochOrder
public import FastConfirmationProofs.FFG.SourceHistory.FFGJustifiedMaximality
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant

@[expose] public section

/-! A deadline-bounded accepted justification carrier raises a remote justified epoch. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- An AU carrier whose checkpoint is at least as recent as receiver finality
passes the exact finalized guard. Its deadline origin then delivers the root. -/
theorem deadline_carrier_known_of_au
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} {n m : ℕ} {tip : Root} {c : Checkpoint Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (htip : tip ∈ (E.store cfg ext v n).block_roots)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (hnext : E.slot_start cfg (E.slot_at cfg n + 1) ≤ m)
    (hlt : n < m)
    (hAU : B.state.AU cfg ext tip c)
    (hFle : (E.store cfg ext w m).finalized_checkpoint.epoch ≤ c.epoch) :
    tip ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgen, hgenSlot⟩
  let F := (E.store cfg ext w m).finalized_checkpoint
  obtain ⟨hcertificate⟩ := B.state.includedJustifiedAtTip_of_AU cfg ext hAU
  have hanchorExact := acceptedAnchorExact_of_trajectory cfg ext E B hT
    hanchor hboundary
  have hprefix : ExactCheckpointPrefix B.state.C F c := by
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate cfg ext B
        hgenShort hanchor (E.store_causal cfg ext w m) with
      hFanchor | ⟨_carrier, _hcarrier, ⟨hFcertificate⟩⟩
    · change ExactCheckpointPrefix B.state.C
        (E.store cfg ext w m).finalized_checkpoint c
      rw [hFanchor]
      exact IncludedCertifiedJustified.anchor_prefix
        (cfg := cfg) P V hanchorExact hcertificate
    · exact B.state.exactFinalizedPrefix_of_accountable cfg P V
        hanchorExact hacc hFcertificate hcertificate hFle
  have hFrealized := E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary (w := w) m
  have hanchorLe : B.anchor.epoch ≤ F.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg)
      (Classical.choice hFrealized.certified)
  have hparent : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled v n
  have hwalk := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
    hanchor hboundary v n hanchorLe htip
  have hcheckpoint : F.root = get_checkpoint_block cfg
      (E.store cfg ext v n) tip F.epoch :=
    exactCheckpointPrefix_root_eq_at_sameTip cfg ext B.coherence
      (E.store_causal cfg ext v n) hparent htip hprefix hAU hFle hwalk
  have hknown := E.deadline_root_known_of_checkpointCompatible cfg ext B hT hrelay
    hanchor hboundary hv hw hHn hHm htip hdue hnext hlt
    hFrealized.root_known hanchorLe hcheckpoint
  exact hknown

/-- Finalization lag makes a recent AU carrier compatible with the receiver.
The relay still requires the carrier's own deadline origin. -/
theorem deadline_carrier_known_of_recent_au
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} {n m : ℕ} {tip : Root} {c : Checkpoint Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (htip : tip ∈ (E.store cfg ext v n).block_roots)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (hnext : E.slot_start cfg (E.slot_at cfg n + 1) ≤ m)
    (hlt : n < m)
    (hAU : B.state.AU cfg ext tip c)
    (hrecent : get_current_store_epoch cfg (E.store cfg ext w m) ≤ c.epoch + 2) :
    tip ∈ (E.store cfg ext w m).block_roots := by
  apply E.deadline_carrier_known_of_au cfg ext B hT hrelay hanchor hboundary
    P V hacc hv hw hHn hHm htip hdue hnext hlt hAU
  rcases hLag (E.store_causal cfg ext w m) with hFa | hlag
  · obtain ⟨cert⟩ := B.state.includedJustifiedAtTip_of_AU cfg ext hAU
    rw [hFa]
    exact IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) cert
  · exact Nat.le_of_add_le_add_right (hlag.trans hrecent)


/-- A carrier either reaches the receiver or the receiver already has a
finalized epoch at least as new as the carrier's justification. In either
case its justified epoch reaches that justification. The `GU` alternative
requires the carrier to be from an earlier epoch at the receiver. -/
theorem deadline_justified_epoch_le_of_carrier
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} {n m : ℕ} {tip : Root} {c : Checkpoint Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (htip : tip ∈ (E.store cfg ext v n).block_roots)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (hnext : E.slot_start cfg (E.slot_at cfg n + 1) ≤ m)
    (hlt : n < m)
    (hselector : c = B.state.GJ tip ∨ c = B.state.GU tip ∧
      get_block_epoch cfg (E.store cfg ext v n) tip <
        get_current_store_epoch cfg (E.store cfg ext w m)) :
    c.epoch ≤ (E.store cfg ext w m).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgen, hgenSlot⟩
  let F := (E.store cfg ext w m).finalized_checkpoint
  by_cases hcle : c.epoch ≤ F.epoch
  · exact hcle.trans (B.globalFinalizedEpoch_le_justified cfg ext
      hgenShort hanchor (E.store_causal cfg ext w m))
  have hFle : F.epoch ≤ c.epoch := Nat.le_of_lt (Nat.lt_of_not_ge hcle)
  have haccepted := E.acceptedRoot_of_causal_known cfg ext
    (E.store_causal cfg ext v n) htip
  have hAU : B.state.AU cfg ext tip c := by
    rcases hselector with hgj | ⟨hgu, _⟩
    · rw [hgj]; exact B.state.gj_AU cfg ext haccepted
    · rw [hgu]; exact B.state.gu_AU cfg ext haccepted
  obtain ⟨hcertificate⟩ := B.state.includedJustifiedAtTip_of_AU cfg ext hAU
  have hanchorExact := acceptedAnchorExact_of_trajectory cfg ext E B hT
    hanchor hboundary
  have hprefix : ExactCheckpointPrefix B.state.C F c := by
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate cfg ext B
        hgenShort hanchor (E.store_causal cfg ext w m) with
      hFanchor | ⟨_carrier, _hcarrier, ⟨hFcertificate⟩⟩
    · change ExactCheckpointPrefix B.state.C
        (E.store cfg ext w m).finalized_checkpoint c
      rw [hFanchor]
      exact IncludedCertifiedJustified.anchor_prefix
        (cfg := cfg) P V hanchorExact hcertificate
    · exact B.state.exactFinalizedPrefix_of_accountable cfg P V
        hanchorExact hacc hFcertificate hcertificate hFle
  have hFrealized := E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary (w := w) m
  have hanchorLe : B.anchor.epoch ≤ F.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg)
      (Classical.choice hFrealized.certified)
  have hparent : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled v n
  have hwalk := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
    hanchor hboundary v n hanchorLe htip
  have hcheckpoint : F.root = get_checkpoint_block cfg
      (E.store cfg ext v n) tip F.epoch :=
    exactCheckpointPrefix_root_eq_at_sameTip cfg ext B.coherence
      (E.store_causal cfg ext v n) hparent htip hprefix hAU hFle hwalk
  have hknown := E.deadline_root_known_of_checkpointCompatible cfg ext B hT hrelay
    hanchor hboundary hv hw hHn hHm htip hdue hnext hlt
    hFrealized.root_known hanchorLe hcheckpoint
  have hmax := (E.store_causal cfg ext w m).acceptedFFGJustifiedMaximality
    B hT.whole_seconds hgenShort hanchor
  have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
      (E.store cfg ext w m) tip :=
    Execution.AcceptedCarrierIn.of_causal_known (E.store_causal cfg ext w m) hknown
  rcases hselector with hgj | ⟨hgu, hold⟩
  · rw [hgj]
    exact hmax.ledger.gj_epoch_le_justified tip hcarrier
  · rw [hgu]
    apply hmax.oldGU tip hcarrier
    have hagree := hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n) (E.blockProvenance cfg ext w m) htip hknown
    simpa only [get_block_epoch, ← hagree] using hold

end Execution
end FastConfirmation.Spec

end
