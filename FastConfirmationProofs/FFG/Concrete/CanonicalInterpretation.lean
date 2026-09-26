module
public import FastConfirmationProofs.FFG.Concrete.CanonicalCheckpoints
public import FastConfirmationStatements.Premises.NextSlotSafety

@[expose] public section

/-! Builds the canonical `ScheduledFFGInterpretation` of an execution run with
the concrete bridge. The anchor is the genesis anchor. The selectors are
`GJ`, `GU`, `GF`, `GUF`, and `checkpointAt`; the formed evidence is
`Formed`. The inclusion relation is an input.

`CanonicalOpenFields` holds exactly the fields that this file does not prove:
the certificate evidence of formed checkpoints, the two finalization
certificates, and the scope restriction `epoch_one_finalization_one_step`.
Their certificates need `IncludedSupermajorityLink`, whose horizon fields
have no bound on accepted roots, and inclusion evidence, whose
`received_from_block` field has no source in an accepted block body. The
causal field needs honest behavior. The file also proves the anchor,
lag, and checkpoint projection fields of `NextSlotSafetyPremises` for this
interpretation. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The fields of `AcceptedBlockFFGState` that the canonical construction
does not prove, stated for the canonical selectors. -/
structure CanonicalOpenFields (E : Execution Root)
    (I : Execution.AcceptedBlockAttestationInclusion B.setup.cfg B.ext E) : Prop where
  formed_evidence : ∀ {r : Root} {c : Checkpoint Root}, B.Formed E r c →
    IncludedCheckpointEvidence B.setup.cfg B.ext E I.Included B.anchorCheckpoint r c
  realized_finalized_evidence : ∀ {r b},
    E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b →
    B.GF r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E I.Included B.anchorCheckpoint r (B.GF r),
        F.child.epoch < compute_epoch_at_slot B.setup.cfg b.slot
  unrealized_finalized_evidence : ∀ {r b},
    E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b →
    B.GUF r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E I.Included B.anchorCheckpoint r (B.GUF r),
        F.child.epoch ≤ compute_epoch_at_slot B.setup.cfg b.slot
  epoch_one_finalization_one_step : ∀ r, E.RootKnownInScheduledPrefix B.setup.cfg B.ext r →
    ((B.GF r).epoch = GENESIS_EPOCH + 1 → B.GF r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E I.Included B.anchorCheckpoint r (B.GF r),
        F.child.epoch = GENESIS_EPOCH + 2) ∧
    ((B.GUF r).epoch = GENESIS_EPOCH + 1 → B.GUF r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E I.Included B.anchorCheckpoint r (B.GUF r),
        F.child.epoch = GENESIS_EPOCH + 2)

/-- **The canonical accepted-block FFG state.** -/
noncomputable def canonicalState (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E)
    (I : Execution.AcceptedBlockAttestationInclusion B.setup.cfg B.ext E)
    (h : B.CanonicalOpenFields E I) :
    AcceptedBlockFFGState B.setup.cfg B.ext E B.anchorCheckpoint where
  includedAttestations := I
  checkpoint_evidence_in_block := B.Formed E
  checkpoint_at_epoch := B.checkpointAt
  realized_justified := B.GJ
  unrealized_justified := B.GU
  realized_finalized := B.GF
  unrealized_finalized := B.GUF
  checkpoint_epoch := fun _ _ => rfl
  formed_carrier_accepted := fun hf => hf.1
  formed_evidence := h.formed_evidence
  realized_justified_mem := fun r hr => ⟨r, .refl r, hr, Or.inl rfl⟩
  unrealized_justified_mem := fun r hr => ⟨r, .refl r, hr, Or.inr (Or.inr (Or.inl rfl))⟩
  realized_finalized_mem := fun r hr => ⟨r, .refl r, hr, Or.inr (Or.inl rfl)⟩
  unrealized_finalized_mem := fun r hr => ⟨r, .refl r, hr, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  realized_justified_anchor_or_before := fun hb => B.realized_justified_anchor_or_before hB hg hb
  realized_justified_max := fun hb hsb hd hlt hE hc =>
    B.realized_justified_max hB hg hwf hb hsb hd hlt hE hc
  realized_justified_realized := fun hb => B.realized_justified_realized hB hg hb
  unrealized_justified_max := fun hb hE hc => B.unrealized_justified_max hB hg hwf hb hE hc
  unrealized_justified_early := fun hb hE => B.unrealized_justified_early hB hg hb hE
  realized_justified_epoch_le_unrealized := fun _ hr =>
    B.realized_justified_epoch_le_unrealized hB hg hr
  unrealized_justified_mono := fun hs ht hd => B.unrealized_justified_mono hB hg hwf hs ht hd
  unrealized_justified_epoch_le_later_realized := fun hsb htb hd hlt =>
    B.unrealized_justified_epoch_le_later_realized hB hg hwf hsb htb hd hlt
  available_checkpoint_epoch_le_block := fun hb hc =>
    B.available_checkpoint_epoch_le_block hB hg hwf hb hc
  realized_finalized_evidence := h.realized_finalized_evidence
  unrealized_finalized_evidence := h.unrealized_finalized_evidence
  epoch_one_finalization_one_step := h.epoch_one_finalization_one_step
  realized_finalized_epoch_le_realized_justified := fun _ hr =>
    B.realized_finalized_epoch_le_realized_justified hB hg hr
  unrealized_finalized_epoch_le_unrealized_justified := fun _ hr =>
    B.unrealized_finalized_epoch_le_unrealized_justified hB hg hr
  unrealized_finalized_epoch_le_realized_justified := fun _ hr =>
    B.unrealized_finalized_epoch_le_realized_justified hB hg hr

/-- **Read and checkpoint agreement** of the canonical state: all eleven
fields are proved. -/
theorem canonicalCoherence (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E)
    (I : Execution.AcceptedBlockAttestationInclusion B.setup.cfg B.ext E)
    (h : B.CanonicalOpenFields E I) :
    FFGStateAndCheckpointReadAgreement B.setup.cfg B.ext (B.canonicalState hB hg hwf I h) where
  genesis_gj := fun r hr => (B.genesis_reads hB hg r hr).1
  genesis_gf := fun r hr => (B.genesis_reads hB hg r hr).2.1
  genesis_gu := fun r hr => (B.genesis_reads hB hg r hr).2.2.1
  genesis_guf := fun r hr => (B.genesis_reads hB hg r hr).2.2.2
  genesis_unrealized_justification := B.genesis_unrealized_justification_reads hg
  transition_gj := fun t => (B.transition_reads hB hg t).1
  transition_gf := fun t => (B.transition_reads hB hg t).2.1
  transition_gu := fun t => (B.transition_reads hB hg t).2.2.1
  transition_guf := fun t => (B.transition_reads hB hg t).2.2.2
  checkpoint_of_known := fun hstore r hr e => B.checkpoint_of_known hB hg hstore r hr e
  available_checkpoint_checkpoint_of_known := fun hstore _ hr _ hc =>
    B.available_checkpoint_of_known hB hg hwf hstore hr hc

/-- **The canonical interpretation** of an execution run with the concrete
bridge from the setup genesis. -/
noncomputable def canonicalScheduledFFGInterpretation (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E)
    (I : Execution.AcceptedBlockAttestationInclusion B.setup.cfg B.ext E)
    (h : B.CanonicalOpenFields E I) : ScheduledFFGInterpretation B.setup.cfg B.ext E where
  anchor := B.anchorCheckpoint
  state := B.canonicalState hB hg hwf I h
  coherence := B.canonicalCoherence hB hg hwf I h

/-! ### Fields of `NextSlotSafetyPremises` -/

section Premises

variable (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
  (hwf : WellFormedExecution E)
  (I : Execution.AcceptedBlockAttestationInclusion B.setup.cfg B.ext E)
  (h : B.CanonicalOpenFields E I)

/-- `anchor_eq`. -/
theorem canonical_anchor_eq :
    (B.canonicalScheduledFFGInterpretation hB hg hwf I h).anchor =
      E.genesis_store.justified_checkpoint :=
  (B.genesis_justified hg).symm

/-- `anchor_state_checkpoints`. -/
theorem canonical_anchor_state_checkpoints :
    E.GenesisOrNormalizedAnchor (B.canonicalScheduledFFGInterpretation hB hg hwf I h).anchor :=
  Or.inl rfl

/-- `anchor_boundary`. -/
theorem canonical_anchor_boundary :
    Execution.InitialAnchorAtEpochBoundary (cfg := B.setup.cfg) (E := E)
      (anchor := (B.canonicalScheduledFFGInterpretation hB hg hwf I h).anchor) := by
  unfold Execution.InitialAnchorAtEpochBoundary
  change (E.genesis_store.blocks B.setup.genesisRoot).slot ≤
    compute_start_slot_at_epoch B.setup.cfg 0
  obtain ⟨anchor, hroot, hslot, -, -, hgs⟩ := hg
  rw [hgs, ← hroot]
  simp [get_forkchoice_store, hslot]

/-- `imported_block_finalization_lag`. -/
theorem canonical_imported_block_finalization_lag :
    E.ImportedBlockFinalizationLag B.setup.cfg B.ext
      (B.canonicalScheduledFFGInterpretation hB hg hwf I h) :=
  B.importedBlockFinalizationLag hB hg hwf _ rfl

/-- `checkpoint_projection`. -/
theorem canonical_checkpoint_projection :
    EpochCheckpointProjectionLaws (B.canonicalScheduledFFGInterpretation hB hg hwf I h).anchor
      (E.RootKnownInScheduledPrefix B.setup.cfg B.ext)
      (B.canonicalScheduledFFGInterpretation hB hg hwf I h).state.checkpoint_at_epoch :=
  B.checkpoint_projection_laws hB hg

end Premises

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
