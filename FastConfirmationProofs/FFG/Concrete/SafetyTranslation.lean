module
public import FastConfirmationProofs.FFG.Concrete.CanonicalEvidence
public import FastConfirmationProofs.FFG.Concrete.BridgeLaws
public import FastConfirmationProofs.FFG.Certificates.PaperCheckpointInclusionProjectionCore
public import FastConfirmationStatements.Premises.ConcreteSafety
public import FastConfirmationInternal.Premises.NextSlotSafety

@[expose] public section

/-! Translates the safety premise of a run with the concrete bridge
(`ConcreteBridge.SafetyPremises`) to the internal premise record
`Execution.NextSlotSafetyPremises`. The FFG interpretation is the canonical
interpretation of the bridge, with the inclusion relation
`TargetIncludedAt`. The public A3.2 view is compatible with it: the view
marks as formed only the carried checkpoints, and every attestation in an
accepted block body was received from the block. The Phase0 source laws and
the balance floor are proved for the bridge. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The anchor active set of a run with the concrete bridge has at least two
`EFFECTIVE_BALANCE_INCREMENT`s of weight. -/
theorem balance_floor (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E) :
    2 * B.setup.cfg.effective_balance_increment ≤
      E.weight (E.anchorActiveValidators B.setup.cfg) := by
  have h := B.total_active_eq hB hg
  have hfloor := hB.setup.balance_floor
  have hinc := B.setup.cfg.effective_balance_increment_pos
  have hmax : E.total_active B.setup.cfg = max B.setup.cfg.effective_balance_increment
      (E.weight (E.anchorActiveValidators B.setup.cfg)) := rfl
  rw [hmax] at h
  rcases le_total (E.weight (E.anchorActiveValidators B.setup.cfg))
    B.setup.cfg.effective_balance_increment with hle | hle
  · rw [max_eq_left hle] at h
    rw [← h] at hfloor
    omega
  · rw [max_eq_right hle] at h
    rw [h]
    exact hfloor

omit [LinearOrder Root] [Inhabited Root] in
/-- The anchor of a run with the concrete bridge commits to the projected
setup genesis state. -/
theorem scheduled_genesis [LinearOrder Root] [Inhabited Root] {E : Execution Root}
    (hg : B.ConcreteGenesis E) :
    ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store B.setup.cfg anchorState anchorBlock ∧
        anchorState.slot = anchorBlock.message.slot ∧
        B.interface.AnchorCommitsToState anchorBlock.message anchorState ∧
        anchorBlock.message.parent_root ≠ anchorBlock.root := by
  obtain ⟨anchorBlock, hroot, hslot, hparent, -, -, hgs⟩ := hg
  refine ⟨B.project B.setup.genesis, anchorBlock, hgs, ?_, ⟨hslot, rfl⟩, ?_⟩
  · rw [hslot]
    rfl
  · rw [hroot]
    exact hparent

/-- A carried checkpoint is formed in the canonical state. -/
theorem carriedOrRealizable_of_carried {E : Execution Root} {x : Root} {c : Checkpoint Root}
    (h : B.Carried E x c) : B.CarriedOrRealizable E x c := by
  obtain ⟨hx, hc⟩ := h
  refine ⟨hx, ?_⟩
  rcases hc with hc | hc | hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))

/-- **Translation to the internal premise.** The safety premise of a run with
the concrete bridge gives the internal premise record for the canonical
interpretation. The honest validator `v` and the in-horizon time `n` give
the fixed committees from `committees_agree`. -/
noncomputable def SafetyPremises.nextSlotSafetyPremises {B : ConcreteBridge Root}
    {E : Execution Root}
    (h : B.SafetyPremises E) {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hn : E.WithinHorizon B.setup.cfg n) :
    E.NextSlotSafetyPremises B.setup.cfg B.interface :=
  have hcomm : B.FixedCommittees E :=
    B.fixedCommittees_of_agree h.externals_coherence.committees_agree hv hn
  let I := B.canonicalInclusion h.admissible h.genesis h.horizon_scope hcomm
    h.body_attestations_delivered
  have hopen := B.canonicalOpenFields h.admissible h.genesis h.wellFormed h.horizon_scope hcomm
    h.body_attestations_delivered h.honest_behavior h.byzantine_bound h.slots_per_epoch_gt_one
    h.epoch_one_finalization_scope
  {
    ffg_interpretation :=
      B.canonicalScheduledFFGInterpretation h.admissible h.genesis h.wellFormed I hopen
    scheduled_execution := {
      whole_seconds := h.whole_seconds
      wellFormed := h.wellFormed
      externals_coherence := h.externals_coherence
      honest_behavior := h.honest_behavior
      genesis := B.scheduled_genesis h.genesis }
    call_conditions := {
      synchrony := h.synchrony
      static_validators := h.static_validators
      byzantine_bound := h.byzantine_bound
      source_coherence := B.phase0SourceCoherence h.admissible
      boundary_source_coherence := B.phase0BoundarySourceCoherence h.admissible
      balance_floor := B.balance_floor h.admissible h.genesis }
    epoch_ends_fit := h.epoch_ends_fit
    anchor_eq := B.canonical_anchor_eq h.admissible h.genesis h.wellFormed I hopen
    anchor_state_checkpoints :=
      B.canonical_anchor_state_checkpoints h.admissible h.genesis h.wellFormed I hopen
    anchor_boundary := B.canonical_anchor_boundary h.admissible h.genesis h.wellFormed I hopen
    imported_block_finalization_lag :=
      B.canonical_imported_block_finalization_lag h.admissible h.genesis h.wellFormed I hopen
    slots_per_epoch_gt_one := h.slots_per_epoch_gt_one
    checkpoint_inclusion := ⟨B.checkpointInclusionView E, rfl, rfl, rfl, rfl,
      fun hf => B.carriedOrRealizable_of_carried hf,
      fun hi => B.bodyIncludedAt_received h.admissible h.genesis h.body_attestations_delivered hi,
      h.checkpoint_inclusion⟩
    checkpoint_projection :=
      B.canonical_checkpoint_projection h.admissible h.genesis h.wellFormed I hopen
    link_checkpoint_agreement := B.canonical_link_checkpoint_agreement h.admissible h.genesis
      h.wellFormed }

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
