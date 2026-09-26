module
public import FastConfirmationWitnesses.NonVacuity.FFGEvidence

@[expose] public section

/-!
Phase0 epoch-1 slot processing can select a certified source newer than eager PJF.
The finite state-function test uses the three included epoch-1 votes of the
existing carrier fixture. It is not a complete execution refinement.
The Python control in `scripts/anchor_semantics_probe.py` checks the same
corner with the pinned state functions. Phase0 beacon-chain.md:1893-1898
and Altair beacon-chain.md:728-733 return before FFG processing in epochs
0 and 1; epoch processing at the end of epoch 2 can justify epoch 1.
The reduced functions show why the eager PJF equation covers one boundary.
`epoch_one_fixture_satisfies_boundary_laws` shows that they satisfy the
`Phase0BoundarySourceCoherence` laws.
-/

namespace FastConfirmation.Spec.EarlyEpochBoundaryWitness

open AcceptedActualFCRJointNonVacuityBase AcceptedActualFCRJointNonVacuityFFG

/-- The identity names the carrier with the three included epoch-1 votes.
The state is at slot 7, in epoch 1, as if those votes were included in an
epoch-1 block. -/
def earlyState : BeaconState WitnessRoot :=
  { carrierState with slot := 7, source_identity := some carrierRoot }

/-- A reduced PJF interpretation with the Phase0 early return. -/
def pjf (st : BeaconState WitnessRoot) : BeaconState WitnessRoot :=
  if compute_epoch_at_slot witnessConfig st.slot ≤ 1 then st
  else if st.source_identity = some carrierRoot then
    { st with current_justified_checkpoint := childEpochOneCheckpoint }
  else st

/-- A reduced empty-slot interpretation that retains the epoch-1 votes
through epoch 2 and processes them before entry into epoch 3. -/
def processSlots (st : BeaconState WitnessRoot) (target : Slot) : BeaconState WitnessRoot :=
  if compute_epoch_at_slot witnessConfig st.slot <
      compute_epoch_at_slot witnessConfig target then
    if compute_epoch_at_slot witnessConfig st.slot = 1 ∧
        3 ≤ compute_epoch_at_slot witnessConfig target ∧ st.source_identity = some carrierRoot then
      { st with slot := target, current_justified_checkpoint := childEpochOneCheckpoint }
    else { pjf st with slot := target }
  else { st with slot := target }

/-- The guarded boundary equality holds for this fixture's state functions.
It includes every start at epoch 2 or later and every single-boundary advance.
The replacement laws keep the single-boundary part, and the part for two or
more boundaries only under a static registry and total active balance: for
the real functions, a later start can also change the source after two
boundaries when the second PJF weighs the start-epoch votes with other
effective balances. -/
theorem guarded_boundary_equality (st : BeaconState WitnessRoot) (target : Slot)
    (hcross : compute_epoch_at_slot witnessConfig st.slot <
      compute_epoch_at_slot witnessConfig target)
    (hguard : 2 ≤ compute_epoch_at_slot witnessConfig st.slot ∨
      compute_epoch_at_slot witnessConfig target ≤
        compute_epoch_at_slot witnessConfig st.slot + 1) :
    (processSlots st target).current_justified_checkpoint =
      (pjf st).current_justified_checkpoint := by
  have hnot : ¬ (compute_epoch_at_slot witnessConfig st.slot = 1 ∧
      3 ≤ compute_epoch_at_slot witnessConfig target ∧ st.source_identity = some carrierRoot) := by
    rintro ⟨he, ht, _⟩
    rcases hguard with hguard | hguard
    · rw [he] at hguard
      exact (by decide : ¬ 2 ≤ 1) hguard
    · rw [he] at hguard
      exact (by decide : ¬ 3 ≤ 2) (ht.trans hguard)
  simp [processSlots, hcross, hnot]

/-- One boundary preserves the epoch-0 source. Two boundaries select epoch
1; its included certificate is present, although eager PJF still returns
before processing it. This is an epoch-boundary regression, not an unsafe execution. -/
theorem epoch_one_boundary_regression :
    compute_epoch_at_slot witnessConfig earlyState.slot = 1 ∧
    (pjf earlyState).current_justified_checkpoint = anchorCheckpoint ∧
    (processSlots earlyState 8).current_justified_checkpoint = anchorCheckpoint ∧
    (processSlots earlyState 12).current_justified_checkpoint = childEpochOneCheckpoint ∧
    (processSlots earlyState 12).current_justified_checkpoint ≠
      (pjf earlyState).current_justified_checkpoint ∧
    IncludedCertifiedJustified witnessConfig witnessExecution witnessIncluded
      anchorCheckpoint carrierRoot (processSlots earlyState 12).current_justified_checkpoint := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact .link .anchor witnessIncludedAnchorChildLink

/-- Externals with the reduced slot processing and PJF of this fixture.
No block transition succeeds, so the block-transition law is vacuous here. -/
def fixtureExternals : BeaconFunctionInterface WitnessRoot :=
  { witnessExternals with
    process_slots := processSlots
    process_justification_and_finalization := pjf
    state_transition := fun _ _ => none }

/-- This epoch-1 corner satisfies the replacement boundary laws: one boundary gives
the eager value, targets in one epoch agree, and the epoch-1 source selected
after two boundaries is not newer than the start epoch. -/
theorem epoch_one_fixture_satisfies_boundary_laws :
    Phase0BoundarySourceCoherence witnessConfig fixtureExternals := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro st target _ hnext
    simp only [fixtureExternals, processSlots, hnext]
    split_ifs with h1 h2
    · obtain ⟨h21, h22, _⟩ := h2
      rw [h21] at h22
      exact absurd h22 (by decide)
    · rfl
    · exact absurd (Nat.lt_succ_self _) h1
  · intro st target target' _ hsame
    simp only [fixtureExternals, processSlots, hsame]
    split_ifs <;> rfl
  · intro pre sb post h
    simp only [fixtureExternals] at h
    exact absurd h (by simp)
  · intro st target hcross _
    simp only [fixtureExternals, processSlots, if_pos hcross]
    split_ifs with h2
    · right
      rw [h2.1]
      exact (by decide : childEpochOneCheckpoint.epoch ≤ 1)
    · simp only [pjf]
      split_ifs with h3 h4
      · left
        rfl
      · right
        exact le_trans (by decide : childEpochOneCheckpoint.epoch ≤ 1)
          (Nat.lt_of_not_le h3).le
      · left
        rfl
  · intro st target hstart htwo _
    exact guarded_boundary_equality st target
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) htwo) (Or.inl hstart)

end FastConfirmation.Spec.EarlyEpochBoundaryWitness

end
