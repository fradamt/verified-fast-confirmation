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
-/

namespace FastConfirmation.Spec.EarlyEpochBoundaryWitness

open AcceptedActualFCRJointNonVacuityBase AcceptedActualFCRJointNonVacuityFFG

/-- The identity names the carrier with the three included epoch-1 votes. -/
def earlyState : BeaconState WitnessRoot :=
  { carrierState with source_identity := some carrierRoot }

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
It includes every start at epoch 2 or later and every single-boundary advance. -/
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
before processing it. This is the M2 corner, not an unsafe execution. -/
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

end FastConfirmation.Spec.EarlyEpochBoundaryWitness

end
