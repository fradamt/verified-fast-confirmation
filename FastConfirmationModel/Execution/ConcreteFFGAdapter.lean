module
public import FastConfirmationModel.Spec.BeaconChain.ConcreteTransition
public import FastConfirmationModel.Execution.Externals

@[expose] public section

/-! Supplies the fixed committee reads and indexed structural check to the
existing reduced `BeaconFunctionInterface`. The reduced `BeaconState` omits
participation and justification bits, so its state-valued methods cannot
carry a concrete FFG post-state. Python: `specs/gloas/beacon-chain.md`,
Committee helpers and indexed attestation validation. -/

namespace FastConfirmation.Spec.ConcreteFFG

/-- Structural part of `is_valid_indexed_attestation` on the legacy indexed
projection. BLS remains in `base.is_valid_indexed_attestation`. Python:
`specs/gloas/beacon-chain.md:1022-1041`. -/
def legacy_indexed_structure (preset : FFGPreset) {Root : Type}
    (state : BeaconState Root) (vote : IndexedAttestation Root) : Bool :=
  !vote.attesting_indices.isEmpty &&
  vote.attesting_indices.length ≤
    preset.max_validators_per_committee * preset.max_committees_per_slot &&
  decide (vote.attesting_indices.Pairwise (· < ·)) &&
  vote.attesting_indices.all (· < state.validators.length)

/-- A `BeaconFunctionInterface` compatible bundle for the operations that
have all their input data in the reduced state. The other methods remain
those of `base`; callers of the concrete FFG transition use
`ConcreteFFG.state_transition` directly. -/
def fixed_schedule_compatibility_bundle {Root : Type}
    (preset : FFGPreset) (schedule : FixedCommitteeSchedule)
    (base : BeaconFunctionInterface Root) : BeaconFunctionInterface Root :=
  { base with
    get_beacon_committee := fun _ slot index =>
      (schedule.committee slot index).getD []
    get_committee_count_per_slot := fun _ epoch =>
      (schedule.count epoch).getD 0
    is_valid_indexed_attestation := fun state vote =>
      legacy_indexed_structure preset state vote &&
        base.is_valid_indexed_attestation state vote }

end FastConfirmation.Spec.ConcreteFFG

end
