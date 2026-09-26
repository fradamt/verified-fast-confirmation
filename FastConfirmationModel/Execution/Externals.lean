module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Interval.Finset.Nat
public import FastConfirmationModel.Spec.Config
public import FastConfirmationModel.Spec.BeaconChain.Types

@[expose] public section

/-! Defines the abstract committee, state-transition, signature, payload, and observation functions required by fork choice. Python: `specs/gloas/fork-choice.md`, Handlers; `specs/phase0/beacon-chain.md`, Helpers. -/

namespace FastConfirmation.Spec
/-- The abstract beacon-chain primitives the transcription bottoms out in:
committee shuffling, the state transition, signature/index validity, local data
availability, execution-envelope verification, and the abstract anchor commitment.
Their read-projection contract is in `docs/MODELING_CHOICES.md`. -/
structure BeaconFunctionInterface (Root : Type*) where
  /-- beacon-chain `get_beacon_committee(state, slot, index)`. -/
  get_beacon_committee : BeaconState Root → Slot → CommitteeIndex → List ValidatorIndex
  /-- beacon-chain `get_committee_count_per_slot(state, epoch)`. -/
  get_committee_count_per_slot : BeaconState Root → Epoch → ℕ
  /-- phase0 `process_slots(state, slot)` (used by `get_pulled_up_head_state`,
      `store_target_checkpoint_state`, and the honest attester's pulled-up
      head state). -/
  process_slots : BeaconState Root → Slot → BeaconState Root
  /-- phase0 `state_transition(state, signed_block, validate_result=True)`:
      `none` = the block is invalid (python raises), `some` = the post-state
      (used by `on_block`). -/
  state_transition : BeaconState Root → SignedBeaconBlock Root → Option (BeaconState Root)
  /-- phase0 `process_justification_and_finalization(state)` (used by
      `compute_pulled_up_tip` to pull the post-state up to the next epoch
      boundary). -/
  process_justification_and_finalization : BeaconState Root → BeaconState Root
  /-- beacon-chain `is_valid_indexed_attestation(state, indexed_attestation)`
      (sorted/nonempty indices + aggregate BLS signature — all absorbed here;
      used by `on_attestation` and `on_attester_slashing`). -/
  is_valid_indexed_attestation : BeaconState Root → IndexedAttestation Root → Bool
  /-- Abstract contract for `anchor_block.state_root == hash_tree_root(anchor_state)`.
      The external interpretation must relate the full block and state before
      projection. The accepted trajectory requires this relation at its anchor;
      slot agreement is a separate premise. This model does not prove a concrete
      hashing result. The default supplies no commitment evidence. -/
  AnchorCommitsToState : BeaconBlock Root → BeaconState Root → Prop :=
    fun _ _ => False
  /-- Ordered PTC, including duplicate positions
  (`specs/gloas/beacon-chain.md:1392`; call at `specs/gloas/fork-choice.md:1134`). -/
  get_ptc : BeaconState Root → Slot → List ValidatorIndex := fun _ _ => []
  /-- PTC index/signature validation (`specs/gloas/beacon-chain.md:1094`;
  call at `specs/gloas/fork-choice.md:1147`). -/
  is_valid_indexed_payload_attestation :
    BeaconState Root → IndexedPayloadAttestation Root → Bool := fun _ _ => false
  /-- Local sidecar and KZG checks (`specs/gloas/fork-choice.md:293`).
  Context is explicit so data can arrive after an earlier failed attempt. -/
  is_data_available : Root → EnvelopeObservation Root → Bool := fun _ _ => false
  /-- Envelope, bid, signature, state and execution-engine validation
  (`specs/gloas/fork-choice.md:658`). The envelope and observation identities
  retain inputs beyond the read projection. Failure is rejection. -/
  verify_execution_payload_envelope : BeaconState Root →
    SignedExecutionPayloadEnvelope Root → EnvelopeObservation Root → Bool :=
      fun _ _ _ => false

variable {Root : Type*}
variable (cfg : Config)
end FastConfirmation.Spec

end
