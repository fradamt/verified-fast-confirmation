import FastConfirmationStatements
import FastConfirmationProofs.ReviewTheorem
import Lean
import FastConfirmationProofs.FCRRule.PredictionSupport
import FastConfirmationProofs.FCRRule.PredictionSupportGeometry

/-! Pin the reviewed claim, premise record fields, and the review theorem's type. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let checkFields (name : Name) (expected : List String) := do
    let actual := (getStructureFields env name).toList.map (fun field => field.getString!)
    if actual != expected then
      throwError "unexpected fields for {name}: {actual}; expected {expected}"
  checkFields `FastConfirmation.Spec.ReviewClaims
    ["confirmed_root_safe_from_next_slot", "live_confirmed_root_monotonicity"]
  checkFields `FastConfirmation.Spec.Execution.NextSlotSafetyPremises
    ["semantics", "trajectory", "completed_calls", "epoch_ends_fit",
     "anchor_eq", "anchor_boundary", "finalization_delay",
     "slots_per_epoch_gt_one", "paper_a32", "checkpoint_projection",
     "exact_link_validity"]
  checkFields `FastConfirmation.Spec.LiveMonotonicityPremises
    ["honest_block_each_slot", "ffg_timely_justification"]
  checkFields `FastConfirmation.Spec.Synchrony
    ["delta", "attestation_delivery",
     "deadline_block_relay", "boundary_block_prefix",
     "attester_slashing_relay"]
  checkFields `FastConfirmation.Spec.NextSlotSynchronyPremises
    ["delta", "attestation_delivery",
     "deadline_block_relay", "boundary_block_prefix",
     "envelope_delivery",
     "data_availability_relay", "attester_slashing_relay"]
  checkFields `FastConfirmation.Spec.BeaconExternalsPremises
    ["process_slots_slot", "process_slots_registry", "state_transition_slot",
     "state_transition_registry", "state_transition_pre_slot_lt",
     "state_transition_checkpoint_epoch", "pjf_checkpoint_epoch",
     "committees_agree", "honest_attestation_valid", "valid_attestation_honest",
     "valid_attestation_committee", "committee_assignment_unique",
     "committee_coverage", "committee_members_active", "valid_attestation_default",
     "process_slots_attestation_valid", "verify_envelope_deterministic"]
  checkFields `FastConfirmation.Spec.ByzantineWeightPremises
    ["effective_balance_quantized", "estimate_sound", "span_fraction"]
  checkFields `FastConfirmation.Spec.FCRPredictionSupportAt
    ["current_target", "selected_previous_result_no_conflict"]
  checkFields `FastConfirmation.Spec.Execution.IncludedAttestationEvidence
    ["carrier_message", "received_from_block", "slot_within_horizon",
     "slot_before_carrier", "target_epoch", "attesters_in_committee"]
  -- Interpretation fidelity is outside the safety premise.
  checkFields `FastConfirmation.Spec.FFGInterpretationFidelity
    ["included_fidelity", "attestation_validity", "gf_epoch_le_guf"]
  checkFields `FastConfirmation.Spec.Execution.IncludedAttestationFidelity
    ["carrier_message", "carrier_accepted", "in_carrier_body",
     "head_descends_target", "target_on_chain", "target_descends_source",
     "attesters_in_registry", "validation_state", "validation_registry", "valid",
     "validation_store", "validation_store_honest", "validation_target_known",
     "validation_state_from_target"]
  IO.println "review surface shape passed"

-- These names must remain in the reviewed Statements surface.
#check FastConfirmation.Spec.DeadlineBlockRelay
#check FastConfirmation.Spec.DeadlineBoundaryBlockPrefix
#check FastConfirmation.Spec.DeadlineEnvelopeDelivery
#check FastConfirmation.Spec.DeadlineDataAvailabilityRelay
#check FastConfirmation.Spec.DeadlineAttesterSlashingRelay

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : FastConfirmation.Spec.Config)
    (ext : FastConfirmation.Spec.Externals Root) :
    FastConfirmation.Spec.ReviewClaims cfg ext :=
  FastConfirmation.Spec.review_claims cfg ext

-- A previous-result guard requires descendant support, with no exact-target equality.
example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : FastConfirmation.Spec.Config) (ext : FastConfirmation.Spec.Externals Root)
    (E : FastConfirmation.Spec.Execution Root) (v : Nat) (q : Nat)
    (query : FastConfirmation.Spec.FastConfirmationStore Root) (input result : Root)
    (h : FastConfirmation.Spec.FCRPredictionSupportAt cfg ext E v q query input)
    (hout : FastConfirmation.Spec.find_latest_confirmed_descendant cfg ext query input = result)
    (hstrict : result ≠ input)
    (hprevious : FastConfirmation.Spec.get_block_epoch cfg query.store result ≠
      FastConfirmation.Spec.get_current_store_epoch cfg query.store)
    (hnotStart : FastConfirmation.Spec.is_start_slot_at_epoch cfg
      (FastConfirmation.Spec.get_current_slot cfg query.store) ≠ true) :
    FastConfirmation.Spec.HonestVotesTargetDescendFrom cfg E result
      (FastConfirmation.Spec.get_current_store_epoch cfg query.store) q :=
  h.selected_previous_result_no_conflict result hout hstrict hprevious hnotStart

-- Proved reductions do not change the two-field prediction-support surface.
#check FastConfirmation.Spec.Execution.currentTargetSelectedEdge_geometry_of_accepted
#check FastConfirmation.Spec.Execution.currentTarget_supportBefore_of_canonical
#check FastConfirmation.Spec.Execution.previousResult_descendSupport_of_canonical
