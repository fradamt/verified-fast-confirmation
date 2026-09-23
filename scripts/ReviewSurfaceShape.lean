import FastConfirmationStatements
import FastConfirmationProofs.ReviewTheorem
import Lean

/-! Pin the reviewed claim, premise record fields, and the review theorem's type. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let checkFields (name : Name) (expected : List String) := do
    let actual := (getStructureFields env name).toList.map (fun field => field.getString!)
    if actual != expected then
      throwError "unexpected fields for {name}: {actual}; expected {expected}"
  checkFields `FastConfirmation.Spec.ReviewClaims
    ["confirmed_root_safe_from_next_slot", "live_confirmed_root_monotonicity",
     "selected_result_safe_from_next_slot_of_scheduled_call"]
  checkFields `FastConfirmation.Spec.Execution.NextSlotSafetyPremises
    ["semantics", "trajectory", "completed_calls", "epoch_ends_fit",
     "anchor_eq", "anchor_boundary", "finalization_delay",
     "slots_per_epoch_gt_one", "paper_a32", "checkpoint_projection",
     "exact_link_validity"]
  checkFields `FastConfirmation.Spec.LiveMonotonicityPremises
    ["honest_block_each_slot", "ffg_timely_justification"]
  checkFields `FastConfirmation.Spec.NextSlotSynchronyPremises
    ["attestation_delivery", "block_relay", "envelope_delivery",
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
  IO.println "review surface shape passed"

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : FastConfirmation.Spec.Config)
    (ext : FastConfirmation.Spec.Externals Root) :
    FastConfirmation.Spec.ReviewClaims cfg ext :=
  FastConfirmation.Spec.review_claims cfg ext
