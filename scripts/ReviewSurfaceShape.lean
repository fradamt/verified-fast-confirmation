import FastConfirmationStatements
import FastConfirmationInternal.FFG.InterpretationFidelity
import FastConfirmationProofs.ReviewTheorem
import Lean
import FastConfirmationProofs.FFG.SelectedSource.TruncatedPredictionPinning
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
    ["confirmed_root_safe_from_next_slot"]
  checkFields `FastConfirmation.Spec.Execution.NextSlotSafetyPremises
    ["ffg_interpretation", "scheduled_execution", "call_conditions", "epoch_ends_fit",
     "anchor_eq", "anchor_state_checkpoints", "anchor_boundary", "imported_block_finalization_lag",
     "slots_per_epoch_gt_one", "checkpoint_inclusion", "checkpoint_projection",
     "link_checkpoint_agreement"]
  checkFields `FastConfirmation.Spec.Synchrony
    ["delta", "attestation_delivery",
     "deadline_block_relay", "boundary_block_prefix",
     "attester_slashing_relay"]
  checkFields `FastConfirmation.Spec.NextSlotSynchronyPremises
    ["delta", "delivery_lookahead",
     "deadline_block_relay", "boundary_block_prefix",
     "envelope_delivery",
     "data_availability_relay", "attester_slashing_relay"]
  checkFields `FastConfirmation.Spec.BeaconExternalsPremises
    ["process_slots_slot", "registry_static_in_horizon", "state_transition_slot",
     "state_transition_pre_slot_lt",
     "state_transition_checkpoint_epoch", "pjf_checkpoint_epoch",
     "committees_agree", "honest_attestation_valid", "valid_attestation_honest",
     "on_attestation_committee", "committee_assignment_unique",
     "committee_coverage", "committee_members_active", "valid_attestation_default",
     "process_slots_attestation_valid", "verify_envelope_deterministic"]
  checkFields `FastConfirmation.Spec.ByzantineWeightPremises
    ["effective_balance_quantized", "estimate_sound", "span_fraction"]
  checkFields `FastConfirmation.Spec.Execution.ScheduledFCRCallPremises
    ["synchrony", "static_validators", "byzantine_bound", "source_coherence",
     "boundary_source_coherence", "balance_floor"]
  checkFields `FastConfirmation.Spec.Execution.IncludedAttestationEvidence
    ["carrier_message", "received_from_block", "slot_within_horizon",
     "slot_before_carrier", "target_epoch", "attesters_in_committee"]
  -- Interpretation fidelity is outside the safety premise.
  checkFields `FastConfirmation.Spec.FFGInterpretationFidelity
    ["included_fidelity", "realized_finalized_epoch_le_unrealized_finalized"]
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
    (ext : FastConfirmation.Spec.BeaconFunctionInterface Root) :
    FastConfirmation.Spec.ReviewClaims cfg ext :=
  FastConfirmation.Spec.review_claims cfg ext

-- The internal support record permits descendant targets for a previous result.
example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : FastConfirmation.Spec.Config) (ext : FastConfirmation.Spec.BeaconFunctionInterface Root)
    (E : FastConfirmation.Spec.Execution Root) (v : Nat) (q : Nat)
    (query : FastConfirmation.Spec.FastConfirmationStore Root) (input result : Root)
    (h : FastConfirmation.Spec.SelectedPredictionVoteSupport cfg ext E v q query input)
    (hout : FastConfirmation.Spec.find_latest_confirmed_descendant cfg ext query input = result)
    (hstrict : result ≠ input)
    (hprevious : FastConfirmation.Spec.get_block_epoch cfg query.store result ≠
      FastConfirmation.Spec.get_current_store_epoch cfg query.store)
    (hnotStart : FastConfirmation.Spec.is_start_slot_at_epoch cfg
      (FastConfirmation.Spec.get_current_slot cfg query.store) ≠ true) :
    FastConfirmation.Spec.HonestVotesTargetDescendFrom cfg E result
      (FastConfirmation.Spec.get_current_store_epoch cfg query.store) q :=
  h.previous_result_vote_support result hout hstrict hprevious hnotStart

-- The joint induction derives support; it is absent from the safety premise.
#check FastConfirmation.Spec.Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold
#check FastConfirmation.Spec.Execution.currentResult_supportBefore_of_endpoint_induction
#check FastConfirmation.Spec.Execution.currentTargetSelectedEdge_geometry_of_accepted
#check FastConfirmation.Spec.Execution.currentTarget_supportBefore_of_canonical
#check FastConfirmation.Spec.Execution.previousResult_descendSupport_of_canonical

#check FastConfirmation.Spec.Execution.completedPrefix_currentTarget_endpoint_root_eq_before
#check FastConfirmation.Spec.Execution.completedPrefix_noConflict_endpoint_descends_before

-- These checks elaborate the statement types, not only their field names.
open FastConfirmation.Spec

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root) :
    ConfirmedRootSafeFromNextSlot cfg ext =
      (∀ E : Execution Root,
        E.NextSlotSafetyPremises cfg ext →
          ∀ v ∈ E.honest, ∀ n : ℕ,
            ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
              E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
              E.WithinHorizon cfg m →
                E.confirmed cfg ext v n ∈ (E.store cfg ext w m).block_roots ∧
                  is_ancestor (E.store cfg ext w m)
                    (get_head cfg (E.store cfg ext w m))
                    (get_node_for_root (E.confirmed cfg ext v n)) = true) := rfl

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext) :
    ScheduledFFGInterpretation cfg ext E := h.ffg_interpretation

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext) :
    E.ScheduledExecutionPremises cfg ext := h.scheduled_execution

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext) :
    E.ScheduledFCRCallPremises cfg ext := h.call_conditions

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext) :
    E.ImportedBlockFinalizationLag cfg ext h.ffg_interpretation :=
  h.imported_block_finalization_lag

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext) :
    h.ffg_interpretation.state.EventualCheckpointInclusion cfg ext :=
  h.checkpoint_inclusion

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext) :
    h.ffg_interpretation.state.LinkCheckpointAgreement :=
  h.link_checkpoint_agreement

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.ScheduledFCRCallPremises cfg ext) :
    NextSlotSynchronyPremises cfg ext E := h.synchrony

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.ScheduledFCRCallPremises cfg ext) :
    Phase0SourceCoherence cfg ext := h.source_coherence

example {Root : Type*} [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (h : E.ScheduledFCRCallPremises cfg ext) :
    Phase0BoundarySourceCoherence cfg ext := h.boundary_source_coherence

-- Include every field type in the record fingerprint. The claim value is included
-- because its declaration type alone is `Prop`.
run_cmd do
  let env ← getEnv
  let records : List Name := [
    `FastConfirmation.Spec.ReviewClaims,
    `FastConfirmation.Spec.Execution.NextSlotSafetyPremises,
    `FastConfirmation.Spec.Execution.ScheduledExecutionPremises,
    `FastConfirmation.Spec.Execution.ScheduledFCRCallPremises,
    `FastConfirmation.Spec.NextSlotSynchronyPremises,
    `FastConfirmation.Spec.BeaconExternalsPremises,
    `FastConfirmation.Spec.ByzantineWeightPremises,
    `FastConfirmation.Spec.HonestBehavior,
    `FastConfirmation.Spec.ScheduledFFGInterpretation,
    `FastConfirmation.Spec.AcceptedBlockFFGState,
    `FastConfirmation.Spec.FFGStateReadAgreement,
    `FastConfirmation.Spec.FFGStateAndCheckpointReadAgreement,
    `FastConfirmation.Spec.EventualCheckpointInclusion,
    `FastConfirmation.Spec.Execution.IncludedAttestationEvidence,
    `FastConfirmation.Spec.Execution.IncludedAttestationFidelity,
    `FastConfirmation.Spec.FFGInterpretationFidelity,
    `FastConfirmation.Spec.EpochCheckpointProjectionLaws,
    `FastConfirmation.Spec.IncludedSupermajorityLink]
  let mut fingerprint : UInt64 := 0
  for record in records do
    let some info := env.find? record
      | throwError "missing review record {record}"
    fingerprint := hash (fingerprint, record, info.type)
    for field in getStructureFields env record do
      let fieldName := record.str field.getString!
      let some fieldInfo := env.find? fieldName
        | throwError "missing review field {fieldName}"
      fingerprint := hash (fingerprint, fieldName, fieldInfo.type)
  match env.find? `FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot with
  | some (.defnInfo info) =>
      fingerprint := hash (fingerprint, info.value)
  | _ => throwError "missing claim definition"
  unless fingerprint == (14368330899410285068 : UInt64) do
    throwError "review surface statement type changed: {fingerprint}"
  IO.println s!"review surface types passed ({fingerprint})"
