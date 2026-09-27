import FastConfirmationStatements
import FastConfirmationInternal.FFG.InterpretationFidelity
import FastConfirmationProofs.ReviewTheorem
import Lean
import Lean.Util.FoldConsts
import FastConfirmationProofs.FFG.SelectedSource.TruncatedPredictionPinning
import FastConfirmationProofs.FCRRule.PredictionSupport
import FastConfirmationProofs.FCRRule.PredictionSupportGeometry

/-! Pin the reviewed claim, premise record fields, and the review theorem's type. -/

open Lean Elab Command

private partial def reachableFrom (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | decl :: rest =>
      if seen.contains decl then reachableFrom env rest seen
      else
        let seen := seen.insert decl
        match env.find? decl with
        | none => reachableFrom env rest seen
        | some info => reachableFrom env (info.getUsedConstantsAsSet.toList ++ rest) seen

private def isProjectDeclaration (env : Environment) (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | none => false
  | some idx =>
      let moduleName := (env.allImportedModuleNames[idx.toNat]!).toString
      moduleName.startsWith "FastConfirmation"

private def declarationValueHash (info : ConstantInfo) : UInt64 :=
  match info with
  | .defnInfo value => hash value.value
  | .thmInfo value => hash value.value
  | .opaqueInfo value => hash value.value
  | _ => 0

run_cmd do
  let env ← getEnv
  let checkFields (name : Name) (expected : List String) := do
    let actual := (getStructureFields env name).toList.map (fun field => field.getString!)
    if actual != expected then
      throwError "unexpected fields for {name}: {actual}; expected {expected}"
  checkFields `FastConfirmation.Spec.ReviewClaims
    ["confirmed_root_safe_from_next_slot"]
  checkFields `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.SafetyPremises
    ["admissible", "genesis", "horizon_scope", "whole_seconds", "wellFormed",
     "externals_coherence", "honest_behavior", "body_attestations_delivered", "synchrony",
     "static_validators", "byzantine_bound", "epoch_ends_fit", "slots_per_epoch_gt_one",
     "epoch_one_finalization_scope", "checkpoint_inclusion"]
  checkFields `FastConfirmation.Spec.CheckpointInclusionView
    ["BlockAt", "Included", "formed", "C", "GJ", "GU", "checkpoint_epoch"]
  checkFields `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge
    ["setup", "states", "blocks", "base"]
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
     "anchor_state_checkpoint_epoch", "committees_agree", "honest_attestation_valid", "valid_attestation_honest",
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

example (Root : Type) [LinearOrder Root] [Inhabited Root] :
    FastConfirmation.Spec.ReviewClaims Root :=
  FastConfirmation.Spec.review_claims Root

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

example (Root : Type) [LinearOrder Root] [Inhabited Root] :
    ConfirmedRootSafeFromNextSlot Root =
      (∀ (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root),
        B.SafetyPremises E →
          ∀ v ∈ E.honest, ∀ n : ℕ,
            ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
              E.slot_at B.setup.cfg n + 1 ≤ E.slot_at B.setup.cfg m →
              E.WithinHorizon B.setup.cfg m →
                E.confirmed B.setup.cfg B.interface v n ∈
                    (E.store B.setup.cfg B.interface w m).block_roots ∧
                  is_ancestor (E.store B.setup.cfg B.interface w m)
                    (get_head B.setup.cfg (E.store B.setup.cfg B.interface w m))
                    (get_node_for_root (E.confirmed B.setup.cfg B.interface v n)) = true) := rfl

example {Root : Type} [LinearOrder Root] [Inhabited Root]
    (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root) (h : B.SafetyPremises E) :
    EventualCheckpointInclusion B.setup.cfg B.interface (B.checkpointInclusionView E) :=
  h.checkpoint_inclusion

example {Root : Type} [LinearOrder Root] [Inhabited Root]
    (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root) :
    (B.checkpointInclusionView E).Included = B.BodyIncludedAt E ∧
      (B.checkpointInclusionView E).formed = B.Carried E ∧
      (B.checkpointInclusionView E).C = B.checkpointAt := ⟨rfl, rfl, rfl⟩

example {Root : Type} [LinearOrder Root] [Inhabited Root]
    (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root) (h : B.SafetyPremises E) :
    NextSlotSynchronyPremises B.setup.cfg B.interface E := h.synchrony

-- The public premise translates to the internal premise record.
noncomputable example {Root : Type} [LinearOrder Root] [Inhabited Root]
    (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root) (h : B.SafetyPremises E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ} (hn : E.WithinHorizon B.setup.cfg n) :
    E.NextSlotSafetyPremises B.setup.cfg B.interface :=
  h.nextSlotSafetyPremises hv hn

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
    `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.SafetyPremises,
    `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge,
    `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.Admissible,
    `FastConfirmation.Spec.ConcreteFFG.FFGSetup,
    `FastConfirmation.Spec.ConcreteFFG.FFGSetup.Admissible,
    `FastConfirmation.Spec.ConcreteFFG.StateCommitment,
    `FastConfirmation.Spec.ConcreteFFG.BlockCommitment,
    `FastConfirmation.Spec.CheckpointInclusionView,
    `FastConfirmation.Spec.NextSlotSynchronyPremises,
    `FastConfirmation.Spec.BeaconExternalsPremises,
    `FastConfirmation.Spec.ByzantineWeightPremises,
    `FastConfirmation.Spec.HonestBehavior,
    `FastConfirmation.Spec.EventualCheckpointInclusion,
    `FastConfirmation.Spec.StaticValidatorSet,
    `FastConfirmation.Spec.WellFormedExecution,
    `FastConfirmation.Spec.HorizonVoteDeliveryLookahead,
    `FastConfirmation.Spec.SourceTargetLinkSupportAt]
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
  -- Include definition bodies and nested premise records in the claim-type
  -- dependency closure. A change to a Prop-valued def can change the theorem
  -- even when its declaration type remains `Prop`.
  let reachable := reachableFrom env
    [``FastConfirmation.Spec.ReviewClaims, ``FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot]
  let declarations := (reachable.toList.filter (isProjectDeclaration env)).mergeSort
    (fun a b => (Name.quickCmp a b).isLE)
  for decl in declarations do
    let some info := env.find? decl
      | throwError "missing reachable declaration {decl}"
    fingerprint := hash (fingerprint, decl, info.type, declarationValueHash info)
  match env.find? `FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot with
  | some (.defnInfo info) =>
      fingerprint := hash (fingerprint, info.value)
  | _ => throwError "missing claim definition"
  unless fingerprint == (7590744976943499440 : UInt64) do
    throwError "review surface statement type changed: {fingerprint}"
  IO.println s!"review surface types passed ({fingerprint})"
