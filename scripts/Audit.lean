import FastConfirmation
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.Old
import Lean.DeclarationRange
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-!
# Project trust audit

This file is run with `lake env lean scripts/Audit.lean` after the project has
been built. It is deliberately outside the library import graph.
-/

open Lean Elab Command

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def publicWitnesses : Array Name :=
  #[
    ``FastConfirmation.Spec.review_claims,
    ``FastConfirmation.Spec.confirmed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.live_confirmed_root_monotonicity,
    ``FastConfirmation.Spec.Execution.NextSlotSafetyPremises.selected_result_safe_from_next_slot_of_scheduled_call,
    ``FastConfirmation.Spec.NextSlotPremiseWitness.finite_execution_satisfies_premises,
    ``FastConfirmation.Spec.NextSlotPremiseWitness.next_slot_premises_nonempty,
    ``FastConfirmation.Spec.StrictPrefixExtraQuery.extra_query_changes_head_counterexample,
    ``FastConfirmation.Spec.PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample,
    ``FastConfirmation.LMDGhost.head_agreement_after_confirmation,
    ``FastConfirmation.LMDGhost.confirmed_block_safety,
    ``FastConfirmation.LMDGhost.confirmed_block_monotonicity,
    ``FastConfirmation.HFC.gate_confirmed_block_safety,
    ``FastConfirmation.HFC.gate_confirmed_block_monotonicity,
    ``FastConfirmation.HFC.rule_confirmed_block_safety,
    ``FastConfirmation.HFC.rule_confirmed_block_monotonicity,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_find_latest_confirmed_descendant,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_find_latest_confirmed_descendant_from_finalized,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head_from_finalized,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head_discharged,
    ``FastConfirmation.Spec.Execution.weak_confirmed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.Execution.weak_confirmed_root_on_honest_heads_from_next_slot,
    ``FastConfirmation.Spec.Execution.weakObserverRestrictedPremises_observer_independent,
    ``FastConfirmation.Spec.replay_eq_weakStore,
    ``FastConfirmation.Spec.replay_eq_weakFcr,
    ``FastConfirmation.Spec.replay_eq_weakConfirmed,
    ``FastConfirmation.Spec.replay_bounded_witness,
    ``FastConfirmation.Spec.Containment.Negative.not_handler_preservation,
    ``FastConfirmation.Spec.Containment.Negative.not_one_shot_containment,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.raw_score_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.attestation_score_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.block_support_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.adversarial_weight_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.block_adversarial_weight_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.support_discount_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.safety_threshold_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.is_one_confirmed_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.honest_ffg_support_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.current_target_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.carrier_certificate,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.witness_certificate,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.no_conflict_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.prev_epoch_loop_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.tentative_loop_eq,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.certified_head_eq_of_certificate,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence.descendant_eq_of_head_eq,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.before_head_confirms_nonanchor,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.before_head_is_certified,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.after_head_carrier_differs,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.after_head_confirms_nonanchor,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.prior_slot_committees_present,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.after_head_prior_slot_committees_present,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.complete_evidence,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.after_head_complete_evidence,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.nonvacuity,
    ``FastConfirmation.Spec.CompleteEvidenceWitness.certified_head_equality_false
  ]

private def unexpectedAxioms (axioms : Array Name) : Array Name :=
  axioms.filter fun name => !allowedAxioms.contains name

private def isProjectModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some moduleIdx =>
      let moduleName := (env.allImportedModuleNames[moduleIdx.toNat]!).toString
      moduleName == "FastConfirmation" ||
        (#["FastConfirmationModel", "FastConfirmationStatements",
          "FastConfirmationInternal", "FastConfirmationProofs",
          "FastConfirmationWitnesses", "FastConfirmationPaper"].any
          fun libName => moduleName == libName || moduleName.startsWith (libName ++ "."))

private def isGeneratedSafePartial (env : Environment) (name : Name)
    (info : ConstantInfo) : CommandElabM Bool := do
  let some parent := Lean.Compiler.isUnsafeRecName? name
    | return false
  unless info.isPartial && !info.isUnsafe do return false
  /- Source declarations have their own range. Equation-compiler details do
  not; `findDeclarationRanges?` would incorrectly fall back to the parent. -/
  if (← Lean.findDeclarationRangesCore? name).isSome then
    return false
  match env.find? parent with
  | some parentInfo =>
      return isProjectModule env parent &&
        env.getModuleIdxFor? name == env.getModuleIdxFor? parent &&
        !parentInfo.isPartial && !parentInfo.isUnsafe &&
        info.type == parentInfo.type
  | none => return false

elab "audit_project_trust" : command => do
  let env ← getEnv
  unless publicWitnesses.size == 57 do
    throwError "public theorem witness set must contain exactly 57 declarations"
  unless publicWitnesses.toList.eraseDups.length == publicWitnesses.size do
    throwError "public theorem witness set contains duplicate declarations"

  let mut projectDeclarations := 0
  let mut projectTheorems := 0
  let mut generatedPartials := 0
  for (name, info) in env.constants do
    if isProjectModule env name then
      projectDeclarations := projectDeclarations + 1
      if info.isUnsafe then
        throwError "project declaration is unsafe: {name}"
      if info.isPartial then
        unless ← isGeneratedSafePartial env name info do
          throwError "project declaration is partial: {name}"
        generatedPartials := generatedPartials + 1
      if Lean.isExtern env name then
        throwError "project declaration has an extern implementation: {name}"
      if (Lean.Compiler.getImplementedBy? env name).isSome then
        throwError "project declaration has an implemented_by override: {name}"
      if info.type.hasSorry then
        throwError "project declaration type contains sorryAx: {name}"
      match info with
      | .axiomInfo _ =>
          throwError "project declaration is an axiom/constant: {name}"
      | .opaqueInfo _ =>
          throwError "project declaration is opaque: {name}"
      | .defnInfo value =>
          if value.value.hasSorry then
            throwError "project definition body contains sorryAx: {name}"
      | .thmInfo value =>
          projectTheorems := projectTheorems + 1
          if value.value.hasSorry then
            throwError "project theorem body contains sorryAx: {name}"
      | _ => pure ()
      let bad := unexpectedAxioms (← Lean.collectAxioms name)
      unless bad.isEmpty do
        throwError "project declaration {name} uses disallowed axioms: {bad.toList}"

  for name in publicWitnesses do
    match env.find? name with
    | some (.thmInfo _) =>
        let axioms ← Lean.collectAxioms name
        let bad := unexpectedAxioms axioms
        unless bad.isEmpty do
          throwError "public theorem {name} uses disallowed axioms: {bad.toList}"
    | some _ =>
        throwError "public witness exists but is not a theorem: {name}"
    | none =>
        throwError "public theorem witness is missing: {name}"

  logInfo m!"project trust audit passed: {projectDeclarations} declarations, \
    {projectTheorems} theorems, {generatedPartials} generated partials, \
    {publicWitnesses.size} public witnesses"

audit_project_trust
