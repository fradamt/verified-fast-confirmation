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
    ``FastConfirmation.Spec.acceptedSpec_safety_next_slot,
    ``FastConfirmation.Spec.Execution.AcceptedActualFCRNextSlotSafetyAssumptions.findLatestConfirmedDescendant_safeFrom_of_actualCall,
    ``FastConfirmation.Spec.AcceptedActualFCRJointNonVacuityFinal.witnessJointNonvacuity,
    ``FastConfirmation.Spec.AcceptedActualFCRJointNonVacuityFinal.acceptedActualFCRNextSlotSafetyAssumptions_nonvacuous,
    ``FastConfirmation.Spec.AcceptedStrictPrefixExtraQueryCounterexample.strict_prefix_extra_query_counterexample,
    ``FastConfirmation.Spec.AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample.pinned_economics_strict_prefix_extra_query_counterexample,
    ``FastConfirmation.LMDGhost.HeadFutureAgreement_proved,
    ``FastConfirmation.LMDGhost.Theorem1_Safety_proved,
    ``FastConfirmation.LMDGhost.Theorem1_Monotonicity_proved,
    ``FastConfirmation.HFC.HFC_Safety_proved,
    ``FastConfirmation.HFC.HFC_Monotonicity_proved,
    ``FastConfirmation.HFC.HFC_Safety_Alg1_proved,
    ``FastConfirmation.HFC.HFC_Monotonicity_Alg1_proved,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_find_latest_confirmed_descendant,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_find_latest_confirmed_descendant_from_finalized,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head_from_finalized,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head_discharged,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_observerCall_closed,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head_closed,
    ``FastConfirmation.Spec.Execution.weak_safeFrom_observerCall_closed_from_finalized,
    ``FastConfirmation.Spec.Execution.weak_confirmed_head_closed_from_finalized
  ]

private def unexpectedAxioms (axioms : Array Name) : Array Name :=
  axioms.filter fun name => !allowedAxioms.contains name

private def isProjectModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some moduleIdx =>
      let moduleName := (env.allImportedModuleNames[moduleIdx.toNat]!).toString
      moduleName == "FastConfirmation" ||
        moduleName.startsWith "FastConfirmation."

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
  unless publicWitnesses.size == 23 do
    throwError "public theorem witness set must contain exactly 23 declarations"
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
