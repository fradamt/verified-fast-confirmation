import FastConfirmationStatements
import Lean.Util.FoldConsts

/-! Check that every authored Statements declaration is reachable from the
safety claim type. -/

open Lean Elab Command

private def moduleOf? (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  env.header.moduleNames[idx.toNat]?

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
        | some info =>
            reachableFrom env (info.getUsedConstantsAsSet.toList ++ rest) seen

private def isSourceDeclaration (env : Environment) (decl : Name) : Bool :=
  if decl.isInternalDetail || (env.getProjectionFnInfo? decl).isSome then false
  else
    match env.find? decl with
    | some (.ctorInfo _) | some (.recInfo _) => false
    | some _ =>
        let final := decl.getString!
        final != "casesOn" && final != "recOn" && final != "noConfusion" &&
        final != "noConfusionType" && final != "ctorIdx" &&
          final != "below" && final != "brecOn" &&
          !final.startsWith "_sizeOf" && !decl.toString.contains ".mk."
    | none => false

run_cmd do
  let env ← getEnv
  let reachable := reachableFrom env
    [``FastConfirmation.Spec.ReviewClaims, ``FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot]
  let statementDecls := env.const2ModIdx.keysArray.toList.filter fun decl =>
    (moduleOf? env decl).any fun m =>
      m.toString == "FastConfirmationStatements" ||
        m.toString.startsWith "FastConfirmationStatements."
  let sources := statementDecls.filter (isSourceDeclaration env)
  let unreachable := sources.filter fun decl =>
    !reachable.contains decl
  IO.println s!"STATEMENT_DECL_COUNT {statementDecls.length}"
  IO.println s!"STATEMENT_SOURCE_COUNT {sources.length}"
  IO.println s!"STATEMENT_REACHABLE_COUNT {(sources.filter reachable.contains).length}"
  IO.println "STATEMENT_APPROVED_COUNT 0"
  IO.println s!"STATEMENT_UNREACHABLE_COUNT {unreachable.length}"
  for decl in sources.mergeSort (Name.quickCmp · · |>.isLE) do
    let status := if reachable.contains decl then "SR" else "SU"
    IO.println s!"{status}\t{(moduleOf? env decl).getD `unknown}\t{decl}"
  -- Lean-derived direct fields of claim-reachable premise records. The full
  -- inventory audit uses these PF rows instead of the source regex.
  let premiseFields := env.const2ModIdx.keysArray.toList.filter fun decl =>
    (env.getProjectionFnInfo? decl).isSome && reachable.contains decl.getPrefix &&
      (getStructureFields env decl.getPrefix).toList.any
        (fun field => field.getString! == decl.getString!) &&
      (moduleOf? env decl).any (fun m =>
        m.toString.startsWith "FastConfirmationStatements.Premises.")
  for decl in premiseFields.mergeSort (Name.quickCmp · · |>.isLE) do
    IO.println s!"PF\t{(moduleOf? env decl).getD `unknown}\t{decl}"
  for decl in [``FastConfirmation.Spec.EpochEndsFitUint64,
               ``FastConfirmation.Spec.BeaconFunctionInterface.AnchorCommitsToState] do
    if reachable.contains decl then
      IO.println s!"RB\t{decl}"
  unless unreachable.isEmpty do
    throwError "statement source contains {unreachable.length} unapproved declarations"
