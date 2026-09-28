import FastConfirmationStatements
import Lean.Util.FoldConsts
import Lean.DeclarationRange

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

-- BEGIN input structures (scripts/PremiseFieldUse.lean has the same block;
-- scripts/test_input_discovery.py runs both copies)
private def isProjectDeclaration (env : Environment) (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | none => false
  | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "FastConfirmation"

/-- The reduced head constant of a binder or field type. An antecedent
of an implication is a binder, so the closure below does not enter it. -/
private def resultHead? (type : Expr) : Meta.MetaM (Option Name) :=
  Meta.withTransparency .default <|
    Meta.forallTelescopeReducing type fun _ body => do
      return (← Meta.whnf body).getAppFn.constName?

/-- A proof-valued field: its type, after its binders, is a proposition. -/
private def isPropValued (type : Expr) : Meta.MetaM Bool :=
  Meta.forallTelescope type fun _ body => Meta.isProp body

/-- A structure whose values are proofs: its type ends in `Prop`. -/
private def isPropStructure (type : Expr) : Meta.MetaM Bool :=
  Meta.forallTelescope type fun _ body => return body.isProp

/-- Input structures of the claim: the project structures that are binder
types of `ConfirmedRootSafeFromNextSlot`, closed under the result types of
their fields. Their proposition-valued fields are the proof-valued inputs of
the claim, recursively: the premise records and the conditions that the
configuration, preset, scope, and commitment data carry. -/
private def inputStructures (env : Environment) : Meta.MetaM (Array Name) := do
  let some (.defnInfo claim) := env.find? ``FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot
    | throwError "missing claim definition"
  let mut todo : Array Name ← Meta.lambdaTelescope claim.value fun _ body =>
    Meta.forallTelescope body fun binders _ => do
      let mut heads := #[]
      for binder in binders do
        if let some head ← resultHead? (← Meta.inferType binder) then
          heads := heads.push head
      return heads
  let mut seen : NameSet := {}
  let mut order := #[]
  while !todo.isEmpty do
    let s := todo.back!
    todo := todo.pop
    unless isStructure env s && isProjectDeclaration env s && !seen.contains s do continue
    seen := seen.insert s
    order := order.push s
    for field in getStructureFields env s do
      let some info := env.find? (s ++ field) | continue
      if let some head ← resultHead? info.type then
        todo := todo.push head
  return order
-- END input structures

private def isSourceDeclaration (env : Environment) (decl : Name) : CommandElabM Bool := do
  if (env.getProjectionFnInfo? decl).isSome || isAuxRecursor env decl ||
      isNoConfusion env decl || (← isRec decl) then return false
  else
    match env.find? decl with
    | some (.ctorInfo _) | some (.recInfo _) => return false
    | some _ => return (← findDeclarationRanges? decl).isSome
    | none => return false

run_cmd do
  let env ← getEnv
  let reachable := reachableFrom env
    [``FastConfirmation.Spec.ReviewClaims, ``FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot]
  let statementDecls := env.const2ModIdx.keysArray.toList.filter fun decl =>
    (moduleOf? env decl).any fun m =>
      m.toString == "FastConfirmationStatements" ||
        m.toString.startsWith "FastConfirmationStatements."
  let sources ← statementDecls.filterM (isSourceDeclaration env)
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
  -- Lean-derived inventory fields (PF rows). The full inventory audit uses
  -- them instead of the source regex. They are every direct field of a
  -- claim-reachable structure in `Statements.Premises`, and every
  -- proposition-valued field of an input structure, in Model or Statements.
  -- A REC row marks a field whose type is itself a proposition-valued input
  -- structure: a record whose own fields have rows.
  let premiseFields := env.const2ModIdx.keysArray.toList.filter fun decl =>
    (env.getProjectionFnInfo? decl).isSome && reachable.contains decl.getPrefix &&
      (getStructureFields env decl.getPrefix).toList.any
        (fun field => field.getString! == decl.getString!) &&
      (moduleOf? env decl).any (fun m =>
        m.toString.startsWith "FastConfirmationStatements.Premises.")
  let inputs ← liftTermElabM <| inputStructures env
  let mut fields : NameSet := premiseFields.foldl NameSet.insert {}
  let mut records : NameSet := {}
  for s in inputs do
    for field in getStructureFields env s do
      let some info := env.find? (s ++ field) | continue
      unless ← liftTermElabM <| isPropValued info.type do continue
      fields := fields.insert (s ++ field)
      if let some head ← liftTermElabM <| resultHead? info.type then
        if inputs.contains head then
          if let some headInfo := env.find? head then
            if ← liftTermElabM <| isPropStructure headInfo.type then
              records := records.insert (s ++ field)
  IO.println s!"INPUT_STRUCTURE_COUNT {inputs.size}"
  for decl in fields.toList.mergeSort (·.toString ≤ ·.toString) do
    IO.println s!"PF\t{(moduleOf? env decl).getD `unknown}\t{decl}"
  for decl in records.toList.mergeSort (·.toString ≤ ·.toString) do
    IO.println s!"REC\t{decl}"
  for decl in [``FastConfirmation.Spec.EpochEndsFitUint64,
               ``FastConfirmation.Spec.BeaconFunctionInterface.AnchorCommitsToState] do
    if reachable.contains decl then
      IO.println s!"RB\t{decl}"
  unless unreachable.isEmpty do
    throwError "statement source contains {unreachable.length} unapproved declarations"
