import FastConfirmation
import Lean.Util.ForEachExpr

/-!
# Premise field use

Run with `lake env lean scripts/PremiseFieldUse.lean` after the project has
been built. It is outside the library import graph, and its ordinary imports
load proof bodies.

The check computes two closures.

* The statement closure: the constants in the type of
  `ConfirmedRootSafeFromNextSlot` and in the bodies of the definitions that
  it reaches. Each structure in this closure has its Prop-valued fields
  listed.
* The proof closure: the constants in the type and the body of
  `confirmed_root_safe_from_next_slot` and, recursively, of each project
  declaration that they name. It records each projection function and each
  primitive projection (`Expr.proj`) that occurs, and each `casesOn`, `rec`,
  or `recOn` of a listed structure.

The input structures are the project structures that are binder types of
the claim, closed under the result types of their fields. They are found, not
listed: a new nested premise record is an input structure. Their Prop fields
are the proof-valued inputs: the fields of the premise records (kind
`premise`) and the conditions of the configuration, preset, scope, and
commitment data (kind `input`).

A Prop field is read when its projection function or its primitive
projection occurs in the proof closure. A structure whose eliminator occurs
is marked, because a destructuring pattern can read a field without a
projection. The check fails when an input field is not read and is not in
`allowedUnread`, and when a project Prop structure of the statement closure
is neither an input structure nor in `nonInputRecords`. The check is a
syntactic reference check. It does not prove that a read field is logically
necessary.
-/

open Lean Elab Command Meta

private def isProjectModule (env : Environment) (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => (`FastConfirmation).isPrefixOf m || m.toString.startsWith "FastConfirmation"
      | none => false
  | none => false

/-- Unread proof-valued inputs that the documents keep on purpose, each with
its reason. -/
private def allowedUnread : List (Name × String) := [
  (`FastConfirmation.Spec.FixedFFGScope.epoch_order,
   "a well-formedness condition of the scope data; the proof reads the scope epochs directly")]

/-- Proposition-valued structures of the statement closure that are not inputs,
each with its reason. Any other such structure fails the check. -/
private def nonInputRecords : List (Name × String) := [
  (`FastConfirmation.Spec.ReviewClaims, "the public claim record, not an input"),
  (`FastConfirmation.Spec.ConcreteFFG.FinalizationLink,
   "a component of the Model finalization definition, not an input")]

-- BEGIN input structures (the same block as scripts/StatementReachability.lean)
private def isProjectDeclaration (env : Environment) (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | none => false
  | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "FastConfirmation"

/-- The head constant of a field type after all of its binders. An antecedent
of an implication is a binder, so the closure below does not enter it. -/
private def resultHead? (type : Expr) : Meta.MetaM (Option Name) :=
  Meta.forallTelescope type fun _ body => return body.getAppFn.constName?

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

private def exprConsts (e : Expr) : Array Name :=
  e.foldConsts #[] fun c acc => acc.push c

private partial def statementClosure (env : Environment) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := [``FastConfirmation.Spec.ConfirmedRootSafeFromNextSlot]
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | d :: rest =>
        todo := rest
        if seen.contains d then continue
        seen := seen.insert d
        match env.find? d with
        | some (.defnInfo info) =>
            todo := (exprConsts info.type).toList ++ (exprConsts info.value).toList ++ todo
        | some (.thmInfo _) => pure ()
        | some (.inductInfo info) => todo := (exprConsts info.type).toList ++ info.ctors ++ todo
        | some info => todo := (exprConsts info.type).toList ++ todo
        | none => pure ()
  return seen

elab "check_premise_field_use" : command => do
  let env ← getEnv
  -- Proof closure over project declarations.
  let seen ← IO.mkRef ({} : NameSet)
  let projs ← IO.mkRef ({} : Std.HashSet (Name × Nat))
  let consts ← IO.mkRef ({} : NameSet)
  let mut todo : Array Name := #[``FastConfirmation.Spec.confirmed_root_safe_from_next_slot]
  while !todo.isEmpty do
    let d := todo.back!
    todo := todo.pop
    if (← seen.get).contains d then continue
    seen.modify (·.insert d)
    let some info := env.find? d | continue
    let exprs := match info with
      | .defnInfo v => #[v.type, v.value]
      | .thmInfo v => #[v.type, v.value]
      | .opaqueInfo v => #[v.type, v.value]
      | i => #[i.type]
    for e in exprs do
      let found ← IO.mkRef (#[] : Array Name)
      e.forEach fun sub => do
        match sub with
        | .const c _ =>
            consts.modify (·.insert c)
            found.modify (·.push c)
        | .proj s i _ => projs.modify (·.insert (s, i))
        | _ => pure ()
      for c in ← found.get do
        if isProjectModule env c && !(← seen.get).contains c then
          todo := todo.push c
  let consts ← consts.get
  let projs ← projs.get
  let stmt := statementClosure env
  let inputs ← liftTermElabM <| inputStructures env
  let structs := ((stmt.toList.filter fun n => isStructure env n) ++
    (inputs.toList.filter (!stmt.contains ·))).mergeSort (·.toString ≤ ·.toString)
  let allowed := allowedUnread.map (·.1)
  let mut failures : Array Name := #[]
  let mut unclassified : Array Name := #[]
  let mut report : Array String := #[]
  let mut checked := 0
  for s in structs do
    let some sinfo := env.find? s | continue
    let propRecord ← liftTermElabM <| isPropStructure sinfo.type
    let isInput := inputs.contains s
    if propRecord && isProjectDeclaration env s && !isInput &&
        !(nonInputRecords.map (·.1)).contains s then
      unclassified := unclassified.push s
    let fields := getStructureFields env s
    let elim := [s ++ `casesOn, s ++ `rec, s ++ `recOn].any consts.contains
    for h : i in [0:fields.size] do
      let field := fields[i]
      let proj := s ++ field
      let some pinfo := env.find? proj | continue
      unless ← liftTermElabM <| isPropValued pinfo.type do continue
      let read := consts.contains proj || projs.contains (s, i)
      let status := if read then "READ" else if elim then "ELIM" else "UNREAD"
      let kind := if !isInput then "other" else if propRecord then "premise" else "input"
      report := report.push s!"{status}\t{kind}\t{proj}"
      if isInput then
        checked := checked + 1
        if !read && !allowed.contains proj then
          failures := failures.push proj
  for line in report do
    IO.println line
  IO.println s!"PROOF_CLOSURE {(← seen.get).size} project declarations"
  IO.println s!"INPUT_FIELDS {checked} in {inputs.size} input structures"
  unless unclassified.isEmpty do
    throwError "proposition-valued records outside the claim inputs: {unclassified.toList}"
  unless failures.isEmpty do
    throwError "premise or input fields that no proof reads: {failures.toList}"
  for name in allowed do
    unless report.any (·.endsWith s!"\t{name}") do
      throwError "allowed unread field is no longer an input field: {name}"
  IO.println "premise field use passed"

check_premise_field_use
