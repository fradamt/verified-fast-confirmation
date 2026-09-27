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

A Prop field is read when its projection function or its primitive
projection occurs in the proof closure. A structure whose eliminator occurs
is marked, because a destructuring pattern can read a field without a
projection. The check fails when a Prop field of a premise record is not
read and is not in `allowedUnread`.
-/

open Lean Elab Command Meta

private def isProjectModule (env : Environment) (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => (`FastConfirmation).isPrefixOf m || m.toString.startsWith "FastConfirmation"
      | none => false
  | none => false

/-- Premise records: the proof receives a value of each record. Fields of
other structures in the statement closure (the A3.2 view and antecedent,
configuration and bridge data) are listed but are not checked. -/
private def premiseRecords : List Name := [
  `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.SafetyPremises,
  `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.Admissible,
  `FastConfirmation.Spec.ConcreteFFG.FFGSetup.Admissible,
  `FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.ConcreteExternalsPremises,
  `FastConfirmation.Spec.WellFormedExecution,
  `FastConfirmation.Spec.HonestBehavior,
  `FastConfirmation.Spec.NextSlotSynchronyPremises,
  `FastConfirmation.Spec.HorizonVoteDeliveryLookahead,
  `FastConfirmation.Spec.ByzantineWeightPremises,
  `FastConfirmation.Spec.EventualCheckpointInclusion]

/-- Unread premise fields that the documents keep on purpose. None remain. -/
private def allowedUnread : List Name := []

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
  let structs := (stmt.toList.filter fun n => isStructure env n).mergeSort
    (fun a b => (Name.quickCmp a b).isLE)
  let mut failures : Array Name := #[]
  let mut report : Array String := #[]
  for s in structs do
    let fields := getStructureFields env s
    let elim := [s ++ `casesOn, s ++ `rec, s ++ `recOn].any consts.contains
    let isPremise := premiseRecords.contains s
    for h : i in [0:fields.size] do
      let field := fields[i]
      let proj := s ++ field
      let some pinfo := env.find? proj | continue
      let isPropField ← liftTermElabM do
        forallTelescope pinfo.type fun _ body => isProp body
      unless isPropField do continue
      let read := consts.contains proj || projs.contains (s, i)
      let status := if read then "READ" else if elim then "ELIM" else "UNREAD"
      let kind := if isPremise then "premise" else "other"
      report := report.push s!"{status}\t{kind}\t{proj}"
      if isPremise && !read && !allowedUnread.contains proj then
        failures := failures.push proj
  for line in report do
    IO.println line
  IO.println s!"PROOF_CLOSURE {(← seen.get).size} project declarations"
  unless failures.isEmpty do
    throwError "premise fields that no proof reads: {failures.toList}"
  IO.println "premise field use passed"

check_premise_field_use
