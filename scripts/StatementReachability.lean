import FastConfirmationStatements
import Lean.Util.FoldConsts

/-! Check that every authored Statements declaration is reachable from the review claims. -/

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

-- The strict-prefix counterexample's public environment record has a
-- `Synchrony` field, so its theorem type needs this older premise bundle.
-- The finite next-slot witness states paper support through the accepted
-- FFG state's specialization, so its theorem type needs that abbreviation.
private def approved : List Name := [
  ``FastConfirmation.Spec.Synchrony,
  ``FastConfirmation.Spec.AcceptedChainFFGState.PaperA32SupportThroughoutEpoch
]

run_cmd do
  let env ← getEnv
  -- The weak rule keeps separate public statement roots, including its open
  -- live claim. Trace and prediction predicates used by the weak proof surface
  -- remain explicit roots until they are assembled into a weak review bundle.
  let roots : List Name := [
    ``FastConfirmation.Spec.ReviewClaims,
    ``FastConfirmation.Spec.findLatestSelectedTrace,
    ``FastConfirmation.Spec.FCRPredictionSupportAt,
    ``FastConfirmation.Spec.CompleteEvidence,
    ``FastConfirmation.Spec.tentativeLoopTrace,
    ``FastConfirmation.Spec.Weak.CertificateHonestSupporter,
    ``FastConfirmation.Spec.Weak.CertificateDissemination,
    ``FastConfirmation.Spec.WeakSpec_Monotonicity_live,
    ``FastConfirmation.Spec.Execution.WeakObserverMarginAssumptions,
    ``FastConfirmation.Spec.Execution.WeakObserverAssumptions,
    ``FastConfirmation.Spec.Execution.AcceptedHistoricalA32CompletedPrefixCallSupplement,
    ``FastConfirmation.Spec.CurrentTargetSelectedEdge,
    ``FastConfirmation.Spec.prevEpochLoopTrace,
    ``FastConfirmation.Spec.PreviousEpochSelectedEdge,
    ``FastConfirmation.Spec.HonestVotesSupportTarget
  ]
  let reachable := reachableFrom env roots
  let statementDecls := env.const2ModIdx.keysArray.toList.filter fun decl =>
    (moduleOf? env decl).any fun m =>
      m.toString == "FastConfirmationStatements" ||
        m.toString.startsWith "FastConfirmationStatements."
  let sources := statementDecls.filter (isSourceDeclaration env)
  let unreachable := sources.filter fun decl =>
    !reachable.contains decl && !approved.contains decl
  IO.println s!"STATEMENT_DECL_COUNT {statementDecls.length}"
  IO.println s!"STATEMENT_SOURCE_COUNT {sources.length}"
  IO.println s!"STATEMENT_REACHABLE_COUNT {(sources.filter reachable.contains).length}"
  IO.println s!"STATEMENT_APPROVED_COUNT {(sources.filter approved.contains).length}"
  IO.println s!"STATEMENT_UNREACHABLE_COUNT {unreachable.length}"
  for decl in sources.mergeSort (Name.quickCmp · · |>.isLE) do
    let status := if reachable.contains decl then "SR"
      else if approved.contains decl then "SH" else "SU"
    IO.println s!"{status}\t{(moduleOf? env decl).getD `unknown}\t{decl}"
  unless unreachable.isEmpty do
    throwError "statement source contains {unreachable.length} unapproved declarations"
