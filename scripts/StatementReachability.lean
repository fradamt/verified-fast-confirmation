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
-- The interpretation-fidelity records are deliberately outside the safety
-- premise; the full-bundle witnesses prove them for their interpretations.
-- Removing helper_provisos also removes the claim's path to the exact-call
-- trace API and its two vote-support predicates. Keep these existing public
-- proof/witness interfaces by name. They are not safety assumptions. The
-- exact completed-call field list is checked by ReviewSurfaceShape.lean.
private def approved : List Name := [
  ``FastConfirmation.Spec.Synchrony,
  ``FastConfirmation.Spec.CausalCarrierFFGState.PaperA32SupportThroughoutEpoch,
  ``FastConfirmation.Spec.Execution.IncludedAttestationFidelity,
  ``FastConfirmation.Spec.FFGInterpretationFidelity,
  -- Existing public support facts used by witness theorem types.
  ``FastConfirmation.Spec.HonestVotesSupportTarget,
  ``FastConfirmation.Spec.HonestVotesTargetDescendFrom,
  -- Exact-call trace vocabulary used by proof and witness interfaces.
  ``FastConfirmation.Spec.findLatestSelectedTrace,
  ``FastConfirmation.Spec.GetLatestSelectorPhase,
  ``FastConfirmation.Spec.getLatestFinalizedRevertGuard,
  ``FastConfirmation.Spec.tentativeLoopTrace,
  ``FastConfirmation.Spec.getLatestSelectorGuard,
  ``FastConfirmation.Spec.CurrentTargetSelectedEdge,
  ``FastConfirmation.Spec.Execution.IsScheduledFCRCallAt,
  ``FastConfirmation.Spec.LatestConfirmedCallTrace,
  ``FastConfirmation.Spec.getLatestAfterObserved,
  ``FastConfirmation.Spec.GetLatestObservedPhase,
  ``FastConfirmation.Spec.getLatestObservedRestartGuard,
  ``FastConfirmation.Spec.prevEpochLoopTrace,
  ``FastConfirmation.Spec.Execution.fcrStoreAtCall,
  ``FastConfirmation.Spec.getLatestAfterFinalized,
  ``FastConfirmation.Spec.GetLatestFinalizedPhase,
  ``FastConfirmation.Spec.Execution.getLatestConfirmedTraceAt,
  ``FastConfirmation.Spec.getLatestConfirmedTrace
]

run_cmd do
  let env ← getEnv
  let reachable := reachableFrom env [``FastConfirmation.Spec.ReviewClaims]
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
