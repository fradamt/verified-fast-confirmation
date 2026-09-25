import FastConfirmationStatements
import FastConfirmationProofs.Weak.LocalFFG.ObserverHeadlines
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
            -- Proof bodies do not make a declaration part of a theorem's statement.
            let deps := match info with
              | .thmInfo _ => info.type.getUsedConstantsAsSet
              | _ => info.getUsedConstantsAsSet
            reachableFrom env (deps.toList ++ rest) seen

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
  ``FastConfirmation.Spec.CausalCarrierFFGState.PaperA32SupportThroughoutEpoch
]

run_cmd do
  let env ← getEnv
  -- The weak rule keeps separate public statement roots, including its open
  -- live claim. Trace and prediction predicates used by the weak proof surface
  -- remain explicit roots until they are assembled into a weak review bundle.
  let roots : List Name := [
    ``FastConfirmation.Spec.ReviewClaims,
    ``FastConfirmation.Spec.Execution.nonhonest_weak_confirmed_root_safe_from_next_slot,
    ``FastConfirmation.Spec.Execution.nonhonest_weak_confirmed_root_on_honest_heads_from_next_slot,
    ``FastConfirmation.Spec.Execution.ActualRunFFG.actualRun_exactInterpretation_observer_independent,
    ``FastConfirmation.Spec.findLatestSelectedTrace,
    ``FastConfirmation.Spec.FCRPredictionSupportAt,
    ``FastConfirmation.Spec.CompletePriorSlotStoreEvidence,
    ``FastConfirmation.Spec.tentativeLoopTrace,
    ``FastConfirmation.Spec.Weak.CertificateHonestSupporter,
    ``FastConfirmation.Spec.Weak.CertificateDisseminationObligation,
    ``FastConfirmation.Spec.WeakStoredRootMonotonicity,
    ``FastConfirmation.Spec.Execution.WeakObserverMarginPremises,
    ``FastConfirmation.Spec.Execution.WeakObserverPremises,
    ``FastConfirmation.Spec.Execution.WeakCompletedFCRCallSupplement,
    ``FastConfirmation.Spec.Execution.WeakObserverRestrictedPremises,
    -- Keep the honest-store adapter and the guarded accepted-link surface visible.
    ``FastConfirmation.Spec.Execution.CausalCarrierAttestationEvidence,
    ``FastConfirmation.Spec.Execution.CausalCarrierAttestationRelation,
    ``FastConfirmation.Spec.Execution.CausalCarrierAttestationRelation.relation,
    ``FastConfirmation.Spec.CausalCarrierFFGState.GuardedExactLinkValidity,
    ``FastConfirmation.Spec.Execution.SameOutsideObserver,
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
