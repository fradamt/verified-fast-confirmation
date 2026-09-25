module
public import FastConfirmationProofs.Weak.Safety.WeakOneShotSafetyClosed
public import FastConfirmationProofs.Weak.Safety.TrustedWeakObserverStrictCallFilterInputs
public import FastConfirmationProofs.Weak.Safety.TrustedWeakObserverCoherence

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem trusted_weak_safeFrom_observerCall_closed_lazy
    {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.AcceptedExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1)))) :
    E.SafeFrom cfg ext (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (n + 1) := by
  have hA := hW.base
  have hWM := hW.toTrustedMarginAssumptions cfg ext E B hT hanchor hboundary
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hstore : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hn1H hcall
  have hbranch := trace.candidateHistoryCallBranch (cfg := cfg) (ext := ext)
  cases hbranch with
  | carriedUnchanged _ hselector =>
      rw [hselector.result_eq_input cfg ext]
      simpa only [hstartEq] using hbase
  | finalizedResetUnchanged _ hselector =>
      rw [hselector.result_eq_input cfg ext]
      simpa only [hstartEq] using hbase
  | observedResetUnchanged _ hselector =>
      rw [hselector.result_eq_input cfg ext]
      simpa only [hstartEq] using hbase
  | strictSelected horigin hselector =>
      rw [hselector.result_eq]
      exact weak_safeFrom_find_latest_confirmed_descendant_discharged cfg ext
        hWM hwalkDomain (n + 1) hn1H (E.weakFcrStep cfg ext obs n) hstore
        trace.afterObserved hinput hbase
        (fun _ => by
          rw [← hselector.result_eq]
          exact
            Weak.StrictSelectorAdvanceAt.trusted_observerCall_selectedStrictEdgeFilterSupplyAt_lazy
              cfg ext B hT hA.synchrony hA.static_validators
              hA.byzantine_bound hA.domain  hanchor hboundary hDelay
              hphase0 hpaper P V hanchorExact hCbase hfit hWM.coherence hprior
              hn1H hcall hinput hbase horigin hselector)

end Execution
end FastConfirmation.Spec
end
