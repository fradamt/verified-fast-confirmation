import FastConfirmation.Spec.Proof.WeakOneShotSafetyNative
import FastConfirmation.Spec.Proof.WeakObserverStrictCallFilterInputs

/-!
# Spec / Proof / WeakOneShotSafetyClosed

Stage S8 of the `hfilter`-discharge wave: the closed one-shot weak safety
theorem at an actual FCR call.

`WeakOneShotSafetyNative.lean`'s `weak_safeFrom_find_latest_confirmed_
descendant_discharged` (Stage J-f) discharges `hmargin` but still carries
`hfilter : Weak.SelectedStrictEdgeFilterSupplyAt …` as a premise, over an
*arbitrary* selector input `lcr`. `WeakObserverStrictCallFilterInputs.lean`'s
`Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_
lazy` (Stage S7/X1) discharges that Prop in full, but only at the *actual*
weak call trajectory (`E.weakFcrStep` / `E.weakGetLatestConfirmedTraceAt`),
only in the branch where the selector genuinely strictly advances
(`Weak.StrictSelectorAdvanceAt`), and against a `hprior :
Weak.ObserverPriorCallWriteBackSafe` supplied by the caller.

This file assembles the two into the one-call step: at a genuine weak FCR
call, with no assumption about which of the four candidate-history branches
the call actually took, the selector's result is `SafeFrom` at the query
second — with no `hmargin`, no `hfilter`, and no residual filter-supply
obligation of any kind.

This content cannot live in either input file: it needs
`WeakOneShotSafetyNative.lean`'s discharged headline (itself downstream of
`WeakCoveredMarginConstruction.lean`/`WeakSelectedEdgeGeometry.lean`) *and*
`WeakObserverStrictCallFilterInputs.lean`'s closed supplier (downstream of
the whole S1–S7 weak phase-dispatcher stack), and neither of those two
already imports the other.

## Assembly

`E.weakGetLatestConfirmedTraceAt cfg ext obs n` has an exact four-way
candidate-history classification
(`Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch`, mirroring the
strong `CandidateHistoryCallBranch`):

* the three "unchanged" branches (`carriedUnchanged`, `finalizedResetUnchanged`,
  `observedResetUnchanged`) all give `trace.result = trace.afterObserved`
  (`Weak.SelectorUnchangedAt.result_eq_input`), so the caller's own `hbase`
  input safety closes the goal directly, once rewritten from the query
  slot's start to the actual call second `n + 1`
  (`Execution.slot_start_eq_succ_of_advance_minimal`, the same "between"
  fact the strong actual-call facade uses);
* the `strictSelected` branch exposes exactly
  `horigin : Weak.OrderedCandidateInputOrigin` and
  `hselector : Weak.StrictSelectorAdvanceAt` for the real trace — precisely
  what the closed supplier consumes. Its output is fed, through
  `hselector.result_eq`, into `weak_safeFrom_find_latest_confirmed_descendant_
  discharged`'s `hfilter` slot.

## The single consumer

The only consumer of this step is the weak safety fold
(`WeakTrajectorySafety.lean`), which is the only context that can supply
`hprior` — it is the fold's own strengthened induction hypothesis at seconds
strictly below `n`.  A *one-shot* statement cannot
(`docs/weak-final-wave.md` §5.2), which is why the one-shot closed witnesses
that used to live here — `weak_safeFrom_observerCall_closed`,
`weak_confirmed_head_closed` and their two `_from_finalized` forms — carried
the eager observer proviso (`observer_helper_provisos`) instead.  Those four
were subsumed by the fold headlines, had no consumers, and existed only as
carriers of that proviso; they were retired together with the proviso
machinery itself.  The audited statements are now the trajectory headlines
(`Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
and friends).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 9 — the closed one-call step: no `hmargin`, no `hfilter` -/

/-- **The closed one-shot weak safety step, at an actual FCR call.**

At a genuine weak FCR call (`hcall : E.IsFCRCallAt cfg ext obs n`), with the
call's own candidate input known and `SafeFrom` from the start of the query
slot, the weak selector's actual result is `SafeFrom` at the call's own
second `n + 1` — with no `hmargin`, `hfilter`, or other residual filter-
supply premise: the entire margin/filter chain (Stages G–S7) is discharged
internally, uniformly over which of the four candidate-history branches the
call actually took.

The historical A3.2 call contract is the unchanged 7-field
`E.AcceptedHistoricalA32CompletedPrefixCallAssumptions` together with
`hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n` — a *derived*
trajectory fact, discharged by the weak safety fold's own strengthened
induction hypothesis at seconds strictly below `n`; the crossing payload the
supplier needs is manufactured lazily at the consuming call rather than
assumed up front.

Observer-wise the premise surface is `hW : WeakObserverAssumptions` — the
floor and committee readback at the observer's own store; `obs` is arbitrary
and may be honest.
`ObserverCoherence.justified_root_known` is *derived* here from `B`/`hT`/
`hanchor`/`hboundary` (`WeakObserverAssumptions.toMarginAssumptions`), so it
never appears as a premise. -/
theorem weak_safeFrom_observerCall_closed_lazy
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1)))) :
    E.SafeFrom cfg ext (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (n + 1) := by
  have hA := hW.base
  have hWM := hW.toMarginAssumptions cfg ext E B hT hanchor hboundary
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
            Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_lazy
              cfg ext B hT hA.synchrony hA.static_validators
              hA.byzantine_bound hA.domain hji hanchor hboundary hDelay
              hphase0 hpaper P V hanchorExact hCbase hfit hWM.coherence hprior
              hn1H hcall hinput hbase horigin hselector)

end Execution

end FastConfirmation.Spec
