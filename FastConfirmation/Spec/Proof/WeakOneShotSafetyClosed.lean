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
closed` (Stage S7/X1) discharges that Prop in full, but only at the *actual*
weak call trajectory (`E.weakFcrStep` / `E.weakGetLatestConfirmedTraceAt`) and
only in the branch where the selector genuinely strictly advances
(`Weak.StrictSelectorAdvanceAt`).

This file assembles the two into the headline: at a genuine weak FCR call,
with no assumption about which of the four candidate-history branches the
call actually took, the selector's result is `SafeFrom` at the query second —
with no `hmargin`, no `hfilter`, and no residual filter-supply obligation of
any kind.

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

## The finalized-base composition

`weak_safeFrom_observerCall_closed_from_finalized` mirrors
`WeakFinalizedInput.lean`'s `weak_safeFrom_find_latest_confirmed_descendant_
discharged_from_finalized`, reindexed at the actual-call trajectory. That
existing corollary derives `hlcr`/`hbase` for an arbitrary caller-chosen
`lcr := fcr_store.store.finalized_checkpoint.root`, independent of what the
real evaluator's selector input actually is at that call. The closed
supplier, by contrast, is pinned to the real trace's own `afterObserved`
field (traces are functionally determined by their query, so there is no
freedom to substitute a different candidate). Composing the two therefore
needs one explicit bridging fact beyond the floor: that the *actual* call's
candidate input is genuinely the observer's own finalized checkpoint,
i.e. `(E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
(E.weakFcrStep cfg ext obs n).store.finalized_checkpoint.root` — the
executable statement of "this call's history reduced to a finalized-reset"
(exactly the content of `Weak.FinalizedResetCandidateInputAt.input_eq` for
this trace). This is a scenario predicate on the real call, not a floor
premise: an arbitrary actual call need not land in the finalized-reset
branch (most seconds are "carried"), and closing the "carried"/"observed-
reset" branches unconditionally would need an induction over
`E.weakConfirmed`'s own `SafeFrom` history that this wave does not build.
It is flagged here, not silently folded into the floor.

Given that one bridging fact, `hlcr`/`hbase` for the actual trace's
`afterObserved` come from exactly the same `WeakFinalizedInput.lean`
machinery the existing finalized-base corollary uses
(`finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory`,
`weak_finalizedReset_safeFrom_of_synchrony`), and the headline
`weak_safeFrom_observerCall_closed` above takes it from there — including its
own internal case split, which does not care why `hinput`/`hbase` hold.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 9 — the closed headline: no `hmargin`, no `hfilter` -/

/-- **The closed one-shot weak safety theorem, at an actual FCR call.**

At a genuine weak FCR call (`hcall : E.IsFCRCallAt cfg ext obs n`), with the
call's own candidate input known and `SafeFrom` from the start of the query
slot, the weak selector's actual result is `SafeFrom` at the call's own
second `n + 1` — with no `hmargin`, `hfilter`, or other residual filter-
supply premise: the entire margin/filter chain (Stages G–S7) is discharged
internally, uniformly over which of the four candidate-history branches the
call actually took.

Observer-wise the premise surface is `hW : WeakObserverAssumptions` — the
floor, `obs ∉ E.honest`, and committee readback at the observer's own store.
`ObserverCoherence.justified_root_known` is *derived* here from `B`/`hT`/
`hanchor`/`hboundary` (`WeakObserverAssumptions.toMarginAssumptions`), so it
never appears as a premise. -/
theorem weak_safeFrom_observerCall_closed
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
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
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
  -- `justified_root_known` is derived here, not assumed: `B`/`hT`/`hanchor`/
  -- `hboundary` are already in scope, so the internal margin bundle is built
  -- from the caller's committee readback alone.
  have hWM := hW.toMarginAssumptions cfg ext E B hT hanchor hboundary
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hstore : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
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
      exact weak_safeFrom_find_latest_confirmed_descendant_discharged cfg ext hWM hwalkDomain
        (n + 1) hn1H (E.weakFcrStep cfg ext obs n) hstore trace.afterObserved hinput hbase
        (fun _ => by
          rw [← hselector.result_eq]
          exact
            Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_closed
              cfg ext B hT hA.synchrony hA.static_validators hA.byzantine_bound hA.domain hji
              hanchor hboundary hDelay hphase0 hpaper P V hanchorExact hC hfit hWM.coherence
              hn1H hcall hinput hbase horigin hselector)

/-- **The lazy twin of the closed one-shot headline.**

Identical conclusion, strictly weaker premises: `hC` is replaced by the
unchanged 7-field `E.AcceptedHistoricalA32CompletedPrefixCallAssumptions`
together with `hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n` —
a *derived* trajectory fact, discharged by the weak safety fold's own
strengthened induction hypothesis at seconds strictly below `n`.

A one-shot statement cannot supply `hprior` from its own `hbase`
(`docs/weak-final-wave.md` §5.2), which is why the four audited witnesses keep
`hC` and take the eager route instead.  The trajectory fold can, which is why
its headline drops to `hC.base`. -/
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

/-- Endpoint form of the closed headline: the weak selector's actual result,
at a genuine FCR call, is canonical at every honest endpoint at or after the
call's own second. -/
theorem weak_confirmed_head_closed
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
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hqm : n + 1 ≤ m) (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      = true :=
  weak_safeFrom_observerCall_closed cfg ext B hT hji hanchor hboundary hDelay hphase0 hpaper
    P V hanchorExact hW hwalkDomain hC hfit hn1H hcall hinput hbase w hw m hqm hHm

/-! ## Section 10 — the fully self-contained composition -/

/-- **The closed headline, seeded at the observer's own finalized checkpoint.**

`hbfr` records that the actual call's candidate input reduced to the
observer's own finalized checkpoint (the executable content of
`Weak.FinalizedResetCandidateInputAt.input_eq` for this trace) — a scenario
fact about which candidate-history branch this particular call took, not a
floor premise. Given it, `hinput`/`hbase` are discharged internally via
`WeakFinalizedInput.lean`, exactly mirroring
`weak_safeFrom_find_latest_confirmed_descendant_discharged_from_finalized`,
so the caller supplies neither. -/
theorem weak_safeFrom_observerCall_closed_from_finalized
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hbfr : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
      (E.weakFcrStep cfg ext obs n).store.finalized_checkpoint.root) :
    E.SafeFrom cfg ext (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (n + 1) := by
  have hacc := SelectedMarginAssumptions.toFFGAccountabilityAssumptions
    cfg ext E hW.base
  have hstore : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
    rw [hbfr, hstore]
    exact (E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) (n + 1)).root_known
  have hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))) := by
    rw [hbfr, hstore]
    exact E.weak_finalizedReset_safeFrom_of_synchrony cfg ext B hT hacc hphase0
      hboundaryPhase hanchor hboundary hW.base.synchrony hn1H
  exact weak_safeFrom_observerCall_closed cfg ext B hT hji hanchor hboundary hDelay hphase0
    hpaper P V hanchorExact hW hwalkDomain hC hfit hn1H hcall hinput hbase

/-- Endpoint form of the fully self-contained composition. -/
theorem weak_confirmed_head_closed_from_finalized
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hbfr : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
      (E.weakFcrStep cfg ext obs n).store.finalized_checkpoint.root)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hqm : n + 1 ≤ m) (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      = true :=
  weak_safeFrom_observerCall_closed_from_finalized cfg ext B hT hji hanchor hboundary hDelay
    hphase0 hboundaryPhase hpaper P V hanchorExact hW hwalkDomain hC hfit hn1H hcall hbfr
    w hw m hqm hHm

end Execution

end FastConfirmation.Spec
