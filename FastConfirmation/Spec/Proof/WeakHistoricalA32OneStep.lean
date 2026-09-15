import FastConfirmation.Spec.Proof.WeakHistoricalA32Step

/-!
# Spec / Proof / WeakHistoricalA32OneStep

The observer-side twin of `AcceptedHistoricalA32OneStep.lean`: one exact weak
`get_latest_confirmed` call preserves or creates the historical A3.2 lineage
whenever its result lands in the query's current epoch.

**Why a twin is needed.**  The strong one-step transformer dispatches the
*ordered evaluator trace* — `E.getLatestConfirmedTraceAt`, whose final phase is
the strong descendant selector.  Rule delta 5 gives the weak model a different
selector (`Weak.find_latest_confirmed_descendant`), so the strong statement
does not instantiate at a weak call even though the branch bookkeeping is
identical.

**The substitutions**, all of them already landed:

* `E.fcrStep` / `E.getLatestConfirmedTraceAt` / `E.confirmed` →
  `E.weakFcrStep` / `E.weakGetLatestConfirmedTraceAt` / `E.weakConfirmed`
  (`WeakFCRCallContracts.lean`, `WeakCandidateHistoryRecurrence.lean`), with
  `E.fcrStep_store` / `E.fcrStep_confirmed_root` →
  `Execution.weakFcrStep_store` / `Execution.weakFcrStep_confirmed_root`;
* the single honesty hub
  `E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory … hv` →
  `Weak.weakFcrStep_historicalA32QueryGeometryAt … hcoh`
  (`WeakHistoricalA32Geometry.lean`), where
  `hcoh : E.ObserverCoherence cfg ext obs` replaces the honest-node binder;
* the three step constructors → `Weak.selectedCurrentNoCrossingLineage`,
  `Weak.selectedCurrentCrossingLineage_of_fixedSourceProducer` and
  `Weak.acceptedFixedSourceProducerAt_of_selectedCurrentCrossing`
  (`WeakHistoricalA32Step.lean`), with `SelectedHelperProvisosAt` →
  `Weak.SelectedHelperProvisosAt` (the observer-quantified normative contract
  of `WeakSelectedStrictEdgeFilterSupply.lean`);
* `Execution.confirmed_current_at_previousStore_of_query` →
  `Weak.confirmed_current_at_previousStore_of_query` and
  `Execution.actualFinalizedResetCurrentAnchorLineage` →
  `Weak.actualFinalizedResetCurrentAnchorLineage`;
* the observed-restart tag `E.actualObservedRestartInputAt` is *not* cloned.
  Its three consumed projections are available individually on the weak side:
  `afterObserved_eq` is the right disjunct of the (model-shared) observed
  phase's `branch_cases`, `root_known` is
  `Weak.weakFcrStep_observed_known` (rule delta 5's `banked_known`, discharged
  for the whole weak trajectory in `WeakBankedJustification.lean`), and
  `previous_epoch` is the second conjunct of `Weak.observedRestartGuard_facts`.

Everything payload-side — `Execution.AcceptedHistoricalA32LineageAt`,
`Execution.AcceptedCurrentTargetA32GateRealizationProducerAt` and its
fixed-source sibling — is honesty-free and evaluator-free and is reused
verbatim, not cloned.  So is
`Execution.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory`,
which is quantified over an arbitrary node `w`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- Weak twin of
`Execution.getLatestConfirmedTraceAt_currentLineage_step`: one exact weak
`get_latest_confirmed` call at the observer preserves or creates the
historical A3.2 lineage whenever its result is in the query's current epoch.

The previous invariant is conditional for the same reason as in the paper
argument: previous-epoch confirmed candidates need no current-epoch payload.
The only fresh payload branches are the trusted anchor and a concrete weak
current-target crossing.

The proof dispatches the ordered weak evaluator trace, not a root-only
disjunction, so the finalized and observed reset tags stay distinguishable
even when their roots coincide with another candidate. -/
noncomputable def getLatestConfirmedTraceAt_currentLineage_step
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hprovisos :
      getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved →
        Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1)
          (E.weakFcrStep cfg ext obs n)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (htargetProducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n))
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e) := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change getLatestSelectorGuard cfg query trace.afterObserved →
    Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1) query
      trace.afterObserved at hprovisos
  change E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext B.anchor
    B.state (n + 1) query at htargetProducer
  change ∃ e : Epoch, Nonempty
    (E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e)
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hqueryConfirmedKnown : query.confirmed_root ∈
      query.store.block_roots := by
    have hknownN1 : E.weakConfirmed cfg ext obs n ∈
        (E.store cfg ext obs (n + 1)).block_roots :=
      (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
    simpa only [query, E.weakFcrStep_confirmed_root, E.weakFcrStep_store]
      using hknownN1
  have hcrossingLineage
      (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
      (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
      {a c : Root}
      (hedge : Weak.CurrentTargetAcceptedEdge cfg ext query
        trace.afterObserved a c) :
      E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
        (get_current_store_epoch cfg query.store) := by
    have hfixedRaw :=
      Weak.acceptedFixedSourceProducerAt_of_selectedCurrentCrossing cfg ext B
        hT hphase hboundaryPhase hanchor hboundary hcoh hHn1
        (by simpa only [query, trace] using hinputKnown)
        (by simpa only [query, trace] using hselector)
        (by simpa only [query, trace] using hresultCurrent)
        (by simpa only [query, trace] using hedge)
        (by simpa only [query] using htargetProducer)
    have hfixed :
        E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
          cfg ext B.anchor B.state (n + 1) query trace.result := by
      simpa only [query, trace] using hfixedRaw
    exact Weak.selectedCurrentCrossingLineage_of_fixedSourceProducer cfg ext B
      hG.causal hG.parent hG.walk hG.head_known hG.current_walk trace
      hinputKnown hselector hresultCurrent (hprovisos hselector) hedge hfixed
  have hnoCrossingLineage
      (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
      (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
      (hnoCrossing : ¬ ∃ a c : Root,
        Weak.CurrentTargetAcceptedEdge cfg ext query trace.afterObserved a c)
      {e : Epoch}
      (hinputLineage : E.AcceptedHistoricalA32LineageAt cfg ext B
        trace.afterObserved e) :
      E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e :=
    Weak.selectedCurrentNoCrossingLineage cfg ext B hT.wellFormed
      hG.exact_core hG.causal hG.parent hG.walk hG.head_known trace
      hinputKnown (hG.slot_upper _ hinputKnown) hselector hresultCurrent
      hnoCrossing (hG.strict_non_genesis _ hinputKnown) hinputLineage
  rcases trace.observed.branch_cases with
      ⟨hobsUnchanged, _hobsFalse⟩ | ⟨hobsRestart, hobsTrue⟩
  · rcases trace.finalized.branch_cases with
        ⟨hcarried, _hfinalizedFalse⟩ | ⟨hfinalized, _hfinalizedTrue⟩
    · have hinputEq : trace.afterObserved = query.confirmed_root :=
        hobsUnchanged.trans hcarried
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        rw [hinputEq]
        exact hqueryConfirmedKnown
      rcases trace.selector_cases cfg ext with
          ⟨hresultEq, _hselectorFalse⟩ | ⟨_resultEq, hselector⟩
      · have hcurrentQ : get_block_epoch cfg query.store
            query.confirmed_root =
              get_current_store_epoch cfg query.store := by
          simpa only [hresultEq, hinputEq] using hresultCurrent
        have hcurrentN := Weak.confirmed_current_at_previousStore_of_query
          cfg ext hT hknownN (by simpa only [query] using hcurrentQ)
        obtain ⟨e, ⟨hlineage⟩⟩ := hprevious hcurrentN
        refine ⟨e, ⟨?_⟩⟩
        have htip : trace.result = E.weakConfirmed cfg ext obs n :=
          hresultEq.trans (hinputEq.trans
            (E.weakFcrStep_confirmed_root cfg ext obs n))
        simpa only [htip] using hlineage
      · by_cases hcrossing : ∃ a c : Root,
            Weak.CurrentTargetAcceptedEdge cfg ext query
              trace.afterObserved a c
        · obtain ⟨a, c, hedge⟩ := hcrossing
          exact ⟨_, ⟨hcrossingLineage hinputKnown hselector hedge⟩⟩
        · have hinputCurrent :=
            Weak.GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing
              cfg ext trace
              hG.parent hG.walk hG.head_known hinputKnown
              (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
          have hcurrentQ : get_block_epoch cfg query.store
              query.confirmed_root =
                get_current_store_epoch cfg query.store := by
            simpa only [hinputEq] using hinputCurrent
          have hcurrentN := Weak.confirmed_current_at_previousStore_of_query
            cfg ext hT hknownN (by simpa only [query] using hcurrentQ)
          obtain ⟨e, ⟨hlineage⟩⟩ := hprevious hcurrentN
          have hinputLineage : E.AcceptedHistoricalA32LineageAt cfg ext B
              trace.afterObserved e := by
            rw [hinputEq]
            simpa only [query, E.weakFcrStep_confirmed_root] using hlineage
          exact ⟨e, ⟨hnoCrossingLineage hinputKnown hselector
            hcrossing hinputLineage⟩⟩
    · have hinputEq : trace.afterObserved =
          query.store.finalized_checkpoint.root :=
        hobsUnchanged.trans hfinalized
      have hrealized :=
        E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
          cfg ext B hT hanchor hboundary (w := obs) (n + 1)
      have hfinalizedKnown : query.store.finalized_checkpoint.root ∈
          query.store.block_roots := by
        simpa only [query, E.weakFcrStep_store] using hrealized.root_known
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        rw [hinputEq]
        exact hfinalizedKnown
      rcases trace.selector_cases cfg ext with
          ⟨hresultEq, _hselectorFalse⟩ | ⟨_resultEq, hselector⟩
      · have hcurrentFinalized : get_block_epoch cfg query.store
            query.store.finalized_checkpoint.root =
          get_current_store_epoch cfg query.store := by
          simpa only [hresultEq, hinputEq] using hresultCurrent
        have hlineage := Weak.actualFinalizedResetCurrentAnchorLineage cfg ext
          B hT hanchor hboundary obs n
            (by simpa only [query] using hcurrentFinalized)
        exact ⟨_, ⟨by simpa only [hresultEq, hinputEq, query] using hlineage⟩⟩
      · by_cases hcrossing : ∃ a c : Root,
            Weak.CurrentTargetAcceptedEdge cfg ext query
              trace.afterObserved a c
        · obtain ⟨a, c, hedge⟩ := hcrossing
          exact ⟨_, ⟨hcrossingLineage hinputKnown hselector hedge⟩⟩
        · have hinputCurrent :=
            Weak.GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing
              cfg ext trace
              hG.parent hG.walk hG.head_known hinputKnown
              (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
          have hcurrentFinalized : get_block_epoch cfg query.store
                query.store.finalized_checkpoint.root =
              get_current_store_epoch cfg query.store := by
            simpa only [hinputEq] using hinputCurrent
          have hlineage := Weak.actualFinalizedResetCurrentAnchorLineage
            cfg ext B hT hanchor hboundary obs n
              (by simpa only [query] using hcurrentFinalized)
          have hinputLineage : E.AcceptedHistoricalA32LineageAt cfg ext B
              trace.afterObserved
                (get_current_store_epoch cfg query.store) := by
            simpa only [hinputEq, query] using hlineage
          exact ⟨_, ⟨hnoCrossingLineage hinputKnown hselector
            hcrossing hinputLineage⟩⟩
  · have hobsFacts := Weak.observedRestartGuard_facts cfg
      (query := query) (candidate := trace.afterFinalized) hobsTrue
    have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
      rw [hobsRestart]
      simpa only [query, E.weakFcrStep_store] using
        Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
    have hinputPrevious : get_block_epoch cfg query.store
          trace.afterObserved + 1 =
        get_current_store_epoch cfg query.store := by
      rw [hobsRestart]
      exact hobsFacts.2.1
    have hfalseOf (hinputCurrent : get_block_epoch cfg query.store
        trace.afterObserved = get_current_store_epoch cfg query.store) :
        False := by
      have hbad : get_current_store_epoch cfg query.store + 1 =
          get_current_store_epoch cfg query.store :=
        (congrArg (fun e => e + 1) hinputCurrent.symm).trans hinputPrevious
      exact Nat.succ_ne_self _ (by simpa only [Nat.add_one] using hbad)
    rcases trace.selector_cases cfg ext with
        ⟨hresultEq, _hselectorFalse⟩ | ⟨_resultEq, hselector⟩
    · exact (hfalseOf (by simpa only [hresultEq] using hresultCurrent)).elim
    · by_cases hcrossing : ∃ a c : Root,
          Weak.CurrentTargetAcceptedEdge cfg ext query
            trace.afterObserved a c
      · obtain ⟨a, c, hedge⟩ := hcrossing
        exact ⟨_, ⟨hcrossingLineage hinputKnown hselector hedge⟩⟩
      · exact (hfalseOf
          (Weak.GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing
            cfg ext trace hG.parent hG.walk hG.head_known hinputKnown
            (hG.slot_upper _ hinputKnown) hselector hresultCurrent
            hcrossing)).elim

end Weak

end FastConfirmation.Spec
