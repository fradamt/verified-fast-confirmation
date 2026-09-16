import FastConfirmation.Spec.Proof.WeakHistoricalA32LazyCrossing

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
  (`WeakHistoricalA32Step.lean`);
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
noncomputable def getLatestConfirmedTraceAt_currentLineage_step_core
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e')
    (hcross : ∀ {a c : Root},
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots →
      getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved →
      Weak.CurrentTargetAcceptedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c →
      Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
        (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
        Cert Supp))
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e Cert Supp)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e Cert Supp) := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change ∃ e : Epoch, Nonempty
    (E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e Cert Supp)
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
      Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result
        (get_current_store_epoch cfg query.store) Cert Supp) :=
    hcross hinputKnown hselector hedge
  have hnoCrossingLineage
      (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
      (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
      (hnoCrossing : ¬ ∃ a c : Root,
        Weak.CurrentTargetAcceptedEdge cfg ext query trace.afterObserved a c)
      {e : Epoch}
      (hinputLineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
        trace.afterObserved e Cert Supp) :
      E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e
        Cert Supp :=
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
          exact ⟨_, hcrossingLineage hinputKnown hselector hedge⟩
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
          have hinputLineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
              trace.afterObserved e Cert Supp := by
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
        have hlineage :=
          Weak.actualFinalizedResetCurrentAnchorLineage_core cfg ext
            B hT hanchor hboundary obs n
              (by simpa only [query] using hcurrentFinalized)
              hanchorCert hanchorSupp
        exact ⟨_, ⟨by simpa only [hresultEq, hinputEq, query] using hlineage⟩⟩
      · by_cases hcrossing : ∃ a c : Root,
            Weak.CurrentTargetAcceptedEdge cfg ext query
              trace.afterObserved a c
        · obtain ⟨a, c, hedge⟩ := hcrossing
          exact ⟨_, hcrossingLineage hinputKnown hselector hedge⟩
        · have hinputCurrent :=
            Weak.GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing
              cfg ext trace
              hG.parent hG.walk hG.head_known hinputKnown
              (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
          have hcurrentFinalized : get_block_epoch cfg query.store
                query.store.finalized_checkpoint.root =
              get_current_store_epoch cfg query.store := by
            simpa only [hinputEq] using hinputCurrent
          have hlineage :=
            Weak.actualFinalizedResetCurrentAnchorLineage_core
              cfg ext B hT hanchor hboundary obs n
                (by simpa only [query] using hcurrentFinalized)
                hanchorCert hanchorSupp
          have hinputLineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
              trace.afterObserved
                (get_current_store_epoch cfg query.store) Cert Supp := by
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
        exact ⟨_, hcrossingLineage hinputKnown hselector hedge⟩
      · exact (hfalseOf
          (Weak.GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing
            cfg ext trace hG.parent hG.walk hG.head_known hinputKnown
            (hG.slot_upper _ hinputKnown) hselector hresultCurrent
            hcrossing)).elim

/-- **The eager instantiation** — the pre-wave weak one-call transformer,
byte-identical in statement.

The crossing branch realizes the certificate and quorum on the spot, driven by
the observer-quantified normative contract `Weak.SelectedHelperProvisosAt`.
This is the instantiation the four closed one-shot weak witnesses keep using;
see `docs/weak-final-wave.md` §5. -/
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
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  refine Weak.getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT
    hanchor hboundary hcoh hHn1 hknownN hresultCurrent
    ⟨CertifiedJustified.anchor⟩ (fun _ _ h _ _ _ _ _ => Or.inl h) ?_ hprevious
  intro a c hinputKnown hselector hedge
  have hfixedRaw :=
    Weak.acceptedFixedSourceProducerAt_of_selectedCurrentCrossing cfg ext B
      hT hphase hboundaryPhase hanchor hboundary hcoh hHn1 hinputKnown
      hselector hresultCurrent hedge htargetProducer
  exact ⟨Weak.selectedCurrentCrossingLineage_of_fixedSourceProducer cfg ext B
    hG.causal hG.parent hG.walk hG.head_known hG.current_walk
    (E.weakGetLatestConfirmedTraceAt cfg ext obs n) hinputKnown hselector
    hresultCurrent (hprovisos hselector) hedge hfixedRaw⟩

/-- **The lazy instantiation.**

The crossing branch records origin-call data and the two closures of
`Weak.LazyCertAt` / `Weak.LazySupportAt` instead of a realized certificate and
quorum, so **no `Weak.SelectedHelperProvisosAt` is consumed anywhere in this
theorem**.  The gate producer stays: it is the action/schedule bridge, not a
proviso, and the closures capture it. -/
noncomputable def getLatestConfirmedTraceAt_currentLineage_step_lazy
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (htargetProducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n))
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e
          (Weak.LazyCertAt cfg ext E B obs (n + 1))
          (Weak.LazySupportAt cfg ext E B obs (n + 1)))) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e
      (Weak.LazyCertAt cfg ext E B obs (n + 1))
      (Weak.LazySupportAt cfg ext E B obs (n + 1))) := by
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  refine Weak.getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT
    hanchor hboundary hcoh hHn1 hknownN hresultCurrent
    (Weak.lazyCertAt_anchor cfg ext)
    (fun _ _ h => Weak.lazySupportAt_anchor cfg ext h) ?_ hprevious
  intro a c hinputKnown hselector hedge
  have hfixedRaw :=
    Weak.acceptedFixedSourceProducerAt_of_selectedCurrentCrossing cfg ext B
      hT hphase hboundaryPhase hanchor hboundary hcoh hHn1 hinputKnown
      hselector hresultCurrent hedge htargetProducer
  exact ⟨Weak.selectedCurrentCrossingLazyLineage cfg ext B hT hA hanchor
    hboundary hcoh hHn1 hcall hG.causal hG.parent hG.walk hG.head_known
    hG.current_walk hinputKnown hselector hresultCurrent hedge hfixedRaw⟩

/-- **The no-crossing instantiation.**

When the observer's call finds no current-target crossing edge, the transformer
creates no payload at all: it transports the input's.  This is the route the
`currentHistorical` certificate consumer takes, and it is why that consumer
only ever needs the threaded fold output strictly below its own call (D1†). -/
noncomputable def getLatestConfirmedTraceAt_currentLineage_step_noCrossing
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetAcceptedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e')
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e Cert Supp)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e Cert Supp) :=
  Weak.getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT hanchor
    hboundary hcoh hHn1 hknownN hresultCurrent hanchorCert hanchorSupp
    (fun _ _ hedge => absurd ⟨_, _, hedge⟩ hnoCrossing) hprevious

/-! ## The write-back route

`docs/weak-final-wave.md` §5.3.  Everything between the weak one-call
transformer and the four closed one-shot witnesses is made
`(Cert, Supp)`-polymorphic and instantiated twice:

* **eagerly** — `Cert N`/`Supp N` are the constant eager obligations and the
  crossing builder is the unchanged
  `Weak.selectedCurrentCrossingLineage_of_fixedSourceProducer`, driven by
  `Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`.  This
  keeps the four frozen witness statements byte-identical;
* **lazily** — `Cert N`/`Supp N` are `Weak.LazyCertAt`/`Weak.LazySupportAt` at
  bound `N` and the crossing builder is
  `Weak.selectedCurrentCrossingLazyLineage`, which consumes no proviso.  This is
  what lets the trajectory fold drop to `hC.base`.

The obligations are *families* indexed by the write-back second, because the
lazy closures are: the induction's extension step widens the bound, which is a
weakening (`Weak.observerHistoricalA32LazyLineage_mono`) and is `id` in the
eager case. -/

/-- The four facts the weak write-back induction needs about an obligation
family: the two anchor discharges, the extension-step widening, the same-epoch
support transport, and the crossing builder at each of the observer's calls. -/
structure ObserverLineageRouteAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) (obs : ValidatorIndex)
    (Cert : ℕ → Checkpoint Root → Prop)
    (Supp : ℕ → Root → Epoch → Prop) : Prop where
  anchor_cert : ∀ N : ℕ, Cert N B.anchor
  anchor_supp : ∀ (N : ℕ) (o : Root) (e' : Epoch),
    B.state.C o e' = B.anchor → Supp N o e'
  mono : ∀ {N : ℕ} {tip : Root} {e : Epoch},
    Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Cert N) (Supp N)) →
    Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Cert (N + 1)) (Supp (N + 1)))
  supp_transport : ∀ {N : ℕ} {origin tip : Root} {e : Epoch},
    B.state.C tip e = B.state.C origin e →
    B.state.GJ tip = B.state.GJ origin →
    Supp N origin e → Supp N tip e
  crossing : ∀ {n : ℕ}, E.IsFCRCallAt cfg ext obs n →
    E.WithinHorizon cfg (n + 1) →
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    ∀ {a c : Root},
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots →
      getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved →
      Weak.CurrentTargetAcceptedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c →
      Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
        (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
        (Cert (n + 1)) (Supp (n + 1)))

/-- The eager obligation family: the constant pair the pre-wave weak trunk
carries. -/
abbrev EagerCertFamily (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) :
    ℕ → Checkpoint Root → Prop :=
  fun _ => E.AcceptedHistoricalA32EagerCert cfg ext B

/-- The eager support family. -/
abbrev EagerSuppFamily (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) :
    ℕ → Root → Epoch → Prop :=
  fun _ => E.AcceptedHistoricalA32EagerSupp cfg ext B

/-- The lazy certification family at the observer. -/
abbrev LazyCertFamily (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) (obs : ValidatorIndex) :
    ℕ → Checkpoint Root → Prop :=
  fun N => Weak.LazyCertAt cfg ext E B obs N

/-- The lazy support family at the observer. -/
abbrev LazySuppFamily (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) (obs : ValidatorIndex) :
    ℕ → Root → Epoch → Prop :=
  fun N => Weak.LazySupportAt cfg ext E B obs N

end Weak

end FastConfirmation.Spec
