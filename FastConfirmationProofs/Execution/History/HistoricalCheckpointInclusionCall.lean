module
public import FastConfirmationProofs.Weak.History.AcceptedHistoricalA32LazyCrossing

@[expose] public section


/-!
# Exact one-call historical A3.2 transformer

The theorem in this file dispatches the ordered evaluator trace, not a
root-only disjunction.  Finalized and observed reset tags therefore remain
distinguishable even when their roots coincide with another candidate.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- One exact `get_latest_confirmed` call preserves or creates the historical
A3.2 lineage whenever its result is in the query's current epoch.

The previous invariant is conditional for the same reason as the paper
argument: previous-epoch confirmed candidates need no current-epoch payload.
The only fresh payload branches are the trusted anchor and a concrete
current-target crossing. -/
noncomputable def getLatestConfirmedTraceAt_currentLineage_step_core
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hresultCurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e')
    (hcross : ∀ {a c : Root},
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
        (E.fcrStoreAtCall cfg ext v n).store.block_roots →
      getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved →
      CurrentTargetSelectedEdge cfg ext (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved a c →
      E.AcceptedHistoricalA32LineageCoreAt cfg ext B
        (E.getLatestConfirmedTraceAt cfg ext v n).result
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
        Cert Supp)
    (hprevious :
      get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.confirmed cfg ext v n) e Cert Supp)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result e Cert Supp) := by
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change ∃ e : Epoch, Nonempty
    (E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e Cert Supp)
  have hG := E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary hv hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hqueryConfirmedKnown : query.confirmed_root ∈
      query.store.block_roots := by
    have hknownN1 : E.confirmed cfg ext v n ∈
        (E.store cfg ext v (n + 1)).block_roots :=
      (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
    simpa only [query, E.fcrStep_confirmed_root, E.fcrStep_store] using
      hknownN1
  have hcrossingLineage
      (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
      (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
      {a c : Root}
      (hedge : CurrentTargetSelectedEdge cfg ext query
        trace.afterObserved a c) :
      E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result
        (get_current_store_epoch cfg query.store) Cert Supp :=
    hcross hinputKnown hselector hedge
  have hnoCrossingLineage
      (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
      (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
      (hnoCrossing : ¬ ∃ a c : Root,
        CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c)
      {e : Epoch}
      (hinputLineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
        trace.afterObserved e Cert Supp) :
      E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e Cert Supp :=
    E.selectedCurrentNoCrossingLineage cfg ext B hT.wellFormed
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
      rcases trace.selector.branch_cases with
          ⟨hresultEq, _hselectorFalse⟩ | ⟨_resultEq, hselector⟩
      · have hcurrentQ : get_block_epoch cfg query.store
            query.confirmed_root = get_current_store_epoch cfg query.store := by
          simpa only [hresultEq, hinputEq] using hresultCurrent
        have hcurrentN := E.confirmed_current_at_previousStore_of_query
          cfg ext hT hknownN (by simpa only [query] using hcurrentQ)
        obtain ⟨e, ⟨hlineage⟩⟩ := hprevious hcurrentN
        refine ⟨e, ⟨?_⟩⟩
        have htip : trace.result = E.confirmed cfg ext v n :=
          hresultEq.trans (hinputEq.trans
            (E.fcrStep_confirmed_root cfg ext v n))
        simpa only [htip] using hlineage
      · by_cases hcrossing : ∃ a c : Root,
            CurrentTargetSelectedEdge cfg ext query
              trace.afterObserved a c
        · obtain ⟨a, c, hedge⟩ := hcrossing
          exact ⟨_, ⟨hcrossingLineage hinputKnown hselector hedge⟩⟩
        · have hinputCurrent :=
            Execution.LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
              cfg ext trace
              hG.parent hG.walk hG.head_known hinputKnown
              (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
          have hcurrentQ : get_block_epoch cfg query.store
              query.confirmed_root = get_current_store_epoch cfg query.store := by
            simpa only [hinputEq] using hinputCurrent
          have hcurrentN := E.confirmed_current_at_previousStore_of_query
            cfg ext hT hknownN (by simpa only [query] using hcurrentQ)
          obtain ⟨e, ⟨hlineage⟩⟩ := hprevious hcurrentN
          have hinputLineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
              trace.afterObserved e Cert Supp := by
            rw [hinputEq]
            simpa only [query, E.fcrStep_confirmed_root] using hlineage
          exact ⟨e, ⟨hnoCrossingLineage hinputKnown hselector
            hcrossing hinputLineage⟩⟩
    · have hinputEq : trace.afterObserved =
          query.store.finalized_checkpoint.root :=
        hobsUnchanged.trans hfinalized
      have hrealized :=
        E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
          cfg ext B hT hanchor hboundary (w := v) (n + 1)
      have hfinalizedKnown : query.store.finalized_checkpoint.root ∈
          query.store.block_roots := by
        simpa only [query, E.fcrStep_store] using hrealized.root_known
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        rw [hinputEq]
        exact hfinalizedKnown
      rcases trace.selector.branch_cases with
          ⟨hresultEq, _hselectorFalse⟩ | ⟨_resultEq, hselector⟩
      · have hcurrentFinalized : get_block_epoch cfg query.store
            query.store.finalized_checkpoint.root =
          get_current_store_epoch cfg query.store := by
          simpa only [hresultEq, hinputEq] using hresultCurrent
        have hlineage := E.actualFinalizedResetCurrentAnchorLineage_core
          cfg ext B hT hanchor hboundary v n
            (by simpa only [query] using hcurrentFinalized)
            hanchorCert hanchorSupp
        exact ⟨_, ⟨by simpa only [hresultEq, hinputEq, query] using hlineage⟩⟩
      · by_cases hcrossing : ∃ a c : Root,
            CurrentTargetSelectedEdge cfg ext query
              trace.afterObserved a c
        · obtain ⟨a, c, hedge⟩ := hcrossing
          exact ⟨_, ⟨hcrossingLineage hinputKnown hselector hedge⟩⟩
        · have hinputCurrent :=
            Execution.LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
              cfg ext trace
              hG.parent hG.walk hG.head_known hinputKnown
              (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
          have hcurrentFinalized : get_block_epoch cfg query.store
                query.store.finalized_checkpoint.root =
              get_current_store_epoch cfg query.store := by
            simpa only [hinputEq] using hinputCurrent
          have hlineage := E.actualFinalizedResetCurrentAnchorLineage_core
            cfg ext B hT hanchor hboundary v n
              (by simpa only [query] using hcurrentFinalized)
              hanchorCert hanchorSupp
          have hinputLineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
              trace.afterObserved
                (get_current_store_epoch cfg query.store) Cert Supp := by
            simpa only [hinputEq, query] using hlineage
          exact ⟨_, ⟨hnoCrossingLineage hinputKnown hselector
            hcrossing hinputLineage⟩⟩
  · have htag := E.actualObservedRestartInputAt cfg ext B hT hanchor
      hboundary v n trace (by simpa only [query] using hobsTrue)
    have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
      rw [htag.afterObserved_eq]
      exact htag.root_known
    rcases trace.selector.branch_cases with
        ⟨hresultEq, _hselectorFalse⟩ | ⟨_resultEq, hselector⟩
    · have hinputCurrent : get_block_epoch cfg query.store
          trace.afterObserved = get_current_store_epoch cfg query.store := by
        simpa only [hresultEq] using hresultCurrent
      have hinputPrevious : get_block_epoch cfg query.store
            trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
        rw [htag.afterObserved_eq]
        exact htag.previous_epoch
      have hfalse : False := by
        have hbad : get_current_store_epoch cfg query.store + 1 =
            get_current_store_epoch cfg query.store :=
          (congrArg (fun e => e + 1) hinputCurrent.symm).trans
            hinputPrevious
        exact Nat.succ_ne_self _ (by
          simpa only [Nat.add_one] using hbad)
      exact hfalse.elim
    · by_cases hcrossing : ∃ a c : Root,
          CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c
      · obtain ⟨a, c, hedge⟩ := hcrossing
        exact ⟨_, ⟨hcrossingLineage hinputKnown hselector hedge⟩⟩
      · have hinputCurrent :=
          Execution.LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
            cfg ext trace
            hG.parent hG.walk hG.head_known hinputKnown
            (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
        have hinputPrevious : get_block_epoch cfg query.store
              trace.afterObserved + 1 =
            get_current_store_epoch cfg query.store := by
          rw [htag.afterObserved_eq]
          exact htag.previous_epoch
        have hfalse : False := by
          have hbad : get_current_store_epoch cfg query.store + 1 =
              get_current_store_epoch cfg query.store :=
            (congrArg (fun e => e + 1) hinputCurrent.symm).trans
              hinputPrevious
          exact Nat.succ_ne_self _ (by
            simpa only [Nat.add_one] using hbad)
        exact hfalse.elim

/-- **The lazy instantiation** — the strong trunk's one-call transformer.

The crossing branch now records origin-call data and the two closures of
`docs/crossing-call-support-residue.md` §4.3 instead of a realized certificate
and quorum, so **no helper-support proviso is consumed anywhere in this
theorem** (the `FCRPredictionSupportAt` record it used to name no longer
exists).  The gate producer stays: it is the action/schedule bridge, not a
proviso, and the closures capture it. -/
noncomputable def getLatestConfirmedTraceAt_currentLineage_step_lazy
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hresultCurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    (htargetProducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n))
    (hprevious :
      get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.confirmed cfg ext v n) e
          (E.LazyCertAt cfg ext B (n + 1))
          (E.LazySupportAt cfg ext B v (n + 1)))) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result e
      (E.LazyCertAt cfg ext B (n + 1))
      (E.LazySupportAt cfg ext B v (n + 1))) := by
  have hG := E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary hv hHn1
  refine E.getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT
    hanchor hboundary hv hHn1 hknownN hresultCurrent
    (E.lazyCertAt_anchor cfg ext)
    (fun _ _ h => E.lazySupportAt_anchor cfg ext h)
    ?_ hprevious
  intro a c hinputKnown hselector hedge
  have hfixed :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
        cfg ext B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).result :=
    E.acceptedFixedSourceProducerAt_of_selectedCurrentCrossing cfg ext B
      hT hphase hboundaryPhase hanchor hboundary hv hHn1 hinputKnown
      hselector hresultCurrent hedge htargetProducer
  exact E.selectedCurrentCrossingLazyLineage cfg ext B hA hanchor hboundary
    hv hHn1 hcall hG.causal hG.parent hG.walk hG.head_known hG.current_walk
    hinputKnown hselector hresultCurrent hedge hfixed

/-- **The no-crossing instantiation.**

When the call finds no current-target crossing edge, the transformer creates no
payload at all: it transports the input's.  The two obligations are therefore
whatever the *input* lineage carried, at whatever second bound it carried them.
This is the route the `currentHistorical` consumer takes, and it is why that
consumer only ever needs the threaded fold output strictly below its own call
(`docs/crossing-call-support-residue.md` §2.1, D1†). -/
noncomputable def getLatestConfirmedTraceAt_currentLineage_step_noCrossing
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hresultCurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetSelectedEdge cfg ext (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved a c)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e')
    (hprevious :
      get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) →
        ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.confirmed cfg ext v n) e Cert Supp)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result e Cert Supp) :=
  E.getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT hanchor
    hboundary hv hHn1 hknownN hresultCurrent hanchorCert hanchorSupp
    (fun _ _ hedge => absurd ⟨_, _, hedge⟩ hnoCrossing) hprevious

end Execution


end FastConfirmation.Spec

end
