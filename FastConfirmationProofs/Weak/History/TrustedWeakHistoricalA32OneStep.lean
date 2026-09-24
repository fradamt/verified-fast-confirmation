module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32OneStep
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Step
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32OriginCall
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Geometry
public import FastConfirmationProofs.Weak.Certificates.TrustedWeakBankedJustification
public import FastConfirmationProofs.Checkpoints.TrustedProcessedResetCheckpointRealization
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32LazyCrossing

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {E : Execution Root} {trusted : Store Root → Prop}

noncomputable def trusted_getLatestConfirmedTraceAt_currentLineage_step_core
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
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
      Weak.CurrentTargetSelectedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c →
      Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
        (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
        Cert Supp))
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e Cert Supp)) :
    ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e Cert Supp) := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change ∃ e : Epoch, Nonempty
    (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e Cert Supp)
  have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
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
      (hedge : Weak.CurrentTargetSelectedEdge cfg ext query
        trace.afterObserved a c) :
      Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B trace.result
        (get_current_store_epoch cfg query.store) Cert Supp) :=
    hcross hinputKnown hselector hedge
  have hnoCrossingLineage
      (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
      (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
      (hnoCrossing : ¬ ∃ a c : Root,
        Weak.CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c)
      {e : Epoch}
      (hinputLineage : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
        trace.afterObserved e Cert Supp) :
      E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e
        Cert Supp :=
    Weak.trusted_selectedCurrentNoCrossingLineage cfg ext B hT.wellFormed
      hG.exact_core hG.causal hG.parent hG.walk hG.head_known trace
      hinputKnown (hG.slot_upper _ hinputKnown) hselector hresultCurrent
      hnoCrossing (hG.strict_non_genesis _ hinputKnown) hinputLineage
  have finalizedCase (hinputEq : trace.afterObserved =
      query.store.finalized_checkpoint.root) :
      ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
        trace.result e Cert Supp) := by
    have hrealized :=
      E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
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
        Weak.trusted_actualFinalizedResetCurrentAnchorLineage_core cfg ext
          B hT hanchor hboundary obs n
            (by simpa only [query] using hcurrentFinalized)
            hanchorCert hanchorSupp
      exact ⟨_, ⟨by simpa only [hresultEq, hinputEq, query] using hlineage⟩⟩
    · by_cases hcrossing : ∃ a c : Root,
          Weak.CurrentTargetSelectedEdge cfg ext query
            trace.afterObserved a c
      · obtain ⟨a, c, hedge⟩ := hcrossing
        exact ⟨_, hcrossingLineage hinputKnown hselector hedge⟩
      · have hinputCurrent :=
          Weak.LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
            cfg ext trace
            hG.parent hG.walk hG.head_known hinputKnown
            (hG.slot_upper _ hinputKnown) hselector hresultCurrent hcrossing
        have hcurrentFinalized : get_block_epoch cfg query.store
              query.store.finalized_checkpoint.root =
            get_current_store_epoch cfg query.store := by
          simpa only [hinputEq] using hinputCurrent
        have hlineage :=
          Weak.trusted_actualFinalizedResetCurrentAnchorLineage_core
            cfg ext B hT hanchor hboundary obs n
              (by simpa only [query] using hcurrentFinalized)
              hanchorCert hanchorSupp
        have hinputLineage : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
            trace.afterObserved
              (get_current_store_epoch cfg query.store) Cert Supp := by
          simpa only [hinputEq, query] using hlineage
        exact ⟨_, ⟨hnoCrossingLineage hinputKnown hselector
          hcrossing hinputLineage⟩⟩
  rcases trace.observed.branch_cases with
      ⟨hobsUnchanged, _hobsFalse⟩ | ⟨hobsRestart, hobsTrue⟩ | hreset
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
            Weak.CurrentTargetSelectedEdge cfg ext query
              trace.afterObserved a c
        · obtain ⟨a, c, hedge⟩ := hcrossing
          exact ⟨_, hcrossingLineage hinputKnown hselector hedge⟩
        · have hinputCurrent :=
            Weak.LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
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
          have hinputLineage : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
              trace.afterObserved e Cert Supp := by
            rw [hinputEq]
            simpa only [query, E.weakFcrStep_confirmed_root] using hlineage
          exact ⟨e, ⟨hnoCrossingLineage hinputKnown hselector
            hcrossing hinputLineage⟩⟩
    · have hinputEq : trace.afterObserved =
          query.store.finalized_checkpoint.root :=
        hobsUnchanged.trans hfinalized
      exact finalizedCase hinputEq
  · have hobsFacts := Weak.observedRestartGuard_facts cfg ext
      (query := query) (candidate := trace.afterFinalized) hobsTrue
    have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
      rw [hobsRestart]
      simpa only [query, E.weakFcrStep_store] using
        Weak.trusted_weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
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
          Weak.CurrentTargetSelectedEdge cfg ext query
            trace.afterObserved a c
      · obtain ⟨a, c, hedge⟩ := hcrossing
        exact ⟨_, hcrossingLineage hinputKnown hselector hedge⟩
      · exact (hfalseOf
          (Weak.LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
            cfg ext trace hG.parent hG.walk hG.head_known hinputKnown
            (hG.slot_upper _ hinputKnown) hselector hresultCurrent
            hcrossing)).elim
  · exact finalizedCase hreset

/-- **The lazy instantiation.**

The crossing branch records origin-call data and the two closures of
`Weak.TrustedLazyCertAt` / `Weak.TrustedLazySupportAt` instead of a realized certificate and
quorum, so **no normative proviso is consumed anywhere in this theorem**.  The gate producer stays: it is the action/schedule bridge, not a
proviso, and the closures capture it. -/
noncomputable def trusted_getLatestConfirmedTraceAt_currentLineage_step_lazy
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (htargetProducer : E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n))
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e
          (Weak.TrustedLazyCertAt cfg ext E B obs (n + 1))
          (Weak.TrustedLazySupportAt cfg ext E B obs (n + 1)))) :
    ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e
      (Weak.TrustedLazyCertAt cfg ext E B obs (n + 1))
      (Weak.TrustedLazySupportAt cfg ext E B obs (n + 1))) := by
  have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  refine Weak.trusted_getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT
    hanchor hboundary hcoh hHn1 hknownN hresultCurrent
    (Weak.trusted_lazyCertAt_anchor cfg ext)
    (fun _ _ h => Weak.trusted_lazySupportAt_anchor cfg ext h) ?_ hprevious
  intro a c hinputKnown hselector hedge
  have hfixedRaw :=
    Weak.trusted_acceptedFixedSourceProducerAt_of_selectedCurrentCrossing cfg ext B
      hT hphase hboundaryPhase hanchor hboundary hcoh hHn1 hinputKnown
      hselector hresultCurrent hedge htargetProducer
  exact ⟨Weak.trusted_selectedCurrentCrossingLazyLineage cfg ext B hT hA hanchor
    hboundary hcoh hHn1 hcall hG.causal hG.parent hG.walk hG.head_known
    hG.current_walk hinputKnown hselector hresultCurrent hedge hfixedRaw⟩

/-- **The no-crossing instantiation.**

When the observer's call finds no current-target crossing edge, the transformer
creates no payload at all: it transports the input's.  This is the route the
`currentHistorical` certificate consumer takes, and it is why that consumer
only ever needs the threaded fold output strictly below its own call (D1†). -/
noncomputable def trusted_getLatestConfirmedTraceAt_currentLineage_step_noCrossing
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
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
      Weak.CurrentTargetSelectedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e')
    (hprevious :
      get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) =
          get_current_store_epoch cfg (E.store cfg ext obs n) →
        ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt
          cfg ext B (E.weakConfirmed cfg ext obs n) e Cert Supp)) :
    ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e Cert Supp) :=
  Weak.trusted_getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT hanchor
    hboundary hcoh hHn1 hknownN hresultCurrent hanchorCert hanchorSupp
    (fun _ _ hedge => absurd ⟨_, _, hedge⟩ hnoCrossing) hprevious

/-! ## The write-back route

`docs/weak-final-wave.md` §5.3.  Everything between the weak one-call
transformer and the weak trajectory headlines is `(Cert, Supp)`-polymorphic.
The wave carried two instantiations; only the **lazy** one survives: `Cert N`/
`Supp N` are `Weak.TrustedLazyCertAt`/`Weak.TrustedLazySupportAt` at bound `N` and the
crossing builder is `Weak.trusted_selectedCurrentCrossingLazyLineage`, which consumes
no proviso.  That is what lets the trajectory fold carry only the unchanged
7-field completed-prefix contract.  The **eager** instantiation — constant
obligations and a proviso-driven crossing builder — existed solely to keep the
four closed one-shot witnesses' statements frozen, and went with them.

The obligations are *families* indexed by the write-back second, because the
lazy closures are: the induction's extension step widens the bound, which is a
weakening (`Weak.observerHistoricalA32LazyLineage_mono`). -/

/-- The four facts the weak write-back induction needs about an obligation
family: the two anchor discharges, the extension-step widening, the same-epoch
support transport, and the crossing builder at each of the observer's calls. -/
structure TrustedObserverLineageRouteAt (E : Execution Root)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted) (obs : ValidatorIndex)
    (Cert : ℕ → Checkpoint Root → Prop)
    (Supp : ℕ → Root → Epoch → Prop) : Prop where
  anchor_cert : ∀ N : ℕ, Cert N B.anchor
  anchor_supp : ∀ (N : ℕ) (o : Root) (e' : Epoch),
    B.state.C o e' = B.anchor → Supp N o e'
  mono : ∀ {N : ℕ} {tip : Root} {e : Epoch},
    Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Cert N) (Supp N)) →
    Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Cert (N + 1)) (Supp (N + 1)))
  supp_transport : ∀ {N : ℕ} {origin tip : Root} {e : Epoch},
    B.state.C tip e = B.state.C origin e →
    B.state.GJ tip = B.state.GJ origin →
    Supp N origin e → Supp N tip e
  crossing : ∀ {n : ℕ}, E.IsScheduledFCRCallAt cfg ext obs n →
    E.WithinHorizon cfg (n + 1) →
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    ∀ {a c : Root},
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots →
      getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved →
      Weak.CurrentTargetSelectedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c →
      Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
        (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
        (Cert (n + 1)) (Supp (n + 1)))

/-- The lazy certification family at the observer. -/
abbrev TrustedLazyCertFamily (E : Execution Root)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted) (obs : ValidatorIndex) :
    ℕ → Checkpoint Root → Prop :=
  fun N => Weak.TrustedLazyCertAt cfg ext E B obs N

/-- The lazy support family at the observer. -/
abbrev TrustedLazySuppFamily (E : Execution Root)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted) (obs : ValidatorIndex) :
    ℕ → Root → Epoch → Prop :=
  fun N => Weak.TrustedLazySupportAt cfg ext E B obs N

end Weak
end FastConfirmation.Spec
end
