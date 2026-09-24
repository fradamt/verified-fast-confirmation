module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32Induction
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32OneStep
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32OriginCall
public import FastConfirmationProofs.Weak.History.TrustedWeakCandidateSourceHistory
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32CallSupplier
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32LazyCrossing
public import FastConfirmationProofs.Weak.Certificates.TrustedWeakBankedJustification
public import FastConfirmationProofs.Checkpoints.TrustedProcessedResetCheckpointRealization
public import FastConfirmationProofs.Weak.Common.TrustedWeakSelectedStrictEdgeLineage

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {trusted : Store Root → Prop}

structure TrustedObserverHistoricalA32CurrentLineageAt (E : Execution Root)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (obs : ValidatorIndex) (n : ℕ)
    (Cert : ℕ → Checkpoint Root → Prop)
    (Supp : ℕ → Root → Epoch → Prop) : Prop where
  confirmed_known : E.weakConfirmed cfg ext obs n ∈
    (E.store cfg ext obs n).block_roots
  current_lineage :
    get_block_epoch cfg (E.store cfg ext obs n)
          (E.weakConfirmed cfg ext obs n) =
        get_current_store_epoch cfg (E.store cfg ext obs n) →
      ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt
        cfg ext B (E.weakConfirmed cfg ext obs n) e (Cert n) (Supp n))

variable {E : Execution Root}

/-- **The lazy route.**

`Cert`/`Supp` are `Weak.TrustedLazyCertAt`/`Weak.TrustedLazySupportAt` at the write-back
bound, and the crossing builder is `Weak.trusted_selectedCurrentCrossingLazyLineage`,
which consumes **no** normative proviso.  Only the unchanged
7-field `E.CompletedFCRCallPremises` is required. -/
theorem trusted_observerLineageRoute_lazy
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) :
    Weak.TrustedObserverLineageRouteAt cfg ext E B obs
      (Weak.TrustedLazyCertFamily cfg ext E B obs)
      (Weak.TrustedLazySuppFamily cfg ext E B obs) :=
  { anchor_cert := fun _ => Weak.trusted_lazyCertAt_anchor cfg ext
    anchor_supp := fun _ _ _ h => Weak.trusted_lazySupportAt_anchor cfg ext h
    mono := fun h =>
      h.map (Weak.trusted_observerHistoricalA32LazyLineage_mono cfg ext
        (Nat.le_succ _))
    supp_transport := fun hcheckpoint hsource hsupp =>
      Weak.trusted_lazySupportAt_transport cfg ext hcheckpoint hsource hsupp
    crossing := by
      intro k hcall hHk1 hresultCurrent a c hinputKnown hselector hedge
      have hMargin : SelectedMarginAssumptions cfg ext E :=
        { genesis := hT.genesis_structure
          wellFormed := hT.wellFormed
          whole_seconds := hT.whole_seconds
          honest_behavior := hT.honest_behavior
          synchrony := hCbase.synchrony
          externals_coherence := hT.externals_coherence
          static_validators := hCbase.static_validators
          byzantine_bound := hCbase.byzantine_bound
          domain := hdomain }
      have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
        hanchor hboundary hcoh hHk1
      have htargetProducer :=
        Execution.trusted_observerCall_acceptedTargetGateProducerAt cfg ext B hT
          hCbase hfit hanchor hboundary hcoh hcall hHk1
      have hfixedRaw :=
        Weak.trusted_acceptedFixedSourceProducerAt_of_selectedCurrentCrossing cfg ext B
          hT hCbase.phase0_source hCbase.phase0_boundary_source hanchor
          hboundary hcoh hHk1 hinputKnown hselector hresultCurrent hedge
          htargetProducer
      exact ⟨Weak.trusted_selectedCurrentCrossingLazyLineage cfg ext B hT hMargin
        hanchor hboundary hcoh hHk1 hcall hG.causal hG.parent hG.walk
        hG.head_known hG.current_walk hinputKnown hselector hresultCurrent
        hedge hfixedRaw⟩ }

/-! ## Exact weak evaluator knownness -/

/-- Weak twin of `Execution.trusted_getLatestConfirmedTraceAt_result_known`: the exact
phased weak evaluator returns a known root whenever the preceding cached weak
root is known.

The finalized input uses the (node-generic) accepted finalized reset
realization; the observed input uses `Weak.trusted_weakFcrStep_observed_known`
instead of the strong `E.actualObservedRestartInputAt … .root_known`, which
is what rule delta 5's banked-justification maintenance already supplies at
every second of the observer's weak trajectory; a selected result uses the
weak known-descendant theorem.  No justification-interface or
selected-margin premise appears. -/
theorem trusted_getLatestConfirmedTraceAt_result_known
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots) :
    (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
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
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    rcases trace.observed.branch_cases with
        ⟨hobsUnchanged, _hobsFalse⟩ | ⟨hobsRestart, _hobsTrue⟩ | hreset
    · rcases trace.finalized.branch_cases with
          ⟨hcarried, _hfinalizedFalse⟩ | ⟨hreverted, _hfinalizedTrue⟩
      · rw [hobsUnchanged, hcarried]
        exact hqueryConfirmedKnown
      · have hrealized :=
          E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
            cfg ext B hT hanchor hboundary (w := obs) (n + 1)
        rw [hobsUnchanged, hreverted]
        simpa only [query, E.weakFcrStep_store] using hrealized.root_known
    · rw [hobsRestart]
      simpa only [query, E.weakFcrStep_store] using
        Weak.trusted_weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
    · have hrealized :=
        E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
          cfg ext B hT hanchor hboundary (w := obs) (n + 1)
      rw [hreset]
      simpa only [query, E.weakFcrStep_store] using hrealized.root_known
  rcases trace.selector_cases cfg ext with
      ⟨hresultEq, _hselectorFalse⟩ | ⟨hresultEq, _hselectorTrue⟩
  · rw [hresultEq]
    exact hinputKnown
  · rw [hresultEq]
    exact (weak_find_latest_confirmed_descendant_ge cfg ext query
      hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown).2

/-! ## Trusted-anchor base -/

/-- Weak twin of `Execution.acceptedHistoricalA32CurrentLineageAt_zero`: the
genesis weak confirmed root initializes both knownness and the anchor
lineage.  The anchor disjunct is recorded directly; no quorum is fabricated.

The only substitution is `E.confirmed_zero` → `E.weakConfirmed_zero`; the
checkpoint identification is the reused, honesty-free
`Execution.trustedAnchor_checkpointForBlock_of_trajectory`. -/
noncomputable def trusted_observerHistoricalA32CurrentLineageAt_zero
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (obs : ValidatorIndex)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp) :
    Weak.TrustedObserverHistoricalA32CurrentLineageAt cfg ext E B obs 0
      Cert Supp := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hconfirmedAnchor : E.weakConfirmed cfg ext obs 0 = B.anchor.root := by
    rw [E.weakConfirmed_zero, hanchor]
    change E.genesis_store.finalized_checkpoint.root =
      E.genesis_store.justified_checkpoint.root
    rw [hgen]
    rfl
  have hanchorRoot : B.anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  have hknown : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgen, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  refine {
    confirmed_known := ?_
    current_lineage := ?_
  }
  · change E.weakConfirmed cfg ext obs 0 ∈ E.genesis_store.block_roots
    simpa only [hconfirmedAnchor] using hknown
  · intro _hcurrent
    let e := get_block_epoch cfg E.genesis_store B.anchor.root
    have hat : E.AcceptedBlockAt cfg ext B.anchor.root
        (E.genesis_store.blocks B.anchor.root) :=
      E.acceptedBlockAt_of_causal_known cfg ext (.genesis) hknown
    have horiginEpoch : compute_epoch_at_slot cfg
        (E.genesis_store.blocks B.anchor.root).slot = e := by
      rfl
    have hcheckpointStore : B.state.C B.anchor.root e =
        get_checkpoint_for_block cfg E.genesis_store B.anchor.root e :=
      B.coherence.checkpoint_of_known (.genesis) B.anchor.root hknown e
    have hcheckpointAnchor : get_checkpoint_for_block cfg E.genesis_store
        B.anchor.root e = B.anchor := by
      simpa only [e] using
        E.trustedAnchor_checkpointForBlock_of_trajectory cfg ext hT
          hanchor hboundary
    have hpayload := Execution.TrustedAcceptedHistoricalA32GatePayloadCoreAt.of_anchor
      cfg ext B hat horiginEpoch
        (hcheckpointStore.trans hcheckpointAnchor)
        (hroute.anchor_cert 0) (hroute.anchor_supp 0)
    refine ⟨e, ⟨?_⟩⟩
    simpa only [hconfirmedAnchor] using
      (Execution.TrustedAcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload)

/-! ## Write-back induction -/

/-- Weak twin of `Execution.acceptedHistoricalA32CurrentLineageAt_all`: the
observer's complete bounded weak trajectory.  At actual weak calls the exact
weak trace transformer is used; between calls, block agreement and the
unchanged slot transport the preceding lineage — that second half is entirely
about `E.store`, which the two models share, so only the write-back equations
change (`E.confirmed_succ_of_*` → `E.weakConfirmed_succ_of_*`). -/
noncomputable def trusted_observerHistoricalA32CurrentLineageAt_all
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      Weak.TrustedObserverHistoricalA32CurrentLineageAt cfg ext E B obs n
        Cert Supp := by
  intro n
  induction n with
  | zero =>
      intro _hH0
      exact Weak.trusted_observerHistoricalA32CurrentLineageAt_zero cfg ext B hT
        hanchor hboundary obs hroute
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hprevious := ih hHn
      have hknownN1Prev : E.weakConfirmed cfg ext obs n ∈
          (E.store cfg ext obs (n + 1)).block_roots :=
        (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
          hprevious.confirmed_known
      by_cases hadv : E.IsScheduledFCRCallAt cfg ext obs n
      · let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
        have htraceKnown := Weak.trusted_getLatestConfirmedTraceAt_result_known
          cfg ext B hT hanchor hboundary hcoh hHn1
            hprevious.confirmed_known
        have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) =
            trace.result :=
          (E.weakConfirmed_succ_of_advance cfg ext obs n hadv).trans
            trace.result_eq.symm
        refine {
          confirmed_known := ?_
          current_lineage := ?_
        }
        · rw [hconfirmedOut]
          simpa only [trace, E.weakFcrStep_store] using htraceKnown
        · intro hcurrentN1
          have htraceCurrent : get_block_epoch cfg
                (E.weakFcrStep cfg ext obs n).store trace.result =
              get_current_store_epoch cfg
                (E.weakFcrStep cfg ext obs n).store := by
            rw [hconfirmedOut] at hcurrentN1
            simpa only [trace, E.weakFcrStep_store] using hcurrentN1
          obtain ⟨e, hlineage⟩ :=
            Weak.trusted_getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B
              hT hanchor hboundary hcoh hHn1 hprevious.confirmed_known
              htraceCurrent (hroute.anchor_cert (n + 1))
              (hroute.anchor_supp (n + 1))
              (fun hinputKnown hselector hedge =>
                hroute.crossing hadv hHn1 htraceCurrent hinputKnown hselector
                  hedge)
              (fun hcur => (hprevious.current_lineage hcur).imp
                (fun _ h => hroute.mono h))
          refine ⟨e, ?_⟩
          simpa only [trace, hconfirmedOut] using hlineage
      · have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) =
            E.weakConfirmed cfg ext obs n :=
          E.weakConfirmed_succ_of_no_advance cfg ext obs n hadv
        have hblockAgree :
            (E.store cfg ext obs n).blocks (E.weakConfirmed cfg ext obs n) =
              (E.store cfg ext obs (n + 1)).blocks
                (E.weakConfirmed cfg ext obs n) :=
          hT.wellFormed.blocks_agree
            (E.blockProvenance cfg ext obs n)
            (E.blockProvenance cfg ext obs (n + 1))
            hprevious.confirmed_known hknownN1Prev
        have hslotMono : get_current_slot cfg (E.store cfg ext obs n) ≤
            get_current_slot cfg (E.store cfg ext obs (n + 1)) := by
          simpa only [E.store_current_slot] using
            E.slot_at_mono cfg (Nat.le_succ n)
        have hslotEq : get_current_slot cfg (E.store cfg ext obs n) =
            get_current_slot cfg (E.store cfg ext obs (n + 1)) :=
          Nat.le_antisymm hslotMono (Nat.le_of_not_gt hadv)
        have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext obs n)
              (E.weakConfirmed cfg ext obs n) =
            get_block_epoch cfg (E.store cfg ext obs (n + 1))
              (E.weakConfirmed cfg ext obs n) := by
          simp only [get_block_epoch, hblockAgree]
        have hcurrentEpochEq :
            get_current_store_epoch cfg (E.store cfg ext obs n) =
              get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
          simp only [get_current_store_epoch, hslotEq]
        refine {
          confirmed_known := ?_
          current_lineage := ?_
        }
        · rw [hconfirmedOut]
          exact hknownN1Prev
        · intro hcurrentN1
          have hcurrentN : get_block_epoch cfg (E.store cfg ext obs n)
                (E.weakConfirmed cfg ext obs n) =
              get_current_store_epoch cfg (E.store cfg ext obs n) := by
            rw [hblockEpochAgree, hcurrentEpochEq, ← hconfirmedOut]
            exact hcurrentN1
          obtain ⟨e, hlineage⟩ := hprevious.current_lineage hcurrentN
          refine ⟨e, ?_⟩
          simpa only [hconfirmedOut] using hroute.mono hlineage

/-- Weak twin of
`Execution.acceptedHistoricalA32CurrentLineage_invariant`, restated at a
single fixed observer (the strong form's `∀ v ∈ E.honest` quantifier has no
weak counterpart: there is exactly one node whose weak call trajectory is
available).

No new assumption is taken beyond the route: `hroute` supplies the crossing
builder and the two anchor discharges, and every top-level weak statement
already carries `B`/`hT`/`hanchor`/`hboundary`. -/
theorem trusted_observerHistoricalA32CurrentLineage_invariant
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      Weak.TrustedObserverHistoricalA32CurrentLineageAt cfg ext E B obs n
        Cert Supp :=
  Weak.trusted_observerHistoricalA32CurrentLineageAt_all cfg ext B hT hanchor
    hboundary hcoh hroute

/-! ## Residual target 1: the weak call's own current-epoch lineage -/

/-- Weak twin of
`Execution.acceptedHistoricalA32CurrentLineage_of_completedPrefixes`, stated
at the weak evaluator's *result* rather than at the cached root, which is the
shape `Weak.ObserverStrictCallFilterInputsAt.current_lineage` asks for.

Rather than routing through the `n + 1` write-back (which would force an
`E.weakConfirmed cfg ext obs (n + 1) = trace.result` rewrite), this applies
the one-call transformer directly to the induction's `n`-th retained facts;
the conclusion is therefore literally the residual field.

`hcall` is unavoidable and is the only extra binder: the route's crossing
builder and the completed-prefix gate producer are both contracted at actual
weak FCR calls only. -/
theorem trusted_observerCall_currentLineage
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp)
    {n : ℕ} (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e
      (Cert (n + 1)) (Supp (n + 1))) := by
  intro hcurrent
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hprevious := Weak.trusted_observerHistoricalA32CurrentLineage_invariant
    cfg ext B hT hanchor hboundary hcoh hroute n hHn
  exact Weak.trusted_getLatestConfirmedTraceAt_currentLineage_step_core cfg ext B hT
    hanchor hboundary hcoh hHn1 hprevious.confirmed_known hcurrent
    (hroute.anchor_cert (n + 1)) (hroute.anchor_supp (n + 1))
    (fun hinputKnown hselector hedge =>
      hroute.crossing hcall hHn1 hcurrent hinputKnown hselector hedge)
    (fun hcur => (hprevious.current_lineage hcur).imp
      (fun _ h => hroute.mono h))

/-! ## Residual target 2: the epoch-start `carried` previous result -/

/-- Weak twin of
`Execution.StrictSelectorAdvanceAt.previousCarried_epochStartLineage`, in the
shape `Weak.ObserverStrictCallFilterInputsAt.previous_epochStart_carried_
lineage` asks for (same three antecedents, same order).

Two deliberate differences from the strong statement.  First, the strong
`hselector : StrictSelectorAdvanceAt` premise is *dropped*: the residual field
does not carry one, and none is needed.  Its only two uses were
`input_recent`, which on a `carried` input is exactly
`Weak.CarriedCandidateInputAt.confirmed_recent`, and the same-epoch
extension, which is needed only when the result actually moved — so the proof
splits on `trace.result = trace.afterObserved` and rebuilds
`Weak.StrictSelectorAdvanceAt` itself in the strict branch.  Second, the
strong `hdomain : SelectedMarginDomain` binder is gone, because
`Weak.StrictSelectorAdvanceAt.trusted_extendHistoricalLineage_sameEpoch_actual`
already replaced it by observer coherence. -/
theorem trusted_observerCall_previousCarried_epochStartLineage
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp)
    {n : ℕ} (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    Weak.CarriedCandidateInputAt cfg ext (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) →
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) = true →
    Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      (Cert n) (Supp n)) := by
  intro horigin hprevious hstart
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hinvariant := Weak.trusted_observerHistoricalA32CurrentLineage_invariant
    cfg ext B hT hanchor hboundary hcoh hroute n hHn
  have hstartStore : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext obs (n + 1))) = true := by
    simpa only [E.weakFcrStep_store] using hstart
  have hrecentConfirmed : get_block_epoch cfg
        (E.weakFcrStep cfg ext obs n).store (E.weakConfirmed cfg ext obs n) +
        1 ≥
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
    simpa only [E.weakFcrStep_confirmed_root] using
      horigin.confirmed_recent cfg ext
  have hcurrentN := Weak.previousConfirmed_current_of_boundary_recent cfg ext
    hT hcall hstartStore hinvariant.confirmed_known hrecentConfirmed
  obtain ⟨e, ⟨hlineageN⟩⟩ := hinvariant.current_lineage hcurrentN
  have hknownN1 : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
      hinvariant.confirmed_known
  have hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots := by
    rw [horigin.input_eq, E.weakFcrStep_confirmed_root, E.weakFcrStep_store]
    exact hknownN1
  have hqueryCausal : E.CausalStore cfg ext
      (E.weakFcrStep cfg ext obs n).store := by
    rw [E.weakFcrStep_store]
    exact E.store_causal cfg ext obs (n + 1)
  have hlineageQ : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved e
      (Cert n) (Supp n) := by
    simpa only [horigin.input_eq, E.weakFcrStep_confirmed_root]
      using hlineageN
  have hinputBlockEq : (E.weakFcrStep cfg ext obs n).store.blocks
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
      hlineageQ.tip_block :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed hqueryCausal hinputKnown).mp hlineageQ.tip_at
  have hinputEpochE : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved = e := by
    simpa only [get_block_epoch, hinputBlockEq] using hlineageQ.tip_epoch
  have hinputPrevious : get_block_epoch cfg
          (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved + 1 =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
    have hepochSucc := E.actualCall_currentEpoch_succ_of_start
      cfg ext hT hcall hstartStore
    have hblockAgree : (E.store cfg ext obs n).blocks
          (E.weakConfirmed cfg ext obs n) =
        (E.store cfg ext obs (n + 1)).blocks
          (E.weakConfirmed cfg ext obs n) :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext obs n)
        (E.blockProvenance cfg ext obs (n + 1))
        hinvariant.confirmed_known hknownN1
    calc
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
            (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved +
            1 =
          get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) + 1 := by
        simp only [horigin.input_eq, E.weakFcrStep_confirmed_root,
          E.weakFcrStep_store, get_block_epoch, hblockAgree]
      _ = get_current_store_epoch cfg (E.store cfg ext obs n) + 1 := by
        rw [hcurrentN]
      _ = get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) :=
        hepochSucc
      _ = get_current_store_epoch cfg
            (E.weakFcrStep cfg ext obs n).store := by
        rw [E.weakFcrStep_store]
  have hresultEpochE : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result = e := by
    have hresultInputEpoch : get_block_epoch cfg
          (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved :=
      Nat.add_right_cancel (hprevious.trans hinputPrevious.symm)
    exact hresultInputEpoch.trans hinputEpochE
  rw [hresultEpochE]
  by_cases hfix : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
  · rw [hfix]
    exact ⟨hlineageQ⟩
  · have hsel : Weak.StrictSelectorAdvanceAt cfg ext
        (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n) := by
      rcases (E.weakGetLatestConfirmedTraceAt cfg ext obs n).selector_cases
          cfg ext with ⟨hresultEq, _hfalse⟩ | ⟨hresultEq, hguard⟩
      · exact absurd hresultEq hfix
      · exact {
          result_eq := hresultEq
          guard_true := hguard
          input_recent := by
            simpa only [horigin.input_eq] using horigin.confirmed_recent cfg ext
          result_ne_input := hfix }
    exact ⟨Weak.StrictSelectorAdvanceAt.trusted_extendHistoricalLineage_sameEpoch_actual
      cfg ext B hT hcoh hHn1 hsel hinputKnown hlineageQ hinputEpochE
      hresultEpochE⟩

/-! ## Residual target 3: the retained A3.2 payload producer at a weak call -/

/-- Weak twin of `Execution.AcceptedBlockAt.executionRoot_for_actualOrientation`.

The strong copy is `private`, so it cannot be applied from here; the strong
development already keeps a second identical private copy
(`AcceptedHistoricalLineageFinalizedPlacement.executionRoot_mixed`) for the
same reason.  Nothing in it is honesty-, evaluator- or model-dependent: it is
pure block provenance. -/
private theorem AcceptedBlockAt.executionRoot_for_observerOrientation
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Weak-side copy of the `private`
`Execution.TrustedAcceptedHistoricalA32LineageAt.payloadAtExecutionStore`: materialize
a retained lineage in an ordinary execution-boundary store.

This is accepted-root reflection plus the trusted-anchor boundary walk; it
uses no endpoint, no-crossing fact or safety conclusion, and it is quantified
over an arbitrary node `v`, so no substitution at all is needed — only the
`private` modifier on the strong copy forces the duplicate. -/
private theorem TrustedAcceptedHistoricalA32LineageCoreAt.payloadAtObserverStore
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {tip : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert Supp)
    (htip : tip ∈ (E.store cfg ext v q).block_roots)
    (htipEpoch : get_block_epoch cfg (E.store cfg ext v q) tip = e)
    (hsuppT : ∀ {origin tip' : Root},
      B.state.C tip' e = B.state.C origin e →
      B.state.GJ tip' = B.state.GJ origin → Supp origin e → Supp tip' e) :
    Nonempty (E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B tip e
      Cert Supp) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  let store := E.store cfg ext v q
  have hstoreCausal : E.CausalStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext v q
  have hstoreParent : ParentSlotLt store := by
    simpa only [store] using E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled v q
  have htip' : tip ∈ store.block_roots := by
    simpa only [store] using htip
  have horiginRoot : E.ExecutionRoot hlineage.origin :=
    Weak.AcceptedBlockAt.executionRoot_for_observerOrientation cfg ext
      hlineage.payload.origin_at
  have horiginReflection :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      htip horiginRoot hlineage.descends
  have horigin : hlineage.origin ∈ store.block_roots := by
    simpa only [store] using horiginReflection.1
  have htipOrigin : is_ancestor store (get_node_for_root tip)
      (get_node_for_root hlineage.origin) = true := by
    simpa only [store] using horiginReflection.2
  have horiginAt : E.AcceptedBlockAt cfg ext hlineage.origin
      (store.blocks hlineage.origin) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstoreCausal horigin
  have horiginBlock : hlineage.payload.origin_block =
      store.blocks hlineage.origin :=
    hlineage.payload.origin_at.unique cfg ext E hT.wellFormed horiginAt
  have horiginEpoch : get_block_epoch cfg store hlineage.origin = e := by
    simpa only [get_block_epoch, ← horiginBlock] using
      hlineage.payload.origin_epoch
  have htipEpoch' : get_block_epoch cfg store tip = e := by
    simpa only [store] using htipEpoch
  have hanchorLe : B.anchor.epoch ≤ e := hlineage.payload.anchor_epoch_le
  have htipWalk : WalkKnown store
      (compute_start_slot_at_epoch cfg e) tip := by
    simpa only [store] using
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v q hanchorLe htip
  exact ⟨hlineage.payloadAtTip cfg ext hphase hstoreCausal hstoreParent
    horigin htip' horiginEpoch htipEpoch' htipOrigin htipWalk
    (fun hcheckpoint hsource hsupp => hsuppT hcheckpoint hsource hsupp)⟩

/-- **The certificate the `currentHistorical` call-site arm reads**, rebuilt
at the observer's consuming call.

Weak twin of `Execution.completedPrefix_acceptedHistoricalCertificateProducerAt`
(`AcceptedActualSelectedJustifiedOrientation.lean`), and this is where the
no-crossing antecedent becomes load-bearing.  Under the lazy route the lineage
carried at write-back second `n + 1` would require the threaded fold output
*at second `n`*, which is what the enclosing dispatcher is proving.  But
`hnoCrossing` says this call created no payload at all: it transported the
input's.  So the one-call transformer is run in its no-crossing form from the
invariant at second `n`, whose certification obligation `certElim` discharges
— under the lazy instantiation, from the fold output strictly below `n`.  This
is D1† of `docs/crossing-call-support-residue.md` §2.1, ported to the weak
side (`docs/weak-final-wave.md` §4). -/
theorem trusted_observerCall_currentTargetHistoricalCertificate
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp)
    {n : Nat}
    (certElim : ∀ {c : Checkpoint Root}, Cert n c →
      Nonempty (CertifiedJustified cfg E B.anchor c))
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetSelectedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c) :
    Nonempty (CertifiedJustified cfg E B.anchor
      (get_current_target cfg (E.weakFcrStep cfg ext obs n).store)) := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hqueryStore : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hinvariantN := Weak.trusted_observerHistoricalA32CurrentLineage_invariant
    cfg ext B hT hanchor hboundary hcoh hroute n hHn
  obtain ⟨e, ⟨hlineage⟩⟩ :=
    Weak.trusted_getLatestConfirmedTraceAt_currentLineage_step_noCrossing cfg ext B hT
      hanchor hboundary hcoh hHn1 hinvariantN.confirmed_known hcurrent
      hnoCrossing (hroute.anchor_cert n) (hroute.anchor_supp n)
      hinvariantN.current_lineage
  have hresultKnown : trace.result ∈ query.store.block_roots :=
    Weak.trusted_getLatestConfirmedTraceAt_result_known cfg ext B hT hanchor hboundary
      hcoh hHn1 hinvariantN.confirmed_known
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    rw [hqueryStore]
    exact E.store_causal cfg ext obs (n + 1)
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal hresultKnown
  have htipBlock : hlineage.tip_block = query.store.blocks trace.result :=
    hlineage.tip_at.unique cfg ext E hT.wellFormed hresultAt
  have hresultEpoch : get_block_epoch cfg query.store trace.result = e := by
    simpa only [get_block_epoch, ← htipBlock] using hlineage.tip_epoch
  obtain ⟨hpayload⟩ :
      Nonempty (E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B
        trace.result e (Cert n) (Supp n)) := by
    apply Weak.TrustedAcceptedHistoricalA32LineageCoreAt.payloadAtObserverStore
      cfg ext B hT hphase hanchor hboundary hlineage
    · simpa only [hqueryStore] using hresultKnown
    · simpa only [hqueryStore] using hresultEpoch
    · intro origin tip' hcheckpoint hsource hsupp
      exact hroute.supp_transport hcheckpoint hsource hsupp
  have hstrictFind : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)
  have hbelow : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hselector.result_eq]
    exact Weak.strictSelectedResult_below_head cfg ext hG.parent hG.walk
      hG.head_known (by simpa only [query, trace] using hinput) hstrictFind
  have hboundaryResult : compute_start_slot_at_epoch cfg e ≤
      (query.store.blocks trace.result).slot := by
    rw [← hresultEpoch]
    exact start_slot_at_block_epoch_le cfg query.store trace.result
  have hwalkHead : WalkKnown query.store
      (compute_start_slot_at_epoch cfg e) (get_head cfg query.store).root := by
    have hanchorLe : B.anchor.epoch ≤ e := hpayload.anchor_epoch_le
    have hw :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary obs (n + 1) hanchorLe
          (by simpa only [hqueryStore] using hG.head_known)
    simpa only [hqueryStore] using hw
  have hcheckpoint : get_checkpoint_block cfg query.store
        (get_head cfg query.store).root e =
      get_checkpoint_block cfg query.store trace.result e :=
    get_checkpoint_block_of_ancestor cfg hG.parent
      (by rw [is_ancestor_node_root] at hbelow; exact hbelow)
      hboundaryResult hwalkHead
  have heCurrent : e = get_current_store_epoch cfg query.store :=
    hresultEpoch.symm.trans hcurrent
  have htarget : get_current_target cfg query.store =
      B.state.C trace.result e := by
    calc
      get_current_target cfg query.store =
          get_checkpoint_for_block cfg query.store
            (get_head cfg query.store).root
              (get_current_store_epoch cfg query.store) := rfl
      _ = get_checkpoint_for_block cfg query.store
            (get_head cfg query.store).root e := by rw [heCurrent]
      _ = get_checkpoint_for_block cfg query.store trace.result e := by
        exact congrArg (Checkpoint.mk e) hcheckpoint
      _ = B.state.C trace.result e :=
        (B.coherence.checkpoint_of_known hqueryCausal trace.result
          hresultKnown e).symm
  rw [htarget]
  exact certElim hpayload.certified

end Weak
end FastConfirmation.Spec
end
