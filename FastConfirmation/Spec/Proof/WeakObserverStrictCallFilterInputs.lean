import FastConfirmation.Spec.Proof.WeakHistoricalA32PayloadProducer

/-!
# Spec / Proof / WeakObserverStrictCallFilterInputs

The producer for `Weak.ObserverStrictCallFilterInputsAt`, the residual record
stage S7 left attached to the weak phase dispatcher and the weak strict-edge
filter supplier.

The record started life with five fields.  The wave has since discharged them:

* `previous_epochStart_observedReset_headDisseminated` — **deleted**.  Its
  gated arm is `Weak.StrictSelectorAdvanceAt.previousObservedReset_gatedHeadDisseminated`
  (rule delta 5's banking gate certifies the query head itself, because at an
  epoch-start call `Weak.update_fast_confirmation_variables` runs on this same
  store), and its ungated arm is vacuous
  (`Weak.observedReset_ungated_absurd`).
* `result_descends_endpoint_justified` and `endpoint_justified_epoch_le_result`
  — the observer-side pre-query SIR chain, proved in
  `WeakSelectedJustifiedOrientation.lean` on top of `WeakPreQuerySIR.lean`.
* `current_lineage` and `previous_epochStart_carried_lineage` — the
  observer-side A3.2 write-back induction over `E.weakConfirmed`.

Nothing is left outside.  The producer below builds the whole record from the
S7 supplier's own premise set, plus an obligation route
(`Weak.ObserverLineageRouteAt`) and the outer safety fold's carried input
safety `hbase` — the same premise the strong actual-call theorem takes.

The producer has exactly one instantiation,
`observerStrictCallFilterInputsAt_of_observerCall_lazy`: it takes only the
6-field `E.AcceptedHistoricalA32CompletedPrefixCallAssumptions` plus the
threaded fold output `Weak.ObserverPriorCallWriteBackSafe obs n`, and the
trajectory fold takes it.  The **eager** instantiation, driven by the
observer-side proviso record, was deleted together with the four closed
one-shot weak witnesses that were its only consumers.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- **The residual bundle, assembled — route-generic.**

Every field of `Weak.ObserverStrictCallFilterInputsAt` is discharged from the
S7 supplier's own premises plus the obligation route, the eliminations it
carries, and the carried input safety `hbase`. -/
theorem observerStrictCallFilterInputsAt_of_route
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.ObserverLineageRouteAt cfg ext E B obs Cert Supp)
    (certElim : ∀ {c : Checkpoint Root}, Cert n c →
      Nonempty (CertifiedJustified cfg E B.anchor c))
    (suppElimCurrent : ∀ {o : Root} {e : Epoch}, Supp (n + 1) o e →
      ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
      E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
      E.IsFCRCallAt cfg ext obs n →
        B.state.C o e = B.anchor ∨
          Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B o e))
    (suppElimPrior : ∀ {o : Root} {e : Epoch}, Supp n o e →
      ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
        B.state.C o e = B.anchor ∨
          Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B o e))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.ObserverStrictCallFilterInputsAt cfg ext E B obs n Cert Supp := by
  have hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext
      E B.anchor (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
    Weak.observerCall_historicalCertificateProducerAt cfg ext B hT
      hCbase.phase0_source hanchor hboundary hcoh hroute certElim hHn1 hinput
      hselector
  refine
    { result_descends_endpoint_justified := ?_
      endpoint_justified_epoch_le_result := ?_
      current_lineage :=
        Weak.observerCall_currentLineage cfg ext B hT hanchor
          hboundary hcoh hroute hcall hHn1
      previous_epochStart_carried_lineage :=
        Weak.observerCall_previousCarried_epochStartLineage cfg ext B hT
          hanchor hboundary hcoh hroute hcall hHn1
      anchor_cert := hroute.anchor_cert
      anchor_supp := hroute.anchor_supp
      supp_transport := fun hcheckpoint hsource hsupp =>
        hroute.supp_transport hcheckpoint hsource hsupp
      supp_elim_current := suppElimCurrent
      supp_elim_prior := suppElimPrior }
  · intro c w m hw hmH hslotQM hcM hselectedC hselectedKnown hIH hnotCovered
    exact
      Weak.observerCall_strictSelected_result_and_child_ancestor_of_endpointJustified
        cfg ext B hT hCbase hfit hdomain hanchor hboundary hcoh hcall hHn1
        hinput hbase hselector hhistorical hw hmH hslotQM hcM hselectedC
        hselectedKnown hIH hnotCovered
  · intro c w m hw hmH hslotQM hcM hselectedC hselectedKnown hIH hnotCovered
    exact Weak.observerCall_strictSelected_endpointJustifiedEpoch_le_result
      cfg ext B hT hCbase hfit hdomain hanchor hboundary hcoh hcall hHn1
      hinput hbase hselector hhistorical hw hmH hslotQM hcM hselectedC
      hselectedKnown hIH hnotCovered

/-- **The lazy instantiation.**

No proviso anywhere: the call contract is the unchanged 6-field
`E.AcceptedHistoricalA32CompletedPrefixCallAssumptions`, and the two payload
obligations are discharged from the trajectory fold's own strictly earlier
output `hprior`, plus — at the late current-epoch cell only — the endpoint
induction's own `hIH`, converted by
`Execution.engineInv_of_selectedCanonical_lateEndpoint`. -/
theorem observerStrictCallFilterInputsAt_of_observerCall_lazy
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.ObserverStrictCallFilterInputsAt cfg ext E B obs n
      (Weak.LazyCertFamily cfg ext E B obs)
      (Weak.LazySuppFamily cfg ext E B obs) := by
  have hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hCbase.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hCbase.static_validators
      byzantine_bound := hCbase.byzantine_bound
      domain := hdomain }
  have hwrite : E.weakConfirmed cfg ext obs (n + 1) =
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
    (E.weakActualCandidateHistoryRecurrence cfg ext hcall).result_writeback
  refine Weak.observerStrictCallFilterInputsAt_of_route cfg ext B hT hCbase
    hfit hdomain hanchor hboundary hcoh
    (Weak.observerLineageRoute_lazy cfg ext B hT hCbase hdomain hfit hanchor
      hboundary hcoh)
    (fun hc => hc hprior) ?_ ?_ hcall hHn1 hinput hbase hselector
  · -- the late current-epoch cell: `k < n` from `hprior`, `k = n` from `hIH`
    intro o e hsupp w hw m hmH hlate hIH _hcall
    refine hsupp w hw m hmH hlate ?_
    refine Weak.observerCallWriteBackEngineSafeUpTo_of_prior_and_current
      cfg ext hprior ?_
    intro _ _
    rw [hwrite]
    exact E.engineInv_of_selectedCanonical_lateEndpoint cfg ext hMargin hlate
      hIH
  · -- the epoch-start previous cell: `k = n` never arises
    intro o e hsupp w hw m hmH hlate
    refine hsupp w hw m hmH hlate ?_
    intro k hk hkH hcallK
    exact E.engineInv_of_safeFrom cfg ext (hprior k (by omega) hkH hcallK)

/-- **The lazy weak strict-edge filter supplier.**

`Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt`
with its `hinputs` binder discharged by the producer above.  The historical
A3.2 call contract is the unchanged 6-field completed-prefix contract
`hCbase` together with `hprior` (a *derived* trajectory fact, supplied by the
weak safety fold's own strengthened induction hypothesis at strictly earlier
seconds).  No normative observer proviso is consumed anywhere below this. -/
noncomputable def
    StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_lazy
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
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
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (horigin : Weak.OrderedCandidateInputOrigin cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      obs (n + 1) (E.weakFcrStep cfg ext obs n) :=
  Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt
    cfg ext B hT hsync hstatic hbyz hdomain hji hanchor hboundary hDelay
    hphase0 hpaper P V hanchorExact hcoh hn1H hcall hinput horigin hselector
    (Weak.observerStrictCallFilterInputsAt_of_observerCall_lazy cfg ext B hT
      hCbase hfit hdomain hanchor hboundary hcoh hprior hcall hn1H hinput
      hbase hselector)

end Weak

end FastConfirmation.Spec
