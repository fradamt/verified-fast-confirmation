module
public import FastConfirmationProofs.Weak.Safety.WeakObserverStrictCallFilterInputs
public import FastConfirmationProofs.Weak.Common.TrustedWeakSelectedStrictEdgeFilterSupply
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32PayloadProducer
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Induction
public import FastConfirmationProofs.Weak.Common.TrustedWeakSelectedJustifiedOrientation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_observerStrictCallFilterInputsAt_of_route
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp)
    (certElim : ∀ {c : Checkpoint Root}, Cert n c →
      Nonempty (CertifiedJustified cfg E B.anchor c))
    (suppElimCurrent : ∀ {o : Root} {e : Epoch}, Supp (n + 1) o e →
      ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
      E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
      E.IsScheduledFCRCallAt cfg ext obs n →
        B.state.C o e = B.anchor ∨
          Nonempty (E.TrustedAcceptedHistoricalA32QuorumAt cfg ext B o e))
    (suppElimPrior : ∀ {o : Root} {e : Epoch}, Supp n o e →
      ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
        B.state.C o e = B.anchor ∨
          Nonempty (E.TrustedAcceptedHistoricalA32QuorumAt cfg ext B o e))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.TrustedObserverStrictCallFilterInputsAt cfg ext E B obs n Cert Supp := by
  have hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext
      E B.anchor (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
    Weak.trusted_observerCall_historicalCertificateProducerAt cfg ext B hT
      hCbase.phase0_source hanchor hboundary hcoh hroute certElim hHn1 hinput
      hselector
  refine
    { result_descends_endpoint_justified := ?_
      endpoint_justified_epoch_le_result := ?_
      current_lineage :=
        Weak.trusted_observerCall_currentLineage cfg ext B hT hanchor
          hboundary hcoh hroute hcall hHn1
      previous_epochStart_carried_lineage :=
        Weak.trusted_observerCall_previousCarried_epochStartLineage cfg ext B hT
          hanchor hboundary hcoh hroute hcall hHn1
      anchor_cert := hroute.anchor_cert
      anchor_supp := hroute.anchor_supp
      supp_transport := fun hcheckpoint hsource hsupp =>
        hroute.supp_transport hcheckpoint hsource hsupp
      supp_elim_current := suppElimCurrent
      supp_elim_prior := suppElimPrior }
  · intro c w m hw hmH hslotQM hcM hselectedC hselectedKnown hIH hnotCovered
    exact
      Weak.trusted_observerCall_strictSelected_result_and_child_ancestor_of_endpointJustified
        cfg ext B hT hCbase hfit hdomain hanchor hboundary hcoh hcall hHn1
        hinput hbase hselector hhistorical hw hmH hslotQM hcM hselectedC
        hselectedKnown hIH hnotCovered
  · intro c w m hw hmH hslotQM hcM hselectedC hselectedKnown hIH hnotCovered
    exact Weak.trusted_observerCall_strictSelected_endpointJustifiedEpoch_le_result
      cfg ext B hT hCbase hfit hdomain hanchor hboundary hcoh hcall hHn1
      hinput hbase hselector hhistorical hw hmH hslotQM hcM hselectedC
      hselectedKnown hIH hnotCovered

/-- **The lazy instantiation.**

No proviso anywhere: the call contract is the unchanged 7-field
`E.CompletedFCRCallPremises`, and the two payload
obligations are discharged from the trajectory fold's own strictly earlier
output `hprior`, plus — at the late current-epoch cell only — the endpoint
induction's own `hIH`, converted by
`Execution.engineInv_of_selectedCanonical_lateEndpoint`. -/
theorem trusted_observerStrictCallFilterInputsAt_of_observerCall_lazy
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.TrustedObserverStrictCallFilterInputsAt cfg ext E B obs n
      (Weak.TrustedLazyCertFamily cfg ext E B obs)
      (Weak.TrustedLazySuppFamily cfg ext E B obs) := by
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
  have hwrite : E.weakConfirmed cfg ext obs (n + 1) =
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
    (E.weakActualCandidateHistoryRecurrence cfg ext hcall).result_writeback
  refine Weak.trusted_observerStrictCallFilterInputsAt_of_route cfg ext B hT hCbase
    hfit hdomain hanchor hboundary hcoh
    (Weak.trusted_observerLineageRoute_lazy cfg ext B hT hCbase hdomain hfit hanchor
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

`Weak.StrictSelectorAdvanceAt.trusted_observerCall_selectedStrictEdgeFilterSupplyAt`
with its `hinputs` binder discharged by the producer above.  The historical
A3.2 call contract is the unchanged 7-field completed-prefix contract
`hCbase` together with `hprior` (a *derived* trajectory fact, supplied by the
weak safety fold's own strengthened induction hypothesis at strictly earlier
seconds).  No normative observer proviso is consumed anywhere below this. -/
noncomputable def
    StrictSelectorAdvanceAt.trusted_observerCall_selectedStrictEdgeFilterSupplyAt_lazy
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)

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
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
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
  Weak.StrictSelectorAdvanceAt.trusted_observerCall_selectedStrictEdgeFilterSupplyAt
    cfg ext B hT hsync hstatic hbyz hdomain  hanchor hboundary hDelay
    hphase0 hpaper P V hanchorExact hcoh hn1H hcall hinput horigin hselector
    (Weak.trusted_observerStrictCallFilterInputsAt_of_observerCall_lazy cfg ext B hT
      hCbase hfit hdomain hanchor hboundary hcoh hprior hcall hn1H hinput
      hbase hselector)

end Weak
end FastConfirmation.Spec
end
