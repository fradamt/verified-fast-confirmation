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
S7 supplier's own premise set, plus `Weak.ObserverHistoricalA32CallAssumptions`
(obligation X1's floor-classified observer call contract) and the outer safety
fold's carried input safety `hbase` — the same premise the strong actual-call
theorem takes.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- **The residual bundle, assembled.**

Every field of `Weak.ObserverStrictCallFilterInputsAt` is discharged from the
S7 supplier's own premises plus the observer call contract `hC`, the carried
input safety `hbase`.  Nothing is left over: the record now carries no
proof obligation at all, so the S8 closed theorem can drop its `hinputs`
binder entirely. -/
theorem observerStrictCallFilterInputsAt_of_observerCall
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
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
    Weak.ObserverStrictCallFilterInputsAt cfg ext E B obs n := by
  have hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
    Weak.observerCall_historicalA32PayloadProducerAt cfg ext B hT hC hfit
      hanchor hboundary hcoh hcall hHn1 hinput hselector
  refine
    { result_descends_endpoint_justified := ?_
      endpoint_justified_epoch_le_result := ?_
      current_lineage :=
        Weak.observerCall_currentLineage cfg ext B hT hC hfit hanchor
          hboundary hcoh hcall hHn1
      previous_epochStart_carried_lineage :=
        Weak.observerCall_previousCarried_epochStartLineage cfg ext B hT hC
          hfit hanchor hboundary hcoh hcall hHn1 }
  · intro c w m hw hmH hslotQM hcM hselectedC hselectedKnown hIH hnotCovered
    exact
      Weak.observerCall_strictSelected_result_and_child_ancestor_of_endpointJustified
        cfg ext B hT hC hfit hdomain hanchor hboundary hcoh hcall hHn1
        hinput hbase hselector hhistorical hw hmH hslotQM hcM hselectedC
        hselectedKnown hIH hnotCovered
  · intro c w m hw hmH hslotQM hcM hselectedC hselectedKnown hIH hnotCovered
    exact Weak.observerCall_strictSelected_endpointJustifiedEpoch_le_result
      cfg ext B hT hC hfit hdomain hanchor hboundary hcoh hcall hHn1
      hinput hbase hselector hhistorical hw hmH hslotQM hcM hselectedC
      hselectedKnown hIH hnotCovered

/-- **The weak strict-edge filter supplier, with no residual bundle.**

`Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt`
with its `hinputs` binder discharged by the producer above.  This is the form
stage S9's closed theorem consumes: the only premises beyond stage S7's own
are `hC` (obligation X1's floor-classified observer call contract) and `hbase`
(the outer safety fold's carried input safety, exactly as in the strong
actual-call theorem). -/
noncomputable def
    StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_closed
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
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
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
    (Weak.observerStrictCallFilterInputsAt_of_observerCall cfg ext B hT hC
      hfit hdomain hanchor hboundary hcoh hcall hn1H hinput hbase hselector)

end Weak

end FastConfirmation.Spec
