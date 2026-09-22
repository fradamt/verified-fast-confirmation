import FastConfirmation.Spec.Proof.AcceptedActualFCRContractScaffold
import FastConfirmation.Spec.Proof.AcceptedSelectedStrictEdgeFilterSupply

/-!
# Accepted actual-FCR strict-helper integration

This module is deliberately downstream of both the branch-sensitive public
contract and the completed strict-edge dispatcher.  It specializes the
contract to the canonical `getLatestConfirmedTraceAt` call, eliminates the
three operationally unchanged branches, and uses
`StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt` in the
one strict branch.

Reset adoption remains outside this theorem.  Its conclusion is exactly the
strict helper tier: if the actual call's carried input is known and already
`SafeFrom (n+1)`, the canonical selector result is `SafeFrom (n+1)`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The completed accepted dispatcher discharges the scaffold's one named
strict filter supplier for the canonical actual-call trace.

The supplier is guarded by `trace.result ≠ trace.afterObserved`, so all three
unchanged candidate-history branches close by contradiction.  The remaining
branch exposes exactly the ordered input origin and strict selector record
consumed by the dispatcher. -/
noncomputable def
    getLatestConfirmedTraceAt_actualFCRStrictSelectedFilterSupplierAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1)))) :
    E.ActualFCRStrictSelectedFilterSupplierAt cfg ext v n
      (E.getLatestConfirmedTraceAt cfg ext v n) := by
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  intro hstrict
  have hbranch := trace.candidateHistoryCallBranch
    (cfg := cfg) (ext := ext)
  cases hbranch with
  | carriedUnchanged _ hselector =>
      have hfalse : False :=
        hstrict (hselector.result_eq_input cfg ext)
      contradiction
  | finalizedResetUnchanged _ hselector =>
      have hfalse : False :=
        hstrict (hselector.result_eq_input cfg ext)
      contradiction
  | observedResetUnchanged _ hselector =>
      have hfalse : False :=
        hstrict (hselector.result_eq_input cfg ext)
      contradiction
  | strictSelected horigin hselector =>
      intro a c w m lo es sigma querySlot hw hmH hgeom hcne hcM
        hparentEdge hselectedC hselectedKnown hIH hnotCovered
      exact
        (Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt
          cfg ext B hT hC hfit hdomain hanchor hboundary hDelay hspe
            hpaper P V hanchorExact hv hHn1 hcall hinput hbase
              horigin hselector) hw hmH hgeom hcne hcM hparentEdge
                hselectedC hselectedKnown hIH hnotCovered

/-- Canonical strict-helper tier with the abstract supplier fully discharged.

The only safety premise is the contract's carried-input induction hypothesis;
no reset `SafeFrom`, whole-output `Spec_Safety`, justification interface, or
legacy pipeline is assumed. -/
theorem getLatestConfirmedTraceAt_result_safeFrom_of_acceptedDispatcher
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hinputSafe : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved (n + 1)) :
    E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).result (n + 1) := by
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.static_validators
      byzantine_bound := hC.byzantine_bound
      domain := hdomain }
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hcall
  have hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))) := by
    simpa only [hstartEq] using hinputSafe
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  exact
    Execution.GetLatestConfirmedTrace.result_safeFrom_of_actualCall_strictSupplier
      cfg ext E hA hwalkDomain hv hHn1 hcall
        (E.getLatestConfirmedTraceAt cfg ext v n) hinput hinputSafe
          (E.getLatestConfirmedTraceAt_actualFCRStrictSelectedFilterSupplierAt
            cfg ext B hT hC hfit hdomain hanchor hboundary hDelay hspe
              hpaper P V hanchorExact hv hHn1 hcall hinput hbase)

end Execution

end FastConfirmation.Spec
