module
public import FastConfirmationProofs.FCRRule.FCRCallInvariants
public import FastConfirmationProofs.Execution.Delivery.SelectedEdgeFilter

@[expose] public section

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
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hinvariant : E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
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
            hpaper P V hanchorExact hv hHn1 hcall hinvariant hinput hbase
              horigin hselector) hw hmH hgeom hcne hcM hparentEdge
                hselectedC hselectedKnown hIH hnotCovered

/-- Canonical strict-helper tier with the abstract supplier fully discharged.

The only safety premise is the contract's carried-input induction hypothesis;
no reset `SafeFrom`, whole-output `Spec_Safety`, justification interface, or
legacy pipeline is assumed. -/
theorem getLatestConfirmedTraceAt_result_safeFrom_of_acceptedDispatcher
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hinvariant : E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
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
    Execution.LatestConfirmedCallTrace.result_safeFrom_of_actualCall_strictSupplier
      cfg ext E hA hwalkDomain hv hHn1 hcall
        (E.getLatestConfirmedTraceAt cfg ext v n) hinput hinputSafe
          (E.getLatestConfirmedTraceAt_actualFCRStrictSelectedFilterSupplierAt
            cfg ext B hT hC hfit hdomain hanchor hboundary hDelay hspe
              hpaper P V hanchorExact hv hHn1 hcall hinvariant hinput hbase)

/-- The call fold derives current-target support after proving the strict
result safe. This supplies the next call's lineage without a global proviso. -/
theorem currentLineage_of_strictResultSafety
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hinvariant : E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n)
    (hstrictSafe : (E.getLatestConfirmedTraceAt cfg ext v n).result ≠
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved →
      E.SafeFrom cfg ext (E.getLatestConfirmedTraceAt cfg ext v n).result (n + 1))
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    ∃ e, Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result e) := by
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hquery : query.store = E.store cfg ext v (n + 1) := E.fcrStep_store cfg ext v n
  have hinput : trace.afterObserved ∈ query.store.block_roots :=
    E.getLatestConfirmedTraceAt_input_known cfg ext B hT hanchor hboundary
      hinvariant.confirmed_known
  have hG := E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary hv hH
  have hprovisos : getLatestSelectorGuard cfg query trace.afterObserved →
      FCRPredictionSupportAt cfg ext E v (n + 1) query trace.afterObserved := by
    intro hguard
    have hresult : trace.result = find_latest_confirmed_descendant cfg ext query
        trace.afterObserved := trace.selected_facts cfg ext hguard
    constructor
    · intro a c hedge
      have hstrict := CurrentTargetSelectedEdge.result_ne_input cfg ext
        hG.parent hG.walk hG.head_known hinput hedge
      have hne : trace.result ≠ trace.afterObserved := by rwa [hresult]
      have hsafe := hstrictSafe hne
      have hselector : StrictSelectorAdvanceAt cfg ext query trace :=
        ⟨hresult, hguard, hguard, hne⟩
      have hfacts := E.actualCall_strictSelectedResultMechanicalFacts cfg ext hT
        hC.synchrony hC.static_validators hC.byzantine_bound hA.domain
        hv hH hinput hselector
      have hstart : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
        E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hH hcall
      let cutoff := compute_start_slot_at_epoch cfg ((get_current_target cfg query.store).epoch + 1)
      have hbefore := E.currentResult_supportBefore_of_endpoint_induction cfg ext hA B hT
        hanchor hboundary hv hH query hquery trace.afterObserved hinput hstrict
        (by simpa only [query, trace, ← hresult] using hcurrent)
        (cutoff := cutoff)
        (by
          intro w hw k hstartK hkH
          rw [← hresult]
          have hqk : n + 1 ≤ k := by simpa only [hstart] using hstartK
          exact E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
            v hv (n + 1) query hquery trace.result hH
            (by simpa only [query, E.fcrStep_store] using hfacts.result_known)
            (by simpa only [query, E.fcrStep_store] using hfacts.parent_known)
            hfacts.confirmed w hw k (E.slot_at_mono cfg hqk) hkH)
        (by
          intro w hw k hstartK _ hkH
          rw [← hresult]
          exact hsafe w hw k (by simpa only [hstart] using hstartK) hkH)
      exact E.support_of_before_epoch_end cfg (Nat.le_refl _) hbefore
    · intro r hr _ hnotCurrent _
      have heq : r = trace.result := hr.symm.trans hresult.symm
      exact False.elim (hnotCurrent (by simpa only [heq] using hcurrent))
  exact E.getLatestConfirmedTraceAt_currentLineage_step cfg ext B hT
    hC.phase0_source hC.phase0_boundary_source hanchor hboundary hv hH
    hinvariant.confirmed_known hcurrent hprovisos
    (E.completedPrefix_acceptedTargetGateProducerAt cfg ext B hT hC hfit
      hanchor hboundary hv hcall hH) hinvariant.current_lineage

end Execution

end FastConfirmation.Spec

end
