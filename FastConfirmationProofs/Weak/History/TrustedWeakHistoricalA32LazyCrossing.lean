module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32LazyCrossing
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Step
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32OriginCall

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_observerHistoricalA32OriginCallAt_of_crossing
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hstore : E.CausalStore cfg ext (E.weakFcrStep cfg ext obs n).store)
    (hparent : ParentSlotLt (E.weakFcrStep cfg ext obs n).store)
    (hwalk : ∀ t ∈ (E.weakFcrStep cfg ext obs n).store.block_roots,
      ∀ r ∈ (E.weakFcrStep cfg ext obs n).store.block_roots,
        WalkKnown (E.weakFcrStep cfg ext obs n).store
          ((E.weakFcrStep cfg ext obs n).store.blocks t).slot r)
    (hhead : (get_head cfg (E.weakFcrStep cfg ext obs n).store).root ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hcurrentWalk : WalkKnown (E.weakFcrStep cfg ext obs n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store))
      (get_head cfg (E.weakFcrStep cfg ext obs n).store).root)
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {a c : Root}
    (hedge : Weak.CurrentTargetSelectedEdge cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c) :
    Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs n
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
        (B.state.C (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
          (get_current_store_epoch cfg
            (E.weakFcrStep cfg ext obs n).store)) ∧
      get_current_target cfg (E.weakFcrStep cfg ext obs n).store =
        B.state.C (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
          (get_current_store_epoch cfg
            (E.weakFcrStep cfg ext obs n).store) := by
  classical
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hquery : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hresult : trace.result =
      Weak.find_latest_confirmed_descendant cfg ext query trace.afterObserved :=
    trace.selected_facts cfg ext hselector
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    Weak.CurrentTargetSelectedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    Weak.strictSelectedResult_below_head cfg ext hparent hwalk hhead
      hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  have htargetCheckpoint :=
    Execution.current_target_eq_checkpoint_of_current_epoch_ancestor cfg hparent
      hbelowResult hresultCurrent hcurrentWalk
  have htarget : get_current_target cfg query.store =
      B.state.C trace.result (get_current_store_epoch cfg query.store) := by
    calc
      get_current_target cfg query.store =
          get_checkpoint_for_block cfg query.store trace.result
            (get_block_epoch cfg query.store trace.result) :=
        htargetCheckpoint
      _ = get_checkpoint_for_block cfg query.store trace.result
            (get_current_store_epoch cfg query.store) := by
        rw [hresultCurrent]
      _ = B.state.C trace.result
            (get_current_store_epoch cfg query.store) :=
        (B.coherence.checkpoint_of_known hstore trace.result hresultKnown
          (get_current_store_epoch cfg query.store)).symm
  -- one-confirmation and parent knownness of the strict weak selector result,
  -- honesty-free: the querying node's honesty binder of the strong twin is
  -- replaced by `ObserverCoherence.justified_root_known`
  have hsel := E.find_latest_confirmed_descendant_selected_minimal_weak cfg ext
    hA obs (n + 1) hHn1 (hcoh.justified_root_known (n + 1) hHn1) query hquery
    trace.afterObserved hinputKnown
  have hfacts :
      _root_.FastConfirmation.Spec.is_one_confirmed cfg ext query.store
          (get_current_balance_source query) trace.result = true ∧
      (query.store.blocks trace.result).parent_root ∈
        query.store.block_roots := by
    rcases hsel with hfixed | ⟨hconf, _hweakConf, _hknown, hparentKnown, _hev⟩
    · exact absurd hfixed hstrict
    · exact ⟨by rw [hresult]; exact hconf, by rw [hresult]; exact hparentKnown⟩
  have hwrite : E.weakConfirmed cfg ext obs (n + 1) = trace.result :=
    (E.weakConfirmed_succ_of_advance cfg ext obs n hcall).trans
      trace.result_eq.symm
  refine ⟨?_, htarget⟩
  exact {
    second_horizon := hHn1
    is_call := hcall
    origin_known := hresultKnown
    origin_parent_known := hfacts.2
    origin_confirmed := hfacts.1
    origin_current := hresultCurrent
    head_descends := hbelowResult
    origin_writeback := hwrite
    gate := will_current_target_be_justified_of_weak cfg ext query.store
      (Weak.CurrentTargetSelectedEdge.current_target_gate cfg ext hedge)
    target_eq := htarget }

/-- **The lazy weak crossing lineage.**

Same executable geometry as the (now deleted) eager weak crossing
constructor, but the payload's two obligations are the closures
`Weak.TrustedLazyCertAt` / `Weak.TrustedLazySupportAt` instead of the eagerly realized
certificate and quorum.  It consumes **no** normative proviso — it is the
only weak crossing builder left. -/
noncomputable def trusted_selectedCurrentCrossingLazyLineage
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hstore : E.CausalStore cfg ext (E.weakFcrStep cfg ext obs n).store)
    (hparent : ParentSlotLt (E.weakFcrStep cfg ext obs n).store)
    (hwalk : ∀ t ∈ (E.weakFcrStep cfg ext obs n).store.block_roots,
      ∀ r ∈ (E.weakFcrStep cfg ext obs n).store.block_roots,
        WalkKnown (E.weakFcrStep cfg ext obs n).store
          ((E.weakFcrStep cfg ext obs n).store.blocks t).slot r)
    (hhead : (get_head cfg (E.weakFcrStep cfg ext obs n).store).root ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hcurrentWalk : WalkKnown (E.weakFcrStep cfg ext obs n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store))
      (get_head cfg (E.weakFcrStep cfg ext obs n).store).root)
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {a c : Root}
    (hedge : Weak.CurrentTargetSelectedEdge cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result) :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
      (Weak.TrustedLazyCertAt cfg ext E B obs (n + 1))
      (Weak.TrustedLazySupportAt cfg ext E B obs (n + 1)) := by
  obtain ⟨horiginCall, _htarget⟩ :=
    Weak.trusted_observerHistoricalA32OriginCallAt_of_crossing cfg ext B hA hcoh hHn1
      hcall hstore hparent hwalk hhead hcurrentWalk hinputKnown hselector
      hresultCurrent hedge
  have hanchorLe : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
    rw [E.weakFcrStep_store]
    exact E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary
      obs (n + 1)
  have hpayload :=
    Execution.TrustedAcceptedHistoricalA32GatePayloadCoreAt.of_causalKnown cfg ext B
      hstore horiginCall.origin_known hresultCurrent hanchorLe
      (Cert := Weak.TrustedLazyCertAt cfg ext E B obs (n + 1))
      (Supp := Weak.TrustedLazySupportAt cfg ext E B obs (n + 1))
      (horiginCall.trusted_lazyCert cfg ext B hT hA hanchor hboundary hcoh
        (Nat.lt_succ_self n) hproducer)
      (horiginCall.trusted_lazySupport cfg ext B hT hA hanchor hboundary hcoh
        hresultCurrent (Nat.le_refl (n + 1)) hproducer)
  exact Execution.TrustedAcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload

end Weak
end FastConfirmation.Spec
end
