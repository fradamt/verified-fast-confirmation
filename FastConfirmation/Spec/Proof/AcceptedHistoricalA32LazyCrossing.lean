import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Step
import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OriginCall

/-!
# The lazy crossing constructor

`docs/crossing-call-support-residue.md` §2.1 established that the historical
A3.2 lineage consumed at an actual call's own second is the lineage that call
just built, and that at a crossing the payload's origin call *is* that call.
Building the payload's positive certification content there is therefore
same-step circular: the only proviso-free route to `HonestVotesSupportTarget`
needs the call's own safety, which is what the fold is proving at that step.

This module replaces that construction by the lazy one.  At the crossing call
it records only the **origin-call data**
(`Execution.AcceptedHistoricalA32OriginCallAt`) — which validator called, at
which second, on which root, with which gate boolean — and packages the
certification and support obligations as the closures
`Execution.LazyCertAt` / `Execution.LazySupportAt`, whose antecedents are the
threaded fold outputs.  Nothing about the fold at the crossing second is
proved here.

The strong eager constructor
`Execution.selectedCurrentCrossingLineage_of_fixedSourceProducer`, which took
an `Execution.SelectedHelperProvisosAt` premise, has been deleted together
with that record; neither trunk has an eager crossing constructor any more.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- **The origin-call record of an actual crossing call.**

Every field is discharged from the call's ordinary executable geometry: the
selector's strict advance gives knownness, one-confirmation and the strict
write-back, the trace's write-back equation gives `origin_writeback`, the
crossing edge gives the executable gate boolean, and the current-epoch
head-descent geometry gives `target_eq`.  No proviso, quorum, certificate or
safety fact is used. -/
theorem acceptedHistoricalA32OriginCallAt_of_crossing
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store)
    (hparent : ParentSlotLt (E.fcrStep cfg ext v n).store)
    (hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r)
    (hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hcurrentWalk : WalkKnown (E.fcrStep cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store))
      (get_head cfg (E.fcrStep cfg ext v n).store).root)
    (hinputKnown : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved a c) :
    E.AcceptedHistoricalA32OriginCallAt cfg ext v n
        (E.getLatestConfirmedTraceAt cfg ext v n).result
        (B.state.C (E.getLatestConfirmedTraceAt cfg ext v n).result
          (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)) ∧
      get_current_target cfg (E.fcrStep cfg ext v n).store =
        B.state.C (E.getLatestConfirmedTraceAt cfg ext v n).result
          (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) := by
  classical
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hquery : query.store = E.store cfg ext v (n + 1) :=
    E.fcrStep_store cfg ext v n
  have hresult : trace.result =
      find_latest_confirmed_descendant cfg ext query trace.afterObserved :=
    trace.selected_facts cfg ext hselector
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    CurrentTargetAcceptedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    strictSelectedResult_below_head cfg ext hparent hwalk hhead
      hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  -- the current target is the selected result's own epoch checkpoint
  have htargetCheckpoint :=
    current_target_eq_checkpoint_of_current_epoch_ancestor cfg hparent
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
  -- one-confirmation and parent knownness of the strict selector result
  have hsel := E.find_latest_confirmed_descendant_selected_minimal cfg ext hA
    v hv (n + 1) hHn1 query hquery trace.afterObserved hinputKnown
  have hfacts : is_one_confirmed cfg ext query.store
        (get_current_balance_source query) trace.result = true ∧
      (query.store.blocks trace.result).parent_root ∈
        query.store.block_roots := by
    rcases hsel with hfixed | ⟨hconf, _hknown, hparentKnown⟩
    · exact absurd hfixed hstrict
    · exact ⟨by rw [hresult]; exact hconf, by rw [hresult]; exact hparentKnown⟩
  have hwrite : E.confirmed cfg ext v (n + 1) = trace.result :=
    (E.confirmed_succ_of_advance cfg ext v n hcall).trans trace.result_eq.symm
  refine ⟨?_, htarget⟩
  exact {
    node_honest := hv
    second_horizon := hHn1
    is_call := hcall
    origin_known := hresultKnown
    origin_parent_known := hfacts.2
    origin_confirmed := hfacts.1
    origin_current := hresultCurrent
    head_descends := hbelowResult
    origin_writeback := hwrite
    origin_strict := by
      intro hbad
      exact hstrict (hresult ▸ hbad)
    gate := hedge.current_target_gate cfg ext
    target_eq := htarget }

/-- **The lazy crossing lineage.**  Same executable geometry as the deleted
eager `selectedCurrentCrossingLineage_of_fixedSourceProducer`, but the
payload's two obligations are the closures of
`docs/crossing-call-support-residue.md` §4.3 instead of the eagerly realized
certificate and quorum.

Consequently it consumes **no** helper-support proviso. -/
noncomputable def selectedCurrentCrossingLazyLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store)
    (hparent : ParentSlotLt (E.fcrStep cfg ext v n).store)
    (hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r)
    (hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hcurrentWalk : WalkKnown (E.fcrStep cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store))
      (get_head cfg (E.fcrStep cfg ext v n).store).root)
    (hinputKnown : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved a c)
    (hproducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
        cfg ext B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).result) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result
      (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
      (E.LazyCertAt cfg ext B (n + 1))
      (E.LazySupportAt cfg ext B v (n + 1)) := by
  obtain ⟨horiginCall, _htarget⟩ :=
    E.acceptedHistoricalA32OriginCallAt_of_crossing cfg ext B hA hv hHn1
      hcall hstore hparent hwalk hhead hcurrentWalk hinputKnown hselector
      hresultCurrent hedge
  have hanchorLe : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary
      v (n + 1)
  have hpayload :=
    AcceptedHistoricalA32GatePayloadCoreAt.of_causalKnown cfg ext B hstore
      horiginCall.origin_known hresultCurrent hanchorLe
      (Cert := E.LazyCertAt cfg ext B (n + 1))
      (Supp := E.LazySupportAt cfg ext B v (n + 1))
      (horiginCall.lazyCert cfg ext E hA B hanchor hboundary
        (Nat.lt_succ_self n) hproducer)
      (horiginCall.lazySupport cfg ext E hA B hanchor hboundary hresultCurrent
        (Nat.le_refl (n + 1)) hproducer)
  exact AcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload

end Execution

end FastConfirmation.Spec
