module
public import FastConfirmationProofs.FFG.SelectedSource.EndpointJustifiedOrientation
public import FastConfirmationProofs.FFG.SelectedSource.TrustedEndpointJustifiedOrientationProducer
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.Execution.History.TrustedCompletedPrefixCallsBase
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionCallInduction
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionCall
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

private theorem AcceptedBlockAt.executionRoot_for_actualOrientation
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Materialize a retained lineage in an ordinary execution-boundary store.
This is accepted-root reflection plus the trusted-anchor boundary walk; it
does not use an endpoint, no-crossing fact, or safety conclusion. -/
private theorem TrustedAcceptedHistoricalA32LineageCoreAt.payloadAtExecutionStore
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {tip : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      Cert Supp)
    (htip : tip ∈ (E.store cfg ext v q).block_roots)
    (htipEpoch : get_block_epoch cfg (E.store cfg ext v q) tip = e)
    (hsuppT : B.state.C tip e = B.state.C hlineage.origin e →
      B.state.GJ tip = B.state.GJ hlineage.origin →
      Supp hlineage.origin e → Supp tip e) :
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
    hlineage.payload.origin_at.executionRoot_for_actualOrientation cfg ext
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
    horigin htip' horiginEpoch htipEpoch' htipOrigin htipWalk hsuppT⟩

/-- The completed-prefix historical induction instantiates the retained
certificate producer on the exact strict selector result.

**This is where the no-crossing antecedent becomes load-bearing.**  Under the
lazy instantiation the lineage carried at write-back second `n + 1` would
require the threaded fold output *at second `n`*, which is what the enclosing
dispatcher is proving.  But `hnoCrossing` says this call created no payload at
all: it transported the input's.  So the transformer is run in its no-crossing
form from the invariant at second `n`, whose certification closure is
discharged by `hprior` — the strictly earlier fold output.  This is D1† of
`docs/crossing-call-support-residue.md` §2.1, now recorded in the types. -/
noncomputable def trusted_completedPrefix_acceptedHistoricalCertificateProducerAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n)) :
    E.HistoricalCurrentTargetCertificateProducerAt cfg ext B.anchor (n + 1)
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  intro hcurrent hnoCrossing
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hqueryStore : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hinvariantN :=
    E.trusted_acceptedHistoricalA32CurrentLineage_invariant_of_completedPrefixes
      cfg ext B hT hC hfit hdomain hanchor hboundary v hv n hHn
  obtain ⟨e, ⟨hlineage⟩⟩ :=
    E.trusted_getLatestConfirmedTraceAt_currentLineage_step_noCrossing cfg ext B hT
      hanchor hboundary hv hHn1 hinvariantN.confirmed_known hcurrent
      hnoCrossing (E.trusted_lazyCertAt_anchor cfg ext)
      (fun _ _ h => E.trusted_lazySupportAt_anchor cfg ext h)
      hinvariantN.current_lineage
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    simpa only [query, trace] using
      E.trusted_getLatestConfirmedTraceAt_result_known cfg ext B hT hanchor hboundary
        hv hHn1 hinvariantN.confirmed_known
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    rw [hqueryStore]
    exact E.store_causal cfg ext v (n + 1)
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal hresultKnown
  have htipBlock : hlineage.tip_block =
      query.store.blocks trace.result :=
    hlineage.tip_at.unique cfg ext E hT.wellFormed hresultAt
  have hresultEpoch : get_block_epoch cfg query.store trace.result = e := by
    simpa only [get_block_epoch, ← htipBlock] using hlineage.tip_epoch
  have hpayload : Nonempty
      (E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B trace.result e
        (E.TrustedLazyCertAt cfg ext B n) (E.TrustedLazySupportAt cfg ext B v n)) := by
    apply hlineage.payloadAtExecutionStore cfg ext B hT hC.phase0_source
      hanchor hboundary (v := v) (q := n + 1)
    · simpa only [hqueryStore] using hresultKnown
    · simpa only [hqueryStore] using hresultEpoch
    · intro hcheckpoint hsource hsupp
      exact E.trusted_lazySupportAt_transport cfg ext hcheckpoint hsource hsupp
  have hparent : ParentSlotLt query.store := by
    let hdomain := E.trusted_storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary
    simpa only [hqueryStore] using (hdomain v hv (n + 1) hHn1).1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    let hdomain := E.trusted_storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary
    simpa only [hqueryStore] using (hdomain v hv (n + 1) hHn1).2.1
  have hhead : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    rw [hqueryStore]
    exact E.trusted_headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hv (n + 1) hHn1
  have hstrictFind : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input
      (hselector.result_eq.trans hfixed)
  have hbelow : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hselector.result_eq]
    exact strictSelectedResult_below_head cfg ext hparent hwalk
      hhead (by simpa only [query, trace] using hinput) hstrictFind
  have hboundaryResult : compute_start_slot_at_epoch cfg e ≤
      (query.store.blocks trace.result).slot := by
    rw [← hresultEpoch]
    exact start_slot_at_block_epoch_le cfg query.store trace.result
  have hwalkHead : WalkKnown query.store
      (compute_start_slot_at_epoch cfg e) (get_head cfg query.store).root := by
    have hanchorLe : B.anchor.epoch ≤ e := hlineage.payload.anchor_epoch_le
    have hw :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v (n + 1) hanchorLe
          (by simpa only [hqueryStore] using hhead)
    simpa only [hqueryStore] using hw
  have hcheckpoint : get_checkpoint_block cfg query.store
        (get_head cfg query.store).root e =
      get_checkpoint_block cfg query.store trace.result e :=
    get_checkpoint_block_of_ancestor cfg hparent
      (by rw [is_ancestor_node_root] at hbelow; exact hbelow)
      hboundaryResult hwalkHead
  have heCurrent : e = get_current_store_epoch cfg query.store := by
    exact hresultEpoch.symm.trans hcurrent
  have htargetEq : get_current_target cfg query.store =
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
  -- the certification closure, discharged by the strictly earlier fold output
  rw [htargetEq]
  exact (Classical.choice hpayload).certified hprior

/-! ## Consumer-ready actual-call orientation -/

end Execution
end FastConfirmation.Spec
end
