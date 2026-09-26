module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionCall

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Initial historical A3.2 lineage and call interface

This module defines the initial knownness and lineage facts and the gate-only
call interface. The joint call/history induction is in ConfirmedCacheSafety.
It derives support after strict-result safety, without a helper-support field.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

/-- The two facts retained by the write-back induction at one execution
second.  Historical payload is required only in the current-epoch case. -/
structure AcceptedHistoricalA32CurrentLineageAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (v : ValidatorIndex) (n : ℕ) : Prop where
  confirmed_known : E.confirmed cfg ext v n ∈
    (E.store cfg ext v n).block_roots
  current_lineage :
    get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
        get_current_store_epoch cfg (E.store cfg ext v n) →
      ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt
        cfg ext B (E.confirmed cfg ext v n) e)

/-- The exact non-operational interface consumed at one actual FCR call.

The producer is conditional on the executable gate and vote support. It
stores neither an unconditional quorum nor prediction support. The joint
induction supplies the latter only after it proves the strict result safe.
-/
structure AcceptedHistoricalA32CallInterfaceAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (v : ValidatorIndex) (n : ℕ) : Prop where
  target_gate_producer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n)

/-- Call interfaces for every honest, in-horizon invocation.  The
`IsScheduledFCRCallAt` argument ensures no interface is demanded between slot
advances. -/
def AcceptedHistoricalA32CallInterfaces
    (B : ScheduledFFGInterpretation cfg ext E) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ,
    E.IsScheduledFCRCallAt cfg ext v n → E.WithinHorizon cfg (n + 1) →
      E.AcceptedHistoricalA32CallInterfaceAt cfg ext B v n

/-! ## Exact evaluator knownness -/

/-- The exact phased evaluator returns a known root whenever the preceding
cached root is known.  Finalized and observed inputs use their accepted reset
realizations; a selected result uses the ordinary known-descendant theorem.
This proof has no justification-interface or selected-margin premise. -/
theorem getLatestConfirmedTraceAt_result_known
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots) :
    (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hG := E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary hv hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hqueryConfirmedKnown : query.confirmed_root ∈
      query.store.block_roots := by
    have hknownN1 : E.confirmed cfg ext v n ∈
        (E.store cfg ext v (n + 1)).block_roots :=
      (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
    simpa only [query, E.fcrStep_confirmed_root, E.fcrStep_store] using
      hknownN1
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    rcases trace.observed.branch_cases with
        ⟨hobsUnchanged, _hobsFalse⟩ | ⟨_hobsRestart, hobsTrue⟩
    · rcases trace.finalized.branch_cases with
          ⟨hcarried, _hfinalizedFalse⟩ | ⟨hreverted, _hfinalizedTrue⟩
      · rw [hobsUnchanged, hcarried]
        exact hqueryConfirmedKnown
      · have hrealized :=
          E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
            cfg ext B hT hanchor hboundary (w := v) (n + 1)
        rw [hobsUnchanged, hreverted]
        simpa only [query, E.fcrStep_store] using hrealized.root_known
    · have htag := E.actualObservedRestartInputAt cfg ext B hT hanchor
        hboundary v n trace (by simpa only [query] using hobsTrue)
      rw [htag.afterObserved_eq]
      exact htag.root_known
  rcases trace.selector.branch_cases with
      ⟨hresultEq, _hselectorFalse⟩ | ⟨hresultEq, _hselectorTrue⟩
  · rw [hresultEq]
    exact hinputKnown
  · rw [hresultEq]
    exact (find_latest_confirmed_descendant_ge cfg ext query
      hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown).2

/-! ## Trusted-anchor base -/

/-- Boundary alignment makes the accepted trusted anchor its own block
checkpoint, using only the scheduled trajectory's genesis facts. -/
theorem trustedAnchor_checkpointForBlock_of_trajectory
    (hT : E.ScheduledExecutionPremises cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := anchor)) :
    get_checkpoint_for_block cfg E.genesis_store anchor.root
        (get_block_epoch cfg E.genesis_store anchor.root) = anchor := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by
    have h := congrArg Checkpoint.root hanchor
    rw [hgen] at h
    simpa only [get_forkchoice_store] using h
  have hepoch : get_block_epoch cfg E.genesis_store anchor.root =
      anchor.epoch := by
    rw [hgen, hroot]
    have h := congrArg Checkpoint.epoch hanchor
    rw [hgen] at h
    simp only [get_block_epoch, get_forkchoice_store,
      Function.update_self, get_current_epoch, hslot] at h ⊢
    exact h.symm
  have hslotEq := E.trustedAnchor_slot_eq_start_of_trajectory cfg ext hT
    hanchor hboundary
  apply checkpoint_eq_of_epoch_root_eq
  · simpa only [get_checkpoint_for_block] using hepoch
  · simp only [get_checkpoint_for_block, get_checkpoint_block]
    rw [hepoch, ← hslotEq, get_ancestor_stop (Nat.le_refl _)]

/-- The genesis confirmed root initializes both knownness and the anchor
lineage.  The anchor disjunct is recorded directly; no quorum is fabricated. -/
noncomputable def acceptedHistoricalA32CurrentLineageAt_zero
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) :
    E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v 0 := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hconfirmedAnchor : E.confirmed cfg ext v 0 = B.anchor.root := by
    rw [E.confirmed_zero, hanchor]
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
  · change E.confirmed cfg ext v 0 ∈ E.genesis_store.block_roots
    simpa only [hconfirmedAnchor] using hknown
  · intro _hcurrent
    let e := get_block_epoch cfg E.genesis_store B.anchor.root
    have hat : E.BlockKnownInScheduledPrefix cfg ext B.anchor.root
        (E.genesis_store.blocks B.anchor.root) :=
      E.acceptedBlockAt_of_causal_known cfg ext (.genesis) hknown
    have horiginEpoch : compute_epoch_at_slot cfg
        (E.genesis_store.blocks B.anchor.root).slot = e := by
      rfl
    have hcheckpointStore : B.state.checkpoint_at_epoch B.anchor.root e =
        get_checkpoint_for_block cfg E.genesis_store B.anchor.root e :=
      B.coherence.checkpoint_of_known (.genesis) B.anchor.root hknown e
    have hcheckpointAnchor : get_checkpoint_for_block cfg E.genesis_store
        B.anchor.root e = B.anchor := by
      simpa only [e] using
        E.trustedAnchor_checkpointForBlock_of_trajectory cfg ext hT
          hanchor hboundary
    have hpayload := AcceptedHistoricalA32GatePayloadAt.of_anchor
      cfg ext B hat horiginEpoch
        (hcheckpointStore.trans hcheckpointAnchor)
    refine ⟨e, ⟨?_⟩⟩
    simpa only [hconfirmedAnchor] using
      (AcceptedHistoricalA32LineageAt.refl cfg ext hpayload)

end Execution

end FastConfirmation.Spec

end
