import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OneStep
import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OriginCall

/-!
# Strong induction for the accepted historical A3.2 payload

This module writes the exact one-call transformer back to the executable
`confirmed` trajectory.  It retains two invariants simultaneously:

* the cached confirmed root is known in the node's current store; and
* whenever that root belongs to the store's current epoch, it has a nonempty
  accepted historical A3.2 lineage.

The call-site interface deliberately remains explicit.  Its helper provisos
are the normative provisos used only when the executable selector runs, while
its gate producer is the action/schedule bridge still to be instantiated at
each actual FCR call.  Neither field is replaced by a legacy selected-margin,
justification-interface, history, canonicity, or safety assumption.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- The two facts retained by the write-back induction at one execution
second.  Historical payload is required only in the current-epoch case. -/
structure AcceptedHistoricalA32CurrentLineageAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (n : ℕ) : Prop where
  confirmed_known : E.confirmed cfg ext v n ∈
    (E.store cfg ext v n).block_roots
  current_lineage :
    get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
        get_current_store_epoch cfg (E.store cfg ext v n) →
      ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
        cfg ext B (E.confirmed cfg ext v n) e
        (E.LazyCertAt cfg ext B n) (E.LazySupportAt cfg ext B v n))

/-- The exact non-operational interface consumed at one actual FCR call.

The interface records no helper-support proviso: the record which stated the
spec's normative provisos at an actual selector call
(`SelectedHelperProvisosAt`) has been deleted.  The gate
producer is intentionally conditional on the executable target gate and
matching target-support proviso; concrete global/scheduled action evidence can
therefore construct it without putting a quorum or A3.2 conclusion in this
interface. -/
structure AcceptedHistoricalA32CallInterfaceAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (n : ℕ) : Prop where
  target_gate_producer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)

/-- Call interfaces for every honest, in-horizon invocation.  The
`IsFCRCallAt` argument ensures no interface is demanded between slot
advances. -/
def AcceptedHistoricalA32CallInterfaces
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ,
    E.IsFCRCallAt cfg ext v n → E.WithinHorizon cfg (n + 1) →
      E.AcceptedHistoricalA32CallInterfaceAt cfg ext B v n

/-! ## Exact evaluator knownness -/

/-- The exact phased evaluator returns a known root whenever the preceding
cached root is known.  Finalized and observed inputs use their accepted reset
realizations; a selected result uses the ordinary known-descendant theorem.
This proof has no justification-interface or selected-margin premise. -/
theorem getLatestConfirmedTraceAt_result_known
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots) :
    (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
  let query := E.fcrStep cfg ext v n
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
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    get_checkpoint_for_block cfg E.genesis_store anchor.root
        (get_block_epoch cfg E.genesis_store anchor.root) = anchor := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis
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
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) :
    E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v 0 := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
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
    have hpayload := AcceptedHistoricalA32GatePayloadCoreAt.of_anchor
      cfg ext B hat horiginEpoch
        (hcheckpointStore.trans hcheckpointAnchor)
        (Cert := E.LazyCertAt cfg ext B 0)
        (Supp := E.LazySupportAt cfg ext B v 0)
        (E.lazyCertAt_anchor cfg ext)
        (fun _ _ h => E.lazySupportAt_anchor cfg ext h)
    refine ⟨e, ⟨?_⟩⟩
    simpa only [hconfirmedAnchor] using
      (AcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload)

/-! ## Write-back induction -/

/-- One validator's complete bounded trajectory.  At actual calls the exact
trace transformer is used; between calls, block agreement and the unchanged
slot transport the preceding lineage. -/
noncomputable def acceptedHistoricalA32CurrentLineageAt_all
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (hcalls : ∀ n : ℕ, E.IsFCRCallAt cfg ext v n →
      E.WithinHorizon cfg (n + 1) →
        E.AcceptedHistoricalA32CallInterfaceAt cfg ext B v n) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n := by
  intro n
  induction n with
  | zero =>
      intro _hH0
      exact E.acceptedHistoricalA32CurrentLineageAt_zero
        cfg ext B hT hanchor hboundary v
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hprevious := ih hHn
      have hknownN1Prev : E.confirmed cfg ext v n ∈
          (E.store cfg ext v (n + 1)).block_roots :=
        (E.store_storeLE cfg ext v (Nat.le_succ n)).1
          hprevious.confirmed_known
      by_cases hadv : E.IsFCRCallAt cfg ext v n
      · let trace := E.getLatestConfirmedTraceAt cfg ext v n
        have hcall := hcalls n hadv hHn1
        have htraceKnown := E.getLatestConfirmedTraceAt_result_known
          cfg ext B hT hanchor hboundary hv hHn1
            hprevious.confirmed_known
        have hconfirmedOut : E.confirmed cfg ext v (n + 1) =
            trace.result := by
          exact (E.confirmed_succ_of_advance cfg ext v n hadv).trans
            trace.result_eq.symm
        refine {
          confirmed_known := ?_
          current_lineage := ?_
        }
        · rw [hconfirmedOut]
          simpa only [trace, E.fcrStep_store] using htraceKnown
        · intro hcurrentN1
          have htraceCurrent : get_block_epoch cfg
                (E.fcrStep cfg ext v n).store trace.result =
              get_current_store_epoch cfg
                (E.fcrStep cfg ext v n).store := by
            rw [hconfirmedOut] at hcurrentN1
            simpa only [trace, E.fcrStep_store] using hcurrentN1
          obtain ⟨e, hlineage⟩ :=
            E.getLatestConfirmedTraceAt_currentLineage_step_lazy cfg ext B hT
              hA hphase hboundaryPhase hanchor hboundary hv hHn1 hadv
              hprevious.confirmed_known htraceCurrent
              hcall.target_gate_producer
              (fun hcur =>
                (hprevious.current_lineage hcur).imp (fun _ h =>
                  h.map (E.acceptedHistoricalA32LazyLineage_mono cfg ext
                    (Nat.le_succ n))))
          refine ⟨e, ?_⟩
          simpa only [trace, hconfirmedOut] using hlineage
      · have hconfirmedOut : E.confirmed cfg ext v (n + 1) =
            E.confirmed cfg ext v n :=
          E.confirmed_succ_of_no_advance cfg ext v n hadv
        have hblockAgree :
            (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
              (E.store cfg ext v (n + 1)).blocks
                (E.confirmed cfg ext v n) :=
          hT.wellFormed.blocks_agree
            (E.blockProvenance cfg ext v n)
            (E.blockProvenance cfg ext v (n + 1))
            hprevious.confirmed_known hknownN1Prev
        have hslotMono : get_current_slot cfg (E.store cfg ext v n) ≤
            get_current_slot cfg (E.store cfg ext v (n + 1)) := by
          simpa only [E.store_current_slot] using
            E.slot_at_mono cfg (Nat.le_succ n)
        have hslotEq : get_current_slot cfg (E.store cfg ext v n) =
            get_current_slot cfg (E.store cfg ext v (n + 1)) :=
          Nat.le_antisymm hslotMono (Nat.le_of_not_gt hadv)
        have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
              (E.confirmed cfg ext v n) =
            get_block_epoch cfg (E.store cfg ext v (n + 1))
              (E.confirmed cfg ext v n) := by
          simp only [get_block_epoch, hblockAgree]
        have hcurrentEpochEq :
            get_current_store_epoch cfg (E.store cfg ext v n) =
              get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
          simp only [get_current_store_epoch, hslotEq]
        refine {
          confirmed_known := ?_
          current_lineage := ?_
        }
        · rw [hconfirmedOut]
          exact hknownN1Prev
        · intro hcurrentN1
          have hcurrentN : get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) =
              get_current_store_epoch cfg (E.store cfg ext v n) := by
            rw [hblockEpochAgree, hcurrentEpochEq, ← hconfirmedOut]
            exact hcurrentN1
          obtain ⟨e, hlineage⟩ := hprevious.current_lineage hcurrentN
          refine ⟨e, ?_⟩
          simpa only [hconfirmedOut] using
            hlineage.map (E.acceptedHistoricalA32LazyLineage_mono cfg ext
              (Nat.le_succ n))

/-- Global bounded invariant for all honest validators. -/
theorem acceptedHistoricalA32CurrentLineage_invariant
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcalls : E.AcceptedHistoricalA32CallInterfaces cfg ext B) :
    ∀ v ∈ E.honest, ∀ n : ℕ, E.WithinHorizon cfg n →
      E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n := by
  intro v hv n hHn
  exact E.acceptedHistoricalA32CurrentLineageAt_all cfg ext B hT hA hphase
    hboundaryPhase hanchor hboundary hv
      (fun k hk hkH => hcalls v hv k hk hkH) n hHn

/-- Headline projection: every honest in-horizon cached confirmed root that
lies in its store's current epoch has a nonempty accepted historical A3.2
lineage, retaining the exact original target, source, and deadline payload. -/
theorem acceptedHistoricalA32CurrentLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcalls : E.AcceptedHistoricalA32CallInterfaces cfg ext B)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageCoreAt
      cfg ext B (E.confirmed cfg ext v n) e
      (E.LazyCertAt cfg ext B n) (E.LazySupportAt cfg ext B v n)) :=
  (E.acceptedHistoricalA32CurrentLineage_invariant cfg ext B hT hA hphase
    hboundaryPhase hanchor hboundary hcalls v hv n hHn).current_lineage
      hcurrent

end Execution


end FastConfirmation.Spec
