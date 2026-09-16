import FastConfirmation.Spec.Proof.WeakHistoricalA32OneStep
import FastConfirmation.Spec.Proof.WeakHistoricalA32CallSupplier
import FastConfirmation.Spec.Proof.WeakCandidateSourceHistory

/-!
# Spec / Proof / WeakHistoricalA32Induction

The observer-side twin of `AcceptedHistoricalA32Induction.lean`: the
historical A3.2 write-back induction, run over the **observer's own** weak
confirmed-root trajectory `E.weakConfirmed cfg ext obs ·` instead of over the
honest-quantified strong `E.confirmed`.

**Why a twin is needed.**  The strong induction is a statement about
`E.confirmed`, which is produced by the strong `Execution.fcr` handler; rule
delta 5 replaces that handler wholesale (`Weak.on_fast_confirmation`), so the
strong invariant says nothing about `E.weakConfirmed`.  Everything the
induction *retains*, on the other hand — knownness and a nonempty
`Execution.AcceptedHistoricalA32LineageAt` — is honesty-free and
evaluator-free and is reused verbatim.

**The substitutions.**

* `E.confirmed` / `E.fcrStep` / `E.getLatestConfirmedTraceAt` →
  `E.weakConfirmed` / `E.weakFcrStep` / `E.weakGetLatestConfirmedTraceAt`,
  with `E.fcrStep_store` / `E.fcrStep_confirmed_root` /
  `E.confirmed_zero` / `E.confirmed_succ_of_advance` /
  `E.confirmed_succ_of_no_advance` replaced by their `weak…` twins
  (`WeakFCRCallContracts.lean`, `WeakCandidateHistoryRecurrence.lean`).
* The one-call transformer
  `Execution.getLatestConfirmedTraceAt_currentLineage_step` →
  `Weak.getLatestConfirmedTraceAt_currentLineage_step`
  (`WeakHistoricalA32OneStep.lean`).
* The honesty hub
  `E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory … hv` →
  `Weak.weakFcrStep_historicalA32QueryGeometryAt … hcoh` with
  `hcoh : E.ObserverCoherence cfg ext obs`, and, in the knownness lemma, the
  observed-restart tag `E.actualObservedRestartInputAt` → the landed
  `Weak.weakFcrStep_observed_known` (rule delta 5's `banked_known`).
* `find_latest_confirmed_descendant_ge` →
  `weak_find_latest_confirmed_descendant_ge` (`WeakSelectorInversion.lean`).

**What is *not* restated.**

* `Execution.trustedAnchor_checkpointForBlock_of_trajectory`
  (`AcceptedHistoricalA32Induction.lean`) has no honesty binder and no
  evaluator: it is a genesis/boundary-alignment fact about
  `E.genesis_store` alone.  It is imported and applied verbatim in the
  genesis base below; no weak twin exists or is needed.
* No new assumption record is introduced.  The strong development's abstract
  `Execution.AcceptedHistoricalA32CallInterfaces` is replaced by the already
  landed `Weak.ObserverHistoricalA32CallAssumptions`
  (`WeakSelectedStrictEdgeFilterSupply.lean`): its `observer_helper_provisos`
  field supplies the normative provisos, and its unchanged strong `base`
  drives `Execution.observerCall_acceptedTargetGateProducerAt`
  (`WeakHistoricalA32CallSupplier.lean`) for the gate producer.  The
  per-call interface below is therefore *derived*, not assumed.
* The whole payload side — `Execution.AcceptedHistoricalA32LineageAt`,
  `Execution.AcceptedHistoricalA32GatePayloadAt` and its `.of_anchor`
  constructor, `Execution.AcceptedCurrentTargetA32GateRealizationProducerAt`
  — is honesty-free and evaluator-free and is reused verbatim.

**The quantifier change.**  The strong `…_invariant` and headline forms
quantify over `∀ v ∈ E.honest`.  On the weak side there is exactly one node
whose contract is available — the fixed observer `obs` carried by
`Weak.ObserverHistoricalA32CallAssumptions` — so both are restated at that
single `obs` rather than under an honest quantifier.

**One private clone.**
`Execution.AcceptedHistoricalA32LineageAt.payloadAtExecutionStore` and
`Execution.AcceptedBlockAt.executionRoot_for_actualOrientation`
(`AcceptedActualSelectedJustifiedOrientation.lean`) are both `private`, so
they cannot be applied from here even though they are node-generic and
honesty-free.  They are re-proved below as private helpers, exactly as the
strong development itself already keeps two copies of the `ExecutionRoot`
projection (`…_for_actualOrientation` and
`AcceptedHistoricalLineageFinalizedPlacement.executionRoot_mixed`).  Nothing
else in this module is cloned.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Retained facts and the derived per-call interface -/

/-- Weak twin of `Execution.AcceptedHistoricalA32CurrentLineageAt`: the two
facts retained by the write-back induction at one execution second of the
observer's weak trajectory.  Historical payload is required only in the
current-epoch case, exactly as in the strong record. -/
structure ObserverHistoricalA32CurrentLineageAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (obs : ValidatorIndex) (n : ℕ) : Prop where
  confirmed_known : E.weakConfirmed cfg ext obs n ∈
    (E.store cfg ext obs n).block_roots
  current_lineage :
    get_block_epoch cfg (E.store cfg ext obs n)
          (E.weakConfirmed cfg ext obs n) =
        get_current_store_epoch cfg (E.store cfg ext obs n) →
      ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt
        cfg ext B (E.weakConfirmed cfg ext obs n) e)

/-- Weak twin of `Execution.AcceptedHistoricalA32CallInterfaceAt`: the exact
non-operational interface consumed at one weak FCR call of the observer.

Unlike the strong record this one is never *assumed*: both fields are
discharged by `Weak.observerHistoricalA32CallInterfaceAt_of_callAssumptions`
from `Weak.ObserverHistoricalA32CallAssumptions`.  It is kept as a named
structure only so that the induction's call hypothesis reads the same way as
the strong one. -/
structure ObserverHistoricalA32CallInterfaceAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (obs : ValidatorIndex) (n : ℕ) : Prop where
  helper_provisos :
    getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved →
      Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1)
        (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
  target_gate_producer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)

variable {E : Execution Root}

/-- Every weak in-horizon call of the observer already has its complete
interface: the provisos are the observer-quantified normative field of
`Weak.ObserverHistoricalA32CallAssumptions`, and the gate producer is the
landed completed-scheduled-prefix producer at the observer's own call.

This is the promised replacement for a second assumption record — the
induction below consumes `hC` and nothing else new. -/
noncomputable def observerHistoricalA32CallInterfaceAt_of_callAssumptions
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    Weak.ObserverHistoricalA32CallInterfaceAt cfg ext E B obs n where
  helper_provisos := hC.observer_helper_provisos n hcall hHn1
  target_gate_producer :=
    Execution.observerCall_acceptedTargetGateProducerAt cfg ext B hT hC.base
      hfit hanchor hboundary hcoh hcall hHn1

/-! ## Exact weak evaluator knownness -/

/-- Weak twin of `Execution.getLatestConfirmedTraceAt_result_known`: the exact
phased weak evaluator returns a known root whenever the preceding cached weak
root is known.

The finalized input uses the (node-generic) accepted finalized reset
realization; the observed input uses `Weak.weakFcrStep_observed_known`
instead of the strong `E.actualObservedRestartInputAt … .root_known`, which
is what rule delta 5's banked-justification maintenance already supplies at
every second of the observer's weak trajectory; a selected result uses the
weak known-descendant theorem.  No justification-interface or
selected-margin premise appears. -/
theorem getLatestConfirmedTraceAt_result_known
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs n).block_roots) :
    (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hqueryConfirmedKnown : query.confirmed_root ∈
      query.store.block_roots := by
    have hknownN1 : E.weakConfirmed cfg ext obs n ∈
        (E.store cfg ext obs (n + 1)).block_roots :=
      (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
    simpa only [query, E.weakFcrStep_confirmed_root, E.weakFcrStep_store]
      using hknownN1
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    rcases trace.observed.branch_cases with
        ⟨hobsUnchanged, _hobsFalse⟩ | ⟨hobsRestart, _hobsTrue⟩
    · rcases trace.finalized.branch_cases with
          ⟨hcarried, _hfinalizedFalse⟩ | ⟨hreverted, _hfinalizedTrue⟩
      · rw [hobsUnchanged, hcarried]
        exact hqueryConfirmedKnown
      · have hrealized :=
          E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
            cfg ext B hT hanchor hboundary (w := obs) (n + 1)
        rw [hobsUnchanged, hreverted]
        simpa only [query, E.weakFcrStep_store] using hrealized.root_known
    · rw [hobsRestart]
      simpa only [query, E.weakFcrStep_store] using
        Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
  rcases trace.selector_cases cfg ext with
      ⟨hresultEq, _hselectorFalse⟩ | ⟨hresultEq, _hselectorTrue⟩
  · rw [hresultEq]
    exact hinputKnown
  · rw [hresultEq]
    exact (weak_find_latest_confirmed_descendant_ge cfg ext query
      hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown).2

/-! ## Trusted-anchor base -/

/-- Weak twin of `Execution.acceptedHistoricalA32CurrentLineageAt_zero`: the
genesis weak confirmed root initializes both knownness and the anchor
lineage.  The anchor disjunct is recorded directly; no quorum is fabricated.

The only substitution is `E.confirmed_zero` → `E.weakConfirmed_zero`; the
checkpoint identification is the reused, honesty-free
`Execution.trustedAnchor_checkpointForBlock_of_trajectory`. -/
noncomputable def observerHistoricalA32CurrentLineageAt_zero
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (obs : ValidatorIndex) :
    Weak.ObserverHistoricalA32CurrentLineageAt cfg ext E B obs 0 := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
  have hconfirmedAnchor : E.weakConfirmed cfg ext obs 0 = B.anchor.root := by
    rw [E.weakConfirmed_zero, hanchor]
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
  · change E.weakConfirmed cfg ext obs 0 ∈ E.genesis_store.block_roots
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
    have hpayload := Execution.AcceptedHistoricalA32GatePayloadAt.of_anchor
      cfg ext B hat horiginEpoch
        (hcheckpointStore.trans hcheckpointAnchor)
    refine ⟨e, ⟨?_⟩⟩
    simpa only [hconfirmedAnchor] using
      (Execution.AcceptedHistoricalA32LineageAt.refl cfg ext hpayload)

/-! ## Write-back induction -/

/-- Weak twin of `Execution.acceptedHistoricalA32CurrentLineageAt_all`: the
observer's complete bounded weak trajectory.  At actual weak calls the exact
weak trace transformer is used; between calls, block agreement and the
unchanged slot transport the preceding lineage — that second half is entirely
about `E.store`, which the two models share, so only the write-back equations
change (`E.confirmed_succ_of_*` → `E.weakConfirmed_succ_of_*`). -/
noncomputable def observerHistoricalA32CurrentLineageAt_all
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    (hcalls : ∀ n : ℕ, E.IsFCRCallAt cfg ext obs n →
      E.WithinHorizon cfg (n + 1) →
        Weak.ObserverHistoricalA32CallInterfaceAt cfg ext E B obs n) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      Weak.ObserverHistoricalA32CurrentLineageAt cfg ext E B obs n := by
  intro n
  induction n with
  | zero =>
      intro _hH0
      exact Weak.observerHistoricalA32CurrentLineageAt_zero cfg ext B hT
        hanchor hboundary obs
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hprevious := ih hHn
      have hknownN1Prev : E.weakConfirmed cfg ext obs n ∈
          (E.store cfg ext obs (n + 1)).block_roots :=
        (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
          hprevious.confirmed_known
      by_cases hadv : E.IsFCRCallAt cfg ext obs n
      · let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
        have hcall := hcalls n hadv hHn1
        have htraceKnown := Weak.getLatestConfirmedTraceAt_result_known
          cfg ext B hT hanchor hboundary hcoh hHn1
            hprevious.confirmed_known
        have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) =
            trace.result :=
          (E.weakConfirmed_succ_of_advance cfg ext obs n hadv).trans
            trace.result_eq.symm
        refine {
          confirmed_known := ?_
          current_lineage := ?_
        }
        · rw [hconfirmedOut]
          simpa only [trace, E.weakFcrStep_store] using htraceKnown
        · intro hcurrentN1
          have htraceCurrent : get_block_epoch cfg
                (E.weakFcrStep cfg ext obs n).store trace.result =
              get_current_store_epoch cfg
                (E.weakFcrStep cfg ext obs n).store := by
            rw [hconfirmedOut] at hcurrentN1
            simpa only [trace, E.weakFcrStep_store] using hcurrentN1
          obtain ⟨e, hlineage⟩ :=
            Weak.getLatestConfirmedTraceAt_currentLineage_step cfg ext B hT
              hphase hboundaryPhase hanchor hboundary hcoh hHn1
              hprevious.confirmed_known htraceCurrent
              hcall.helper_provisos hcall.target_gate_producer
              hprevious.current_lineage
          refine ⟨e, ?_⟩
          simpa only [trace, hconfirmedOut] using hlineage
      · have hconfirmedOut : E.weakConfirmed cfg ext obs (n + 1) =
            E.weakConfirmed cfg ext obs n :=
          E.weakConfirmed_succ_of_no_advance cfg ext obs n hadv
        have hblockAgree :
            (E.store cfg ext obs n).blocks (E.weakConfirmed cfg ext obs n) =
              (E.store cfg ext obs (n + 1)).blocks
                (E.weakConfirmed cfg ext obs n) :=
          hT.wellFormed.blocks_agree
            (E.blockProvenance cfg ext obs n)
            (E.blockProvenance cfg ext obs (n + 1))
            hprevious.confirmed_known hknownN1Prev
        have hslotMono : get_current_slot cfg (E.store cfg ext obs n) ≤
            get_current_slot cfg (E.store cfg ext obs (n + 1)) := by
          simpa only [E.store_current_slot] using
            E.slot_at_mono cfg (Nat.le_succ n)
        have hslotEq : get_current_slot cfg (E.store cfg ext obs n) =
            get_current_slot cfg (E.store cfg ext obs (n + 1)) :=
          Nat.le_antisymm hslotMono (Nat.le_of_not_gt hadv)
        have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext obs n)
              (E.weakConfirmed cfg ext obs n) =
            get_block_epoch cfg (E.store cfg ext obs (n + 1))
              (E.weakConfirmed cfg ext obs n) := by
          simp only [get_block_epoch, hblockAgree]
        have hcurrentEpochEq :
            get_current_store_epoch cfg (E.store cfg ext obs n) =
              get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
          simp only [get_current_store_epoch, hslotEq]
        refine {
          confirmed_known := ?_
          current_lineage := ?_
        }
        · rw [hconfirmedOut]
          exact hknownN1Prev
        · intro hcurrentN1
          have hcurrentN : get_block_epoch cfg (E.store cfg ext obs n)
                (E.weakConfirmed cfg ext obs n) =
              get_current_store_epoch cfg (E.store cfg ext obs n) := by
            rw [hblockEpochAgree, hcurrentEpochEq, ← hconfirmedOut]
            exact hcurrentN1
          obtain ⟨e, hlineage⟩ := hprevious.current_lineage hcurrentN
          refine ⟨e, ?_⟩
          simpa only [hconfirmedOut] using hlineage

/-- Weak twin of
`Execution.acceptedHistoricalA32CurrentLineage_invariant`, restated at the
single fixed observer carried by `Weak.ObserverHistoricalA32CallAssumptions`
(the strong form's `∀ v ∈ E.honest` quantifier has no weak counterpart: there
is exactly one node whose weak call contract is available).

No new assumption is taken: `hC` alone supplies both interface fields as well
as the two phase-0 coherences, through its unchanged strong `base`. -/
theorem observerHistoricalA32CurrentLineage_invariant
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      Weak.ObserverHistoricalA32CurrentLineageAt cfg ext E B obs n :=
  Weak.observerHistoricalA32CurrentLineageAt_all cfg ext B hT
    hC.base.phase0_source hC.base.phase0_boundary_source hanchor hboundary
    hcoh
    (fun _k hk hkH => Weak.observerHistoricalA32CallInterfaceAt_of_callAssumptions
      cfg ext B hT hC hfit hanchor hboundary hcoh hk hkH)

/-- Weak twin of `Execution.acceptedHistoricalA32CurrentLineage`: the headline
projection at the fixed observer.  Every in-horizon cached *weak* confirmed
root that lies in its store's current epoch has a nonempty accepted historical
A3.2 lineage, retaining the exact original target, source and deadline
payload. -/
theorem observerHistoricalA32CurrentLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn : E.WithinHorizon cfg n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext obs n)
        (E.weakConfirmed cfg ext obs n) =
      get_current_store_epoch cfg (E.store cfg ext obs n)) :
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt
      cfg ext B (E.weakConfirmed cfg ext obs n) e) :=
  (Weak.observerHistoricalA32CurrentLineage_invariant cfg ext B hT hC hfit
    hanchor hboundary hcoh n hHn).current_lineage hcurrent

/-! ## Residual target 1: the weak call's own current-epoch lineage -/

/-- Weak twin of
`Execution.acceptedHistoricalA32CurrentLineage_of_completedPrefixes`, stated
at the weak evaluator's *result* rather than at the cached root, which is the
shape `Weak.ObserverStrictCallFilterInputsAt.current_lineage` asks for.

Rather than routing through the `n + 1` write-back (which would force an
`E.weakConfirmed cfg ext obs (n + 1) = trace.result` rewrite), this applies
the one-call transformer directly to the induction's `n`-th retained facts;
the conclusion is therefore literally the residual field.

`hcall` is unavoidable and is the only extra binder: the normative provisos
of `Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos` and
the completed-prefix gate producer are both contracted at actual weak FCR
calls only. -/
theorem observerCall_currentLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e) := by
  intro hcurrent
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hprevious := Weak.observerHistoricalA32CurrentLineage_invariant
    cfg ext B hT hC hfit hanchor hboundary hcoh n hHn
  have hinterface := Weak.observerHistoricalA32CallInterfaceAt_of_callAssumptions
    cfg ext B hT hC hfit hanchor hboundary hcoh hcall hHn1
  exact Weak.getLatestConfirmedTraceAt_currentLineage_step cfg ext B hT
    hC.base.phase0_source hC.base.phase0_boundary_source hanchor hboundary
    hcoh hHn1 hprevious.confirmed_known hcurrent hinterface.helper_provisos
    hinterface.target_gate_producer hprevious.current_lineage

/-! ## Residual target 2: the epoch-start `carried` previous result -/

/-- Weak twin of
`Execution.StrictSelectorAdvanceAt.previousCarried_epochStartLineage`, in the
shape `Weak.ObserverStrictCallFilterInputsAt.previous_epochStart_carried_
lineage` asks for (same three antecedents, same order).

Two deliberate differences from the strong statement.  First, the strong
`hselector : StrictSelectorAdvanceAt` premise is *dropped*: the residual field
does not carry one, and none is needed.  Its only two uses were
`input_recent`, which on a `carried` input is exactly
`Weak.CarriedCandidateInputAt.confirmed_recent`, and the same-epoch
extension, which is needed only when the result actually moved — so the proof
splits on `trace.result = trace.afterObserved` and rebuilds
`Weak.StrictSelectorAdvanceAt` itself in the strict branch.  Second, the
strong `hdomain : SelectedMarginDomain` binder is gone, because
`Weak.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual`
already replaced it by observer coherence. -/
theorem observerCall_previousCarried_epochStartLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    Weak.CarriedCandidateInputAt cfg ext (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) →
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) = true →
    Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)) := by
  intro horigin hprevious hstart
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hinvariant := Weak.observerHistoricalA32CurrentLineage_invariant
    cfg ext B hT hC hfit hanchor hboundary hcoh n hHn
  have hstartStore : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext obs (n + 1))) = true := by
    simpa only [E.weakFcrStep_store] using hstart
  have hrecentConfirmed : get_block_epoch cfg
        (E.weakFcrStep cfg ext obs n).store (E.weakConfirmed cfg ext obs n) +
        1 ≥
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
    simpa only [E.weakFcrStep_confirmed_root] using
      horigin.confirmed_recent cfg ext
  have hcurrentN := Weak.previousConfirmed_current_of_boundary_recent cfg ext
    hT hcall hstartStore hinvariant.confirmed_known hrecentConfirmed
  obtain ⟨e, ⟨hlineageN⟩⟩ := hinvariant.current_lineage hcurrentN
  have hknownN1 : E.weakConfirmed cfg ext obs n ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
      hinvariant.confirmed_known
  have hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots := by
    rw [horigin.input_eq, E.weakFcrStep_confirmed_root, E.weakFcrStep_store]
    exact hknownN1
  have hqueryCausal : E.CausalStore cfg ext
      (E.weakFcrStep cfg ext obs n).store := by
    rw [E.weakFcrStep_store]
    exact E.store_causal cfg ext obs (n + 1)
  have hlineageQ : E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved e := by
    simpa only [horigin.input_eq, E.weakFcrStep_confirmed_root]
      using hlineageN
  have hinputBlockEq : (E.weakFcrStep cfg ext obs n).store.blocks
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
      hlineageQ.tip_block :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed hqueryCausal hinputKnown).mp hlineageQ.tip_at
  have hinputEpochE : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved = e := by
    simpa only [get_block_epoch, hinputBlockEq] using hlineageQ.tip_epoch
  have hinputPrevious : get_block_epoch cfg
          (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved + 1 =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
    have hepochSucc := E.actualCall_currentEpoch_succ_of_start
      cfg ext hT hcall hstartStore
    have hblockAgree : (E.store cfg ext obs n).blocks
          (E.weakConfirmed cfg ext obs n) =
        (E.store cfg ext obs (n + 1)).blocks
          (E.weakConfirmed cfg ext obs n) :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext obs n)
        (E.blockProvenance cfg ext obs (n + 1))
        hinvariant.confirmed_known hknownN1
    calc
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
            (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved +
            1 =
          get_block_epoch cfg (E.store cfg ext obs n)
            (E.weakConfirmed cfg ext obs n) + 1 := by
        simp only [horigin.input_eq, E.weakFcrStep_confirmed_root,
          E.weakFcrStep_store, get_block_epoch, hblockAgree]
      _ = get_current_store_epoch cfg (E.store cfg ext obs n) + 1 := by
        rw [hcurrentN]
      _ = get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) :=
        hepochSucc
      _ = get_current_store_epoch cfg
            (E.weakFcrStep cfg ext obs n).store := by
        rw [E.weakFcrStep_store]
  have hresultEpochE : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result = e := by
    have hresultInputEpoch : get_block_epoch cfg
          (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved :=
      Nat.add_right_cancel (hprevious.trans hinputPrevious.symm)
    exact hresultInputEpoch.trans hinputEpochE
  rw [hresultEpochE]
  by_cases hfix : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
  · rw [hfix]
    exact ⟨hlineageQ⟩
  · have hsel : Weak.StrictSelectorAdvanceAt cfg ext
        (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n) := by
      rcases (E.weakGetLatestConfirmedTraceAt cfg ext obs n).selector_cases
          cfg ext with ⟨hresultEq, _hfalse⟩ | ⟨hresultEq, hguard⟩
      · exact absurd hresultEq hfix
      · exact {
          result_eq := hresultEq
          guard_true := hguard
          input_recent := by
            simpa only [horigin.input_eq] using horigin.confirmed_recent cfg ext
          result_ne_input := hfix }
    exact ⟨Weak.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual
      cfg ext B hT hcoh hHn1 hsel hinputKnown hlineageQ hinputEpochE
      hresultEpochE⟩

/-! ## Residual target 3: the retained A3.2 payload producer at a weak call -/

/-- Weak twin of `Execution.AcceptedBlockAt.executionRoot_for_actualOrientation`.

The strong copy is `private`, so it cannot be applied from here; the strong
development already keeps a second identical private copy
(`AcceptedHistoricalLineageFinalizedPlacement.executionRoot_mixed`) for the
same reason.  Nothing in it is honesty-, evaluator- or model-dependent: it is
pure block provenance. -/
private theorem AcceptedBlockAt.executionRoot_for_observerOrientation
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Weak-side copy of the `private`
`Execution.AcceptedHistoricalA32LineageAt.payloadAtExecutionStore`: materialize
a retained lineage in an ordinary execution-boundary store.

This is accepted-root reflection plus the trusted-anchor boundary walk; it
uses no endpoint, no-crossing fact or safety conclusion, and it is quantified
over an arbitrary node `v`, so no substitution at all is needed — only the
`private` modifier on the strong copy forces the duplicate. -/
private theorem AcceptedHistoricalA32LineageAt.payloadAtObserverStore
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {tip : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B tip e)
    (htip : tip ∈ (E.store cfg ext v q).block_roots)
    (htipEpoch : get_block_epoch cfg (E.store cfg ext v q) tip = e) :
    Nonempty (E.AcceptedHistoricalA32GatePayloadAt cfg ext B tip e) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
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
    Weak.AcceptedBlockAt.executionRoot_for_observerOrientation cfg ext
      hlineage.payload.origin_at
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
    horigin htip' horiginEpoch htipEpoch' htipOrigin htipWalk⟩

/-- The payload core behind both producer spellings: at a weak strict-selector
call whose result is current, the observer-side write-back induction pins the
query's current target to the result's own checkpoint and materializes the
retained A3.2 payload there.

This is the observer twin of the body of
`Execution.completedPrefix_acceptedHistoricalA32PayloadProducerAt`, with
`E.storeDomainK_of_acceptedGlobalTrajectory … hv` /
`E.headRootKnown_of_acceptedGlobalTrajectory … hv` replaced by the geometry
hub `Weak.weakFcrStep_historicalA32QueryGeometryAt … hcoh`,
`strictSelectedResult_below_head` by `Weak.strictSelectedResult_below_head`,
and the strong write-back invariant by `Weak.observerCall_currentLineage`.
The producers' no-crossing antecedent is not used, in either model: the
lineage invariant is strictly stronger than it. -/
theorem observerCall_currentTargetHistoricalA32Payload
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : Nat} (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) :
    ∃ e : Epoch,
      get_current_target cfg (E.weakFcrStep cfg ext obs n).store =
          B.state.C (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e ∧
        Nonempty (E.AcceptedHistoricalA32GatePayloadAt cfg ext B
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e) := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  have hqueryStore : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  obtain ⟨e, ⟨hlineage⟩⟩ := Weak.observerCall_currentLineage cfg ext B hT hC
    hfit hanchor hboundary hcoh hcall hHn1 hcurrent
  have hresultKnown : trace.result ∈ query.store.block_roots :=
    Weak.getLatestConfirmedTraceAt_result_known cfg ext B hT hanchor hboundary
      hcoh hHn1 (Weak.observerHistoricalA32CurrentLineage_invariant cfg ext B
        hT hC hfit hanchor hboundary hcoh n
        (E.withinHorizon_mono cfg (Nat.le_succ n) hHn1)).confirmed_known
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    rw [hqueryStore]
    exact E.store_causal cfg ext obs (n + 1)
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal hresultKnown
  have htipBlock : hlineage.tip_block = query.store.blocks trace.result :=
    hlineage.tip_at.unique cfg ext E hT.wellFormed hresultAt
  have hresultEpoch : get_block_epoch cfg query.store trace.result = e := by
    simpa only [get_block_epoch, ← htipBlock] using hlineage.tip_epoch
  have hpayload : Nonempty
      (E.AcceptedHistoricalA32GatePayloadAt cfg ext B trace.result e) := by
    apply Weak.AcceptedHistoricalA32LineageAt.payloadAtObserverStore cfg ext B
      hT hC.base.phase0_source hanchor hboundary hlineage
    · simpa only [hqueryStore] using hresultKnown
    · simpa only [hqueryStore] using hresultEpoch
  have hstrictFind : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)
  have hbelow : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hselector.result_eq]
    exact Weak.strictSelectedResult_below_head cfg ext hG.parent hG.walk
      hG.head_known (by simpa only [query, trace] using hinput) hstrictFind
  have hboundaryResult : compute_start_slot_at_epoch cfg e ≤
      (query.store.blocks trace.result).slot := by
    rw [← hresultEpoch]
    exact start_slot_at_block_epoch_le cfg query.store trace.result
  have hwalkHead : WalkKnown query.store
      (compute_start_slot_at_epoch cfg e) (get_head cfg query.store).root := by
    have hanchorLe : B.anchor.epoch ≤ e := hlineage.payload.anchor_epoch_le
    have hw :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary obs (n + 1) hanchorLe
          (by simpa only [hqueryStore] using hG.head_known)
    simpa only [hqueryStore] using hw
  have hcheckpoint : get_checkpoint_block cfg query.store
        (get_head cfg query.store).root e =
      get_checkpoint_block cfg query.store trace.result e :=
    get_checkpoint_block_of_ancestor cfg hG.parent hbelow
      hboundaryResult hwalkHead
  have heCurrent : e = get_current_store_epoch cfg query.store :=
    hresultEpoch.symm.trans hcurrent
  refine ⟨e, ?_, hpayload⟩
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

/-- The observer-side twin of
`Execution.completedPrefix_acceptedHistoricalA32PayloadProducerAt`, in the
*strong* producer spelling.

This spelling is available because the producers' no-crossing antecedent is
never read.  The weak-edge spelling, `Weak.HistoricalA32PayloadProducerAt`
(`WeakSelectedJustifiedOrientation.lean`), is the one the weak call-site
classifier needs; it is derived from the same core in
`WeakHistoricalA32PayloadProducer.lean`, which is kept as a separate module so
that this induction does not depend on the pre-query SIR layer. -/
noncomputable def observerCall_acceptedHistoricalA32PayloadProducerAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : Nat} (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
  fun hcurrent _hnoCrossing =>
    Weak.observerCall_currentTargetHistoricalA32Payload cfg ext B hT hC hfit
      hanchor hboundary hcoh hcall hHn1 hinput hselector hcurrent

end Weak

end FastConfirmation.Spec
