import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Step
import FastConfirmation.Spec.Proof.WeakObserverDomain
import FastConfirmation.Spec.Proof.WeakFCRCallContracts

/-!
# Spec / Proof / WeakHistoricalA32Geometry

The observer-side twin of the historical-A3.2 stack's **single honesty hub**.

`Execution.HistoricalA32QueryGeometryAt` is stated over a bare
`query : FastConfirmationStore Root` with zero honesty, so the weak
development targets exactly the strong structure.  Its only producer,
`Execution.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory`
(`AcceptedHistoricalA32Step.lean`), is where the query node's honesty enters,
and it enters exactly twice:

* `storeDomainK_of_acceptedGlobalTrajectory … v hv (n + 1)` — replaced by
  `Execution.observerStoreDomainK` (`WeakObserverDomain.lean`);
* `headRootKnown_of_acceptedGlobalTrajectory … hv (n + 1)` — replaced by
  `Execution.head_root_known_at_observer`.

Everything else in that proof (`exact_core`, `causal`, `current_walk`,
`slot_upper`, `strict_non_genesis`) is already proved for an arbitrary node.
Since every honesty use in the whole A3.2 step layer routes through this one
producer — its six consumers in `AcceptedHistoricalA32Step.lean` /
`AcceptedHistoricalA32Induction.lean` / `AcceptedHistoricalA32OneStep.lean`
are the only `hv` binders there — this module is the hinge on which the
observer-side port of that layer turns.

The twin below is stated over an arbitrary `query` with
`hquery : query.store = E.store cfg ext obs (n + 1)` rather than over a fixed
evaluator, because the strong proof reads the query only through
`E.fcrStep_store`.  The weak evaluator's own instance is the corollary
`Weak.weakFcrStep_historicalA32QueryGeometryAt`, via
`Execution.weakFcrStep_store`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- Observer-side twin of
`Execution.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory`.

The honest-node binder `hv` is replaced by `E.ObserverCoherence cfg ext obs`,
which is all the two substituted domain hubs need; the query is any store
snapshot re-seated on the observer's own second-`(n + 1)` store. -/
theorem historicalA32QueryGeometryAt_at_observer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext obs (n + 1)) :
    E.HistoricalA32QueryGeometryAt cfg ext query := by
  let ast : BeaconState Root := Classical.choose hT.genesis
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hslot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hanchorParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT
  have hcausal : E.CausalStore cfg ext query.store := by
    rw [hquery]
    exact E.store_causal cfg ext obs (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [hquery] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [hquery] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    rw [hquery]
    exact E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) :=
    E.trustedAnchor_epoch_le_currentEpoch_of_trajectory cfg ext hT
      hanchor hboundary obs (n + 1)
  have hcurrentWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root := by
    have hheadStore : (get_head cfg query.store).root ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [hquery] using hhead
    have hboundaryWalk :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary obs (n + 1) hanchorEpochLeCurrent hheadStore
    simpa only [hquery] using hboundaryWalk
  refine {
    exact_core := hcore
    causal := hcausal
    parent := hparent
    walk := hwalk
    head_known := hhead
    current_walk := hcurrentWalk
    slot_upper := ?_
    strict_non_genesis := ?_
  }
  · intro r hr
    have hrStore : r ∈ (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [hquery] using hr
    simpa only [hquery] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hslot⟩ obs (n + 1) r hrStore
  · intro base hbase r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [hquery] using hr
    have hanchorBlock : query.store.blocks ablk.root = ablk.message := by
      rw [hquery]
      exact E.store_anchor_block cfg ext hT.wellFormed hgen obs (n + 1)
        hanchorKnown
    have hbaseKnown : base ∈ (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [hquery] using hbase
    have hanchorLeBase : ablk.message.slot ≤
        (query.store.blocks base).slot := by
      rw [hquery]
      exact E.store_anchor_min_slot cfg ext hT.wellFormed
        hT.externals_coherence hgen hslot hanchorParent obs (n + 1)
          base hbaseKnown
    have hbad : (query.store.blocks base).slot < ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeBase) hbad

/-- The weak evaluator's own instance of the geometry hub. -/
theorem weakFcrStep_historicalA32QueryGeometryAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.HistoricalA32QueryGeometryAt cfg ext (E.weakFcrStep cfg ext obs n) :=
  Weak.historicalA32QueryGeometryAt_at_observer cfg ext B hT hanchor hboundary
    hcoh hHn1 (E.weakFcrStep_store cfg ext obs n)

end Weak

end FastConfirmation.Spec
