module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32Step
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32OriginCall
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Geometry
public import FastConfirmationProofs.Checkpoints.TrustedSameEpochSegmentRealization
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionCarriedBranch
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetGateGeometry
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionEvaluatorReset

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_selectedCurrentNoCrossingAcceptedSegment
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (trace : Weak.LatestConfirmedCallTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state
      trace.afterObserved trace.result := by
  have hresult := trace.selected_facts cfg ext hselector
  have hinputEpochUpper : get_block_epoch cfg query.store
        trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpper
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    by_cases heq : get_block_epoch cfg query.store trace.afterObserved =
        get_current_store_epoch cfg query.store
    · exact Or.inl heq
    · right
      have hguard : get_block_epoch cfg query.store trace.afterObserved + 1 ≥
          get_current_store_epoch cfg query.store := by
        simpa only [getLatestSelectorGuard] using hselector
      exact Nat.le_antisymm
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
        hguard
  have hselectedCurrent : get_block_epoch cfg query.store
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved) =
      get_current_store_epoch cfg query.store := by
    rw [← hresult]
    exact hresultCurrent
  have hinputCurrent : get_block_epoch cfg query.store trace.afterObserved =
      get_current_store_epoch cfg query.store :=
    Weak.selectedInput_current_of_result_current_no_crossing cfg ext
      hparent hwalk hhead hinputKnown hinputEpoch hselectedCurrent hnoCrossing
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hancestor : is_ancestor query.store
      (get_node_for_root trace.result)
      (get_node_for_root trace.afterObserved) = true := by
    rw [hresult]
    exact hselectedFacts.1
  have hlands : (get_ancestor query.store (ForkChoiceNode.mk trace.result .pending)
      (query.store.blocks trace.afterObserved).slot).root = trace.afterObserved := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
      using hancestor
  have hsameEpoch : compute_epoch_at_slot cfg
        (query.store.blocks trace.afterObserved).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      hinputCurrent.trans hresultCurrent.symm
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store trace.afterObserved
        trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor_root cfg hparent
      (hwalk trace.afterObserved hinputKnown trace.result hresultKnown)
      hlands hsameEpoch hstrictNonGenesis
  exact E.trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment
    cfg ext hwfE hcore hstore hknownSegment

/-- Weak twin of `Execution.trusted_selectedCurrentNoCrossingLineage`
(`AcceptedHistoricalA32Step.lean`): preserve a historical lineage through a
no-crossing weak selector phase, regardless of whether the input was carried
or supplied by a reset.

Substitutions are the same as for the segment lemma above.  The payload side
(`Execution.TrustedAcceptedHistoricalA32LineageAt` and its `.extend`,
`Execution.acceptedBlockAt_of_causal_known`,
`Execution.CausalStore.acceptedBlockAt_iff_eq`,
`trusted_acceptedProjectedSameEpochSegment_rootDescends`) is honesty-free and
selector-free and is reused verbatim. -/
noncomputable def trusted_selectedCurrentNoCrossingLineage
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (trace : Weak.LatestConfirmedCallTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots)
    {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hprevious : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.afterObserved e Cert Supp) :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e
      Cert Supp := by
  have hsegment := Weak.trusted_selectedCurrentNoCrossingAcceptedSegment cfg ext B hwfE
    hcore hstore hparent hwalk hhead trace hinputKnown hinputSlotUpper
      hselector hresultCurrent hnoCrossing hstrictNonGenesis
  have hresult := trace.selected_facts cfg ext hselector
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact (weak_find_latest_confirmed_descendant_ge cfg ext query hparent hwalk
      hhead trace.afterObserved hinputKnown).2
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hresultKnown
  have hinputBlockEq : query.store.blocks trace.afterObserved =
      hprevious.tip_block :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E hwfE hstore
      hinputKnown).mp hprevious.tip_at
  have hinputEpochE : get_block_epoch cfg query.store
      trace.afterObserved = e := by
    simpa only [get_block_epoch, hinputBlockEq] using hprevious.tip_epoch
  have hresultEpochE : get_block_epoch cfg query.store trace.result = e := by
    have hinputCurrent : get_block_epoch cfg query.store trace.afterObserved =
        get_current_store_epoch cfg query.store := by
      have hinputEpochUpper : get_block_epoch cfg query.store
            trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
        simp only [get_block_epoch, get_current_store_epoch,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right hinputSlotUpper
      have hinputEpoch :
          get_block_epoch cfg query.store trace.afterObserved =
              get_current_store_epoch cfg query.store ∨
            get_block_epoch cfg query.store trace.afterObserved + 1 =
              get_current_store_epoch cfg query.store := by
        by_cases heq : get_block_epoch cfg query.store trace.afterObserved =
            get_current_store_epoch cfg query.store
        · exact Or.inl heq
        · right
          exact Nat.le_antisymm
            (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
            (by simpa only [getLatestSelectorGuard] using hselector)
      apply Weak.selectedInput_current_of_result_current_no_crossing cfg ext
        hparent hwalk hhead hinputKnown hinputEpoch
      · rw [← hresult]
        exact hresultCurrent
      · exact hnoCrossing
    exact hresultCurrent.trans (hinputCurrent.symm.trans hinputEpochE)
  exact hprevious.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [get_block_epoch] using hresultEpochE)
    (E.trusted_acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-! ## Weak-evaluator query facts -/

/-- Weak twin of
`Execution.LatestConfirmedCallTrace.trusted_input_current_of_selected_current_no_crossing`
(`AcceptedHistoricalA32Step.lean`): expose the current-input fact already used
internally by the generic no-crossing constructor.

Substitutions: `LatestConfirmedCallTrace` → `Weak.LatestConfirmedCallTrace` (so
that, unlike the strong declaration, this one really is reachable by dot
notation on a weak trace), `CurrentTargetSelectedEdge` →
`Weak.CurrentTargetSelectedEdge`, and the inheritance lemma → the weak twin
above.  The selector guard `getLatestSelectorGuard` is shared between the two
models and is reused verbatim. -/
theorem LatestConfirmedCallTrace.trusted_input_current_of_selected_current_no_crossing
    {query : FastConfirmationStore Root}
    (trace : Weak.LatestConfirmedCallTrace cfg ext query)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c) :
    get_block_epoch cfg query.store trace.afterObserved =
      get_current_store_epoch cfg query.store := by
  have hresult := trace.selected_facts cfg ext hselector
  have hinputEpochUpper : get_block_epoch cfg query.store
        trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpper
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    by_cases heq : get_block_epoch cfg query.store trace.afterObserved =
        get_current_store_epoch cfg query.store
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
        (by simpa only [getLatestSelectorGuard] using hselector))
  apply Weak.selectedInput_current_of_result_current_no_crossing cfg ext
    hparent hwalk hhead hinputKnown hinputEpoch
  · rw [← hresult]
    exact hresultCurrent
  · exact hnoCrossing

/-- Weak twin of `Execution.trusted_confirmed_current_at_previousStore_of_query`
(`AcceptedHistoricalA32Step.lean`): transport current-epoch status of the
carried root from the weak query store back to the preceding execution store.
Store growth preserves its block, while the preceding clock bound forces
equality of the two current epochs in precisely this case.

Substitutions: `E.confirmed` → `E.weakConfirmed`, `E.fcrStoreAtCall` →
`E.weakFcrStep`, and `E.fcrStep_store` / `E.fcrStep_confirmed_root` →
`E.weakFcrStep_store` / `E.weakFcrStep_confirmed_root`
(`WeakFCRCallContracts.lean`).  Everything else here is about `E.store`, which
the weak model shares with the strong one verbatim: `store_storeLE`,
`blocks_agree`, `store_blocks_slot_le_current`, `store_current_slot` and
`slot_at_mono` are reused unchanged. -/
theorem trusted_confirmed_current_at_previousStore_of_query
    (hT : E.ScheduledPrefixPremises cfg ext)
    {v : ValidatorIndex} {n : ℕ}
    (hknownN : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hcurrentQ : get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
        (E.weakFcrStep cfg ext v n).confirmed_root =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) :
    get_block_epoch cfg (E.store cfg ext v n) (E.weakConfirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hknownN1 : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.weakConfirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.weakConfirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
  have hinputSlotUpperN :
      ((E.store cfg ext v n).blocks
        (E.weakConfirmed cfg ext v n)).slot ≤
        get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v n (E.weakConfirmed cfg ext v n) hknownN
  have hcurrentMono : get_current_store_epoch cfg (E.store cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
  have hblockEpochNUpper : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpperN
  have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) =
      get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.weakConfirmed cfg ext v n) := by
    simp only [get_block_epoch, hblockAgree]
  have hcurrentQ' : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.weakConfirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.weakFcrStep_store, E.weakFcrStep_confirmed_root]
      using hcurrentQ
  have hreverse : get_current_store_epoch cfg
      (E.store cfg ext v (n + 1)) ≤
        get_current_store_epoch cfg (E.store cfg ext v n) := by
    rw [← hcurrentQ', ← hblockEpochAgree]
    exact hblockEpochNUpper
  have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    Nat.le_antisymm hcurrentMono hreverse
  exact hblockEpochAgree.trans (hcurrentQ'.trans hcurrentEq.symm)

/-- Weak twin of `Execution.trusted_actualFinalizedResetCurrentAnchorLineage`
(`AcceptedHistoricalA32Step.lean`): the only current-epoch finalized reset
payload is the trusted-anchor payload.  No quorum is synthesized in this
branch.

This is the "store-only" case flagged in the port plan.  The strong statement
and its whole proof mention the evaluator solely through
`(E.fcrStoreAtCall cfg ext v n).store`, and `Execution.weakFcrStep_store` gives the
weak query the very same `E.store cfg ext v (n + 1)`.  So rather than replay
roughly forty lines of reset classification, this twin *transports* the strong
theorem along `E.weakFcrStep_store` / `E.fcrStep_store`; nothing is cloned and
the reset classifiers of `AcceptedResetCheckpointClassification.lean` are used
only through the strong theorem. -/
noncomputable def trusted_actualFinalizedResetCurrentAnchorLineage_core
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
        (E.weakFcrStep cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e') :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      (E.weakFcrStep cfg ext v n).store.finalized_checkpoint.root
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store)
      Cert Supp := by
  have hstrong := E.trusted_actualFinalizedResetCurrentAnchorLineage_core cfg ext B hT
    hanchor hboundary v n
    (by simpa only [E.weakFcrStep_store, E.fcrStep_store] using hcurrent)
    hanchorCert hanchorSupp
  simpa only [E.weakFcrStep_store, E.fcrStep_store] using hstrong

/-- Eager instantiation, unchanged for every pre-existing weak caller. -/
noncomputable def trusted_actualFinalizedResetCurrentAnchorLineage
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
        (E.weakFcrStep cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) :
    E.TrustedAcceptedHistoricalA32LineageAt cfg ext B
      (E.weakFcrStep cfg ext v n).store.finalized_checkpoint.root
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) :=
  Weak.trusted_actualFinalizedResetCurrentAnchorLineage_core cfg ext B hT hanchor
    hboundary v n hcurrent ⟨CertifiedJustified.anchor⟩
    (fun _ _ h _ _ _ _ _ => Or.inl h)

/-! ## Observer-facing wrappers -/

/-- Weak twin of
`Execution.trusted_acceptedFixedSourceProducerAt_of_selectedCurrentCrossing`
(`AcceptedHistoricalA32Step.lean`): retie the query-local accepted target gate
to the weak selected result, including the skipped-boundary old-target case,
and eta-expand it to the fixed-source producer consumed by the weak historical
dispatcher.

Honesty substitution: the strong wrapper's `hv : v ∈ E.honest` is replaced by
`hcoh : E.ObserverCoherence cfg ext obs`, and its single use — the call to
`E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory` — by
`Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt`
(`WeakHistoricalA32Geometry.lean`).  That is the only honesty use in the whole
strong step layer.

Selector substitutions: `E.getLatestConfirmedTraceAt` →
`E.weakGetLatestConfirmedTraceAt`, `E.fcrStoreAtCall` → `E.weakFcrStep`,
`findLatestSelectedTrace(_parentTrace, _fst)` → the `Weak.` twins,
`find_latest_confirmed_descendant(_ge)` → `Weak.…` /
`weak_find_latest_confirmed_descendant_ge`, `strictSelectedResult_below_head`
→ `Weak.strictSelectedResult_below_head`, `CurrentTargetSelectedEdge` →
`Weak.CurrentTargetSelectedEdge`.  Both producer types and
`Execution.AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedTargetWalk`
are honesty-free, selector-free and gate-transparent here (the gate arrives as
the producer's own `intro`duced antecedent, never from the weak edge), so they
are reused verbatim. -/
noncomputable def
    trusted_acceptedFixedSourceProducerAt_of_selectedCurrentCrossing
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
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
    (htargetProducer : E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)) :
    E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  change trace.afterObserved ∈ query.store.block_roots at hinputKnown
  change getLatestSelectorGuard cfg query trace.afterObserved at hselector
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change Weak.CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c
    at hedge
  change E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext B.anchor
    B.state (n + 1) query at htargetProducer
  change E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) query trace.result
  intro hgate hsupport
  have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hresult := trace.selected_facts cfg ext hselector
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hparentTrace := findLatestSelectedTrace_parentTrace cfg ext query
    hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown
  have hm : (a, c) ∈
      (Weak.findLatestSelectedTrace cfg ext query trace.afterObserved).2.1 ++
        (Weak.findLatestSelectedTrace cfg ext query trace.afterObserved).2.2 :=
    List.mem_append.mpr (Or.inr hedge.1)
  have hinputToA : get_block_epoch cfg query.store trace.afterObserved ≤
      get_block_epoch cfg query.store a := by
    simp only [get_block_epoch, compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (hparentTrace.start_slot_le_edge_parent hG.parent hm)
  have hchildToResult : get_block_epoch cfg query.store c ≤
      get_block_epoch cfg query.store trace.result := by
    have hslots := hparentTrace.edge_child_slot_le_result hG.parent hm
    rw [findLatestSelectedTrace_fst, ← hresult] at hslots
    simp only [get_block_epoch, compute_epoch_at_slot]
    exact Nat.div_le_div_right hslots
  have hinputOld : get_block_epoch cfg query.store trace.afterObserved <
      get_current_store_epoch cfg query.store := by
    calc
      get_block_epoch cfg query.store trace.afterObserved ≤
          get_block_epoch cfg query.store a := hinputToA
      _ < get_block_epoch cfg query.store c := hedge.2
      _ ≤ get_block_epoch cfg query.store trace.result := hchildToResult
      _ = get_current_store_epoch cfg query.store := hresultCurrent
  have hcurrentNonGenesis : ∀ r ∈ query.store.block_roots,
      get_block_epoch cfg query.store r =
          (get_current_target cfg query.store).epoch →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hrCurrent
    apply hG.strict_non_genesis trace.afterObserved hinputKnown r hr
    apply Nat.lt_of_not_ge
    intro hrLeInput
    have hepochLe : get_block_epoch cfg query.store r ≤
        get_block_epoch cfg query.store trace.afterObserved := by
      simp only [get_block_epoch, compute_epoch_at_slot]
      exact Nat.div_le_div_right hrLeInput
    have hcurrentLeInput : get_current_store_epoch cfg query.store ≤
        get_block_epoch cfg query.store trace.afterObserved := by
      calc
        get_current_store_epoch cfg query.store =
            (get_current_target cfg query.store).epoch := rfl
        _ = get_block_epoch cfg query.store r := hrCurrent.symm
        _ ≤ get_block_epoch cfg query.store trace.afterObserved := hepochLe
    exact (Nat.not_le_of_gt hinputOld) hcurrentLeInput
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    Weak.CurrentTargetSelectedEdge.result_ne_input cfg ext hG.parent hG.walk
      hG.head_known hinputKnown hedge
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    Weak.strictSelectedResult_below_head cfg ext hG.parent hG.walk
      hG.head_known hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  have htargetCheckpoint :=
    Execution.current_target_eq_checkpoint_of_current_epoch_ancestor cfg
      hG.parent hbelowResult hresultCurrent hG.current_walk
  let target := get_current_target cfg query.store
  have heta : (get_ancestor query.store
      (ForkChoiceNode.mk (get_head cfg query.store).root .pending)
      (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
    rfl
  have htargetSpec := get_ancestor_spec hG.parent hG.current_walk
  rw [show compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) =
      compute_start_slot_at_epoch cfg target.epoch by rfl] at htargetSpec
  rw [heta] at htargetSpec
  have hcarrierWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg target.epoch) trace.result := by
    exact (hG.walk target.root htargetSpec.1 trace.result hresultKnown).mono
      htargetSpec.2
  have hlandsRoot :
      (get_ancestor query.store (ForkChoiceNode.mk trace.result .pending)
        (compute_start_slot_at_epoch cfg target.epoch)).root =
          target.root := by
    have hroot := congrArg Checkpoint.root htargetCheckpoint
    simpa only [target, get_checkpoint_for_block, get_checkpoint_block,
      hresultCurrent] using hroot.symm
  have hcarrierEpoch : get_block_epoch cfg query.store trace.result =
      target.epoch := hresultCurrent
  have htargetGate := htargetProducer hgate hsupport
  exact
    Execution.TrustedAcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedTargetWalk_root
      (E := E) cfg ext B hT.wellFormed hG.exact_core hphase hboundaryPhase
        hG.causal hG.parent hcarrierEpoch
        (by simpa only [target] using hcurrentNonGenesis)
        hcarrierWalk hlandsRoot htargetGate

/-- Weak twin of
`Execution.trusted_selectedCurrentNoCrossingLineageAt_of_acceptedGlobalTrajectory`
(`AcceptedHistoricalA32Step.lean`): the action-facing arbitrary-input
no-crossing wrapper.  Honesty substitution `hv` → `hcoh` through
`Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt`, plus the evaluator
substitutions `E.fcrStoreAtCall` → `E.weakFcrStep` and `E.getLatestConfirmedTraceAt`
→ `E.weakGetLatestConfirmedTraceAt`; the body just re-plumbs the geometry
bundle into `Weak.trusted_selectedCurrentNoCrossingLineage`. -/
noncomputable def
    trusted_selectedCurrentNoCrossingLineageAt_at_observer
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetSelectedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    {e : Epoch}
    (hprevious : E.TrustedAcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved e) :
    E.TrustedAcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e := by
  have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  exact Weak.trusted_selectedCurrentNoCrossingLineage cfg ext B hT.wellFormed
    hG.exact_core hG.causal hG.parent hG.walk hG.head_known
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) hinputKnown
      (hG.slot_upper _ hinputKnown) hselector hresultCurrent hnoCrossing
      (hG.strict_non_genesis _ hinputKnown) hprevious

end Weak
end FastConfirmation.Spec
end
