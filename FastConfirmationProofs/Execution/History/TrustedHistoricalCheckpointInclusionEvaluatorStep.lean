module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionEvaluatorStep
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionEvaluatorReset
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionCarriedBranch
public import FastConfirmationProofs.Checkpoints.TrustedSameEpochSegmentRealization
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetGateGeometry
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
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
    (trace : LatestConfirmedCallTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c)
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
        (find_latest_confirmed_descendant cfg ext query trace.afterObserved) =
      get_current_store_epoch cfg query.store := by
    rw [← hresult]
    exact hresultCurrent
  have hinputCurrent : get_block_epoch cfg query.store trace.afterObserved =
      get_current_store_epoch cfg query.store :=
    selectedInput_current_of_result_current_no_crossing cfg ext
      hparent hwalk hhead hinputKnown hinputEpoch hselectedCurrent hnoCrossing
  have hselectedFacts := find_latest_confirmed_descendant_ge cfg ext query
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
      cfg ext     hwfE hcore hstore hknownSegment

/-- Preserve a historical lineage through a no-crossing selector phase,
regardless of whether the input was carried or supplied by a reset. -/
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
    (trace : LatestConfirmedCallTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c)
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
  have hsegment := E.trusted_selectedCurrentNoCrossingAcceptedSegment cfg ext B hwfE
    hcore hstore hparent hwalk hhead trace hinputKnown hinputSlotUpper
      hselector hresultCurrent hnoCrossing hstrictNonGenesis
  have hresult := trace.selected_facts cfg ext hselector
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact (find_latest_confirmed_descendant_ge cfg ext query hparent hwalk
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
      apply selectedInput_current_of_result_current_no_crossing cfg ext
        hparent hwalk hhead hinputKnown hinputEpoch
      · rw [← hresult]
        exact hresultCurrent
      · exact hnoCrossing
    exact hresultCurrent.trans (hinputCurrent.symm.trans hinputEpochE)
  exact hprevious.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [get_block_epoch] using hresultEpochE)
    (E.trusted_acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-! ## Selector-input generic crossing -/

/-- Reconstruct the accepted same-epoch segment from the current target to a
current result selected from any exact ordered evaluator input. -/
theorem trusted_selectedCurrentCrossingAcceptedTargetSegment
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
    (hcurrentWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root)
    (trace : LatestConfirmedCallTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (htargetEpoch : get_block_epoch cfg query.store
      (get_current_target cfg query.store).root =
        (get_current_target cfg query.store).epoch)
    {a c : Root}
    (hedge : CurrentTargetSelectedEdge cfg ext query
      trace.afterObserved a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks (get_current_target cfg query.store).root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state
      (get_current_target cfg query.store).root trace.result := by
  have hresult := trace.selected_facts cfg ext hselector
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    CurrentTargetSelectedEdge.result_ne_input cfg ext hparent hwalk hhead
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
  obtain ⟨htargetKnown, hresultDescendsTarget⟩ :=
    currentEpochBlock_descends_currentTarget cfg hparent hwalk hhead
      hresultKnown hbelowResult hcurrentWalk hresultCurrent
  have hlands : (get_ancestor query.store (ForkChoiceNode.mk trace.result .pending)
      (query.store.blocks (get_current_target cfg query.store).root).slot).root = (get_current_target cfg query.store).root := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
      using hresultDescendsTarget
  have htargetCurrent : (get_current_target cfg query.store).epoch =
      get_current_store_epoch cfg query.store := rfl
  have hsameEpoch : compute_epoch_at_slot cfg
        (query.store.blocks (get_current_target cfg query.store).root).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      htargetEpoch.trans (htargetCurrent.trans hresultCurrent.symm)
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store
        (get_current_target cfg query.store).root trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor_root cfg hparent
      (hwalk (get_current_target cfg query.store).root htargetKnown
        trace.result hresultKnown)
      hlands hsameEpoch hstrictNonGenesis
  exact E.trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment
      cfg ext     hwfE hcore hstore hknownSegment

/-! ## Accepted-global geometry for one exact query -/

theorem trusted_historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.HistoricalA32QueryGeometryAt cfg ext (E.fcrStoreAtCall cfg ext v n) := by
  let ast : BeaconState Root := Classical.choose hT.genesis_structure
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis_structure)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis_structure)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hslot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hanchorParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT
  have hcausal : E.CausalStore cfg ext (E.fcrStoreAtCall cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hdomain := E.trusted_storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt (E.fcrStoreAtCall cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStoreAtCall cfg ext v n).store
          ((E.fcrStoreAtCall cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStoreAtCall cfg ext v n).store).root ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.trusted_headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hv (n + 1) hHn1
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    E.trustedAnchor_epoch_le_currentEpoch_of_trajectory cfg ext hT
      hanchor hboundary v (n + 1)
  have hcurrentWalk : WalkKnown (E.fcrStoreAtCall cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store))
      (get_head cfg (E.fcrStoreAtCall cfg ext v n).store).root := by
    have hheadStore : (get_head cfg
        (E.fcrStoreAtCall cfg ext v n).store).root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hhead
    have hboundaryWalk :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v (n + 1) hanchorEpochLeCurrent hheadStore
    simpa only [E.fcrStep_store] using hboundaryWalk
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
    have hrStore : r ∈ (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hr
    simpa only [E.fcrStep_store] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hslot⟩ v (n + 1) r hrStore
  · intro base hbase r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hr
    have hanchorBlock :
        (E.fcrStoreAtCall cfg ext v n).store.blocks ablk.root = ablk.message := by
      rw [E.fcrStep_store]
      exact E.store_anchor_block cfg ext hT.wellFormed hgen v (n + 1)
        hanchorKnown
    have hbaseKnown : base ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hbase
    have hanchorLeBase : ablk.message.slot ≤
        ((E.fcrStoreAtCall cfg ext v n).store.blocks base).slot := by
      rw [E.fcrStep_store]
      exact E.store_anchor_min_slot cfg ext hT.wellFormed
        hT.externals_coherence hgen hslot hanchorParent v (n + 1)
          base hbaseKnown
    have hbad : ((E.fcrStoreAtCall cfg ext v n).store.blocks base).slot <
        ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeBase) hbad

/-- Retie the query-local accepted target gate to the exact selected result,
including the skipped-boundary old-target case, and eta-expand it to the
fixed-source producer consumed by the historical dispatcher. -/
noncomputable def
    trusted_acceptedFixedSourceProducerAt_of_selectedCurrentCrossing
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinputKnown : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store)
    {a c : Root}
    (hedge : CurrentTargetSelectedEdge cfg ext (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved a c)
    (htargetProducer : E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n)) :
    E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  change trace.afterObserved ∈ query.store.block_roots at hinputKnown
  change getLatestSelectorGuard cfg query trace.afterObserved at hselector
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c
    at hedge
  change E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext B.anchor
    B.state (n + 1) query at htargetProducer
  change E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) query trace.result
  intro hgate hsupport
  have hG := E.trusted_historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary hv hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hresult := trace.selected_facts cfg ext hselector
  have hselectedFacts := find_latest_confirmed_descendant_ge cfg ext query
    hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hparentTrace := findLatestSelectedTrace_parentTrace cfg ext query
    hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown
  have hm : (a, c) ∈
      (findLatestSelectedTrace cfg ext query trace.afterObserved).2.1 ++
        (findLatestSelectedTrace cfg ext query trace.afterObserved).2.2 :=
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
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    CurrentTargetSelectedEdge.result_ne_input cfg ext hG.parent hG.walk
      hG.head_known hinputKnown hedge
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    strictSelectedResult_below_head cfg ext hG.parent hG.walk hG.head_known
      hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  have htargetCheckpoint :=
    current_target_eq_checkpoint_of_current_epoch_ancestor cfg hG.parent
      hbelowResult hresultCurrent hG.current_walk
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
        (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
    have hroot := congrArg Checkpoint.root htargetCheckpoint
    simpa only [target, get_checkpoint_for_block, get_checkpoint_block,
      hresultCurrent] using hroot.symm
  have hcarrierEpoch : get_block_epoch cfg query.store trace.result =
      target.epoch := by
    exact hresultCurrent
  have htargetGate := htargetProducer hgate hsupport
  exact TrustedAcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedTargetWalk_root
    (E := E) cfg ext B hT.wellFormed hG.exact_core hphase hboundaryPhase hG.causal
      hG.parent hcarrierEpoch (by simpa only [target] using hcurrentNonGenesis)
      hcarrierWalk hlandsRoot htargetGate


end Execution
end FastConfirmation.Spec
end
