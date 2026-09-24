module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionBranches
public import FastConfirmationProofs.Checkpoints.ResetCheckpointClassification
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetGateGeometry

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# One-step historical A3.2 payload induction

This module is the exact evaluator-step layer.  It works over
`getLatestConfirmedTraceAt`, preserving the payload's concrete quorum, common
source, and `start (e + 1)` deadline.  Reset semantics enter only through the
tagged classifiers in `AcceptedResetCheckpointClassification`; no reset is
treated as a generic certificate or payload producer.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Selector-input generic inheritance -/

/-- The no-crossing accepted segment for the exact final selector phase,
independent of which ordered reset phase supplied its input. -/
theorem selectedCurrentNoCrossingAcceptedSegment
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
    AcceptedProjectedSameEpochSegment cfg ext E B.state
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
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwfE hcore hstore hknownSegment

/-- Preserve a historical lineage through a no-crossing selector phase,
regardless of whether the input was carried or supplied by a reset. -/
noncomputable def selectedCurrentNoCrossingLineage
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      trace.afterObserved e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e := by
  have hsegment := E.selectedCurrentNoCrossingAcceptedSegment cfg ext B hwfE
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
    (E.acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-! ## Selector-input generic crossing -/

/-- Reconstruct the accepted same-epoch segment from the current target to a
current result selected from any exact ordered evaluator input. -/
theorem selectedCurrentCrossingAcceptedTargetSegment
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
    AcceptedProjectedSameEpochSegment cfg ext E B.state
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
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwfE hcore hstore hknownSegment

/-- A current crossing from any exact evaluator input creates a fresh
historical payload at the concrete selected result. -/
noncomputable def selectedCurrentCrossingLineage
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    {v : ValidatorIndex} {q : ℕ}
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
    (hprovisos : FCRPredictionSupportAt cfg ext E v q query
      trace.afterObserved)
    {a c : Root}
    (hedge : CurrentTargetSelectedEdge cfg ext query
      trace.afterObserved a c)
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks (get_current_target cfg query.store).root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
      (get_current_store_epoch cfg query.store) := by
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
  have hsegment := E.selectedCurrentCrossingAcceptedTargetSegment cfg ext B
    hwfE hcore hstore hparent hwalk hhead hcurrentWalk trace hinputKnown
      hselector hresultCurrent htargetEpoch hedge hstrictNonGenesis
  have hgateAndSupport :=
    E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
  have htargetGate := hproducer hgateAndSupport.1 hgateAndSupport.2
  have htargetCurrent : (get_current_target cfg query.store).epoch =
      get_current_store_epoch cfg query.store := rfl
  have hresultTargetEpoch : get_block_epoch cfg query.store trace.result =
      (get_current_target cfg query.store).epoch :=
    hresultCurrent.trans htargetCurrent.symm
  have hfixed :=
    AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedSameEpochSegment
      cfg ext B hphase htargetEpoch hresultTargetEpoch hsegment htargetGate
  have hpayload :=
    AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget cfg ext B
      hstore hresultKnown hresultCurrent htarget hfixed
  exact AcceptedHistoricalA32LineageAt.refl cfg ext hpayload

/-- Fresh crossing constructor at the exact fixed-source seam.

This is the form consumed by the one-step dispatcher.  Its producer must
already preserve the selected result's `VSAt` source, so it remains valid
whether the epoch-boundary checkpoint block is current or old.  The separate
target-local wrapper above is only one way to construct this producer in the
non-skipped-boundary case. -/
noncomputable def selectedCurrentCrossingLineage_of_fixedSourceProducer
    (B : CausalPrefixFFGInterpretation cfg ext E)
    {v : ValidatorIndex} {q : ℕ}
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
    (hprovisos : FCRPredictionSupportAt cfg ext E v q query
      trace.afterObserved)
    {a c : Root}
    (hedge : CurrentTargetSelectedEdge cfg ext query
      trace.afterObserved a c)
    (hproducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
        cfg ext B.anchor B.state q query trace.result) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
      (get_current_store_epoch cfg query.store) := by
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
  have hgateAndSupport :=
    E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
  have hfixed := hproducer hgateAndSupport.1 hgateAndSupport.2
  have hpayload :=
    AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget cfg ext B
      hstore hresultKnown hresultCurrent htarget hfixed
  exact AcceptedHistoricalA32LineageAt.refl cfg ext hpayload

/-! ## Accepted-global geometry for one exact query -/

/-- All store geometry shared by the three ordered evaluator input cases.
The bundle contains no reset classification and no historical payload. -/
structure HistoricalA32QueryGeometryAt
    (query : FastConfirmationStore Root) : Prop where
  exact_core : E.ExactCausalStoreWellFormedCore cfg ext
  causal : E.CausalStore cfg ext query.store
  parent : ParentSlotLt query.store
  walk : ∀ t ∈ query.store.block_roots,
    ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r
  head_known : (get_head cfg query.store).root ∈ query.store.block_roots
  current_walk : WalkKnown query.store
    (compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg query.store))
    (get_head cfg query.store).root
  slot_upper : ∀ r ∈ query.store.block_roots,
    (query.store.blocks r).slot ≤ get_current_slot cfg query.store
  strict_non_genesis : ∀ base ∈ query.store.block_roots,
    ∀ r ∈ query.store.block_roots,
      (query.store.blocks base).slot < (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots

/-- Expose the current-input fact already used internally by the generic
no-crossing constructor. -/
theorem LatestConfirmedCallTrace.input_current_of_selected_current_no_crossing
    {query : FastConfirmationStore Root}
    (trace : LatestConfirmedCallTrace cfg ext query)
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
      CurrentTargetSelectedEdge cfg ext query trace.afterObserved a c) :
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
  apply selectedInput_current_of_result_current_no_crossing cfg ext
    hparent hwalk hhead hinputKnown hinputEpoch
  · rw [← hresult]
    exact hresultCurrent
  · exact hnoCrossing

/-- Transport current-epoch status of the carried root from the exact query
store back to the preceding execution store.  Store growth preserves its
block, while the preceding clock bound forces equality of the two current
epochs in precisely this case. -/
theorem confirmed_current_at_previousStore_of_query
    (hT : E.ScheduledPrefixPremises cfg ext)
    {v : ValidatorIndex} {n : ℕ}
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hcurrentQ : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).confirmed_root =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.confirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
  have hinputSlotUpperN :
      ((E.store cfg ext v n).blocks
        (E.confirmed cfg ext v n)).slot ≤
        get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v n (E.confirmed cfg ext v n) hknownN
  have hcurrentMono : get_current_store_epoch cfg (E.store cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
  have hblockEpochNUpper : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpperN
  have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) =
      get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v n) := by
    simp only [get_block_epoch, hblockAgree]
  have hcurrentQ' : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.fcrStep_store, E.fcrStep_confirmed_root] using hcurrentQ
  have hreverse : get_current_store_epoch cfg
      (E.store cfg ext v (n + 1)) ≤
        get_current_store_epoch cfg (E.store cfg ext v n) := by
    rw [← hcurrentQ', ← hblockEpochAgree]
    exact hblockEpochNUpper
  have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    Nat.le_antisymm hcurrentMono hreverse
  exact hblockEpochAgree.trans (hcurrentQ'.trans hcurrentEq.symm)

/-- The only current-epoch finalized reset payload is the trusted-anchor
payload.  No quorum is synthesized in this branch. -/
noncomputable def actualFinalizedResetCurrentAnchorLineage
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) := by
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hknown : (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
    simpa only [E.fcrStep_store] using hrealized.root_known
  have hstore : E.CausalStore cfg ext (E.fcrStoreAtCall cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  let root := (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root
  have hat : E.AcceptedBlockAt cfg ext root
      ((E.fcrStoreAtCall cfg ext v n).store.blocks root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hknown
  have hcheckpointStore : B.state.C root
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) =
      get_checkpoint_for_block cfg (E.fcrStoreAtCall cfg ext v n).store root
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :=
    B.coherence.checkpoint_of_known hstore root hknown _
  have hcheckpointAnchor :=
    E.actualFinalizedReset_currentCheckpoint_eq_anchor cfg ext B hT hanchor
      hboundary v n hcurrent
  have hpayload := AcceptedHistoricalA32GatePayloadAt.of_anchor cfg ext B hat
    (by simpa only [root, get_block_epoch] using hcurrent)
    (hcheckpointStore.trans (by simpa only [root] using hcheckpointAnchor))
  exact AcceptedHistoricalA32LineageAt.refl cfg ext hpayload

/-- Produce the common query geometry once from the accepted global
trajectory, rather than rebuilding it separately in every reset case. -/
theorem historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
  have hdomain := E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
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
    exact E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
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
    acceptedFixedSourceProducerAt_of_selectedCurrentCrossing
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
    (htargetProducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n)) :
    E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
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
  change E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext B.anchor
    B.state (n + 1) query at htargetProducer
  change E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) query trace.result
  intro hgate hsupport
  have hG := E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory
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
  exact AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedTargetWalk_root
    (E := E) cfg ext B hT.wellFormed hG.exact_core hphase hboundaryPhase hG.causal
      hG.parent hcarrierEpoch (by simpa only [target] using hcurrentNonGenesis)
      hcarrierWalk hlandsRoot htargetGate




end Execution


end FastConfirmation.Spec

end
