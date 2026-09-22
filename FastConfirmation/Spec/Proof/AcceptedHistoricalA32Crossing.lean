module
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Trajectory

@[expose] public section

/-!
# Fresh historical A3.2 lineage at a retained current-target crossing

This file handles the payload-producing complement of the carried/current/
no-crossing branch.  A retained tentative crossing exposes the exact helper
gate and its call-site honest-target support.  The accepted fixed-source gate
producer turns those executable facts into the concrete A3.2 quorum payload.

The new lineage starts at the selector result itself.  Its accepted segment is
therefore reflexive: the path from the carried input to the result crosses an
epoch boundary and is deliberately not mislabeled as a same-epoch segment.
Finalized and observed-reset branches remain separate.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

namespace AcceptedCurrentTargetA32GateRealization

/-- Retie an accepted target-local gate realization to a later carrier in the
same accepted epoch segment.

This is a lossless source rewrite.  The concrete quorum, its votes, deadline,
weight bound, and certificate are unchanged.  Accepted phase-0 coherence
makes `GJ` constant along the segment; the two exact block-epoch equations
then reduce both paper `VSAt` selectors to those `GJ` values. -/
def fixedSource_of_acceptedSameEpochSegment
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} {b : Root}
    (htargetEpoch : get_block_epoch cfg store
      (get_current_target cfg store).root =
        (get_current_target cfg store).epoch)
    (hbEpoch : get_block_epoch cfg store b =
      (get_current_target cfg store).epoch)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      (get_current_target cfg store).root b)
    (hgate : AcceptedCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store) :
    AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store b := by
  refine ⟨hgate.certified, ?_⟩
  rcases hgate.support_branch with hanchor | ⟨hne, Q, hsource⟩
  · exact Or.inl hanchor
  · refine Or.inr ⟨hne, Q, ?_⟩
    have hgj : B.state.GJ b =
        B.state.GJ (get_current_target cfg store).root :=
      hsegment.gj_eq_first hphase
        B.coherence.toAcceptedFFGSelectorCoherence
    calc
      Q.source = B.state.VSAt cfg ext store
          (get_current_target cfg store).root
          (get_current_target cfg store).epoch := hsource
      _ = B.state.GJ (get_current_target cfg store).root := by
        simp only [AcceptedChainFFGState.VSAt, htargetEpoch, if_pos]
      _ = B.state.GJ b := hgj.symm
      _ = B.state.VSAt cfg ext store b
          (get_current_target cfg store).epoch := by
        simp only [AcceptedChainFFGState.VSAt, hbEpoch, if_pos]

end AcceptedCurrentTargetA32GateRealization

/-- A carried selector invocation with a retained current-target crossing
creates a fresh data-bearing historical lineage at its concrete selected
result.

The producer premise is indexed by the exact query and selected carrier.  It
contains the fixed-source quorum realization, rather than merely a
certificate.  Selector ancestry is reconstructed from the canonical trace and
is used only to identify the current target with the selected result's current
epoch checkpoint. -/
noncomputable def carriedCurrentCrossingLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
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
    (hinputKnown : query.confirmed_root ∈ query.store.block_roots)
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext query)
    (hobserved : getLatestObservedRestartGuard cfg query
      query.confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg query query.confirmed_root)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query
      query.confirmed_root)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext query
      query.confirmed_root a c)
    (hproducer : E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query trace.result) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
      (get_current_store_epoch cfg query.store) := by
  obtain ⟨_afterFinalized, _afterObserved, hresult⟩ :=
    GetLatestConfirmedTrace.carriedSelected_facts cfg ext trace
      hfinalized hobserved hselector
  have hstrict : find_latest_confirmed_descendant cfg ext query
      query.confirmed_root ≠ query.confirmed_root :=
    CurrentTargetAcceptedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead query.confirmed_root hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query
          query.confirmed_root)) = true :=
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
  have hgate :=
    (E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge).1
  have hsupport :=
    (E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge).2
  have hrealization := hproducer hgate hsupport
  have hpayload :=
    AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget cfg ext B
      hstore hresultKnown hresultCurrent htarget hrealization
  exact AcceptedHistoricalA32LineageAt.refl cfg ext hpayload

/-! ## Target-local gate source retie from the concrete selector path -/

/-- Reconstruct the accepted same-epoch segment from the query's current
target root to the concrete selected result.

The current-target root is proved known and below the result from ordinary
head-chain geometry.  Exact last-writer provenance then lifts that known
parent walk into the accepted transition relation.  As in the no-crossing
branch, the generic causal-store form keeps the strict non-genesis fact
visible; the exact-call specialization below proves it from the unique trusted
anchor message and its minimum-slot property. -/
theorem carriedCurrentCrossingAcceptedTargetSegment
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
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
    (hinputKnown : query.confirmed_root ∈ query.store.block_roots)
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext query)
    (hobserved : getLatestObservedRestartGuard cfg query
      query.confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg query query.confirmed_root)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (htargetEpoch : get_block_epoch cfg query.store
      (get_current_target cfg query.store).root =
        (get_current_target cfg query.store).epoch)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext query
      query.confirmed_root a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks (get_current_target cfg query.store).root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    AcceptedProjectedSameEpochSegment cfg ext E B.state
      (get_current_target cfg query.store).root trace.result := by
  obtain ⟨_afterFinalized, _afterObserved, hresult⟩ :=
    GetLatestConfirmedTrace.carriedSelected_facts cfg ext trace
      hfinalized hobserved hselector
  have hstrict : find_latest_confirmed_descendant cfg ext query
      query.confirmed_root ≠ query.confirmed_root :=
    CurrentTargetAcceptedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead query.confirmed_root hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected := strictSelectedResult_below_head cfg ext hparent
    hwalk hhead hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  obtain ⟨htargetKnown, hresultDescendsTarget⟩ :=
    currentEpochBlock_descends_currentTarget cfg hparent hwalk hhead
      hresultKnown hbelowResult hcurrentWalk hresultCurrent
  have hlands : get_ancestor query.store (ForkChoiceNode.mk trace.result)
      (query.store.blocks (get_current_target cfg query.store).root).slot =
        ForkChoiceNode.mk (get_current_target cfg query.store).root := by
    simpa only [is_ancestor, decide_eq_true_eq, get_node_for_root]
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
    E.knownSameEpochAncestrySegment_of_known_ancestor cfg hparent
      (hwalk (get_current_target cfg query.store).root htargetKnown
        trace.result hresultKnown)
      hlands hsameEpoch hstrictNonGenesis
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwfE hcore hstore hknownSegment

/-! ## Exact execution-call specialization -/

/-- The fresh crossing lineage at the actual `fcrStep` evaluator call.

All store geometry is discharged from the selected-margin execution domain.
The trusted-anchor boundary supplies the walk at the query's current epoch
boundary which identifies `get_current_target` with the selected carrier's
checkpoint.  The gate producer and helper provisos are indexed by `n + 1`,
the clock of the concrete query store. -/
noncomputable def carriedCurrentCrossingLineageAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext
      (E.fcrStep cfg ext v n))
    (hobserved : getLatestObservedRestartGuard cfg
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v (n + 1)
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root a c)
    (hproducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
        cfg ext B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).result) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result
      (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) := by
  have hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
  have hparent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hv (n + 1) hHn1
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hinputKnown : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact hknownN1
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary
      v (n + 1)
  have hcurrentWalk : WalkKnown (E.fcrStep cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store))
      (get_head cfg (E.fcrStep cfg ext v n).store).root := by
    have hheadStore : (get_head cfg
        (E.fcrStep cfg ext v n).store).root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hhead
    have hboundaryWalk := E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA
      hanchor hboundary v (n + 1) hanchorEpochLeCurrent hheadStore
    simpa only [E.fcrStep_store] using hboundaryWalk
  exact E.carriedCurrentCrossingLineage cfg ext B hstore hparent hwalk
    hhead hcurrentWalk hinputKnown
      (E.getLatestConfirmedTraceAt cfg ext v n) hfinalized hobserved
        hselector hresultCurrent hprovisos hedge hproducer

/-- Action-facing crossing constructor for the target-local accepted gate
producer supplied by the global query-prefix bridge.

Unlike `carriedCurrentCrossingLineageAt`, this theorem does not ask the
upstream bridge to know the selected carrier's source.  It reconstructs the
accepted segment from the current-target root to the selected result, reties
the already constructed concrete quorum along that segment, and only then
initializes the fresh historical lineage.  No historical payload or accepted
segment is an input. -/
noncomputable def carriedCurrentCrossingLineageAt_of_targetGateProducer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext
      (E.fcrStep cfg ext v n))
    (hobserved : getLatestObservedRestartGuard cfg
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (htargetEpoch : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (get_current_target cfg (E.fcrStep cfg ext v n).store).root =
      (get_current_target cfg (E.fcrStep cfg ext v n).store).epoch)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v (n + 1)
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root)
    {a c : Root}
    (hedge : CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root a c)
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result
      (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) := by
  let ast : BeaconState Root := Classical.choose hA.genesis
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hA.genesis)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hA.genesis)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hslot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hanchorParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot
      hanchorParent).core
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore
      hA.externals_coherence.state_transition_slot hgenCore
  have hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
  have hparent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hv (n + 1) hHn1
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hinputKnown : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact hknownN1
  have hanchorEpochLeCurrent : B.anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary
      v (n + 1)
  have hcurrentWalk : WalkKnown (E.fcrStep cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store))
      (get_head cfg (E.fcrStep cfg ext v n).store).root := by
    have hheadStore : (get_head cfg
        (E.fcrStep cfg ext v n).store).root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hhead
    have hboundaryWalk := E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA
      hanchor hboundary v (n + 1) hanchorEpochLeCurrent hheadStore
    simpa only [E.fcrStep_store] using hboundaryWalk
  let target := get_current_target cfg (E.fcrStep cfg ext v n).store
  have heta : get_ancestor (E.fcrStep cfg ext v n).store
      (get_head cfg (E.fcrStep cfg ext v n).store)
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)) =
        get_node_for_root target.root := by
    rfl
  have htargetSpec := get_ancestor_spec hparent hcurrentWalk
  rw [heta] at htargetSpec
  have htargetKnown : target.root ∈
      (E.fcrStep cfg ext v n).store.block_roots := htargetSpec.1
  have hstrictNonGenesis : ∀ r ∈
      (E.fcrStep cfg ext v n).store.block_roots,
      ((E.fcrStep cfg ext v n).store.blocks target.root).slot <
          ((E.fcrStep cfg ext v n).store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hr
    have hanchorBlock :
        (E.fcrStep cfg ext v n).store.blocks ablk.root = ablk.message := by
      rw [E.fcrStep_store]
      exact E.store_anchor_block cfg ext hA.wellFormed hgen v (n + 1)
        hanchorKnown
    have htargetKnownStore : target.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [target, E.fcrStep_store] using htargetKnown
    have hanchorLeTarget : ablk.message.slot ≤
        ((E.fcrStep cfg ext v n).store.blocks target.root).slot := by
      rw [E.fcrStep_store]
      exact E.store_anchor_min_slot cfg ext hA.wellFormed
        hA.externals_coherence hgen hslot hanchorParent v (n + 1)
          target.root htargetKnownStore
    have hbad : ((E.fcrStep cfg ext v n).store.blocks target.root).slot <
        ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeTarget) hbad
  have hsegment := E.carriedCurrentCrossingAcceptedTargetSegment cfg ext B
    hA.wellFormed hcore hstore hparent hwalk hhead hcurrentWalk hinputKnown
      (E.getLatestConfirmedTraceAt cfg ext v n) hfinalized hobserved
        hselector hresultCurrent htargetEpoch hedge
          (by simpa only [target] using hstrictNonGenesis)
  have hgateAndSupport :=
    E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
  have htargetGate := hproducer hgateAndSupport.1 hgateAndSupport.2
  have htargetCurrent :
      (get_current_target cfg (E.fcrStep cfg ext v n).store).epoch =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := rfl
  have hresultTargetEpoch : get_block_epoch cfg
      (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      (get_current_target cfg (E.fcrStep cfg ext v n).store).epoch :=
    hresultCurrent.trans htargetCurrent.symm
  have hfixed :=
    AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedSameEpochSegment
      cfg ext B hphase htargetEpoch hresultTargetEpoch hsegment htargetGate
  have hfixedProducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt cfg ext
        B.anchor B.state (n + 1) (E.fcrStep cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).result := by
    intro _hgate _hsupport
    exact hfixed
  exact E.carriedCurrentCrossingLineageAt cfg ext B hA hanchor hboundary
    hv hHn1 hknownN hfinalized hobserved hselector hresultCurrent
      hprovisos hedge hfixedProducer

end Execution


end FastConfirmation.Spec

end
