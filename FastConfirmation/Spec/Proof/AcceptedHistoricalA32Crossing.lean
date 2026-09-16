import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Trajectory

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

end Execution


end FastConfirmation.Spec
