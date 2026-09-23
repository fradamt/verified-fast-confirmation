module
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Trajectory
public import FastConfirmation.Spec.Proof.ModelFacts

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

/-! ## Target-local gate source retie from the concrete selector path -/




end Execution


end FastConfirmation.Spec

end
