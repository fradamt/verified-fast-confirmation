module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionCarriedBranch
public import FastConfirmationProofs.FFG.SourceHistory.TrustedFFGSourceCoherence

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_acceptedProjectedSameEpochTransition_parentEdge
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {parent child : Root}
    (h : TrustedAcceptedProjectedSameEpochTransition cfg ext E B.state parent child) :
    E.ParentEdge child parent := by
  obtain ⟨edge⟩ := h
  obtain ⟨hlt, hevent⟩ :=
    List.getElem?_eq_some_iff.mp edge.transition.event_at
  have hmemAt :
      (E.schedule edge.transition.atPrefix.node
        (edge.transition.atPrefix.previousSecond + 1)
      )[edge.transition.atPrefix.processedCount]'hlt ∈
        E.schedule edge.transition.atPrefix.node
          (edge.transition.atPrefix.previousSecond + 1) :=
    List.getElem_mem hlt
  have hmem : Event.block edge.transition.signedBlock ∈
      E.schedule edge.transition.atPrefix.node
        (edge.transition.atPrefix.previousSecond + 1) := by
    rw [hevent] at hmemAt
    exact hmemAt
  exact Or.inr ⟨edge.transition.atPrefix.node,
    edge.transition.atPrefix.previousSecond + 1,
    edge.transition.signedBlock, hmem,
    edge.child_eq.symm, edge.parent_eq.symm⟩

/-- Every accepted same-epoch segment is semantic descent from its last root
to its first root. -/
theorem trusted_acceptedProjectedSameEpochSegment_rootDescends
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {first last : Root}
    (h : TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state first last) :
    E.RootDescends last first := by
  induction h with
  | refl => exact .refl _
  | tail hprefix hedge ih =>
      exact .step
        (E.trusted_acceptedProjectedSameEpochTransition_parentEdge cfg ext hedge) ih

end Execution
end FastConfirmation.Spec
end
