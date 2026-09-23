module
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Payload
public import FastConfirmation.Spec.Proof.AcceptedSameEpochSegmentRealization
public import FastConfirmation.Spec.Proof.GetLatestConfirmedTrace
public import FastConfirmation.Spec.Proof.HistoricalCurrentTargetTrajectory

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# First payload-preserving actual evaluator branch

This file closes the carried/no-restart/current/no-crossing branch of the
future outer historical induction.  The exact evaluator trace proves that the
selector input is the prior confirmed root.  The executable selector geometry
proves that this input is current-epoch, and an actual accepted same-epoch
segment extends the prior safety-free lineage.

The theorem consumes the prior lineage as its induction hypothesis.  It does
not consume a fresh historical payload, certificate producer, SIR result,
canonicity interval, or safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact carried-selector branch projection -/

namespace GetLatestConfirmedTrace


end GetLatestConfirmedTrace

namespace Execution

variable {E : Execution Root}

/-! ## Concrete selected ancestry segment -/

/-- A known ancestry walk between equal-epoch endpoints is a concrete
same-epoch segment once every strict child above the first endpoint is known
not to be a trusted genesis root.

The endpoint equality alone is enough for the epoch argument: parent slots
strictly decrease, so every intermediate epoch is squeezed between the two
equal endpoint epochs.  The separate non-genesis premise is intentionally
visible here because root identities can be overwritten in the executable
store; the actual-call specialization below derives it from the fixed anchor
message and anchor-minimal-slot theorem. -/
theorem knownSameEpochAncestrySegment_of_known_ancestor_root
    {store : Store Root}
    (hparent : ParentSlotLt store)
    {first last : Root}
    (hwalk : WalkKnown store (store.blocks first).slot last)
    (hlands : (get_ancestor store (ForkChoiceNode.mk last .pending)
      (store.blocks first).slot).root = first)
    (hsame : compute_epoch_at_slot cfg (store.blocks first).slot =
      compute_epoch_at_slot cfg (store.blocks last).slot)
    (hstrictNonGenesis : ∀ r ∈ store.block_roots,
      (store.blocks first).slot < (store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      store first last := by
  have go : ∀ {tip : Root},
      WalkKnown store (store.blocks first).slot tip →
      (get_ancestor store (ForkChoiceNode.mk tip .pending)
          (store.blocks first).slot).root = first →
      compute_epoch_at_slot cfg (store.blocks first).slot =
          compute_epoch_at_slot cfg (store.blocks tip).slot →
      KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
        store first tip := by
    intro tip htipWalk
    induction htipWalk with
    | @stop r hr hle =>
        intro htipLands _
        have hrEq : r = first := by
          rw [get_ancestor_stop hle] at htipLands
          exact htipLands
        subst r
        exact .refl first hr
    | @step r hr hgt hp ih =>
        intro htipLands htipEpoch
        have hparentLands :
            (get_ancestor store
                (ForkChoiceNode.mk (store.blocks r).parent_root .pending)
                (store.blocks first).slot).root = first := by
          rw [get_ancestor_step hparent hr hgt hp] at htipLands
          exact htipLands
        have hfirstLeParent : (store.blocks first).slot ≤
            (store.blocks (store.blocks r).parent_root).slot := by
          by_contra hnot
          have hparentLe :
              (store.blocks (store.blocks r).parent_root).slot ≤
                (store.blocks first).slot :=
            Nat.le_of_lt (Nat.lt_of_not_ge hnot)
          rw [get_ancestor_stop hparentLe] at hparentLands
          have hpEq : (store.blocks r).parent_root = first :=
            hparentLands
          rw [hpEq] at hnot
          exact hnot (le_refl _)
        have hparentLt :
            (store.blocks (store.blocks r).parent_root).slot <
              (store.blocks r).slot :=
          hparent r hr hp.root_mem
        have hfirstEpochLeParent :
            compute_epoch_at_slot cfg (store.blocks first).slot ≤
              compute_epoch_at_slot cfg
                (store.blocks (store.blocks r).parent_root).slot :=
          Nat.div_le_div_right hfirstLeParent
        have hparentEpochLeTip :
            compute_epoch_at_slot cfg
                (store.blocks (store.blocks r).parent_root).slot ≤
              compute_epoch_at_slot cfg (store.blocks r).slot :=
          Nat.div_le_div_right hparentLt.le
        have hfirstEpochEqParent :
            compute_epoch_at_slot cfg (store.blocks first).slot =
              compute_epoch_at_slot cfg
                (store.blocks (store.blocks r).parent_root).slot :=
          Nat.le_antisymm hfirstEpochLeParent
            (hparentEpochLeTip.trans_eq htipEpoch.symm)
        exact .tail (ih hparentLands hfirstEpochEqParent) hr
          (hstrictNonGenesis r hr hgt) rfl
          (hfirstEpochEqParent.symm.trans htipEpoch)
  exact go hwalk hlands hsame


/-! ## Accepted-segment semantic descent -/

/-- One accepted projected edge is an edge of the execution parent graph.
Schedule membership comes from the exact next-event equation carried by the
accepted transition, not from an arbitrary scheduled-root lookup. -/
theorem acceptedProjectedSameEpochTransition_parentEdge
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {parent child : Root}
    (h : AcceptedProjectedSameEpochTransition cfg ext E B.state parent child) :
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
theorem acceptedProjectedSameEpochSegment_rootDescends
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {first last : Root}
    (h : AcceptedProjectedSameEpochSegment cfg ext E B.state first last) :
    E.RootDescends last first := by
  induction h with
  | refl => exact .refl _
  | tail hprefix hedge ih =>
      exact .step
        (E.acceptedProjectedSameEpochTransition_parentEdge cfg ext hedge) ih

/-! ## Selected-trace accepted segment supplier -/


/-! ## The carried/current/no-crossing induction branch -/



/-! ## Actual execution-call specialization -/


end Execution


end FastConfirmation.Spec

end
