module
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.Execution.Trajectory.ChainWalkClosure
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack
public import FastConfirmationProofs.Execution.Trajectory.InductionHypothesis
public import FastConfirmationProofs.Checkpoints.CheckpointMarginInputs

@[expose] public section

/-!
# Strong-prefix safety interfaces

Proves ancestor comparability for confirmed roots in a common safe execution prefix.

This module contains `ancestor_comparable_of_common` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)






end Execution

/-! ## Conditional strong-prefix theorem -/





omit [Inhabited Root] in
/-- **Two ancestors of a common node, the lower slot below.** If `a` and `b` are both
ancestors of `x` and `(blocks a).slot ≤ (blocks b).slot`, then `a` is an ancestor of `b`
(`b ⪰ a`). The walk from `x` down to `b`'s slot lands on `b` (`hb`); continuing it to `a`'s
slot lands on `a` (`ha`) by walk composition (`get_ancestor_comp`) — so the walk from `b` to
`a`'s slot is `a`. Purely the `get_ancestor` composition law; the `WalkKnown` witness is the
walk of `x` down to `a`'s slot. -/
theorem ancestor_comparable_of_common {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x a b : Root} (hle : (store.blocks a).slot ≤ (store.blocks b).slot)
    (hwa : WalkKnown store (store.blocks a).slot x)
    (ha : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk a .pending) = true)
    (hb : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk b .pending) = true) :
    is_ancestor store (ForkChoiceNode.mk b .pending) (ForkChoiceNode.mk a .pending) = true := by
  simp only [is_ancestor_pending, decide_eq_true_eq] at ha hb ⊢
  have hcomp := get_ancestor_comp_root hwf hle hwa
  rw [hb, ha] at hcomp
  exact hcomp






end FastConfirmation.Spec

end
