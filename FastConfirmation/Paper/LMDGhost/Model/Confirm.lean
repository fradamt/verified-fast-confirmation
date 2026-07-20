import FastConfirmation.Paper.LMDGhost.Model.Weights

/-!
# LMDGhost / Model / Confirm

Definition 8: the single-block check `isOneConfirmed` (`Q_b > safetyThreshold`,
evaluated at `slot(t)-1`) and its lift over all ancestors, `isLMDGHOSTSafe`.
Both are filter-agnostic (the eligibility filter enters only the fork choice).
These are `Prop`-valued, so no `noncomputable` marker is needed even though they
rest on the noncomputable `Q`.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- Definition 8 single-block check, evaluated at `slot(t)-1`. -/
def isOneConfirmed (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (A : Anchor n) (V : View n P) (b : Block n) (t : Time) : Prop :=
  Q A cm V b (τ.slotOf t - 1) > safetyThreshold A cm fm pb b (τ.slotOf t - 1)

/-- Definition 8: every ancestor of `b` is one-confirmed (or genesis). -/
def isLMDGHOSTSafe (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (A : Anchor n) (V : View n P) (b : Block n) (t : Time) : Prop :=
  ∀ ⦃b' : Block n⦄, b' ≼ b → b' = Block.genesis ∨ isOneConfirmed τ fm cm pb A V b' t

end FastConfirmation.LMDGhost
