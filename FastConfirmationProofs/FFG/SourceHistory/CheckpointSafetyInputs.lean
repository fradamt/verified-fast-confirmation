module
public import FastConfirmationProofs.Checkpoints.EdgeWeightAlgebra
public import FastConfirmationProofs.Execution.Delivery.VoteDeliveryMargin
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.ForkChoice.Head.AheadHeadDominance
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack

@[expose] public section

/-!
# Spec / Proof / Cruxes

Carries checkpoint epoch ordering and safety conditions across FFG source history.

This module contains `ce_mono` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `compute_epoch_at_slot` is monotone (folded form, so `omega` sees the epochs as
consistent atoms — a bare `Nat.div_le_div_right` unfolds them). -/
theorem ce_mono {a b : Slot} (h : a ≤ b) :
    compute_epoch_at_slot cfg a ≤ compute_epoch_at_slot cfg b :=
  Nat.div_le_div_right h

namespace Execution

variable (E : Execution Root)

/-! ## Crux 3 — `hcov`: the full-epoch honest-coverage floor -/


/-! ## Crux 4 — `hsat`: the post-`T1` saturation crux -/



/-! ## Crux 6 — `hrec`: every `Sclass` member records a `c`-supporting message -/


/-! ## Crux 2 — `hPS`: the parent-stuck honest slice `⊆ Aclass lo es \ Aclass sa es` -/


end Execution

end FastConfirmation.Spec

end
