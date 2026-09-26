module
public import FastConfirmationStatements.Review
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Monotonicity.LiveConfirmation

@[expose] public section

/-!
# Single review entry point

This theorem proves the two fields of `ReviewClaims` from the public safety
and live monotonicity theorems.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The public safety and live monotonicity guarantees. -/
theorem review_claims : ReviewClaims cfg ext := by
  exact ⟨confirmed_root_safe_from_next_slot cfg ext,
    live_confirmed_root_monotonicity cfg ext⟩

end FastConfirmation.Spec

end
