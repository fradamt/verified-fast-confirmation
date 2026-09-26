module
public import FastConfirmationStatements.Review
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Monotonicity.LiveConfirmation

@[expose] public section

/-!
# Single review entry point

This theorem proves the safety field of `ReviewClaims`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The public safety guarantee. -/
theorem review_claims : ReviewClaims cfg ext := by
  exact ⟨confirmed_root_safe_from_next_slot cfg ext⟩

end FastConfirmation.Spec

end
