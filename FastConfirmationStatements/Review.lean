module
public import FastConfirmationStatements.Claims

@[expose] public section

/-!
Defines the public FCR review claim for next-slot safety. The separate live
result is conditional on `LiveMonotonicityPremises`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The public executable FCR safety claim. -/
structure ReviewClaims : Prop where
  confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot cfg ext

end FastConfirmation.Spec

end
