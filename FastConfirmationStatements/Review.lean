module
public import FastConfirmationStatements.Claims

@[expose] public section

/-!
Defines the public FCR review claim for next-slot safety.
-/

namespace FastConfirmation.Spec

variable (Root : Type) [LinearOrder Root] [Inhabited Root]

/-- The public executable FCR safety claim for the root type `Root`. -/
structure ReviewClaims : Prop where
  confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot Root

end FastConfirmation.Spec

end
