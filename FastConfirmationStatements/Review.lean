module
public import FastConfirmationStatements.Claims

@[expose] public section

/-!
Defines the two public FCR claims for next-slot safety and live confirmed-root monotonicity.
The safety field uses
`Execution.NextSlotSafetyPremises`; the live field also uses
`LiveMonotonicityPremises` through `LiveConfirmedRootMonotonicity`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The two public executable FCR claims reviewed together. -/
structure ReviewClaims : Prop where
  confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot cfg ext
  live_confirmed_root_monotonicity : LiveConfirmedRootMonotonicity cfg ext

end FastConfirmation.Spec

end
