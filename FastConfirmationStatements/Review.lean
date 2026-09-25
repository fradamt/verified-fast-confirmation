module
public import FastConfirmationStatements.Claims

@[expose] public section

/-!
# Public FCR review claims

The two fields claim that a confirmed root is safe from the next slot and
that live confirmed roots remain monotone. The safety field uses
`Execution.NextSlotSafetyPremises`; the live field also uses
`LiveMonotonicityPremises` through `LiveConfirmedRootMonotonicity`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The two public executable FCR claims reviewed together. -/
structure ReviewClaims : Prop where
  confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot cfg ext
  live_confirmed_root_monotonicity : LiveConfirmedRootMonotonicity cfg ext

end FastConfirmation.Spec

end
