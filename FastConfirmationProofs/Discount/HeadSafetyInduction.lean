module
public import FastConfirmationProofs.Discount.CommitteeWindowWeight
public import FastConfirmationProofs.Discount.RecordedSupport
public import FastConfirmationInternal.Discount.HeadSafetyInvariant

@[expose] public section

/-!
# Spec / Proof / EngineInduction: the input package and invariant

Proves downward monotonicity of the head-safety engine invariant defined in
`FastConfirmationInternal.Discount.HeadSafetyInvariant`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The invariant is monotone downward in the slot bound. -/
theorem EngineInv.mono {E : Execution Root} {b : Root} {n₀ : ℕ} {k k' : Slot}
    (h : EngineInv cfg ext E b n₀ k) (hk : k' ≤ k) :
    EngineInv cfg ext E b n₀ k' :=
  fun w hw m hm hsl hH => h w hw m hm (le_trans hsl hk) hH

end FastConfirmation.Spec

end
