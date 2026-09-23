module
public import FastConfirmationProofs.Discount.CommitteeWindowWeight
public import FastConfirmationProofs.Discount.RecordedSupport
public import FastConfirmationInternal.Discount.HeadSafetyInvariant

@[expose] public section

/-!
# Spec / Proof / EngineInduction: the input package and invariant

The head-safety engine's induction vocabulary. `ConfirmedSupport` is the
confirmation-time package the L4 layer extracts from `is_one_confirmed` +
`honest_support_majority` at the confirming node: the honest supporter set
`HS₀` with per-member newest-vote facts (node-independent objects — a
validator's newest pre-`s` vote is the same at every honest node once
delivered, which is what makes the majority transportable), plus the frozen
old-window ledger inequality. `EngineInv` is the strong-induction invariant:
heads descend from `b` at every honest node through slot `k`.
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
