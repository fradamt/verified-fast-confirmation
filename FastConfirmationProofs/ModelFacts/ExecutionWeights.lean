module
public import FastConfirmationStatements.Premises.Economics

@[expose] public section

/-!
# Assumptions model facts

Proofs about Model/Assumptions. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
end Execution
/-- Horizon-bounded activity constancy specialized to epochs no later than
execution-clock epochs. The caller-supplied clock bounds put both epochs below
`E.verification_horizon`. -/
theorem StaticValidatorSet.activity_constant_of_epoch_le
    {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {i : ValidatorIndex} {e e' : Epoch} {n n' : ℕ}
    (he : e ≤ compute_epoch_at_slot cfg (E.slot_at cfg n))
    (he' : e' ≤ compute_epoch_at_slot cfg (E.slot_at cfg n'))
    (hn : compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon)
    (hn' : compute_epoch_at_slot cfg (E.slot_at cfg n') < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) e =
      is_active_validator (E.registry.getD i default) e' := by
  exact hsv.activity_constant i e e'
    (lt_of_le_of_lt he hn) (lt_of_le_of_lt he' hn')

/-- Slot form of `activity_constant_of_epoch_le`: slots bounded by execution
clock slots have activity-equivalent epochs. -/
theorem StaticValidatorSet.activity_constant_of_slot_le
    {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {i : ValidatorIndex} {s s' : Slot} {n n' : ℕ}
    (hs : s ≤ E.slot_at cfg n) (hs' : s' ≤ E.slot_at cfg n')
    (hn : compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon)
    (hn' : compute_epoch_at_slot cfg (E.slot_at cfg n') < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) (compute_epoch_at_slot cfg s) =
      is_active_validator (E.registry.getD i default) (compute_epoch_at_slot cfg s') :=
  hsv.activity_constant_of_epoch_le (cfg := cfg)
    (Nat.div_le_div_right hs) (Nat.div_le_div_right hs') hn hn'

end FastConfirmation.Spec

end
