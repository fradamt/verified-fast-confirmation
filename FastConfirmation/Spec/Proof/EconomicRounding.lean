module
public import FastConfirmation.Spec.Model.Assumptions

@[expose] public section

/-!
# Spec / Proof / EconomicRounding

Arithmetic facts separating the executable rule's `// 100` rounding from the
probabilistic committee-weight assumption.  Effective balances are quantized by
`EFFECTIVE_BALANCE_INCREMENT`; when that increment is divisible by `100`, every
finite validator-set weight is divisible by `100`.  The ordinary spec-level
estimate soundness inequality `actual ≤ estimate` then implies the post-floor
bound used by the confirmation arithmetic.

No committee-sampling or safety conclusion is assumed in this module.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- A value divisible by `100` lies below the largest multiple of `100` not
exceeding any of its upper bounds. -/
theorem le_hundred_mul_div_of_dvd
    {actual estimate : ℕ} (hdiv : 100 ∣ actual) (hle : actual ≤ estimate) :
    actual ≤ 100 * (estimate / 100) := by
  obtain ⟨k, rfl⟩ := hdiv
  exact Nat.mul_le_mul_left 100
    ((Nat.le_div_iff_mul_le (by decide)).2 (by
      simpa [Nat.mul_comm] using hle))

/-- Divisibility of every summand transfers to the execution weight of a
finite validator set. -/
theorem Execution.dvd_weight (E : Execution Root) {d : ℕ}
    (hweights : ∀ i : ValidatorIndex, d ∣ E.weight_of i)
    (S : Finset ValidatorIndex) : d ∣ E.weight S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Execution.weight]
  | @insert i S hi ih =>
      simp only [Execution.weight, Finset.sum_insert hi]
      exact Nat.dvd_add (hweights i) ih

/-- The `get_total_balance` minimum and the nonzero preset increment make the
ground-truth total active balance positive, including an execution with no
active validators. -/
theorem Execution.total_active_pos (cfg : Config) (E : Execution Root) :
    0 < E.total_active cfg := by
  unfold Execution.total_active get_total_active_balance get_total_balance
  exact lt_of_lt_of_le cfg.effective_balance_increment_pos (Nat.le_max_left _ _)

/-- Phase0 quantization makes every finite ground-truth validator-set weight a
multiple of `100`. -/
theorem Execution.hundred_dvd_weight (cfg : Config) (E : Execution Root)
    (hbb : ByzantineBound cfg E) (S : Finset ValidatorIndex) :
    100 ∣ E.weight S := by
  apply E.dvd_weight
  intro i
  exact dvd_trans cfg.hundred_dvd_effective_balance_increment
    (hbb.effective_balance_quantized i)

/-- Ordinary estimate soundness implies the exact post-floor inequality used
by the FCR arithmetic once real effective-balance quantization is restored. -/
theorem estimate_floor_dominates (cfg : Config) (E : Execution Root)
    (hbb : ByzantineBound cfg E) (S : Finset ValidatorIndex)
    {estimate : ℕ} (hle : E.weight S ≤ estimate) :
    E.weight S ≤ 100 * (estimate / 100) :=
  le_hundred_mul_div_of_dvd (E.hundred_dvd_weight cfg hbb S) hle

end FastConfirmation.Spec

end
