module
public import FastConfirmationProofs.Handlers.CommitteeWeightFractions
public import FastConfirmationProofs.Discount.HeadSafetyInduction
public import FastConfirmationInternal.Discount.SupportClasses

@[expose] public section

/-!
# Spec / Proof / Ledger

Proves partition and monotonicity facts for the vote support classes in Internal.

The definitions of `SupportsDesc`, `AncestorOrVoteless`, and `Sclass` are in
`FastConfirmationInternal.Discount.SupportClasses`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the ground-truth vote classes -/

/-! ## Section 2 — weight accessors -/

/-! ## Section 3 — the honest-window partition `J = s + a + x` -/

omit [LinearOrder Root] [Inhabited Root] in
/-- A set's weight splits three ways along a predicate pair `p`, `q`: `p`, then
`¬p ∧ q`, then `¬p ∧ ¬q`. Pure `Finset.filter` algebra (two
`sum_filter_add_sum_filter_not` steps + `filter_filter`). -/
theorem weight_three_split (W : Finset ValidatorIndex) (p q : ValidatorIndex → Prop)
    [DecidablePred p] [DecidablePred q] :
    E.weight W = E.weight (W.filter p)
      + E.weight (W.filter (fun i => ¬ p i ∧ q i))
      + E.weight (W.filter (fun i => ¬ p i ∧ ¬ q i)) := by
  simp only [Execution.weight]
  rw [← Finset.sum_filter_add_sum_filter_not W p E.weight_of,
      ← Finset.sum_filter_add_sum_filter_not (W.filter (fun i => ¬ p i)) q E.weight_of,
      Finset.filter_filter, Finset.filter_filter]
  ring

/-- **The honest-window partition**: `J(σ) = s(σ) + a(σ) + x(σ)`. `Sclass` /
`Aclass` / `Xclass` are `S`, `¬S ∧ A`, `¬S ∧ ¬A` filters of the same honest
window, so their weights sum to the honest committee-union weight `Jspec lo σ`. -/
theorem weight_partition (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    E.Jspec lo σ = E.Sval cfg ext v₀ n₀ b' lo σ + E.Aval cfg ext v₀ n₀ b' lo σ
      + E.Xval cfg ext v₀ n₀ b' lo σ := by
  classical
  rw [Execution.Sval, Execution.Aval, Execution.Xval, Execution.Sclass,
    Execution.Aclass, Execution.Xclass, Execution.Jspec]
  exact E.weight_three_split ((E.span_committee lo σ).filter (fun i => i ∈ E.honest))
    (fun i => E.SupportsDesc cfg ext v₀ n₀ b' σ i)
    (fun i => E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i)

/-! ## Section 4 — the invariant and the F3 capacity floor -/

/-- Pure-ℕ core of `Rterm_nonneg`: from the cross-multiplied `span_fraction`
`100·B ≤ C·(J + B)` and `C ≤ 100`, the R-term subtraction is un-truncated,
`(100−C)·B ≤ C·J`. -/
private theorem sub_mul_le_of_span {C B J : ℕ} (hC : C ≤ 100)
    (h : 100 * B ≤ C * (J + B)) : (100 - C) * B ≤ C * J := by
  have h1 : (100 - C) * B + C * B = 100 * B := by
    rw [← Nat.add_mul]; congr 1; omega
  rw [Nat.mul_add] at h
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- **The R-term is nonnegative** (its ℕ subtraction is un-truncated):
`(100−C)·B(σ) ≤ C·J(σ)`, from `span_fraction` in set form
(`100·B ≤ C·(J + B)`) and `weight_split_honest`. This is what lets the `min`
in `INVstar` behave as a genuine capacity rather than clamping to `0`. -/
theorem Rterm_nonneg (hbb : ByzantineBound cfg E) (lo σ : Slot)
    (hloH : E.SlotWithinHorizon cfg lo) (hσH : E.SlotWithinHorizon cfg σ) :
    (100 - cfg.confirmation_byzantine_threshold) * E.Bval lo σ ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo σ := by
  have hC : cfg.confirmation_byzantine_threshold ≤ 100 :=
    le_trans cfg.confirmation_byzantine_threshold_le (by norm_num)
  have hsf := hbb.span_fraction lo σ hloH hσH
  rw [E.weight_split_honest (E.span_committee lo σ)] at hsf
  rw [Execution.Bval, Execution.Bwin, Execution.Jspec]
  exact sub_mul_le_of_span hC hsf

/-! ## Section 5 — monotonicity of the window quantities -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Ground-truth weight is monotone under set inclusion. -/
theorem weight_mono {s t : Finset ValidatorIndex} (h : s ⊆ t) :
    E.weight s ≤ E.weight t := by
  simp only [Execution.weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => Nat.zero_le _)



omit [LinearOrder Root] [Inhabited Root] in
/-- Honest committee-union weight `J` is monotone in the window end. -/
theorem Jspec_mono (lo : Slot) {σ σ' : Slot} (h : σ ≤ σ') :
    E.Jspec lo σ ≤ E.Jspec lo σ' := by
  simp only [Execution.Jspec]
  exact E.weight_mono (Finset.filter_subset_filter _ (E.span_committee_mono lo h))


/-! ## Section 6 — the pure-ℕ ledger step -/



end Execution

end FastConfirmation.Spec

end
