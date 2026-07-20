import FastConfirmation.Spec.Model.Assumptions
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Spec / Proof / FFGQuorum

Weighted quorum-intersection arithmetic used by the concrete Casper-FFG
certificate layer.  This module deliberately proves the set/weight fact before
introducing justification semantics: two two-thirds quorums inside the same
validator universe must share an honest signer when the non-honest weight is at
most 25 percent.

No fork-choice or FFG safety conclusion is assumed here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

private theorem quorum_intersection_arith
    {W q₁ q₂ u i b wu C : ℕ}
    (hW : 0 < W)
    (hq₁ : 2 * W ≤ 3 * q₁) (hq₂ : 2 * W ≤ 3 * q₂)
    (hsum : u + i = q₁ + q₂)
    (hu : u ≤ W) (hi : i ≤ b)
    (hfrac : 100 * b ≤ C * wu) (hwu : wu ≤ W) (hC : C ≤ 25) : False := by
  have hq : 4 * W ≤ 3 * (q₁ + q₂) := by omega
  have hCwu : C * wu ≤ 25 * W := by
    exact (Nat.mul_le_mul hC hwu)
  omega

private theorem one_third_intersection_arith {W s t : ℕ}
    (hs : W < 3 * s) (ht : 2 * W ≤ 3 * t)
    (hsum : s + t ≤ W) : False := by
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- Weight is monotone under finite-set inclusion. -/
private theorem weight_mono (E : Execution Root)
    {A B : Finset ValidatorIndex} (hAB : A ⊆ B) :
    E.weight A ≤ E.weight B := by
  simp only [Execution.weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun _ _ _ => Nat.zero_le _)

omit [LinearOrder Root] [Inhabited Root] in
/-- Two weighted two-thirds quorums contained in the same validator universe
intersect in an honest validator when the universe's non-honest weight is at
most `C ≤ 25` percent and its reference total is positive.

The universe weight may be smaller than the reference total (as with
`get_total_active_balance`'s minimum floor); this only strengthens the result.
-/
theorem two_quorums_intersect_honest
    (E : Execution Root) {U S T : Finset ValidatorIndex} {W C : ℕ}
    (hW : 0 < W)
    (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hU : E.weight U ≤ W)
    (hfrac : 100 * E.weight (U.filter (fun i => i ∉ E.honest)) ≤
      C * E.weight U)
    (hC : C ≤ 25)
    (hS : 2 * W ≤ 3 * E.weight S)
    (hT : 2 * W ≤ 3 * E.weight T) :
    ∃ i ∈ S, i ∈ T ∧ i ∈ E.honest := by
  classical
  by_contra hnone
  push Not at hnone
  have hI : S ∩ T ⊆ U.filter (fun i => i ∉ E.honest) := by
    intro i hi
    have hiS : i ∈ S := (Finset.mem_inter.mp hi).1
    have hiT : i ∈ T := (Finset.mem_inter.mp hi).2
    exact Finset.mem_filter.mpr ⟨hSU hiS, hnone i hiS hiT⟩
  have hUnion : S ∪ T ⊆ U := Finset.union_subset hSU hTU
  have hsum : E.weight (S ∪ T) + E.weight (S ∩ T) =
      E.weight S + E.weight T := by
    simpa only [Execution.weight] using
      (Finset.sum_union_inter :
        (∑ i ∈ S ∪ T, E.weight_of i) + ∑ i ∈ S ∩ T, E.weight_of i =
          (∑ i ∈ S, E.weight_of i) + ∑ i ∈ T, E.weight_of i)
  exact quorum_intersection_arith hW hS hT hsum
    ((weight_mono E hUnion).trans hU) (weight_mono E hI)
    hfrac hU hC

omit [LinearOrder Root] [Inhabited Root] in
/-- A strictly-greater-than-one-third honest set intersects every two-thirds
quorum in the same weighted universe.  This is the arithmetic core of the
paper's no-conflicting-checkpoint argument: unlike two-quorum accountable
safety, no Byzantine-fraction subtraction is needed because every member of
the smaller set is already known honest. -/
theorem one_third_honest_intersects_two_thirds
    (E : Execution Root) {U S T : Finset ValidatorIndex} {W : ℕ}
    (hSU : S ⊆ U) (hTU : T ⊆ U)
    (hSHonest : S ⊆ E.honest)
    (hU : E.weight U ≤ W)
    (hS : W < 3 * E.weight S)
    (hT : 2 * W ≤ 3 * E.weight T) :
    ∃ i ∈ S, i ∈ T ∧ i ∈ E.honest := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    exact hnone i hiS hiT (hSHonest hiS)
  have hUnion : S ∪ T ⊆ U := Finset.union_subset hSU hTU
  have hweightUnion : E.weight (S ∪ T) =
      E.weight S + E.weight T := by
    simp only [Execution.weight]
    exact Finset.sum_union hdisjoint
  have hsum : E.weight S + E.weight T ≤ W := by
    rw [← hweightUnion]
    exact (weight_mono E hUnion).trans hU
  exact one_third_intersection_arith hS hT hsum

end FastConfirmation.Spec
