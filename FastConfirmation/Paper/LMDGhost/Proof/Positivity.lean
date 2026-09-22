module
public import Mathlib.Tactic
public import FastConfirmation.Paper.LMDGhost.Model.Weights

@[expose] public section

/-!
# LMDGhost / Proof / Positivity

Positivity and monotonicity of the weight functions (balances are positive),
plus the `slotOf (st s) = s` round-trip. Division steps in the `Q`/`P` algebra
all need a denominator-positivity side condition sourced from here.
-/

namespace FastConfirmation.LMDGhost

variable {n : ℕ} {P : Type}

/-- Total weight of a nonempty set is strictly positive (balances are positive). -/
theorem totalWeight_pos (A : Anchor n) {X : Finset (Validator n)} (hX : X.Nonempty) :
    0 < totalWeight A X := by
  simpa [totalWeight] using Finset.sum_pos (fun i _ => A.hpos i) hX

/-- Total weight is nonnegative. -/
theorem totalWeight_nonneg (A : Anchor n) (X : Finset (Validator n)) : 0 ≤ totalWeight A X := by
  unfold totalWeight
  exact Finset.sum_nonneg (fun i _ => (A.hpos i).le)

/-- Total weight is monotone in the set. -/
theorem totalWeight_mono (A : Anchor n) {X Y : Finset (Validator n)} (h : X ⊆ Y) :
    totalWeight A X ≤ totalWeight A Y :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => (A.hpos i).le)

/-- Honest committee weight is at most total committee weight. -/
theorem J_le_W (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (b : Block n) (s : Slot) :
    J A cm fm b s ≤ W A cm b s := by
  simp only [J, W]
  exact totalWeight_mono A (Finset.filter_subset _ _)

/-- Honest support is at most honest committee weight. -/
theorem H_le_J (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b : Block n) (s : Slot) : H A cm fm V b s ≤ J A cm fm b s := by
  simp only [H, J]
  apply totalWeight_mono
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.1⟩

/-- Honest support is at most total support. -/
theorem H_le_S (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b : Block n) (s : Slot) : H A cm fm V b s ≤ S A cm V b s := by
  simp only [H, S]
  apply totalWeight_mono
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.2⟩

/-- The committee union grows with the upper slot. -/
theorem committeeUnion_mono (cm : Committees n) (lo : Slot) {s s' : Slot} (h : s ≤ s') :
    committeeUnion cm lo s ⊆ committeeUnion cm lo s' := by
  unfold committeeUnion
  apply Finset.biUnion_subset_biUnion_of_subset_left
  exact Finset.Icc_subset_Icc_right h

/-- `W` is monotone in the upper slot. -/
theorem W_le_of_slot_le (A : Anchor n) (cm : Committees n) (b : Block n) {s s' : Slot}
    (h : s ≤ s') : W A cm b s ≤ W A cm b s' := by
  unfold W
  exact totalWeight_mono A (committeeUnion_mono cm b.psPlus1 h)

/-- A nonempty committee union has positive total weight. -/
theorem W_pos_of_nonempty_committee (A : Anchor n) (cm : Committees n) (b : Block n) (s : Slot)
    (hne : (committeeUnion cm b.psPlus1 s).Nonempty) : 0 < W A cm b s := by
  simpa [W] using totalWeight_pos A hne

/-- `slotOf (st s) = s` (slots round-trip through their start time). -/
theorem Timing.slotOf_st (τ : Timing) (s : Slot) : τ.slotOf (τ.st s) = s := by
  simp only [Timing.slotOf, Timing.st]
  exact Nat.mul_div_cancel s τ.hSlot

/-- The start instant of the slot containing `t` is at or before `t`. -/
theorem Timing.st_slotOf_le (τ : Timing) (t : Time) : τ.st (τ.slotOf t) ≤ t := by
  simp only [Timing.slotOf, Timing.st]
  exact Nat.div_mul_le_self t τ.slotDur

/-- `st` is monotone in the slot. -/
theorem Timing.st_le_st (τ : Timing) {s s' : Slot} (h : s ≤ s') : τ.st s ≤ τ.st s' := by
  simp only [Timing.st]
  exact Nat.mul_le_mul_right τ.slotDur h

end FastConfirmation.LMDGhost

end
