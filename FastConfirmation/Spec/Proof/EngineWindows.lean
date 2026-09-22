module
public import FastConfirmation.Spec.Proof.EngineBudget
public import FastConfirmation.Spec.Proof.EngineSupport

@[expose] public section

/-!
# Spec / Proof / EngineWindows — shared slot-window / set-weight helpers

Pure `Finset` and `span_committee` weight helpers used by `StepDischarge`,
`ByzVpre`, `Endpoint`, `LastAlgebra`, `Reanchor`, and `LedgerV2`:

* **`weight_union_le`** — set-weight subadditivity over a union.
* **`span_committee_subset_union` / `span_committee_mono_lo`** — the slot-window
  covering and lower-bound-widening facts for `span_committee`.
* **`weight_span_committee_split`** — the union window's weight is at most the sum
  of the two sub-window weights.
* **`weight_add4_le`** — four-disjoint-parts superadditivity into a common
  superset (the four-way analogue of `EngineBudget.weight_add3_le`).

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Set-weight subadditivity and the slot-window covering -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Ground-truth weight is subadditive over a union (the intersection is counted
once, the effective balances are nonnegative). -/
theorem weight_union_le {E : Execution Root} (A B : Finset ValidatorIndex) :
    E.weight (A ∪ B) ≤ E.weight A + E.weight B := by
  have h : (∑ i ∈ A ∪ B, E.weight_of i) + ∑ i ∈ A ∩ B, E.weight_of i
      = (∑ i ∈ A, E.weight_of i) + ∑ i ∈ B, E.weight_of i := Finset.sum_union_inter
  change (∑ i ∈ A ∪ B, E.weight_of i)
    ≤ (∑ i ∈ A, E.weight_of i) + ∑ i ∈ B, E.weight_of i
  exact le_trans (Nat.le_add_right _ _) (le_of_eq h)

omit [LinearOrder Root] [Inhabited Root] in
/-- The union window `[lo, hi]`'s committee is covered by the old window
`[lo, mid − 1]` and the new window `[mid, hi]` — a slot `t ∈ [lo, hi]` is either
below `mid` (old) or at/above it (new). Holds unconditionally (truncated
subtraction handles the `mid = 0` edge: every slot lands in the new window). -/
theorem span_committee_subset_union {E : Execution Root} (lo mid hi : Slot) :
    E.span_committee lo hi ⊆
      E.span_committee lo (mid - 1) ∪ E.span_committee mid hi := by
  intro i hmem
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc,
    Finset.mem_union] at hmem ⊢
  obtain ⟨t, ⟨hlo, hhi⟩, hc⟩ := hmem
  by_cases hts : t < mid
  · exact Or.inl ⟨t, ⟨hlo, Nat.le_sub_one_of_lt hts⟩, hc⟩
  · exact Or.inr ⟨t, ⟨Nat.le_of_not_lt hts, hhi⟩, hc⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- Widening a span committee's lower slot bound only adds members. -/
theorem span_committee_mono_lo {E : Execution Root} {lo lo' hi : Slot} (h : lo ≤ lo') :
    E.span_committee lo' hi ⊆ E.span_committee lo hi := by
  intro i hmem
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hmem ⊢
  obtain ⟨t, ⟨hl, hr⟩, hc⟩ := hmem
  exact ⟨t, ⟨le_trans h hl, hr⟩, hc⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- **Window split.** The union window's weight is at most the sum of the old and
new sub-windows' weights (covering + subadditivity). -/
theorem weight_span_committee_split {E : Execution Root} (lo mid hi : Slot) :
    E.weight (E.span_committee lo hi) ≤
      E.weight (E.span_committee lo (mid - 1)) + E.weight (E.span_committee mid hi) :=
  le_trans (weight_mono (span_committee_subset_union lo mid hi)) (weight_union_le _ _)

/-! ## Four-disjoint-parts superadditivity

The four-way analogue of `EngineBudget.weight_add3_le`: sibling supporters, `b`'s
old honest support, the fork-parent stuck set, and the new-window honest
committee are pairwise disjoint subsets of the union window `U`, so their weights
sum to at most `weight U`. The new-window honest committee is the fourth part —
its weight cancels against the honest half of the new window on the estimate
side, which is what turns `weight U ≤ Wold + Bnew + Hnew` into the ledger's
`sib + H0 + D ≤ Wold + Bnew`. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Superadditivity into a common superset over four pairwise-disjoint parts. -/
theorem weight_add4_le {E : Execution Root} {A B C F U : Finset ValidatorIndex}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAF : Disjoint A F)
    (hBC : Disjoint B C) (hBF : Disjoint B F) (hCF : Disjoint C F)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hCU : C ⊆ U) (hFU : F ⊆ U) :
    E.weight A + E.weight B + E.weight C + E.weight F ≤ E.weight U := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hAB]
  rw [← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)]
  rw [← Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hAF, hBF⟩, hCF⟩)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset hAU hBU) hCU) hFU

end FastConfirmation.Spec

end
