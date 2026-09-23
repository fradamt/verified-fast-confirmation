module
public import FastConfirmationProofs.ForkChoice.Head.HeadMembership
public import FastConfirmationProofs.Execution.Trajectory.LatestMessageProvenance
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Gloas.Payload.MajorityPersists
public import FastConfirmationProofs.Discount.RecordedSupport

@[expose] public section

/-!
# Spec / Proof / EngineBudget

This module contains `weight_mono` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Set-weight monotonicity and superadditivity -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Ground-truth weight is monotone under `Finset` inclusion (the effective
balances are nonnegative). -/
theorem weight_mono {E : Execution Root} {A B : Finset ValidatorIndex} (h : A ⊆ B) :
    E.weight A ≤ E.weight B := by
  simp only [Execution.weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)


/-! ## result 1 — sibling window confinement

Every supporter of the sibling `c'` at a store carrying `LatestMessageProvenance`
lies in the ground-truth span committee `[c'.slot, current_slot − 1]`. This is
`supporter_mem_span_committee` instantiated at `b := c'` with the span start
pushed all the way up to `c'`'s own slot (`sa = (blocks c').slot`): the pre-fork
zero-contribution argument (a slot-`t` member with `t < c'.slot` has a
vote-block of slot `≤ t < c'.slot`, which `c'` cannot descend from) is precisely
the `get_ancestor_slot_le` slot chain inside that lemma. -/


/-! ## result 2 (upper half) — the sibling score is bounded by the window estimate

`c'`'s recorded score is the ground-truth weight of its supporter set
(`attestation_score_eq_weight`); that set is confined to the span committee
`[c'.slot, k−1]` (result 1), whose weight the estimate bounds
(`ByzantineWeightPremises.estimate_sound`). Hence the sibling score never exceeds the
union-window committee estimate — the top of the `hsib` ledger's right-hand
side. -/


/-! ## Set-weight honest/Byzantine split

The span committee's weight splits into its honest and non-honest parts. -/


/-! ## result 2 (disjointness) — the sibling avoids `b`'s support

`MajorityPersists.supporters_disjoint` already gives that the two siblings'
supporter sets are disjoint. Since the old honest supporter set `HS₀` supports
the `b`-side child `c` (via `SupportTransport` / `EngineSupport`), it sits inside
`c`'s supporter set, hence is disjoint from `c'`'s. This is the disjointness the
additive `hsib` ledger needs between the sibling and `b`'s recorded support. -/







end FastConfirmation.Spec

/-!
# Spec / Proof / EngineWindows — shared slot-window / set-weight helpers

This module contains `weight_union_le`, `span_committee_subset_union`, `span_committee_mono_lo` and related declarations.
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


end FastConfirmation.Spec

end
