module
public import FastConfirmationProofs.Checkpoints.CheckpointEquivalence
public import FastConfirmationProofs.Checkpoints.CrossingCheckpointMargin
public import FastConfirmationProofs.Discount.ByzantineSiblingWeight
public import FastConfirmationProofs.Execution.Trajectory.InductionHypothesis

@[expose] public section

/-!
# Spec / Proof / LastAlgebra

Proves additive committee-weight bounds for the checkpoint edge safety argument.

This module contains `weight_add_sdiff`, `weight_add_le`, `hR4b_of_confinement` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## Set-weight `sdiff` algebra

The uniform-`σ = es` anchor makes every honest identity a growth split of the
window classes as `lo` widens from `sa` to `lo`. `weight_add_sdiff` is the single
`Finset.sum_sdiff` step it all rests on. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Weight splits as the base plus the growth (`sdiff`): `weight A + weight (B \ A)
= weight B` for `A ⊆ B`. -/
theorem weight_add_sdiff {A B : Finset ValidatorIndex} (h : A ⊆ B) :
    E.weight A + E.weight (B \ A) = E.weight B := by
  simp only [Execution.weight]
  rw [add_comm]
  exact Finset.sum_sdiff h



/-! ## `hJV` — supporter confinement -/


/-! ## `hXval` — the sibling-stuck window growth split -/


/-! ## `hR4b` — the V-span byz partition -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Superadditivity into a common superset over disjoint parts (local copy of the
`HonestWeight`/`Discount` private helper). -/
theorem weight_add_le {A B C : Finset ValidatorIndex}
    (hdisj : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    E.weight A + E.weight B ≤ E.weight C := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAC hBC)
    (fun _ _ _ => Nat.zero_le _)

/-- **`hR4b`** (VpreIdentities field 4). V-span byz partition: the byzantine
supporters of `b` plus the V-span equivocation score are within the V-span enemy
weight `Bval sa es`. This is the disjoint-into-`Bwin` half of
`HonestWeight.byz_plus_equiv_le` (before `span_bound`): byz supporters are
non-equivocating (`AttSupporters` filter) and confined to `span_committee sa es`
(`hspan`, from `supporter_mem_span_committee`); active equivocators are
`hne`-non-honest span members; the two are disjoint, both inside `Bwin sa es`. -/
theorem hR4b_of_confinement (hec : BeaconExternalsPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    {sa es : Slot}
    (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es ≤ E.Bval sa es := by
  rw [byz_score_eq_weight cfg hval,
    get_equivocation_score_eq_weight cfg ext hec hv n hnH hval sa es hesH]
  simp only [Execution.Bval, Execution.Bwin]
  refine E.weight_add_le ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨lm, _, hnoteq, _⟩ := mem_AttSupporters cfg hiBS.1
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnoteq hiEA.1.2
  · intro i hi
    simp only [List.mem_toFinset, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  · intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-! ## `hhead` — the head block-state slot bound -/


/-! ## `hcov` — the full-epoch coverage floor `total_active ≤ 2·Jspec` -/



/-! ## `hJfull` — the two-region honest partition -/




/-! ## `hBbadfin` — the full-window byz partition -/








end Execution

end FastConfirmation.Spec

end
