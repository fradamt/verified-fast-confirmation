import Mathlib.Tactic
import FastConfirmation.Paper.LMDGhost.Proof.Support
import FastConfirmation.Paper.LMDGhost.Proof.Positivity

/-!
# LMDGhost / Proof / Monotone

Lemma 1 building blocks: how the committee weight `W` and honest committee weight
`J` grow with the cutoff slot, and the support-set monotonicity that makes the
honest support weight `H` non-decreasing.

The key arithmetic fact (`P_nondecreasing`) is **Lemma 1** in its faithful Def-7
form: the honest LMD-GHOST safety indicator `Phon = H/J` never decreases as the
cutoff grows, provided base supporters persist and every newly-counted honest
committee member supports `b'`. Writing `a = H_{σ₀}`, `b = J_{σ₀}`, and `gH` for the
honest weight of the committee growth set, `J_σ = b + gH` (exactly) while
`H_σ ≥ a + gH`, so `Phon_σ = H_σ/J_σ ≥ (a+gH)/(b+gH) ≥ a/b = Phon_{σ₀}`, the last
step needing only `a ≤ b`, i.e. `H ≤ J` (a free fact — `H_le_J`). **No growth bound
on the adversary is needed** — this is precisely why `HonestGrowth` is unnecessary
and the absolute-margin route was the wrong one: recurring honest validators dedup
identically on numerator and denominator, and adversarial weight never enters `J`.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- `committeeUnion` over `[lo, s']` decomposes into `[lo, s]` plus the growth set. -/
theorem committeeUnion_subset_growth (cm : Committees n) (lo : Slot) {s s' : Slot}
    (h : s ≤ s') :
    committeeUnion cm lo s ⊆ committeeUnion cm lo s' :=
  committeeUnion_mono cm lo h

/-- `J` is monotone in the upper slot (honest committee weight grows). -/
theorem J_le_of_slot_le (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (b : Block n)
    {s s' : Slot} (h : s ≤ s') : J A cm fm b s ≤ J A cm fm b s' := by
  unfold J
  apply totalWeight_mono
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨committeeUnion_mono cm b.psPlus1 h hi.1, hi.2⟩

/-- `W` decomposes as the value at `s` plus the weight of the committee growth set. -/
theorem W_eq_add_growth (A : Anchor n) (cm : Committees n) (b : Block n) {s s' : Slot}
    (h : s ≤ s') :
    W A cm b s' = W A cm b s
      + totalWeight A (committeeUnion cm b.psPlus1 s' \ committeeUnion cm b.psPlus1 s) := by
  unfold W totalWeight
  rw [add_comm]
  exact (Finset.sum_sdiff (committeeUnion_mono cm b.psPlus1 h)).symm

/-- `J` decomposes as the value at `s` plus the honest weight of the committee growth set. -/
theorem J_eq_add_growth (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (b : Block n)
    {s s' : Slot} (h : s ≤ s') :
    J A cm fm b s' = J A cm fm b s
      + totalWeight A ((committeeUnion cm b.psPlus1 s' \ committeeUnion cm b.psPlus1 s).filter
          (fun i => i ∈ fm.honest)) := by
  unfold J totalWeight
  have hset : (committeeUnion cm b.psPlus1 s' \ committeeUnion cm b.psPlus1 s).filter
        (fun i => i ∈ fm.honest)
      = (committeeUnion cm b.psPlus1 s').filter (fun i => i ∈ fm.honest)
          \ (committeeUnion cm b.psPlus1 s).filter (fun i => i ∈ fm.honest) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [add_comm, hset]
  exact (Finset.sum_sdiff (Finset.filter_subset_filter _
    (committeeUnion_mono cm b.psPlus1 h))).symm

/-- Honest support `H` grows by at least the honest weight of the committee growth
    set, when base supporters persist and all new honest committee members support `b'`. -/
theorem H_ge_add_growth (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b' : Block n) {σ₀ σ : Slot} (hσ : σ₀ ≤ σ)
    (hpersist : ∀ i ∈ committeeUnion cm b'.psPlus1 σ₀, i ∈ fm.honest →
      V.supportsLMD b' i σ₀ = true → V.supportsLMD b' i σ = true)
    (hcanon : ∀ i ∈ committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀,
      i ∈ fm.honest → V.supportsLMD b' i σ = true) :
    H A cm fm V b' σ₀
      + totalWeight A ((committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀).filter
          (fun i => i ∈ fm.honest))
      ≤ H A cm fm V b' σ := by
  set U₀ := committeeUnion cm b'.psPlus1 σ₀ with hU₀
  set U := committeeUnion cm b'.psPlus1 σ with hU
  have hsub : U₀ ⊆ U := committeeUnion_mono cm b'.psPlus1 hσ
  -- The base honest-supporter set, the honest growth set, and their disjoint union.
  set B₀ := U₀.filter (fun i => i ∈ fm.honest ∧ V.supportsLMD b' i σ₀ = true) with hB₀
  set Gh := (U \ U₀).filter (fun i => i ∈ fm.honest) with hGh
  have hdisj : Disjoint B₀ Gh := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hB₀, hGh, Finset.mem_filter, Finset.mem_sdiff] at hi hi'
    exact hi'.1.2 hi.1
  have hunion_sub : B₀ ∪ Gh ⊆ U.filter (fun i => i ∈ fm.honest ∧ V.supportsLMD b' i σ = true) := by
    intro i hi
    simp only [Finset.mem_union, hB₀, hGh, Finset.mem_filter, Finset.mem_sdiff] at hi
    simp only [Finset.mem_filter]
    rcases hi with ⟨hiU₀, hih, hisup⟩ | ⟨⟨hiU, hni⟩, hih⟩
    · exact ⟨hsub hiU₀, hih, hpersist i hiU₀ hih hisup⟩
    · exact ⟨hiU, hih, hcanon i (Finset.mem_sdiff.mpr ⟨hiU, hni⟩) hih⟩
  have hHeq : H A cm fm V b' σ₀ = totalWeight A B₀ := rfl
  have hkey : H A cm fm V b' σ₀ + totalWeight A Gh = totalWeight A (B₀ ∪ Gh) := by
    rw [hHeq]
    simp only [totalWeight, Finset.sum_union hdisj]
  rw [hkey]
  unfold H totalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hunion_sub (fun i _ _ => (A.hpos i).le)

/-- **Lemma 1 (Def-7 form): `Phon` is non-decreasing in the cutoff.** Given the base
    honest committee weight is positive (`hJpos`), base supporters persist, and every
    newly-counted honest committee member supports `b'`, the honest LMD-GHOST safety
    indicator `Phon_{σ₀} = H_{σ₀}/J_{σ₀}` does not exceed `Phon_σ`. The proof is the
    `(a+gH)/(b+gH) ≥ a/b` argument with `a = H_{σ₀}`, `b = J_{σ₀}`, `gH` the honest
    growth-set weight: `J_σ = b + gH` exactly, `H_σ ≥ a + gH`, and `a ≤ b` (`H_le_J`).
    **No adversarial-growth premise.** -/
theorem P_nondecreasing (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b' : Block n) {σ₀ σ : Slot} (hσ : σ₀ ≤ σ)
    (hJpos : 0 < J A cm fm b' σ₀)
    (hpersist : ∀ i ∈ committeeUnion cm b'.psPlus1 σ₀, i ∈ fm.honest →
      V.supportsLMD b' i σ₀ = true → V.supportsLMD b' i σ = true)
    (hcanon : ∀ i ∈ committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀,
      i ∈ fm.honest → V.supportsLMD b' i σ = true) :
    Phon A cm fm V b' σ₀ ≤ Phon A cm fm V b' σ := by
  -- `a = H_{σ₀}`, `b = J_{σ₀}`, `gH` = honest growth-set weight.
  set gH := totalWeight A ((committeeUnion cm b'.psPlus1 σ \ committeeUnion cm b'.psPlus1 σ₀).filter
      (fun i => i ∈ fm.honest)) with hgH
  have hgH0 : 0 ≤ gH := totalWeight_nonneg A _
  have hHgrow : H A cm fm V b' σ₀ + gH ≤ H A cm fm V b' σ :=
    H_ge_add_growth A cm fm V b' hσ hpersist hcanon
  have hJeq : J A cm fm b' σ = J A cm fm b' σ₀ + gH :=
    J_eq_add_growth A cm fm b' hσ
  have hHJ0 : H A cm fm V b' σ₀ ≤ J A cm fm b' σ₀ := H_le_J A cm fm V b' σ₀
  have hJσpos : 0 < J A cm fm b' σ := by rw [hJeq]; linarith [hgH0]
  -- `Phon_{σ₀} = H_{σ₀}/J_{σ₀} ≤ H_σ/J_σ = Phon_σ`.
  change H A cm fm V b' σ₀ / J A cm fm b' σ₀ ≤ H A cm fm V b' σ / J A cm fm b' σ
  rw [div_le_div_iff₀ hJpos hJσpos, hJeq]
  -- `H_{σ₀}·(J_{σ₀} + gH) ≤ H_σ·J_{σ₀}`, using `H_σ ≥ H_{σ₀} + gH` and `H_{σ₀} ≤ J_{σ₀}`.
  nlinarith [hHgrow, hHJ0, hgH0, hJpos.le]

end FastConfirmation.LMDGhost
