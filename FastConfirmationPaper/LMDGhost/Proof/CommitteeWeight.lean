module
public import Mathlib.Tactic
public import FastConfirmationPaper.LMDGhost.Model.Weights
public import FastConfirmationPaper.LMDGhost.Model.Assumptions

@[expose] public section

/-!
# LMDGhost / Proof / Weights

Foundational weight-decomposition lemmas: the committee-union weight `W` (and the
support weight `S`) split into honest and adversarial parts, and Assumption 2
(`CommitteeHonestMajority`) bounds the adversarial committee weight by `β · W`.
These feed the Lemma 3–4 algebra (`Q`-threshold ⇒ honest majority).
-/

namespace FastConfirmation.LMDGhost

variable {n : ℕ} {P : Type}

/-- The committee-union weight splits into its honest part (`J`) and adversarial part. -/
theorem W_eq_J_add_adv (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (b : Block n) (s : Slot) :
    W A cm b s = J A cm fm b s
      + totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i => i ∉ fm.honest)) := by
  simp only [W, J, totalWeight]
  exact (Finset.sum_filter_add_sum_filter_not (committeeUnion cm b.psPlus1 s)
    (fun i => i ∈ fm.honest) A.bal).symm

/-- The adversarial committee weight is at most `β · W` (Assumption 2). -/
theorem adv_committee_le (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (b : Block n) (s : Slot) (h : CommitteeHonestMajority fm cm A) :
    totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i => i ∉ fm.honest))
      ≤ fm.β * W A cm b s := by
  have hsplit := W_eq_J_add_adv A cm fm b s
  have hcm := h b.psPlus1 s
  have hW : W A cm b s = totalWeight A (committeeUnion cm b.psPlus1 s) := rfl
  simp only [J] at hsplit hcm
  rw [hW] at hsplit ⊢
  have key : (1 - fm.β) * totalWeight A (committeeUnion cm b.psPlus1 s)
      = totalWeight A (committeeUnion cm b.psPlus1 s)
        - fm.β * totalWeight A (committeeUnion cm b.psPlus1 s) := by ring
  linarith [hsplit, hcm, key]

/-- The support weight `S` splits into its honest part (`H`) and adversarial part. -/
theorem S_eq_H_add_adv (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b : Block n) (s : Slot) :
    S A cm V b s = H A cm fm V b s
      + totalWeight A (((committeeUnion cm b.psPlus1 s).filter
          (fun i => V.supportsLMD b i s = true)).filter (fun i => i ∉ fm.honest)) := by
  have hset :
      (committeeUnion cm b.psPlus1 s).filter (fun i => i ∈ fm.honest ∧ V.supportsLMD b i s = true)
        = ((committeeUnion cm b.psPlus1 s).filter
            (fun i => V.supportsLMD b i s = true)).filter (fun i => i ∈ fm.honest) := by
    ext i; simp only [Finset.mem_filter]; tauto
  simp only [S, H, totalWeight, hset]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- Adversarial support weight is at most adversarial committee weight (supporters
    are a subset of the committee union; balances are nonneg). -/
theorem adv_support_le_committee (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) :
    totalWeight A (((committeeUnion cm b.psPlus1 s).filter
        (fun i => V.supportsLMD b i s = true)).filter (fun i => i ∉ fm.honest))
      ≤ totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i => i ∉ fm.honest)) := by
  simp only [totalWeight]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => le_of_lt (A.hpos i))
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1.1, hi.2⟩

/-- Support weight is at most committee weight (supporters ⊆ committee union). -/
theorem S_le_W (A : Anchor n) (cm : Committees n) (V : View n P) (b : Block n) (s : Slot) :
    S A cm V b s ≤ W A cm b s := by
  simp only [S, W, totalWeight]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => le_of_lt (A.hpos i))

/-- The adversarial support weight is at most `β · W` (chains `adv_support_le_committee`
    and `adv_committee_le`). -/
theorem adv_support_le_beta (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) (h : CommitteeHonestMajority fm cm A) :
    totalWeight A (((committeeUnion cm b.psPlus1 s).filter
        (fun i => V.supportsLMD b i s = true)).filter (fun i => i ∉ fm.honest))
      ≤ fm.β * W A cm b s :=
  le_trans (adv_support_le_committee A cm fm V b s) (adv_committee_le A cm fm b s h)

end FastConfirmation.LMDGhost

end
