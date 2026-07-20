import Mathlib.Tactic
import FastConfirmation.Paper.LMDGhost.Proof.Weights
import FastConfirmation.Paper.LMDGhost.Proof.Positivity
import FastConfirmation.Paper.LMDGhost.Model.Confirm

/-!
# LMDGhost / Proof / Quorum

Lemmas 3–4 (combined): the `Q`-threshold of Definition 8 implies an honest
majority `H_b > (W_b + W_p)/2`. Proof: with `W > 0`, `Q > ½(1 + W_p/W) + β`
gives `S > ½(W + W_p) + βW`; since `H = S − S_adv` and `S_adv ≤ βW`
(Assumption 2), `H > ½(W + W_p)`. This honest majority is exactly what the
GHOST canonicality lemma (Lemma 2) consumes.

The **P = H/J reformulation** (faithful to Def 7) factors this through the honest
LMD-GHOST safety indicator `P_b = H_b / J_b`:

* `P_base_of_Q` (Lemma 4): the `Q`-threshold implies the P-lower-bound
  `P_b > (1/(2(1−β)))·(1 + W_p/W_b)`. This is the recurrence-robust quantity the
  Lemma 6 induction maintains (it never decreases as the cutoff grows — see
  `P_nondecreasing` — because it needs only `H ≤ J`, not an adversarial-growth bound).
* `Hmargin_of_P` (Lemma 3): the P-bound, together with Assumption 2 (`J ≥ (1−β)W`),
  converts back to the absolute honest margin `H_b > (W_b + W_p)/2` at the point where
  GHOST canonicality (Lemma 2) needs it. The `(1−β)` from Assumption 2 exactly cancels
  the `1/(2(1−β))` in the P-bound.
-/

namespace FastConfirmation.LMDGhost

variable {n : ℕ} {P : Type}

/-- If the `Q`-threshold holds then the committee-union weight is strictly positive
    (otherwise `Q = 0` while the threshold is `≥ 1/2`). -/
theorem W_pos_of_Q_threshold (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) (pb : Weight)
    (hQ : Q A cm V b s > (1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β) :
    0 < W A cm b s := by
  rcases lt_or_eq_of_le (totalWeight_nonneg A (committeeUnion cm b.psPlus1 s)) with h | h
  · exact h
  · exfalso
    have hW0 : W A cm b s = 0 := h.symm
    rw [show Q A cm V b s = S A cm V b s / W A cm b s from rfl, hW0,
      div_zero, div_zero] at hQ
    have hβ0 := fm.hβ0
    norm_num at hQ
    linarith

/-- **Lemmas 3–4 (combined).** The `Q`-threshold implies the honest-majority bound. -/
theorem Q_imp_H_majority (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) (pb : Weight)
    (hcm : CommitteeHonestMajority fm cm A) (hW : 0 < W A cm b s)
    (hQ : Q A cm V b s > (1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β) :
    H A cm fm V b s > (W A cm b s + Wp A pb) / 2 := by
  have hWne : W A cm b s ≠ 0 := ne_of_gt hW
  have hSsplit := S_eq_H_add_adv A cm fm V b s
  have hSa := adv_support_le_beta A cm fm V b s hcm
  rw [gt_iff_lt, show Q A cm V b s = S A cm V b s / W A cm b s from rfl,
    lt_div_iff₀ hW] at hQ
  have h3 : ((1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β) * W A cm b s
      = (W A cm b s + Wp A pb) / 2 + fm.β * W A cm b s := by
    field_simp
  rw [h3] at hQ
  linarith [hSsplit, hSa, hQ]

/-- **Monotone-`g` helper** (the one piece of new division algebra in Lemma 4). For
    `0 ≤ A ≤ βW`, `S ≤ W`, and `1 − β > 0` (so `W − βW = (1−β)W ≥ 0`), the map
    `g(x) = (S − x)/(W − x)` is decreasing: `(S − A)/(W − A) ≥ (S − βW)/(W − βW)`.
    The cross-difference `(S − A)(W − βW) − (S − βW)(W − A) = (βW − A)(W − S)` is a
    product of two nonnegatives. -/
theorem g_mono_helper {S W A β : Weight}
    (hβ1 : (0 : Weight) < 1 - β) (hA0 : 0 ≤ A) (hAβ : A ≤ β * W)
    (hSW : S ≤ W) (hW0 : 0 < W) :
    (S - β * W) / (W - β * W) ≤ (S - A) / (W - A) := by
  have hβ0 : 0 ≤ β := by nlinarith [hW0]
  have hWβ : 0 < W - β * W := by nlinarith [hβ1, hW0]
  have hWA : 0 < W - A := by
    have : β * W ≤ W := by nlinarith [hβ0, hW0, hβ1]
    linarith [hAβ, this]
  rw [div_le_div_iff₀ hWβ hWA]
  -- `(S − βW)(W − A) ≤ (S − A)(W − βW)`, i.e. `0 ≤ (βW − A)(W − S)`.
  nlinarith [mul_nonneg (sub_nonneg.mpr hAβ) (sub_nonneg.mpr hSW)]

/-- **Lemma 4 (Q ⇒ P-lower-bound).** Given Assumption 2 (via `hcm`), the `Q`-threshold
    of Definition 8 forces the honest LMD-GHOST safety indicator `P_b = H_b/J_b` above
    `(1/(2(1−β)))·(1 + W_p/W_b)`. This is the recurrence-robust quantity the head-safety
    induction maintains. Faithful to the paper's Lemma 4 chain
    `P = H/J ≥ (S−A)/(W−A) ≥ (S−βW)/(W−βW) = (Q−β)/(1−β) > (1/(2(1−β)))(1+W_p/W)`. -/
theorem P_base_of_Q (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) (pb : Weight)
    (hcm : CommitteeHonestMajority fm cm A) (hW : 0 < W A cm b s)
    (hQ : Q A cm V b s > (1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β) :
    Phon A cm fm V b s > (1 / (2 * (1 - fm.β))) * (1 + Wp A pb / W A cm b s) := by
  have hβ1 : (0 : Weight) < 1 - fm.β := by have := fm.hβ; linarith
  -- abbreviations
  set Wb := W A cm b s with hWb
  set Sb := S A cm V b s with hSb
  set Hb := H A cm fm V b s with hHb
  set Jb := J A cm fm b s with hJb
  set Ac := totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i => i ∉ fm.honest)) with hAc
  -- structural facts
  have hWsplit : Wb = Jb + Ac := W_eq_J_add_adv A cm fm b s
  have hAβ : Ac ≤ fm.β * Wb := adv_committee_le A cm fm b s hcm
  have hA0 : 0 ≤ Ac := totalWeight_nonneg A _
  have hSW : Sb ≤ Wb := S_le_W A cm V b s
  have hSsplit : Sb = Hb + totalWeight A (((committeeUnion cm b.psPlus1 s).filter
      (fun i => V.supportsLMD b i s = true)).filter (fun i => i ∉ fm.honest)) :=
    S_eq_H_add_adv A cm fm V b s
  have hadvS := adv_support_le_committee A cm fm V b s
  -- `H ≥ S − Ac` and `J = W − Ac`.
  have hHge : Sb - Ac ≤ Hb := by nlinarith [hadvS, hSsplit]
  have hJeq : Jb = Wb - Ac := by linarith [hWsplit]
  have hJpos : 0 < Jb := by rw [hJeq]; nlinarith [hAβ, hβ1, hW]
  have hWAc : 0 < Wb - Ac := by rw [← hJeq]; exact hJpos
  -- Phon = H/J ≥ (S − Ac)/(W − Ac) ≥ (S − βW)/(W − βW)
  have hstep1 : (Sb - Ac) / (Wb - Ac) ≤ Hb / Jb := by
    rw [hJeq]; exact (div_le_div_iff_of_pos_right hWAc).mpr hHge
  have hstep2 : (Sb - fm.β * Wb) / (Wb - fm.β * Wb) ≤ (Sb - Ac) / (Wb - Ac) :=
    g_mono_helper hβ1 hA0 hAβ hSW hW
  -- `(S − βW)/(W − βW) = (Q − β)/(1 − β)`, and `Q > ½(1 + Wp/W) + β` gives the bound.
  have hQval : Q A cm V b s = Sb / Wb := rfl
  have hWne : Wb ≠ 0 := ne_of_gt hW
  -- threshold: `(1/(2(1−β)))·(1 + Wp/W)`.
  set thr := (1 / 2) * (1 + Wp A pb / Wb) with hthr
  have hQthr : Sb / Wb > thr + fm.β := by rw [hthr]; exact hQ
  -- `(S − βW)/(W − βW) = (S/W − β)/(1 − β)`.
  have heq3 : (Sb - fm.β * Wb) / (Wb - fm.β * Wb) = (Sb / Wb - fm.β) / (1 - fm.β) := by
    rw [div_eq_div_iff (by nlinarith [hβ1, hW]) (ne_of_gt hβ1)]
    field_simp
  -- `(S/W − β)/(1 − β) > thr/(1 − β)` since `S/W − β > thr`.
  have hgt : thr / (1 - fm.β) < (Sb / Wb - fm.β) / (1 - fm.β) := by
    rw [div_lt_div_iff_of_pos_right hβ1]
    linarith [hQthr]
  -- `thr/(1 − β) = (1/(2(1−β)))·(1 + Wp/W)`.
  have heqthr : thr / (1 - fm.β) = (1 / (2 * (1 - fm.β))) * (1 + Wp A pb / Wb) := by
    rw [hthr]; field_simp
  -- assemble.
  change (1 / (2 * (1 - fm.β))) * (1 + Wp A pb / Wb) < Phon A cm fm V b s
  have hPeq : Phon A cm fm V b s = Hb / Jb := rfl
  rw [hPeq, ← heqthr]
  calc thr / (1 - fm.β)
      < (Sb / Wb - fm.β) / (1 - fm.β) := hgt
    _ = (Sb - fm.β * Wb) / (Wb - fm.β * Wb) := heq3.symm
    _ ≤ (Sb - Ac) / (Wb - Ac) := hstep2
    _ ≤ Hb / Jb := hstep1

/-- If the P-threshold holds then the committee-union weight is strictly positive
    (otherwise `Wp/W = 0` and `Phon = H/J`; but `J = 0` too when `W = 0`, giving
    `Phon = 0`, which cannot exceed the threshold `≥ 1/(2(1−β)) > 0`). -/
theorem W_pos_of_P_threshold (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) (pb : Weight)
    (hP : Phon A cm fm V b s > (1 / (2 * (1 - fm.β))) * (1 + Wp A pb / W A cm b s)) :
    0 < W A cm b s := by
  have hβ1 : (0 : Weight) < 1 - fm.β := by have := fm.hβ; linarith
  rcases lt_or_eq_of_le (totalWeight_nonneg A (committeeUnion cm b.psPlus1 s)) with h | h
  · exact h
  · exfalso
    have hW0 : W A cm b s = 0 := h.symm
    -- `W = 0 ⇒ J = 0` (J ≤ W) ⇒ `Phon = H/0 = 0`.
    have hJ0 : J A cm fm b s = 0 :=
      le_antisymm (le_trans (J_le_W A cm fm b s) (le_of_eq hW0)) (totalWeight_nonneg A _)
    have hP0 : Phon A cm fm V b s = 0 := by
      rw [show Phon A cm fm V b s = H A cm fm V b s / J A cm fm b s from rfl, hJ0, div_zero]
    rw [hP0, hW0, div_zero, add_zero, mul_one] at hP
    have : (0 : Weight) < 1 / (2 * (1 - fm.β)) := by positivity
    linarith

/-- **Lemma 3 (P ⇒ H-margin).** Given Assumption 2 (`J ≥ (1−β)W`), the P-lower-bound
    `Phon > (1/(2(1−β)))·(1 + Wp/W)` converts to the absolute honest margin
    `H > (W + Wp)/2`. The `(1−β)` from Assumption 2 exactly cancels the `1/(2(1−β))`
    in the P-bound: `H = Phon·J > (1/(2(1−β)))(1+Wp/W)·(1−β)W = (W+Wp)/2`. -/
theorem Hmargin_of_P (A : Anchor n) (cm : Committees n) (fm : FaultModel n)
    (V : View n P) (b : Block n) (s : Slot) (pb : Weight)
    (hcm : CommitteeHonestMajority fm cm A)
    (hpb : 0 ≤ pb)
    (hP : Phon A cm fm V b s > (1 / (2 * (1 - fm.β))) * (1 + Wp A pb / W A cm b s)) :
    H A cm fm V b s > (W A cm b s + Wp A pb) / 2 := by
  have hβ1 : (0 : Weight) < 1 - fm.β := by have := fm.hβ; linarith
  have hW : 0 < W A cm b s := W_pos_of_P_threshold A cm fm V b s pb hP
  have hWne : W A cm b s ≠ 0 := ne_of_gt hW
  -- `J ≥ (1−β)W > 0`.
  have hJW : (1 - fm.β) * W A cm b s ≤ J A cm fm b s := by
    have := hcm b.psPlus1 s; simpa [W, J] using this
  have hJpos : 0 < J A cm fm b s := by nlinarith [hJW, hβ1, hW]
  -- `H = Phon · J`.
  have hHeq : H A cm fm V b s = Phon A cm fm V b s * J A cm fm b s := by
    rw [show Phon A cm fm V b s = H A cm fm V b s / J A cm fm b s from rfl,
      div_mul_cancel₀ _ (ne_of_gt hJpos)]
  -- the threshold coefficient `1 + Wp/W ≥ 0`.
  have hWpnn : 0 ≤ Wp A pb := mul_nonneg hpb (totalWeight_nonneg A _)
  have hcoef : 0 ≤ 1 + Wp A pb / W A cm b s := by positivity
  -- `Phon · J ≥ (1/(2(1−β)))(1+Wp/W) · (1−β)W`.
  set thr := (1 / (2 * (1 - fm.β))) * (1 + Wp A pb / W A cm b s) with hthr
  have hthr_nn : 0 ≤ thr := by rw [hthr]; positivity
  -- `thr · (1−β)W = (W + Wp)/2`.
  have hval : thr * ((1 - fm.β) * W A cm b s) = (W A cm b s + Wp A pb) / 2 := by
    rw [hthr]
    field_simp
  -- `(W+Wp)/2 = thr·(1−β)W ≤ thr·J < Phon·J = H`.
  have hstrict : thr * J A cm fm b s < Phon A cm fm V b s * J A cm fm b s :=
    mul_lt_mul_of_pos_right hP hJpos
  have hge : thr * ((1 - fm.β) * W A cm b s) ≤ thr * J A cm fm b s :=
    mul_le_mul_of_nonneg_left hJW hthr_nn
  rw [hval] at hge
  rw [hHeq]
  linarith [hstrict, hge]

/-- **Definition 8 ⇒ honest majority.** A one-confirmed block has an honest majority
    at cutoff `slotOf t - 1` (combines `W_pos_of_Q_threshold` and `Q_imp_H_majority`). -/
theorem Hmaj_of_isOneConfirmed (τ : Timing) (A : Anchor n) (cm : Committees n)
    (fm : FaultModel n) (pb : Weight) (V : View n P) (b : Block n) (t : Time)
    (hcm : CommitteeHonestMajority fm cm A)
    (h1c : isOneConfirmed τ fm cm pb A V b t) :
    H A cm fm V b (τ.slotOf t - 1) > (W A cm b (τ.slotOf t - 1) + Wp A pb) / 2 := by
  unfold isOneConfirmed safetyThreshold at h1c
  have hW := W_pos_of_Q_threshold A cm fm V b (τ.slotOf t - 1) pb h1c
  exact Q_imp_H_majority A cm fm V b (τ.slotOf t - 1) pb hcm hW h1c

end FastConfirmation.LMDGhost
