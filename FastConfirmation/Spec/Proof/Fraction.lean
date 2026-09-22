module
public import FastConfirmation.Spec.Proof.Registry
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# Spec / Proof / Fraction

Port of the fraction-invariant engine accounting in
`FastConfirmation/Paper/LMDGhost/Model/Weights.lean` and
`FastConfirmation/Paper/LMDGhost/Proof/Monotone.lean` to the spec side, in **ℕ,
cross-multiplied** (the paper works in ℚ; ground-truth weights are `Gwei = ℕ`).

The paper's Lemma 1 maintains the **fraction** `Phon = H / J` (honest supporters
over honest committee-union weight, per-validator over the growing window
`[a, b]`): `J_{b'} = J_b + g` exactly and `H_{b'} ≥ H_b + g` (every newly-counted
honest committee member supports the block), so `(H_b+g)/(J_b+g) ≥ H_b/J_b`.
Recurring validators dedup identically on numerator and denominator, so the
cross-epoch seat-overlap problem cannot arise; **adversarial weight never enters
the invariant**.

Ground-truth quantities (all over `E.span_committee`, `E.weight`, `E.honest`):

* `Jspec E a b` — honest committee-union weight over `[a, b]` (paper `J`).
* `Hspec E a b sup` — honest weight of those *also* satisfying an abstract
  supporter predicate `sup` (paper `H`; kept store-agnostic via `sup`).

The pieces: growth decompositions (`Jspec_eq_add_growth`, `Hspec_ge_add_growth`),
the pure-ℕ cross-multiplied fraction step (`frac_cross`), and the assembled
fraction monotonicity (`Pspec_nondecreasing`).

The absolute-margin endpoint
(`Hmargin_of_fraction`/`Hmargin_of_confirmed`) and its `honest_span_majority`
rearrangement (`two_W_lt_three_J`) use a
committee Byzantine fraction `β = 1/3` that mismatched the confirmation's own
`β = CONFIRMATION_BYZANTINE_THRESHOLD/100 ≤ 1/4` reservation (the β-mismatch that
blocks the strong `Phon ≥ 3/4` base). The INV\* ledger
(`FastConfirmation/Spec/Proof/Ledger.lean` and `FastConfirmation/Spec/Proof/Base.lean`)
instead uses a single min-potential invariant
consuming the revised `ByzantineBound.span_fraction` directly, so no
absolute-margin conversion is needed here. This module now exports only the
reusable growth/monotonicity machinery INV\* reuses.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the ground-truth fraction quantities -/

/-- `J_b`: honest committee-union weight over the slot span `[a, b]` (paper `J`,
`Weights.lean`). -/
def Jspec (a b : Slot) : Gwei :=
  E.weight ((E.span_committee a b).filter (fun i => i ∈ E.honest))

/-- `H_b`: honest weight of the committee-union validators over `[a, b]` that
*also* satisfy the abstract supporter predicate `sup` (paper `H`). Kept
store-agnostic via `sup : ValidatorIndex → Prop` so the engine instantiates it
with the concrete "recorded latest message supports node `c`" predicate. -/
def Hspec (a b : Slot) (sup : ValidatorIndex → Prop) [DecidablePred sup] : Gwei :=
  E.weight ((E.span_committee a b).filter (fun i => i ∈ E.honest ∧ sup i))

omit [LinearOrder Root] [Inhabited Root] in
/-- The span committee grows with the upper slot (paper `committeeUnion_mono`). -/
theorem span_committee_mono (a : Slot) {b b' : Slot} (h : b ≤ b') :
    E.span_committee a b ⊆ E.span_committee a b' := by
  simp only [Execution.span_committee]
  apply Finset.biUnion_subset_biUnion_of_subset_left
  exact Finset.Icc_subset_Icc_right h

omit [LinearOrder Root] [Inhabited Root] in
/-- Ground-truth weight of a set splits into its honest and non-honest parts. -/
theorem weight_split_honest (s : Finset ValidatorIndex) :
    E.weight s = E.weight (s.filter (fun i => i ∈ E.honest))
      + E.weight (s.filter (fun i => i ∉ E.honest)) := by
  simp only [Execution.weight]
  exact (Finset.sum_filter_add_sum_filter_not s (fun i => i ∈ E.honest) E.weight_of).symm

omit [LinearOrder Root] [Inhabited Root] in
/-- Honest support is at most honest committee weight (`H ≤ J`, paper `H_le_J`). -/
theorem Hspec_le_Jspec (a b : Slot) (sup : ValidatorIndex → Prop) [DecidablePred sup] :
    E.Hspec a b sup ≤ E.Jspec a b := by
  simp only [Execution.Hspec, Execution.Jspec, Execution.weight]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1⟩
  · intro i _ _; exact Nat.zero_le _

/-! ## Section 2 — growth decompositions -/

omit [LinearOrder Root] [Inhabited Root] in
/-- `J` decomposes as the value at `b` plus the honest weight of the committee
growth set (paper `J_eq_add_growth`, `Monotone.lean`). Exact equality — no
support hypotheses. -/
theorem Jspec_eq_add_growth (a : Slot) {b b' : Slot} (h : b ≤ b') :
    E.Jspec a b' = E.Jspec a b
      + E.weight ((E.span_committee a b' \ E.span_committee a b).filter
          (fun i => i ∈ E.honest)) := by
  simp only [Execution.Jspec, Execution.weight]
  have hset : (E.span_committee a b' \ E.span_committee a b).filter (fun i => i ∈ E.honest)
      = (E.span_committee a b').filter (fun i => i ∈ E.honest)
          \ (E.span_committee a b).filter (fun i => i ∈ E.honest) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [add_comm, hset]
  exact (Finset.sum_sdiff (Finset.filter_subset_filter _ (E.span_committee_mono a h))).symm

omit [LinearOrder Root] [Inhabited Root] in
/-- Honest support `H` grows by at least the honest weight of the committee
growth set, provided every newly-counted honest committee member supports the
block (paper `H_ge_add_growth`). With a single fixed `sup`, base supporters
persist automatically (the predicate is unchanged), so only the "new honest
members support" hypothesis `hcanon` is needed. -/
theorem Hspec_ge_add_growth (a : Slot) {b b' : Slot}
    (sup : ValidatorIndex → Prop) [DecidablePred sup] (h : b ≤ b')
    (hcanon : ∀ i ∈ E.span_committee a b' \ E.span_committee a b, i ∈ E.honest → sup i) :
    E.Hspec a b sup
      + E.weight ((E.span_committee a b' \ E.span_committee a b).filter
          (fun i => i ∈ E.honest))
      ≤ E.Hspec a b' sup := by
  set U₀ := E.span_committee a b with hU₀
  set U := E.span_committee a b' with hU
  have hsub : U₀ ⊆ U := E.span_committee_mono a h
  set B₀ := U₀.filter (fun i => i ∈ E.honest ∧ sup i) with hB₀
  set Gh := (U \ U₀).filter (fun i => i ∈ E.honest) with hGh
  have hdisj : Disjoint B₀ Gh := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hB₀, hGh, Finset.mem_filter, Finset.mem_sdiff] at hi hi'
    exact hi'.1.2 hi.1
  have hunion_sub : B₀ ∪ Gh ⊆ U.filter (fun i => i ∈ E.honest ∧ sup i) := by
    intro i hi
    simp only [Finset.mem_union, hB₀, hGh, Finset.mem_filter, Finset.mem_sdiff] at hi
    simp only [Finset.mem_filter]
    rcases hi with ⟨hiU₀, hih, hisup⟩ | ⟨⟨hiU, hni⟩, hih⟩
    · exact ⟨hsub hiU₀, hih, hisup⟩
    · exact ⟨hiU, hih, hcanon i (Finset.mem_sdiff.mpr ⟨hiU, hni⟩) hih⟩
  have hHeq : E.Hspec a b sup = E.weight B₀ := by
    simp only [Execution.Hspec, hB₀, hU₀]
  have hkey : E.Hspec a b sup + E.weight Gh = E.weight (B₀ ∪ Gh) := by
    rw [hHeq]
    simp only [Execution.weight]
    exact (Finset.sum_union hdisj).symm
  rw [hkey]
  simp only [Execution.Hspec, Execution.weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg hunion_sub (fun i _ _ => Nat.zero_le _)

/-! ## Section 3 — the pure-ℕ fraction step and assembled monotonicity -/

/-- **The cross-multiplied fraction step** (paper `P_nondecreasing`, pure ℕ). From
`J' = J + g` (denominator grows by the growth-set weight), `H + g ≤ H'`
(numerator grows by at least the same), and `H ≤ J`, the fraction `H'/J'` is at
least `H/J`, i.e. `H · J' ≤ H' · J`. No adversarial-growth premise: recurring
validators dedup identically on both sides. -/
private theorem frac_cross {H J g H' J' : ℕ}
    (hJ' : J' = J + g) (hH' : H + g ≤ H') (hHJ : H ≤ J) :
    H * J' ≤ H' * J := by
  subst hJ'
  calc H * (J + g) = H * J + g * H := by ring
    _ ≤ H * J + g * J := by gcongr
    _ = (H + g) * J := by ring
    _ ≤ H' * J := by gcongr

omit [LinearOrder Root] [Inhabited Root] in
/-- **Fraction monotonicity** (paper `P_nondecreasing`), cross-multiplied over
ℕ: as the window's upper slot grows from `b` to `b'`, the honest support fraction
does not decrease, i.e. `H_b · J_{b'} ≤ H_{b'} · J_b`. Only `hcanon` (every new
honest committee member supports the block) is needed. -/
theorem Pspec_nondecreasing (a : Slot) {b b' : Slot}
    (sup : ValidatorIndex → Prop) [DecidablePred sup] (h : b ≤ b')
    (hcanon : ∀ i ∈ E.span_committee a b' \ E.span_committee a b, i ∈ E.honest → sup i) :
    E.Hspec a b sup * E.Jspec a b' ≤ E.Hspec a b' sup * E.Jspec a b := by
  have hJ' : E.Jspec a b' = E.Jspec a b
      + E.weight ((E.span_committee a b' \ E.span_committee a b).filter
          (fun i => i ∈ E.honest)) := E.Jspec_eq_add_growth a h
  have hH' : E.Hspec a b sup
      + E.weight ((E.span_committee a b' \ E.span_committee a b).filter
          (fun i => i ∈ E.honest)) ≤ E.Hspec a b' sup := E.Hspec_ge_add_growth a sup h hcanon
  have hHJ : E.Hspec a b sup ≤ E.Jspec a b := E.Hspec_le_Jspec a b sup
  exact frac_cross hJ' hH' hHJ

end Execution

end FastConfirmation.Spec

end
