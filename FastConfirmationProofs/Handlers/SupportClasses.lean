module
public import FastConfirmationProofs.Handlers.CommitteeWeightFractions
public import FastConfirmationProofs.Discount.HeadSafetyInduction

@[expose] public section

/-!
# Spec / Proof / Ledger

This module contains `SupportsDesc`, `AncestorOrVoteless`, `Sclass` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the ground-truth vote classes -/

/-- `i`'s newest vote by `σ` **supports `subtree(b′)`**: there is a vote at some
slot `t ≤ σ` with no later vote through `σ`, whose block descends from `b′` at the
confirming store (`b′` is an ancestor of the vote block). Mirrors
`ConfirmedSupport.votes`, parameterized by the window end `σ`. -/
def SupportsDesc (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ : Slot)
    (i : ValidatorIndex) : Prop :=
  ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t ≤ σ ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' ≤ σ → E.vote i t' = none) ∧
    is_ancestor (E.store cfg ext v₀ n₀)
      (get_node_for_root a.data.beacon_block_root) (get_node_for_root b') = true

/-- `i` **backs no sibling** of `b′` by `σ`: either it has cast no vote through
`σ` (voteless), or its newest vote's block is an **ancestor of** `b′` (`b′`
descends from the vote block — the reversed `is_ancestor` orientation). -/
def AncestorOrVoteless (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ : Slot)
    (i : ValidatorIndex) : Prop :=
  (∀ t' : Slot, t' ≤ σ → E.vote i t' = none) ∨
  (∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t ≤ σ ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' ≤ σ → E.vote i t' = none) ∧
    is_ancestor (E.store cfg ext v₀ n₀)
      (get_node_for_root b') (get_node_for_root a.data.beacon_block_root) = true)

open Classical in
/-- `Sclass σ` — honest window members whose newest vote by `σ` supports
`subtree(b′)`; weight `s(σ)`. -/
noncomputable def Sclass (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => E.SupportsDesc cfg ext v₀ n₀ b' σ i)

open Classical in
/-- `Aclass σ` — honest window members that are **not** `Sclass` and back no
sibling of `b′` (voteless or ancestor-voting); weight `a(σ)`. The `¬S` guard
keeps `Sclass`/`Aclass` disjoint. -/
noncomputable def Aclass (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => ¬ E.SupportsDesc cfg ext v₀ n₀ b' σ i ∧
      E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i)

open Classical in
/-- `Xclass σ` — the remaining honest window members (`¬S ∧ ¬A`; sibling-stuck);
weight `x(σ)`. -/
noncomputable def Xclass (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => ¬ E.SupportsDesc cfg ext v₀ n₀ b' σ i ∧
      ¬ E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i)

/-- `Bwin σ` — the window's non-honest members (the enemy set; weight `B(σ)`). -/
def Bwin (lo σ : Slot) : Finset ValidatorIndex :=
  (E.span_committee lo σ).filter (fun i => i ∉ E.honest)

open Classical in
/-- `Unrec σ` — the not-yet-recurred **base** supporters: `Sclass es` members with
no committee assignment in `(es, σ]`; weight `U(σ)`. Their future recurrence
slots are the only pay-go-free byz-arrival opportunities. -/
noncomputable def Unrec (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) :
    Finset ValidatorIndex :=
  (E.Sclass cfg ext v₀ n₀ b' lo es).filter
    (fun i => ∀ t : Slot, es < t → t ≤ σ → i ∉ E.committee t)

/-! ## Section 2 — weight accessors -/

/-- `s(σ)` — `Sclass` weight. -/
noncomputable def Sval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) : Gwei :=
  E.weight (E.Sclass cfg ext v₀ n₀ b' lo σ)

/-- `a(σ)` — `Aclass` weight. -/
noncomputable def Aval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) : Gwei :=
  E.weight (E.Aclass cfg ext v₀ n₀ b' lo σ)

/-- `x(σ)` — `Xclass` weight. -/
noncomputable def Xval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) : Gwei :=
  E.weight (E.Xclass cfg ext v₀ n₀ b' lo σ)

/-- `B(σ)` — enemy (non-honest window) weight. -/
noncomputable def Bval (lo σ : Slot) : Gwei :=
  E.weight (E.Bwin lo σ)

/-- `U(σ)` — not-yet-recurred base-supporter weight. -/
noncomputable def Uval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) : Gwei :=
  E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ)

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

/-- **INV\*** at window end `σ` (cross-multiplied, `C := confirmation_byzantine_threshold`):
`(100−C)·s ≥ (100−C)·(x + B + boost + 1) + min (C·U) (C·J − (100−C)·B)`. The single
per-chain-block persistence invariant; the `min` caps the enemy's future
arrivals both by the recurrence tax on unrecurred base supporters (`C·U`) and by
the remaining F3 window capacity (`C·J − (100−C)·B`, un-truncated by
`Rterm_nonneg`). -/
def INVstar (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (boost : ℕ) : Prop :=
  (100 - cfg.confirmation_byzantine_threshold) *
        (E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + boost + 1)
      + min (cfg.confirmation_byzantine_threshold * E.Uval cfg ext v₀ n₀ b' lo es σ)
          (cfg.confirmation_byzantine_threshold * E.Jspec lo σ
            - (100 - cfg.confirmation_byzantine_threshold) * E.Bval lo σ)
    ≤ (100 - cfg.confirmation_byzantine_threshold) * E.Sval cfg ext v₀ n₀ b' lo σ

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
