import FastConfirmation.Spec.Proof.Fraction
import FastConfirmation.Spec.Proof.EngineInduction

/-!
# Spec / Proof / Ledger: INV\* — the single ledger invariant

The head-safety engine's persistence invariant, ported from the paper's proven
fraction engine but stated as **one min-potential inequality per chain block**
(the `INVstar` design). All quantities are
ground-truth weights over `E.span_committee` (recurrence-proof set form), so the
cross-epoch committee-overlap problem cannot arise.

Fix a confirming anchor `(cfg, ext, v₀, n₀)`, a chain block `b′`, a window start
`lo` (`:= parent(b′).slot + 1` at the call site) and a base end `es`
(`:= slot_at n₀`). The honest members of the growing window `[lo, σ]` split into
three classes by their **ground-truth newest vote** (`E.vote`, node-independent):

* `Sclass σ` — newest vote by `σ` exists and its block **descends from** `b′`
  (supports `subtree(b′)`); weight `s(σ)`.
* `Aclass σ` — voteless by `σ`, or newest vote's block is an **ancestor of** `b′`
  (backs no sibling); weight `a(σ)`. Defined disjoint from `Sclass` (the `¬S`
  guard) so the three classes partition the honest window.
* `Xclass σ` — the rest (`¬S ∧ ¬A`; sibling-stuck); weight `x(σ)`.

`weight_partition` gives `J(σ) = s(σ) + a(σ) + x(σ)` with `J := Jspec lo σ`
(Fraction's honest committee-union weight). The enemy is the window's non-honest
weight `B(σ) := weight (Bwin σ)`, always inside the window by the slot-cap. The
potential's two caps are the recurrence tax on the not-yet-recurred base
supporters `U(σ)` (weight of `Sclass es` members with no assignment in `(es, σ]`)
and the remaining F3 (`span_fraction`) capacity `C·J − (100−C)·B`, kept
cross-multiplied to avoid division:

  INV\*(σ):  `(100−C)·s(σ) ≥ (100−C)·(x(σ) + B(σ) + boost + 1)`
             `+ min (C·U(σ)) (C·J(σ) − (100−C)·B(σ))`

with `C := cfg.confirmation_byzantine_threshold ≤ 25`. This module delivers the
**vocabulary** (classes, accessors, `weight_partition`, `Rterm_nonneg`,
monotonicity) and the **pure-ℕ step lemma** (`invstar_step_arith`, the four-case
ledger arithmetic wrapped as `INVstar_step`). No store-dynamics obligations: the
per-slot class-delta facts (every honest member of slot `t`'s committee re-votes
`desc(b′)` by the engine IH + `votes_head` + delivery) are discharged by the
engine shell (the reduction), which instantiates the step lemma's abstract deltas.
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
/-- The enemy set grows with the window (`span_committee_mono` + filter). -/
theorem Bwin_mono (lo : Slot) {σ σ' : Slot} (h : σ ≤ σ') :
    E.Bwin lo σ ⊆ E.Bwin lo σ' := by
  simp only [Execution.Bwin]
  exact Finset.filter_subset_filter _ (E.span_committee_mono lo h)

omit [LinearOrder Root] [Inhabited Root] in
/-- Enemy weight `B` is monotone in the window end. -/
theorem Bval_mono (lo : Slot) {σ σ' : Slot} (h : σ ≤ σ') :
    E.Bval lo σ ≤ E.Bval lo σ' :=
  E.weight_mono (E.Bwin_mono lo h)

omit [LinearOrder Root] [Inhabited Root] in
/-- Honest committee-union weight `J` is monotone in the window end. -/
theorem Jspec_mono (lo : Slot) {σ σ' : Slot} (h : σ ≤ σ') :
    E.Jspec lo σ ≤ E.Jspec lo σ' := by
  simp only [Execution.Jspec]
  exact E.weight_mono (Finset.filter_subset_filter _ (E.span_committee_mono lo h))

/-- `Unrec` is **antitone**: a later window end can only remove base supporters
(more slots in `(es, σ']` to avoid an assignment in), so
`σ ≤ σ' → Unrec σ' ⊆ Unrec σ`. -/
theorem Unrec_anti (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    {σ σ' : Slot} (h : σ ≤ σ') :
    E.Unrec cfg ext v₀ n₀ b' lo es σ' ⊆ E.Unrec cfg ext v₀ n₀ b' lo es σ := by
  intro i hi
  simp only [Execution.Unrec, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, fun t ht1 ht2 => hi.2 t ht1 (le_trans ht2 h)⟩

/-! ## Section 6 — the pure-ℕ ledger step -/

/-- **The INV\* step, pure-ℕ abstract form** (all quantities pre-scaled by `C`
or `D := 100 − C`, so the four-case ledger arithmetic is linear and `omega`
discharges it). Reading the atoms as `Ds = D·s`, `Dx = D·x`, `DB = D·B`,
`CU = C·U`, `CJ = C·J`, `e1 = D·(boost+1)`, and the deltas `Dξ = D·ξ` … the
hypotheses are the per-slot facts the engine shell supplies:

* `hs'` — honest support grows by the migrants + fresh (`s' ≥ s + ξ + α + φ`);
* `hx'` — the sibling-stuck class loses the `x→s` migrants (`x' + ξ ≤ x`);
* `hB'` — the enemy grows by at most the new byz `β` (`B' ≤ B + β`);
* `hJ'` — the honest window grows by exactly the fresh members (`J' = J + φ`);
* `hUσt` — the recurring **base** supporters leave the unrecurred set
  (`U' + σt ≤ U`; here `σt = U − U'` is the base-supporter recurrence, which is
  `0` within an epoch by `committee_assignment_unique` and accrues only across
  epoch boundaries — it is what funds the tax when `min = C·U`);
* `hQ`/`hQ'` — the R-term is un-truncated at both ends (`Rterm_nonneg`);
* `hF3` — the per-slot `span_fraction` on `[t,t]` (`D·β ≤ C·(σt+ξ+α+φ)`);
* `hbξ`/`hbα`/`hbφ` — the `C ≤ D` coefficient bridges (`C·ξ ≤ D·ξ`, …).

Tax branch (`min = C·U`): the freed tax `C·(U−U') ≥ C·σt` plus the bridges
absorb `D·β`. R branch (`min = C·J − D·B`): the `D·B` cancels and `C·φ ≤ D·φ`
covers the growth. -/
private theorem invstar_step_arith
    {Ds Ds' Dx Dx' DB DB' CU CU' CJ CJ' e1 Dξ Dα Dφ Dβ Cξ Cα Cφ Cσt : ℕ}
    (hINV : Dx + DB + e1 + min CU (CJ - DB) ≤ Ds)
    (hs' : Ds + Dξ + Dα + Dφ ≤ Ds')
    (hx' : Dx' + Dξ ≤ Dx)
    (hB' : DB' ≤ DB + Dβ)
    (hJ' : CJ' = CJ + Cφ)
    (hUσt : CU' + Cσt ≤ CU)
    (hQ : DB ≤ CJ) (hQ' : DB' ≤ CJ')
    (hF3 : Dβ ≤ Cσt + Cξ + Cα + Cφ)
    (hbξ : Cξ ≤ Dξ) (hbα : Cα ≤ Dα) (hbφ : Cφ ≤ Dφ) :
    Dx' + DB' + e1 + min CU' (CJ' - DB') ≤ Ds' := by
  omega

/-- **The INV\* step over the ledger defs.** Given the per-slot class deltas
`ξ` (`x→s` migrants), `α` (`a→s` migrants), `φ` (fresh honest joining `s`), `β`
(new byz), `σt` (base-supporter recurrers leaving `Unrec`, i.e. `U − U'`),
phrased as ℕ relations between the accessor values at `σ` and `σ'` (the
"class-delta facts" the engine shell discharges from `votes_head` + IH +
delivery + `committee_assignment_unique`),
`INVstar` at `σ` propagates to `σ'`. The `span_fraction` R-term floor
(`Rterm_nonneg`) is supplied at both ends from `hbb`; the coefficient bridges
`C ≤ 100 − C` follow from `C ≤ 25`. No store dynamics: this scales the raw
deltas by `C`/`(100−C)` and hands the linear ledger arithmetic to
`invstar_step_arith`. -/
theorem INVstar_step (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) {σ σ' : Slot}
    (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ) (hσ'H : E.SlotWithinHorizon cfg σ')
    (boost ξ α φ β σt : ℕ)
    (hs' : E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α + φ ≤ E.Sval cfg ext v₀ n₀ b' lo σ')
    (hx' : E.Xval cfg ext v₀ n₀ b' lo σ' + ξ ≤ E.Xval cfg ext v₀ n₀ b' lo σ)
    (hB' : E.Bval lo σ' ≤ E.Bval lo σ + β)
    (hJ' : E.Jspec lo σ' = E.Jspec lo σ + φ)
    (hUσt : E.Uval cfg ext v₀ n₀ b' lo es σ' + σt ≤ E.Uval cfg ext v₀ n₀ b' lo es σ)
    (hF3 : (100 - cfg.confirmation_byzantine_threshold) * β ≤
      cfg.confirmation_byzantine_threshold * (σt + ξ + α + φ))
    (hinv : E.INVstar cfg ext v₀ n₀ b' lo es σ boost) :
    E.INVstar cfg ext v₀ n₀ b' lo es σ' boost := by
  have hQ := E.Rterm_nonneg cfg hbb lo σ hloH hσH
  have hQ' := E.Rterm_nonneg cfg hbb lo σ' hloH hσ'H
  simp only [Execution.INVstar] at hinv ⊢
  set C := cfg.confirmation_byzantine_threshold with hCdef
  have hC25 : C ≤ 25 := cfg.confirmation_byzantine_threshold_le
  -- scale the raw deltas by `C` / `100 − C`:
  have i1 : (100 - C) * (E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α + φ)
      ≤ (100 - C) * E.Sval cfg ext v₀ n₀ b' lo σ' := by gcongr
  have i2 : (100 - C) * (E.Xval cfg ext v₀ n₀ b' lo σ' + ξ)
      ≤ (100 - C) * E.Xval cfg ext v₀ n₀ b' lo σ := by gcongr
  have i3 : (100 - C) * E.Bval lo σ' ≤ (100 - C) * (E.Bval lo σ + β) := by gcongr
  have i5 : C * (E.Uval cfg ext v₀ n₀ b' lo es σ' + σt)
      ≤ C * E.Uval cfg ext v₀ n₀ b' lo es σ := by gcongr
  have i6 : C * ξ ≤ (100 - C) * ξ := by gcongr; omega
  have i7 : C * α ≤ (100 - C) * α := by gcongr; omega
  have i8 : C * φ ≤ (100 - C) * φ := by gcongr; omega
  have i9 : C * E.Jspec lo σ' = C * E.Jspec lo σ + C * φ := by rw [hJ', mul_add]
  -- the R-term subtractions are un-truncated (`Rterm_nonneg`), so `omega` can
  -- atomize `C·J` and relate it to the `min`'s second argument:
  have hR := Nat.sub_add_cancel hQ
  have hR' := Nat.sub_add_cancel hQ'
  -- distribute every scaled product in place, leaving only atoms `omega` combines:
  simp only [mul_add, mul_one] at i1 i2 i3 i5 hinv hF3 ⊢
  omega

end Execution

end FastConfirmation.Spec
