import FastConfirmation.Spec.Proof.LedgerV2

/-!
# Spec / Proof / Crossing: the epoch-crossing window

The previous-epoch-loop path
of the L4 fold (`L4Fold.advance_safe`) confirms blocks whose window
`[parent.slot+1, es]` crosses an epoch boundary; `get_adversarial_weight`'s
epoch-crossing branch fires and `maximum_support` uses the `999`-ceil adjusted
estimate.

## 1. The base arms are unchanged (crossing reuses `Arms.arms_pure`)

`Arms.arms_pure` is **window-shape-agnostic**: it consumes `estimate_dominates`
(`hR8cW : WU ≤ 100·(MU//100)`), never the same-epoch additivity `R9`. The crossing
`999`-ceil `adjust_committee_weight_estimate_to_ensure_safety` only **inflates**
`MU` (`adjust_committee_weight_estimate_ge`, proved below), so `estimate_dominates`
still discharges `hR8cW` (bigger `MU`) and the rule `hR1` is only *more* demanding
(bigger `MU` on the RHS). Hence the confirmed-instance base disjunction

  `s₀ ≥ x₀ + Bbad + m₁ + ⌊C·s₀/D⌋  ∨  s₀ ≥ x₀ + m₁ + ⌊C·J₀/D⌋`

holds verbatim in the crossing case. The member arm need not hold; the tax-only
regime remains possible.

## 2. Maintenance splits: the member arm closes; the tax arm is separate

* **Member-arm branch.** When the base
  gives the *member* arm `s₀ ≥ x₀ + m₁ + ⌊C·J₀/D⌋`, the invariant

    `INVmem(σ):  x(σ) + boost + 1 + ⌊C·J(σ)/D⌋ ≤ s(σ)`

  is **Enemy-free**, so its step needs **no byz / F3 / ρ accounting** — it is
  immune to the epoch-seam double-recurrence. It is maintained per slot from the
  class deltas alone (`x`↓, `s`↑, `J` grows by fresh `φ`; `interval_cases C` +
  `omega`), and the unconditional window cap
  `LedgerV2.Enemy_capacity` (`D·Enemy ≤ C·J`) strips it to the endpoint
  `x(σ) + Enemy(σ) + boost + 1 ≤ s(σ)` that `Endpoint.lean` consumes.
  Holds for every `C ≤ 50` (a fortiori `C ≤ 25`).

* **Tax-arm branch.** When
  only the *tax* arm holds (¬member arm; `J₀ ≫ s₀`, i.e. large parent-stuck `a₀`
  or sibling-stuck `x₀`), the epoch-crossing tail lets every base supporter with an
  `epoch(es)−1` supporting vote recur **twice** in `(es, T1]` (once per epoch,
  `committee_assignment_unique` + `committee_coverage`). The second recurrence
  funds byz arrivals via per-slot `span_fraction` with **no reserve backing** (the
  base's `⌊C·s₀/D⌋` reserve banks only one recurrence), and — under the model's
  arbitrary `Externals.committee` — the adversary front-loads those recurrences and
  defers the honest `x₀`/`a₀` migrations, so the endpoint is violated by a margin
  that **scales as `⌊C·s₀/(100−C)⌋`**. In particular, the `LedgerV2.INV2_step`
  need not hold once `hF3` carries `ρ`. The spec's `span_fraction`
  assumption family (per-span fractions, arbitrary committees) does **not** by
  itself entail the cross-epoch LMD margin against an assignment-order adversary.
  A proof of that branch therefore requires either committee regularity or an FFG
  never-filtered argument carrying the cross-seam segment. The results below cover
  the member-arm, same-epoch, and saturated crossing instances.
-/

namespace FastConfirmation.Spec

/-- Two-sided floor bounds of `n / m` (`0 < m`) as linear atoms. This is the analogue of
`Arms.div_floor_bounds`; the divisor stays a variable so `omega` uses the
`div_add_mod`/`mod_lt` atoms rather than native literal-division reasoning. -/
private theorem div_floor_bounds (n m : ℕ) (hm : 0 < m) :
    m * (n / m) ≤ n ∧ n < m * (n / m + 1) := by
  have e := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  rw [Nat.mul_succ]
  omega

/-- Pure-ℕ over free variables (`q := ⌊(a+999)/1000⌋` abstracted so `omega` avoids
native literal-division reasoning): `a + 999 < 1000·(q+1) ⟹ a ≤ 1000·q`. -/
private theorem ceil_mul_ge_aux (a q : ℕ) (hb : a + 999 < 1000 * (q + 1)) :
    a ≤ 1000 * q := by omega

/-! ## Part A — the `999`-ceil adjustment only inflates `MU` (base reuses `arms_pure`) -/

/-- **The crossing estimate adjustment inflates.**
`adjust_committee_weight_estimate_to_ensure_safety cfg e ≥ e` — the
`ceil = (e + 999)//1000`, `ceil·(1000 + factor)` per-mille rounding
never decreases the estimate (`ceil·1000 ≥ e` from `Nat.div_add_mod`, and the
`+factor` only grows it). Consequence: in the epoch-crossing branch of
`estimate_committee_weight_between_slots`, `MU := maximum_support` is at least the
raw pro-rated committee weight, so `ByzantineBound.estimate_dominates` still bounds
the window weight `WU ≤ 100·(MU//100)` and the confirmation rule `hR1` only grows
more demanding — `Arms.arms_pure` applies to the crossing window verbatim. -/
theorem adjust_committee_weight_estimate_ge (cfg : Config) (e : Gwei) :
    e ≤ adjust_committee_weight_estimate_to_ensure_safety cfg e := by
  simp only [adjust_committee_weight_estimate_to_ensure_safety]
  have h1 : e ≤ 1000 * ((e + 999) / 1000) :=
    ceil_mul_ge_aux e ((e + 999) / 1000) (div_floor_bounds (e + 999) 1000 (by norm_num)).2
  calc e ≤ 1000 * ((e + 999) / 1000) := h1
    _ = (e + 999) / 1000 * 1000 := by rw [Nat.mul_comm]
    _ ≤ (e + 999) / 1000 * (1000 + cfg.committee_weight_estimation_adjustment_factor) :=
        Nat.mul_le_mul (le_refl _) (by omega)

/-! ## Part B — the pure-ℕ member-branch step and endpoint (the closable regime)

`INVmem` is the member-cap branch of `INV2` with the `Enemy` term folded out
(`x + Enemy + m₁ + (⌊C·J/D⌋ − Enemy) = x + m₁ + ⌊C·J/D⌋`). Because the enemy has
cancelled, the step arithmetic references **no byz weight** and hence no per-slot
`span_fraction`/`ρ` funding — this is why it survives the epoch-crossing tail. -/

/-- **Member-branch step, pure ℕ.** From `INVmem(σ)` (`x + m₁ + ⌊C·J/D⌋ ≤ s`), the
class-migration deltas (`x` never grows: `x' + ξ ≤ x`; `s` grows by the migrants
and fresh: `s + ξ + α + φ ≤ s'`) and the window growth `J' = J + φ` (fresh honest
only), `INVmem(σ+1)` follows. The floor witnesses `rJ`, `rJ'` carry the two-sided
`⌊·⌋` bounds; `interval_cases C` makes every `C`/`D` product literal and `omega`
closes each case — the key linear fact it extracts is `rJ' ≤ rJ + φ` (`C ≤ D`).
No byz term appears: the ρ-hole cannot arise. -/
private theorem crossing_member_step_arith
    {C x x' s s' J J' m1 ξ α φ rJ rJ' : ℕ}
    (hC : C ≤ 25)
    (hINV : x + m1 + rJ ≤ s)
    (hx' : x' + ξ ≤ x)
    (hs' : s + ξ + α + φ ≤ s')
    (hJ' : J' = J + φ)
    (hrJlo : (100 - C) * rJ ≤ C * J) (hrJhi : C * J < (100 - C) * (rJ + 1))
    (hrJ'lo : (100 - C) * rJ' ≤ C * J') (hrJ'hi : C * J' < (100 - C) * (rJ' + 1)) :
    x' + m1 + rJ' ≤ s' := by
  subst hJ'
  interval_cases C <;> omega

/-- **Member-branch endpoint, pure ℕ.** `INVmem(σ)` (`x + m₁ + ⌊C·J/D⌋ ≤ s`) and the
window cap `D·Enemy ≤ C·J` (`LedgerV2.Enemy_capacity`, unconditional) give the plain
endpoint `x + Enemy + m₁ ≤ s`: the cap forces `Enemy ≤ ⌊C·J/D⌋`. -/
theorem crossing_member_endpoint_arith {C x s J m1 Enemy : ℕ}
    (hC : C ≤ 25)
    (hINV : x + m1 + C * J / (100 - C) ≤ s)
    (hcap : (100 - C) * Enemy ≤ C * J) :
    x + Enemy + m1 ≤ s := by
  have hDpos : 0 < 100 - C := by omega
  have hE : Enemy ≤ C * J / (100 - C) := by
    rw [Nat.le_div_iff_mul_le hDpos, Nat.mul_comm]; exact hcap
  omega

/-! ## Part C — the member-branch invariant over the ledger accessors

`INVmem` is `LedgerV2.INV2`'s member-cap branch with `Enemy` cancelled. It is the
drop-in replacement for `LedgerV2.INV2`/`StepDischargeII.INV2_maintained_same_epoch`
on **member-arm crossing instances**: the step needs only the honest class deltas
(`hx'`/`hs'`/`hJ'`, the same store-dynamics residue the shell already discharges for
the same-epoch step), and the endpoint rides `LedgerV2.Enemy_capacity` — no per-slot
`span_fraction`/`ρ`/`committee_coverage`, so it is immune to the epoch-crossing tail.
The base is the member arm of `Arms.arms_pure` (`s₀ ≥ x₀ + m₁ + ⌊C·J₀/D⌋`). -/

namespace Execution

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root) (E : Execution Root)

/-- **`INVmem`** — the member-cap branch of `INV2` at window end `σ` with the
`Enemy` term cancelled: `x(σ) + boost + 1 + ⌊C·J(σ)/D⌋ ≤ s(σ)`
(`C := confirmation_byzantine_threshold`, `D := 100 − C`, `J := Jspec lo σ`). -/
def INVmem (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) (boost : ℕ) : Prop :=
  E.Xval cfg ext v₀ n₀ b' lo σ + boost + 1
      + cfg.confirmation_byzantine_threshold * E.Jspec lo σ
          / (100 - cfg.confirmation_byzantine_threshold)
    ≤ E.Sval cfg ext v₀ n₀ b' lo σ

/-- **`INVmem` endpoint.** With the unconditional window cap `LedgerV2.Enemy_capacity`
(`D·Enemy(σ) ≤ C·J(σ)`), `INVmem(σ)` strips to the plain endpoint
`x(σ) + Enemy(σ) + boost + 1 ≤ s(σ)` — the shape `Endpoint.lean` / the shell's `hsat`
consume. Needs `hlo : lo ≤ es + 1`, `hes : es ≤ σ` (for `Enemy_capacity`). -/
theorem INVmem_endpoint (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo) (hσH : E.SlotWithinHorizon cfg σ)
    (hlo : lo ≤ es + 1) (hes : es ≤ σ)
    (hinv : E.INVmem cfg ext v₀ n₀ b' lo σ boost) :
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hcap := E.Enemy_capacity cfg ext hbb v₀ n₀ b' lo es σ hloH hσH hlo hes
  have h := crossing_member_endpoint_arith (C := cfg.confirmation_byzantine_threshold)
    (x := E.Xval cfg ext v₀ n₀ b' lo σ) (s := E.Sval cfg ext v₀ n₀ b' lo σ)
    (J := E.Jspec lo σ) (m1 := boost + 1)
    (Enemy := E.Enemy cfg ext v₀ n₀ b' lo es σ)
    cfg.confirmation_byzantine_threshold_le (by rw [← Nat.add_assoc]; exact hinv) hcap
  omega

/-- **`INVmem` step.** From `INVmem(σ)` and the honest class deltas — `x` never grows
(`hx'`), `s` grows by the migrants/fresh (`hs'`), the honest window grows by fresh
only (`hJ'`: `Jspec lo (σ+1) = Jspec lo σ + φ`) — `INVmem(σ+1)` follows. No byz/F3
term (`crossing_member_step_arith`). -/
theorem INVmem_step (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot)
    (boost ξ α φ : ℕ)
    (hx' : E.Xval cfg ext v₀ n₀ b' lo (σ + 1) + ξ ≤ E.Xval cfg ext v₀ n₀ b' lo σ)
    (hs' : E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α + φ ≤ E.Sval cfg ext v₀ n₀ b' lo (σ + 1))
    (hJ' : E.Jspec lo (σ + 1) = E.Jspec lo σ + φ)
    (hinv : E.INVmem cfg ext v₀ n₀ b' lo σ boost) :
    E.INVmem cfg ext v₀ n₀ b' lo (σ + 1) boost := by
  simp only [Execution.INVmem] at hinv ⊢
  set C := cfg.confirmation_byzantine_threshold with hCdef
  have hC25 : C ≤ 25 := cfg.confirmation_byzantine_threshold_le
  have hDpos : 0 < 100 - C := by omega
  obtain ⟨hrJlo, hrJhi⟩ := div_floor_bounds (C * E.Jspec lo σ) (100 - C) hDpos
  obtain ⟨hrJ'lo, hrJ'hi⟩ := div_floor_bounds (C * E.Jspec lo (σ + 1)) (100 - C) hDpos
  have h := crossing_member_step_arith (C := C)
    (x := E.Xval cfg ext v₀ n₀ b' lo σ) (x' := E.Xval cfg ext v₀ n₀ b' lo (σ + 1))
    (s := E.Sval cfg ext v₀ n₀ b' lo σ) (s' := E.Sval cfg ext v₀ n₀ b' lo (σ + 1))
    (J := E.Jspec lo σ) (J' := E.Jspec lo (σ + 1)) (m1 := boost + 1)
    (ξ := ξ) (α := α) (φ := φ)
    (rJ := C * E.Jspec lo σ / (100 - C)) (rJ' := C * E.Jspec lo (σ + 1) / (100 - C))
    hC25 (by rw [← Nat.add_assoc]; exact hinv) hx' hs' hJ' hrJlo hrJhi hrJ'lo hrJ'hi
  omega

/-- **`INVmem` maintained.** From the base `INVmem(es)` (the member arm) and the
per-slot step `hstep` (each `INVmem(σ) ⟹ INVmem(σ+1)`, discharged by `INVmem_step`
from the class deltas), `INVmem(σ)` holds for every `σ ≥ es`. A plain
`Nat.le_induction` — no saturation regime, no `committee_coverage`, because the
member branch never accrues an unfunded byz term across the epoch seam. -/
theorem INVmem_maintained (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    (boost : ℕ) (hbase : E.INVmem cfg ext v₀ n₀ b' lo es boost)
    (hstep : ∀ σ : Slot, es ≤ σ →
      E.INVmem cfg ext v₀ n₀ b' lo σ boost → E.INVmem cfg ext v₀ n₀ b' lo (σ + 1) boost) :
    ∀ σ : Slot, es ≤ σ → E.INVmem cfg ext v₀ n₀ b' lo σ boost := by
  intro σ hσ
  induction σ, hσ using Nat.le_induction with
  | base => exact hbase
  | succ σ hσ ih => exact hstep σ hσ ih

end Execution

end FastConfirmation.Spec
