import FastConfirmation.Spec.Proof.Base
import FastConfirmation.Spec.Proof.Registry

/-!
# Spec / Proof / Arms: the base arms

The confirmed-instance base of the
head-safety ledger, as the machine-checked disjunction

  `s₀ ≥ x₀ + Bbad + m₁ + (C·s₀)/D  ∨  s₀ ≥ x₀ + m₁ + (C·J₀)/D`

with `C := cfg.confirmation_byzantine_threshold`, `D := 100 − C`, `m₁ := boost+1`,
both arms floored (ℕ-division). For every `C ∈ [0,25]`, the corrected enemy accounting uses
the base
enemy `Bbad = B₀ − Bsup − eq − Bpar` is only the byz *not* already accounted as
a `b′`-supporter, equivocator, or parent-stuck voter — a byz recorded supporter
of `b′` cannot simultaneously back a sibling, and flipping costs a fresh vote at
the validator's own future assignment slot (the v2 ledger's per-slot capacity).

The proof is organized as follows:

* **Part A — ingredient lemmas from the Model defs** (`proposer_score_boost_link`
  = R13, `estimate_same_epoch`/`estimate_additive` = R9′). Both are
  **redundant** for the floored arms — the machine check closes without the
  estimate slot-structure or the boost link (they were load-bearing only for the
  earlier cross-multiplied `(★)∨(★R)` form). They remain useful
  `estimate_committee_weight_between_slots` and `compute_proposer_score` facts, although the
  arms lemma does not consume them.
* **Part B — the pure-ℕ arms lemma** (`arms_pure`): the disjunction follows from
  `interval_cases C` (0..25) and `omega`.
* **Part C — the assembly** (`arms_of_confirmed`): the arms over the confirmed
  instance's class/enemy weights, wiring `is_one_confirmed_ineq` + the
  `maximum_support // 100` bounds and taking the store-dynamics /
  byz-decomposition bridges as explicit hypotheses (as `Base.weak_base_of_rule`
  takes `hHsup`/`hdisc`).
-/

namespace FastConfirmation.Spec

/-! ## Part A — ingredient lemmas (R13, R9′) from the Model defs

Both are true facts about `compute_proposer_score` /
`estimate_committee_weight_between_slots`; the machine-checked arms do **not**
consume them; they close the earlier cross-multiplied form. -/

/-- **R13 (boost link), symbolic-product form.** `100·compute_proposer_score ≤
proposer_score_boost·(TAB / SLOTS_PER_EPOCH)`. Unconditional — no
`proposer_score_boost ≤ 40` needed for *this* inequality (that bound would only
enter the earlier cross-multiplied arithmetic, which the floored arms avoid). The
floor `x·psb/100 ≤` is discharged by `Nat.mul_div_le`. -/
theorem proposer_score_boost_link {Root : Type*} (cfg : Config) (bs : BeaconState Root) :
    100 * compute_proposer_score cfg bs ≤
      cfg.proposer_score_boost * (get_total_active_balance cfg bs / cfg.slots_per_epoch) := by
  simp only [compute_proposer_score]
  rw [Nat.mul_comm cfg.proposer_score_boost
    (get_total_active_balance cfg bs / cfg.slots_per_epoch)]
  exact Nat.mul_div_le _ 100

/-- **R9′ (same-epoch estimate linearity).** On a nonempty span `[a,b]` lying in
one epoch (`is_full_validator_set_covered` false, `epoch a = epoch b`),
`estimate = (TAB / SLOTS_PER_EPOCH)·(b − a + 1)` — the same-epoch branch of
`estimate_committee_weight_between_slots`. The covered/epoch guards are explicit
hypotheses (they are true of the spec's confirmation spans but not free in
general — a span can cover a full epoch, or straddle a boundary). -/
theorem estimate_same_epoch (cfg : Config) (tab : Gwei) (a b : Slot)
    (hab : a ≤ b)
    (hcov : is_full_validator_set_covered cfg a b = false)
    (hep : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg b) :
    estimate_committee_weight_between_slots cfg tab a b
      = tab / cfg.slots_per_epoch * (b - a + 1) := by
  simp only [estimate_committee_weight_between_slots, hep]
  split_ifs with hgt hcovered
  · exact absurd hgt (Nat.not_lt.mpr hab)
  · rw [hcov] at hcovered; exact absurd hcovered (by decide)
  · rfl

/-- Pure-ℕ slot-count split (`omega` on genuine `ℕ`; abbrev-typed `Slot` goals
trip `omega`, hence the extraction). -/
private theorem slotcount_split (a b c : ℕ) (hab : a ≤ b) (hbc : b + 1 ≤ c) :
    b - a + 1 + (c - (b + 1) + 1) = c - a + 1 := by omega

/-- **R9′ (same-epoch additivity).** With both `[a,b]` and `[b+1,c]` in one epoch,
the estimate is additive: `estimate a c = estimate a b + estimate (b+1) c`. Pure
consequence of the linearity (`estimate_same_epoch`) on the three spans — the
`(c − a + 1) = (b − a + 1) + (c − b)` slot count splits, `b+1 ≤ c`, `a ≤ b`. -/
theorem estimate_additive (cfg : Config) (tab : Gwei) (a b c : Slot)
    (hab : a ≤ b) (hbc : b + 1 ≤ c)
    (hcovAC : is_full_validator_set_covered cfg a c = false)
    (hcovAB : is_full_validator_set_covered cfg a b = false)
    (hcovBC : is_full_validator_set_covered cfg (b + 1) c = false)
    (hepAC : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg c)
    (hepAB : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg b)
    (hepBC : compute_epoch_at_slot cfg (b + 1) = compute_epoch_at_slot cfg c) :
    estimate_committee_weight_between_slots cfg tab a c
      = estimate_committee_weight_between_slots cfg tab a b
        + estimate_committee_weight_between_slots cfg tab (b + 1) c := by
  rw [estimate_same_epoch cfg tab a c (le_trans hab (le_trans (Nat.le_succ b) hbc)) hcovAC hepAC,
      estimate_same_epoch cfg tab a b hab hcovAB hepAB,
      estimate_same_epoch cfg tab (b + 1) c hbc hcovBC hepBC,
      ← Nat.mul_add, slotcount_split a b c hab hbc]

/-! ## Part B — the pure-ℕ arms lemma

The confirmed-instance base disjunction uses 16 pre-scaled ℕ atoms.
`interval_cases C` turns each
`qV·C` and the two floored terms into literal-coefficient linear systems, closed
by `omega` per case (26 cases; the ℕ-subtractions are pre-eliminated into the
additive `hR2d1`/`hR3a`/`hR3b` forms so `omega` never branches on truncation;
the division is handled by `arms_pure`).

Atom legend (all pre-scaled ground-truth weights over `E.span_committee`):
`s₀`=honest supporters, `x₀=xV+xpre`=sibling-stuck, honest window union
`J₀=s₀+aV+xV+Hpar+apre+xpre`, `B₀`=enemy (U-span non-honest); `Bsup`/`eqV`/`Bpar`
=byz supporters / V-span equivocators / parent-stuck byz (the accounted enemy),
`Bbad`=the unaccounted remainder; `A`=`get_adversarial_weight` (V-span),
`d`=`get_support_discount`, `MU`=`maximum_support` estimate,
`qV=MV//100`, `qU=MU//100`, `boost`=`compute_proposer_score`. -/

/-- The two-sided floor bounds of `n / m` when `0 < m`, as linear facts over the
atoms `m * (n/m)`, `n % m`, `n`, `m` (no symbolic-product expansion — `omega`
combines `div_add_mod` with `mod_lt`). -/
private theorem div_floor_bounds (n m : ℕ) (hm : 0 < m) :
    m * (n / m) ≤ n ∧ n < m * (n / m + 1) := by
  have e := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  rw [Nat.mul_succ]
  omega

/-- **Division-free core.** The arms over abstract floor witnesses `rT`, `mc`
(their two-sided floor bounds `hrTlo`/`hrThi`, `hmclo`/`hmchi` supplied as linear
hypotheses). After `interval_cases C` every product with `C` becomes a
literal-coefficient linear term, so `omega` closes each of the 26 cases on a
purely linear, subtraction-free system. -/
private theorem arms_core
    {s0 aV xV Hpar apre xpre B_V B0 Bsup eqV Bpar
     boost d A qV qU MU Bbad C rT mc : ℕ}
    (hC : C ≤ 25)
    (hR1 : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 1 + 2 * A)
    (hR2d1 : d ≤ Hpar + Bpar)
    (hR3a : A ≤ qV * C)
    (hR3b : qV * C ≤ A + eqV)
    (hR4a : Bsup ≤ A)
    (hR4b : Bsup + eqV ≤ B_V)
    (hR8aW : s0 + aV + xV + B_V ≤ 100 * qV)
    (hR8cW : s0 + aV + xV + (Hpar + apre + xpre) + B0 ≤ 100 * qU)
    (hR8cM1 : 100 * qU ≤ MU)
    (hR8cM2 : MU ≤ 100 * qU + 99)
    (hBbad : Bbad + Bsup + eqV + Bpar ≤ B0)
    (hrTlo : (100 - C) * rT ≤ C * s0)
    (hrThi : C * s0 < (100 - C) * (rT + 1))
    (hmclo : (100 - C) * mc ≤ C * (s0 + aV + xV + (Hpar + apre + xpre)))
    (hmchi : C * (s0 + aV + xV + (Hpar + apre + xpre)) < (100 - C) * (mc + 1)) :
    s0 ≥ xV + xpre + Bbad + (boost + 1) + rT
    ∨ s0 ≥ xV + xpre + (boost + 1) + mc := by
  interval_cases C <;> omega

/-- **The base arms (pure ℕ).** From the confirmation rule (`R1`,
`is_one_confirmed_ineq`), the discount bound (`R2d1`, `d ≤ Hpar + Bpar` =
`compute_empty_slot_support_discount ≤` pre-region support), the V-span
adversarial budget (`R3a`/`R3b`/`R4a`/`R4b`/`R8aW`), the U-span estimate
domination (`R8cW`/`R8cM`), and the enemy partition `hBbad`
(`Bbad + Bsup + eqV + Bpar ≤ B₀` — the accounted byz sit inside the window
enemy), the confirmed-instance base disjunction holds: either the
recurrence-tax/capacity arm

  `s₀ ≥ x₀ + Bbad + (boost+1) + ⌊C·s₀/(100−C)⌋`

or the member-cap arm `s₀ ≥ x₀ + (boost+1) + ⌊C·J₀/(100−C)⌋`. Both arms use
floored ℕ-division and hold for every `C ∈ [0,25]`. -/
theorem arms_pure
    {s0 aV xV Hpar apre xpre B_V B0 Bsup eqV Bpar
     boost d A qV qU MU Bbad C : ℕ}
    (hC : C ≤ 25)
    (hR1 : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 1 + 2 * A)
    (hR2d1 : d ≤ Hpar + Bpar)
    (hR3a : A ≤ qV * C)
    (hR3b : qV * C ≤ A + eqV)
    (hR4a : Bsup ≤ A)
    (hR4b : Bsup + eqV ≤ B_V)
    (hR8aW : s0 + aV + xV + B_V ≤ 100 * qV)
    (hR8cW : s0 + aV + xV + (Hpar + apre + xpre) + B0 ≤ 100 * qU)
    (hR8cM1 : 100 * qU ≤ MU)
    (hR8cM2 : MU ≤ 100 * qU + 99)
    (hBbad : Bbad + Bsup + eqV + Bpar ≤ B0) :
    s0 ≥ xV + xpre + Bbad + (boost + 1) + C * s0 / (100 - C)
    ∨ s0 ≥ xV + xpre + (boost + 1)
        + C * (s0 + aV + xV + (Hpar + apre + xpre)) / (100 - C) := by
  have hDpos : 0 < 100 - C := by omega
  obtain ⟨hrTlo, hrThi⟩ := div_floor_bounds (C * s0) (100 - C) hDpos
  obtain ⟨hmclo, hmchi⟩ :=
    div_floor_bounds (C * (s0 + aV + xV + (Hpar + apre + xpre))) (100 - C) hDpos
  exact arms_core hC hR1 hR2d1 hR3a hR3b hR4a hR4b hR8aW hR8cW hR8cM1 hR8cM2 hBbad
    hrTlo hrThi hmclo hmchi

/-! ## Part C — assembly from a confirmed instance

`arms_of_confirmed` produces the base arms from `is_one_confirmed = true`. The
**spec-specific** content is wired directly: `is_one_confirmed_ineq` supplies the
confirmation rule (`hR1` via `rule_to_R1`); `qU := maximum_support // 100` gives
`hR8cM` (`Nat.mul_div_le` + `div_le_hundred_mul_div_add`); `boost`, `A`, `d` are
the spec functions `compute_proposer_score` / `get_adversarial_weight` /
`get_support_discount`.

The remaining hypotheses are the **store-dynamics / accounting bridges** — the
honest/byz weight decompositions over the confirmation window `[lo, es]` and its
`V`/`pre` split. These are the explicit ledger-accounting inputs (the
`Fraction`/`EngineWindows`-style window bookkeeping and the reverse
Provenance→ground-truth bridges of `Base.weak_base_of_rule`'s `hHsup`/`hdisc`),
supplied here as explicit hypotheses tied to the real spec quantities:

* `hS` — recorded supporters `≤ s₀ + Bsup` (honest supporters within `Sval`, byz
  supporters `Bsup`); the un-netted `honest_support_majority` bridge.
* `hd` — the discount `≤ Hpar + Bpar` (`Discount.support_discount_le_parent_stuck`
  gives the stronger `≤ Hpar`; the pre-region byz `Bpar` only relaxes it).
* `hAhi`/`hAlo` — `get_adversarial_weight`'s guard bounds vs `qV·C`
  (`compute_adversarial_weight`'s `max(qV·C − eqV, 0)`; derivable by unfolding).
* `hBsup` — byz supporters `≤ get_adversarial_weight`
  (`HonestWeight.byz_score_le_adversarial_weight`).
* `hR4b`/`hR8aW` — the V-span byz-committee budget and estimate domination
  (`ByzantineBound.estimate_dominates` over `[b.slot, es]`).
* `hR8cW` — the U-span estimate domination (`estimate_dominates` over `[lo, es]`,
  the `maximum_support` window).
* `hBbad` — the accounted byz `Bsup + eqV + Bpar` sit inside the window enemy `B₀`
  (disjoint-subset weight bound; `BbadVal := B₀ − ⋯` is the Ledger-v2 definition).

Conclusion: the floored arms over `s₀`/`x₀ = xV+xpre`/`Bbad`/`J₀`, ready for
the Ledger-v2 endpoint. Same-epoch window shape is implicit in the caller's
`qV` (V-span) vs `maximum_support` (U-span) instantiation; the crossing case
(with the `999`-ceil estimate adjustment) is handled separately. -/

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Pure-ℕ: the confirmation rule `2·S + d ≥ MU + boost + 2·A + 1` with the
honest-supporter bridge `S ≤ s₀ + Bsup` yields `arms_pure`'s `hR1`. -/
private theorem rule_to_R1 {S d MU boost A s0 Bsup : ℕ}
    (hrule : 2 * S + d ≥ MU + boost + 2 * A + 1) (hS : S ≤ s0 + Bsup) :
    2 * s0 + 2 * Bsup + d ≥ MU + boost + 1 + 2 * A := by omega

/-- Pure-ℕ: `n ≤ 100·⌊n/100⌋ + 99` (the upper floor bound for `qU := MU//100`). -/
private theorem div_le_hundred_mul_div_add (n : ℕ) : n ≤ 100 * (n / 100) + 99 := by
  have e := Nat.div_add_mod n 100
  have hlt := Nat.mod_lt n (by norm_num : 0 < 100)
  omega

/-- **Assembly.** From `is_one_confirmed cfg ext store bs b = true` and the
accounting bridges (see the section note — the honest/byz window-weight
decompositions the ledger packages supply), the confirmed-instance base arms
hold over the abstract class weights `s₀`/`aV`/`xV`/`Hpar`/`apre`/`xpre` and enemy
`Bbad`. The confirmation rule and the `maximum_support // 100` bounds are wired;
the bridges are explicit store-dynamics premises. -/
theorem arms_of_confirmed
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hconf : is_one_confirmed cfg ext store bs b = true)
    {s0 aV xV Hpar apre xpre B_V B0 Bsup eqV Bpar Bbad qV : ℕ}
    (hS : get_attestation_score cfg store (get_node_for_root b) bs ≤ s0 + Bsup)
    (hd : get_support_discount cfg ext store bs b ≤ Hpar + Bpar)
    (hAhi : get_adversarial_weight cfg ext store bs b
        ≤ qV * cfg.confirmation_byzantine_threshold)
    (hAlo : qV * cfg.confirmation_byzantine_threshold
        ≤ get_adversarial_weight cfg ext store bs b + eqV)
    (hBsup : Bsup ≤ get_adversarial_weight cfg ext store bs b)
    (hR4b : Bsup + eqV ≤ B_V)
    (hR8aW : s0 + aV + xV + B_V ≤ 100 * qV)
    (hR8cW : s0 + aV + xV + (Hpar + apre + xpre) + B0
        ≤ 100 * (estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b).parent_root).slot + 1)
            (get_current_slot cfg store - 1) / 100))
    (hBbad : Bbad + Bsup + eqV + Bpar ≤ B0) :
    s0 ≥ xV + xpre + Bbad + (compute_proposer_score cfg bs + 1)
          + cfg.confirmation_byzantine_threshold * s0
              / (100 - cfg.confirmation_byzantine_threshold)
    ∨ s0 ≥ xV + xpre + (compute_proposer_score cfg bs + 1)
          + cfg.confirmation_byzantine_threshold * (s0 + aV + xV + (Hpar + apre + xpre))
              / (100 - cfg.confirmation_byzantine_threshold) := by
  have hR1 := rule_to_R1 (is_one_confirmed_ineq cfg ext hconf) hS
  exact arms_pure cfg.confirmation_byzantine_threshold_le hR1 hd hAhi hAlo hBsup hR4b hR8aW
    hR8cW (Nat.mul_div_le _ 100) (div_le_hundred_mul_div_add _) hBbad

end FastConfirmation.Spec
