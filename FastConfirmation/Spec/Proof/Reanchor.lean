module
public import FastConfirmation.Spec.Proof.LedgerV2
public import FastConfirmation.Spec.Proof.Provenance

@[expose] public section

/-!
# Spec / Proof / Reanchor: the crossing endpoint on `[slot(b′), σ]`

The crossing
epoch case (`epoch(b′) > epoch(parent(b′))`) of the head-safety ledger, whose
`[parent(b′).slot+1, σ]`-anchored full-window ledger is SAT-violable (the §11
"tax-arm landslide"), is discharged by **re-anchoring the entire engine on the
sub-window `[slot(b′), σ]`**. The pre-region `[ps+1, slot(b′)−1]` (where the
empty-slot discount lives) then enters only through the base charge, disjoint
from the sub-window honest set — which is exactly what defeats the encoding
artifact (a parent-stuck honest mass simultaneously inflating the window-cap
floor and feeding the discount credit).

The proof has three components:

* **Supporter slots and `Sclass`/`Sval` anchor invariance.**
  A `SupportsDesc b′` vote's attestation slot is `≥ (blocks b′).slot`, so a
  supporter's committee seat lies in `[slot(b′), ·]`; hence
  `Sclass (parent(b′).slot+1) σ = Sclass (slot(b′)) σ` and the base honest
  support `Sval` is identical whether anchored at `ps+1` or at `slot(b′)`. This
  is the linchpin that lands the rule's full-window charge on the sub-window `J`.
* **`reanchored_endpoint` over ℕ.** The single per-cutoff
  inequality (`interval_cases C <;> omega`): from the confirmed-instance base
  charge at `es` (`is_one_confirmed_ineq` with `MU ≥ W_U` and the sub-window
  adversarial guard) and the window `span_fraction` cap at `σ`
  (`Enemy_capacity`/`Rterm_nonneg`), the OLD-sibling endpoint
  `xP + x(σ) + Bpre + B(σ) + boost + 1 ≤ s(σ)` holds — no `INV2_step` chaining,
  no `committee_coverage`. The new sibling is the `xP = Bpre = 0` specialization.
* **The crossing GHOST step.** Instantiating the window-generic
  `Ledger`/`LedgerV2` accessors at `lo := slot(b′)` and wiring the base + cap into
  `reanchored_endpoint`, the crossing sibling loses to the `b′`-side child in
  `get_weight` (`Endpoint.ghost_arith`/`fork_weight_lt`) — the crossing analog of
  `Endpoint.ghost_step_dominates`, replacing the `INV2`-chaining that the
  same-epoch shell uses for this leg.

## Principal hypotheses

1. **`MU` is the FULL window `[parent.slot+1, current−1]`**
   (`is_one_confirmed_ineq`'s `estimate_committee_weight_between_slots … (parent.slot+1)
   (current−1)`), so `MU ≥ W_pre + W_sub`. The full-window bound is necessary for old
   siblings; a bound by `W_sub` alone is insufficient.
2. **The crossing `get_adversarial_weight(b′)` uses its full epoch-start span**
   (`get_adversarial_weight_eq`: the crossing branch runs over
   `[compute_start_slot_at_epoch(epoch b′), current−1]`, and
   `compute_start_slot_at_epoch(epoch b′) ≤ (blocks b′).slot`). The
   full-span consumer charges `qFull·C ≤ A + eqSub + eqExtra` and dominates the
   full span's actual mass; no sub-window adversarial guard is used.
3. **The discount split is overlap-safe** (`compute_empty_slot_support_discount`
   over `[parent.slot+1, slot(b′)−1]`,
   `Discount.support_discount_le_parent_stuck`): `d ≤ Hpre + Hsub`, where `Hpre`
   is the set-difference outside the sub-window and `Hsub` is already counted in
   `Aval`. No raw cross-epoch disjointness is assumed.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## `supporter_slot_ge_block` and `Sclass`/`Sval` anchor invariance

A `SupportsDesc b′` honest voter's newest-vote attestation slot `t` is `≥
(blocks b′).slot`, so its committee seat at `t` lies in `[slot(b′), σ]`. Since the
window classes are `span_committee`-filtered, lowering the anchor from
`slot(b′)` to `parent(b′).slot+1` adds no supporters — the base honest support is
the same at both anchors. This is what lets the rule's full-window charge (over
`[parent.slot+1, es]`) land on the sub-window `J` (over `[slot(b′), es]`) in
`reanchored_endpoint`'s `hMU`/`hJgrow`.

The block-slot cap `bs ≤ t` (`hslotcap`) is the provenance/head-timeliness fact:
the vote block descends from `b′` so its slot `≥ (blocks b').slot`
(`is_ancestor` slot-monotonicity, `AncestryRoots.get_ancestor_slot_le`), and the
honest head at the vote second sits at-or-below the vote slot
(`Delivery.store_blocks_slot_le_current` + cross-store `BlockAgreement`). It is
taken as a hypothesis in the same store-dynamics shape the engine ledger consumes
its class-delta facts (`Ledger.INVstar_step`, `LedgerV2.INV2_step`); the L4 fold
discharges it from `WellFormedExecution`. -/

/-- **Supporter seat in the sub-window.** An honest `SupportsDesc b′ σ` voter has a
committee seat at a slot `t ∈ [bs, σ]` (`bs := (blocks b').slot`). The seat slot is
the newest-vote slot: `≤ σ` and `i ∈ committee t` by `votes_assigned`; `bs ≤ t`
from the block-slot cap `hslotcap`. -/
theorem supporter_seat (hhb : HonestBehavior cfg ext E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {bs σ : Slot} {i : ValidatorIndex}
    (hhon : i ∈ E.honest)
    (hsupp : E.SupportsDesc cfg ext v₀ n₀ b' σ i)
    (hslotcap : ∀ (t : Slot) (k : ℕ) (a : Attestation Root), t ≤ σ →
      E.vote i t = some (k, a) →
      is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root a.data.beacon_block_root) (get_node_for_root b') = true →
      bs ≤ t) :
    ∃ t : Slot, bs ≤ t ∧ t ≤ σ ∧ i ∈ E.committee t := by
  obtain ⟨t, k, a, htσ, hvote, _, hanc⟩ := hsupp
  exact ⟨t, hslotcap t k a htσ hvote hanc, htσ,
    hhb.votes_assigned i hhon t (by rw [hvote]; exact Option.some_ne_none _)⟩

/-- **`Sclass` anchor-invariance.** With every `SupportsDesc b′ σ` supporter seated
in `[slot(b′), σ]` (`hslotcap`, per supporter) and `parent(b′).slot+1 ≤ slot(b′)`
(`hps1`), the honest support class is identical at the two anchors:
`Sclass (parent(b′).slot+1) σ = Sclass (slot(b′)) σ`. The `⊇` direction is free
(the wider window only adds members that still support); the `⊆` direction reseats
each supporter into the sub-window via `supporter_seat`. -/
theorem Sclass_anchor_invariant (hhb : HonestBehavior cfg ext E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {ps1 bs σ : Slot}
    (hps1 : ps1 ≤ bs)
    (hslotcap : ∀ i ∈ E.honest, E.SupportsDesc cfg ext v₀ n₀ b' σ i →
      ∀ (t : Slot) (k : ℕ) (a : Attestation Root), t ≤ σ →
        E.vote i t = some (k, a) →
        is_ancestor (E.store cfg ext v₀ n₀)
          (get_node_for_root a.data.beacon_block_root) (get_node_for_root b') = true →
        bs ≤ t) :
    E.Sclass cfg ext v₀ n₀ b' ps1 σ = E.Sclass cfg ext v₀ n₀ b' bs σ := by
  apply Finset.Subset.antisymm
  · intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨_, hhon⟩, hsupp⟩ := hi
    obtain ⟨t, hbst, htσ, hcomm⟩ :=
      E.supporter_seat cfg ext hhb hhon hsupp (hslotcap i hhon hsupp)
    exact ⟨⟨Finset.mem_biUnion.mpr ⟨t, Finset.mem_Icc.mpr ⟨hbst, htσ⟩, hcomm⟩, hhon⟩, hsupp⟩
  · intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨hspan, hhon⟩, hsupp⟩ := hi
    exact ⟨⟨span_committee_mono_lo hps1 hspan, hhon⟩, hsupp⟩

/-- **`Sval` anchor-invariance.** The base honest support weight is identical at
the two anchors (`E.weight` of the `Sclass_anchor_invariant`-equal sets). This is
the key link by which the rule's full-window charge
`2·s₀` lands on the sub-window `s(σ)`. -/
theorem Sval_anchor_invariant (hhb : HonestBehavior cfg ext E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {ps1 bs σ : Slot}
    (hps1 : ps1 ≤ bs)
    (hslotcap : ∀ i ∈ E.honest, E.SupportsDesc cfg ext v₀ n₀ b' σ i →
      ∀ (t : Slot) (k : ℕ) (a : Attestation Root), t ≤ σ →
        E.vote i t = some (k, a) →
        is_ancestor (E.store cfg ext v₀ n₀)
          (get_node_for_root a.data.beacon_block_root) (get_node_for_root b') = true →
        bs ≤ t) :
    E.Sval cfg ext v₀ n₀ b' ps1 σ = E.Sval cfg ext v₀ n₀ b' bs σ := by
  rw [Execution.Sval, Execution.Sval,
    E.Sclass_anchor_invariant cfg ext hhb hps1 hslotcap]

end Execution

/-! ## The pure-ℕ re-anchored endpoint

The confirmed-instance atoms (all ground-truth `Gwei` weights over
`E.span_committee`), read at the crossing geometry `p(b′) [slot ps] → b′
[slot bs] → … → b`, `pre = [ps+1, bs−1]`, `V = [bs, es]` (`es = current_slot−1`),
tail `(es, σ]`:

| atom | meaning |
|---|---|
| `s0`,`aS0`,`xS0` | honest sub-window classes at `es` (`Sval`/`Aval`/`Xval` at `[bs,es]`) |
| `Bsub0` | sub-window byz at `es` (`Bval [bs,es]`) |
| `Hpar` | parent-stuck honest (pre-region; the discount source) |
| `xP`,`Bpre` | OLD-sibling pre-region honest backers / byz (`slot < bs`) |
| `Bsup`,`eqV` | byz `b′`-supporters / equivocators inside `V` |
| `A`,`qV` | `get_adversarial_weight(b′)` / `estimate(V)//100` |
| `d`,`boost`,`MU` | `get_support_discount` / `compute_proposer_score` / `maximum_support` |
| `Bsig`,`Jsig`,`ssig`,`aSsig`,`xSsig` | sub-window byz / honest-`J` / `s` / `a` / `x` at `σ` |

For every `C ∈ [0,55]`, the hypotheses below imply the endpoint inequality for
both sibling cases. Each named hypothesis contributes one of the required base,
capacity, growth, or antitonicity bounds. -/

/-- **The re-anchored crossing endpoint, pure ℕ.**

Hypotheses:

* `hbase` — the rule at the confirmation store (`is_one_confirmed_ineq`, with the
  recorded score `= s0 + Bsup` split honest/byz): `2·s0 + 2·Bsup + d ≥ MU + boost
  + 2·A + 1`.
* `hMU` — `estimate_dominates` on the FULL window: `W_sub + (Hpar+xP+Bpre) ≤ MU`
  (anchor 1).
* `hd` — the discount is pre-only, `d ≤ Hpar` (`Discount.support_discount_le_parent_stuck`,
  anchor 3).
* `hAguard` — the sub-window adversarial guard `qV·C ≤ A + eqV`
  (`compute_adversarial_weight`; anchor 2).
* `hdom` — `estimate_dominates` on `V`: `W_sub ≤ 100·qV`.
* `hbyzsub` — byz supporters + equivocators fit the sub-window byz:
  `Bsup + eqV ≤ Bsub0`.
* `hcap` — the window `span_fraction` cap at `σ` (`Enemy_capacity`/`Rterm_nonneg`):
  `(100−C)·Bsig ≤ C·Jsig`.
* `hJgrow`/`hBgrow` — the honest / byz sub-window grows to `σ`: `J(es) ≤ Jsig`,
  `Bsub0 ≤ Bsig`.
* `hsigma` — the honest partition at `σ`: `ssig + aSsig + xSsig = Jsig`.
* `haS`/`hxS` — the `a`/`x` classes never grow (engine IH): `aSsig ≤ aS0`,
  `xSsig ≤ xS0`.
* `hC` — `C ≤ 25` (`cfg.confirmation_byzantine_threshold_le`; holds up to `C ≤ 55`).

Conclusion: `xP + xSsig + Bpre + Bsig + boost + 1 ≤ ssig` — the OLD-sibling
recorded contest at `σ`. The NEW sibling is the `xP = Bpre = 0` specialization
(`reanchored_endpoint_new`). -/
theorem reanchored_endpoint
    {s0 aS0 xS0 Bsub0 Hpar xP Bpre Bsup eqV A d boost MU qV
      Bsig Jsig ssig aSsig xSsig C : ℕ}
    (hbase : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 2 * A + 1)
    (hMU : (s0 + aS0 + xS0 + Bsub0) + (Hpar + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpar)
    (hAguard : qV * C ≤ A + eqV)
    (hdom : s0 + aS0 + xS0 + Bsub0 ≤ 100 * qV)
    (hbyzsub : Bsup + eqV ≤ Bsub0)
    (hcap : (100 - C) * Bsig ≤ C * Jsig)
    (hJgrow : s0 + aS0 + xS0 ≤ Jsig)
    (hBgrow : Bsub0 ≤ Bsig)
    (hsigma : ssig + aSsig + xSsig = Jsig)
    (haS : aSsig ≤ aS0)
    (hxS : xSsig ≤ xS0)
    (hC : C ≤ 25) :
    xP + xSsig + Bpre + Bsig + boost + 1 ≤ ssig := by
  interval_cases C <;> omega

/-- **The NEW-sibling specialization** (`xP = Bpre = 0`): a sibling `c̃` with
`slot(c̃) ≥ slot(b′)` has no pre-region backers, so its recorded contest is
`x(σ) + B(σ) + boost + 1 ≤ s(σ)`. Direct from `reanchored_endpoint` at
`xP = Bpre = 0`. -/
theorem reanchored_endpoint_new
    {s0 aS0 xS0 Bsub0 Hpar Bsup eqV A d boost MU qV
      Bsig Jsig ssig aSsig xSsig C : ℕ}
    (hbase : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 2 * A + 1)
    (hMU : (s0 + aS0 + xS0 + Bsub0) + Hpar ≤ MU)
    (hd : d ≤ Hpar)
    (hAguard : qV * C ≤ A + eqV)
    (hdom : s0 + aS0 + xS0 + Bsub0 ≤ 100 * qV)
    (hbyzsub : Bsup + eqV ≤ Bsub0)
    (hcap : (100 - C) * Bsig ≤ C * Jsig)
    (hJgrow : s0 + aS0 + xS0 ≤ Jsig)
    (hBgrow : Bsub0 ≤ Bsig)
    (hsigma : ssig + aSsig + xSsig = Jsig)
    (haS : aSsig ≤ aS0)
    (hxS : xSsig ≤ xS0)
    (hC : C ≤ 25) :
    xSsig + Bsig + boost + 1 ≤ ssig := by
  have h := reanchored_endpoint (xP := 0) (Bpre := 0) hbase
    (by simpa using hMU) hd hAguard hdom hbyzsub hcap hJgrow hBgrow hsigma haS hxS hC
  simpa using h

/-! ## Full-span, k-independent crossing endpoint

The multi-seam crossing arm keeps the real adversarial span
`[start_slot(epoch b'), es]`.  `HAextra`/`Bextra`/`eqExtra` are its prefix
outside the re-anchored sub-window; they are subsets of the pre-region masses,
and prefix equivocators are removed from the old sibling's usable `Bpre`.
No seam count or per-seam fuel occurs in this statement. -/

/-- **Full-span re-anchored endpoint with combined non-supporter
antitonicity.** The full adversarial guard and estimate, full-MU
charge, overlap-safe discount split, endpoint union cap, the combined `a+x`
bound, and the separate `x` cap imply the old-sibling strip independently of
the number of epoch seams. -/
theorem reanchored_endpoint_fullSpan
    {s0 aS0 xS0 Bsub0 Hpre Hsub xP Bpre Bsup eqSub eqExtra HAextra Bextra
      A d boost MU qFull Bsig Jsig ssig aSsig xSsig C : ℕ}
    (hbase : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 2 * A + 1)
    (hMU : (s0 + aS0 + xS0 + Bsub0) + (Hpre + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpre + Hsub)
    (hHsub : Hsub ≤ aS0)
    (hAguard : qFull * C ≤ A + eqSub + eqExtra)
    (hdom : (s0 + aS0 + xS0 + Bsub0) + HAextra + Bextra ≤ 100 * qFull)
    (hBextra : Bextra ≤ Bpre)
    (heqExtra : eqExtra ≤ Bextra)
    (hbyzsub : Bsup + eqSub ≤ Bsub0)
    (hbyzfull : Bsub0 + Bextra ≤ qFull * C)
    (hcap : (100 - C) * Bsig ≤ C * Jsig)
    (hJgrow : s0 + aS0 + xS0 ≤ Jsig)
    (hsigma : ssig + aSsig + xSsig = Jsig)
    (hAX : aSsig + xSsig ≤ aS0 + xS0)
    (hxS : xSsig ≤ xS0)
    (hC : C ≤ 25) :
    xP + xSsig + (Bpre - eqExtra) + Bsig + boost + 1 ≤ ssig := by
  interval_cases C <;> omega

/-! ## Instantiation at `lo := slot(b′)` and the crossing leg

The window-generic `Ledger`/`LedgerV2` accessors are re-instantiated at
`lo := slot(b′)`; `reanchored_endpoint`'s abstract atoms become the accessor
values (`s0 = Sval lo es`, `Bsig = Bval lo σ`, `Jsig = Jspec lo σ`, …), the window
cap `hcap` is `Rterm_nonneg lo σ` (the `Enemy_capacity`/`span_fraction` cap at
`σ`), and the honest partition / growth links are `weight_partition` / `Jspec_mono`
/ `Bval_mono`. The base-charge atoms (`hbase` from `is_one_confirmed_ineq` with the
recorded score split `= Sval + Bsup`, `hMU` from `estimate_dominates`, `hAguard`
from `get_adversarial_weight`, `hd` from `Discount.support_discount_le_parent_stuck`)
and the class-non-growth facts (`haS`/`hxS`, the engine IH) are the crossing
**certificate** — taken as hypotheses in the store-dynamics shape the L4 fold /
shell supplies (as `Ledger.INVstar_step` / `LedgerV2.INV2_step` take their
class-delta facts). The output feeds `Endpoint`'s GHOST step directly, replacing
`INV2`-chaining for this leg. -/

/-- Pure-ℕ core of the crossing GHOST step (`Gwei` weights are opaque to `omega`
across simp-rewritten atoms, so the linear arithmetic is discharged over plain ℕ
and unified via the lemma type — mirrors `Endpoint.ghost_arith`). The crossing
enemy `XB := xP + x(σ) + Bpre + B(σ)` is one ℕ atom. -/
private theorem crossing_ghost_arith {sc scc XB P S : ℕ}
    (hbside : S ≤ sc) (hend : XB + P + 1 ≤ S) (hsib : scc ≤ XB) : scc + P < sc := by omega

namespace Execution

variable (E : Execution Root)

/-- **The re-anchored endpoint over the ledger accessors** (the crossing
certificate ⟹ the per-`σ` old-sibling inequality). The window cap, honest
partition and growth links are discharged internally (`Rterm_nonneg`,
`weight_partition`, `Jspec_mono`, `Bval_mono`); the base-charge atoms
(`hbase`/`hMU`/`hd`/`hAguard`/`hdom`/`hbyzsub`) and the class-non-growth facts
(`haS`/`hxS`) are the certificate, supplied by the fold. -/
theorem reanchored_endpoint_of_certificate (hbb : ByzantineBound cfg E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es σ : Slot}
    {Bsup eqV A d MU qV Hpar xP Bpre boost : ℕ}
    (hes : es ≤ σ) (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hbase : 2 * E.Sval cfg ext v₀ n₀ b' lo es + 2 * Bsup + d ≥ MU + boost + 2 * A + 1)
    (hMU : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es) + (Hpar + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpar)
    (hAguard : qV * cfg.confirmation_byzantine_threshold ≤ A + eqV)
    (hdom : E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es ≤ 100 * qV)
    (hbyzsub : Bsup + eqV ≤ E.Bval lo es)
    (haS : E.Aval cfg ext v₀ n₀ b' lo σ ≤ E.Aval cfg ext v₀ n₀ b' lo es)
    (hxS : E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es) :
    xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hJgrow : E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
      + E.Xval cfg ext v₀ n₀ b' lo es ≤ E.Jspec lo σ := by
    rw [← E.weight_partition cfg ext v₀ n₀ b' lo es]; exact E.Jspec_mono lo hes
  have hsigma : E.Sval cfg ext v₀ n₀ b' lo σ + E.Aval cfg ext v₀ n₀ b' lo σ
      + E.Xval cfg ext v₀ n₀ b' lo σ = E.Jspec lo σ :=
    (E.weight_partition cfg ext v₀ n₀ b' lo σ).symm
  exact reanchored_endpoint hbase hMU hd hAguard hdom hbyzsub
    (E.Rterm_nonneg cfg hbb lo σ hloH hσH) hJgrow (E.Bval_mono lo hes) hsigma haS hxS
    cfg.confirmation_byzantine_threshold_le

/-- **The full-span crossing certificate over ledger accessors.**  Unlike
`reanchored_endpoint_of_certificate`, this consumer keeps the real crossing
adversarial span explicit and consumes the authorized endpoint pair: combined
antitonicity of `Aval + Xval` plus separate antitonicity of `Xval`. Prefix
equivocators `eqExtra` are removed from the pre-region enemy mass available to
an old sibling. -/
theorem reanchored_endpoint_of_fullSpan_certificate (hbb : ByzantineBound cfg E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es σ : Slot}
    {Bsup eqSub eqExtra HAextra Bextra A d MU qFull Hpre Hsub xP Bpre boost : ℕ}
    (hes : es ≤ σ) (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hbase : 2 * E.Sval cfg ext v₀ n₀ b' lo es + 2 * Bsup + d
      ≥ MU + boost + 2 * A + 1)
    (hMU : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es)
      + (Hpre + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpre + Hsub)
    (hHsub : Hsub ≤ E.Aval cfg ext v₀ n₀ b' lo es)
    (hAguard : qFull * cfg.confirmation_byzantine_threshold
      ≤ A + eqSub + eqExtra)
    (hdom : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es)
      + HAextra + Bextra ≤ 100 * qFull)
    (hBextra : Bextra ≤ Bpre)
    (heqExtra : eqExtra ≤ Bextra)
    (hbyzsub : Bsup + eqSub ≤ E.Bval lo es)
    (hbyzfull : E.Bval lo es + Bextra
      ≤ qFull * cfg.confirmation_byzantine_threshold)
    (hAX : E.Aval cfg ext v₀ n₀ b' lo σ + E.Xval cfg ext v₀ n₀ b' lo σ
      ≤ E.Aval cfg ext v₀ n₀ b' lo es + E.Xval cfg ext v₀ n₀ b' lo es)
    (hxS : E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es) :
    xP + E.Xval cfg ext v₀ n₀ b' lo σ + (Bpre - eqExtra) + E.Bval lo σ
        + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hJgrow : E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
      + E.Xval cfg ext v₀ n₀ b' lo es ≤ E.Jspec lo σ := by
    rw [← E.weight_partition cfg ext v₀ n₀ b' lo es]
    exact E.Jspec_mono lo hes
  have hsigma : E.Sval cfg ext v₀ n₀ b' lo σ + E.Aval cfg ext v₀ n₀ b' lo σ
      + E.Xval cfg ext v₀ n₀ b' lo σ = E.Jspec lo σ :=
    (E.weight_partition cfg ext v₀ n₀ b' lo σ).symm
  exact reanchored_endpoint_fullSpan hbase hMU hd hHsub hAguard hdom hBextra heqExtra
    hbyzsub hbyzfull (E.Rterm_nonneg cfg hbb lo σ hloH hσH) hJgrow hsigma hAX hxS
    cfg.confirmation_byzantine_threshold_le

/-- **The crossing GHOST step dominates** (the crossing analog of
`Endpoint.ghost_step_dominates`). From the re-anchored endpoint `hend` (the
OLD-sibling recorded contest bound, supplied by the full-span consumer), the
`b′`-side child's recorded lower bound `hbside` (`Endpoint.recorded_bside_ge` at
`lo := slot(b′)`) and the crossing sibling's recorded upper bound `hsib` (its
supporters confined to the pre-region backers `xP`/`Bpre` plus the window
`Xclass`/`Bwin` at `lo`), the sibling `cc` loses to the `b′`-side child `c` in
`get_weight`. The proposer boost is charged to the sibling in full
(`MajorityPersists.fork_weight_lt`). -/
theorem crossing_ghost_step_dominates {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c cc : Root} {lo σ : Slot} {xP Bpre : ℕ}
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hend : xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ
        + get_proposer_score cfg store + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : get_attestation_score cfg store (get_node_for_root cc)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ) :
    get_weight cfg store (ForkChoiceNode.mk cc) < get_weight cfg store (ForkChoiceNode.mk c) := by
  simp only [get_node_for_root] at hbside hsib
  exact fork_weight_lt cfg (crossing_ghost_arith hbside hend hsib)

/-- **A crossing certificate builds one `DescendStep`.** At a fork with parent `h`
and `b′`-side child `c` (a filtered-tree child), the re-anchored endpoint `hend`
plus the `b′`-side lower bound `hbside` plus an old-sibling upper bound `hsib` *for
every competing child* dominate the fork in `get_weight`, so `c` is the descent-step
choice. The crossing analog of `Endpoint.ledger_descendStep`. -/
theorem crossing_ledger_descendStep {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot} {xP Bpre : ℕ}
    (hchild : ForkChoiceNode.mk c ∈
      get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h))
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hend : xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ
        + get_proposer_score cfg store + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' ∈
        get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h) →
      c' ≠ c →
      get_attestation_score cfg store (get_node_for_root c')
          (store.checkpoint_states store.justified_checkpoint)
        ≤ xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c :=
  descendStep_of_dom cfg hchild
    (fun c' hc' hne => E.crossing_ghost_step_dominates cfg ext hbside hend (hsib c' hc' hne))

end Execution

end FastConfirmation.Spec

end
