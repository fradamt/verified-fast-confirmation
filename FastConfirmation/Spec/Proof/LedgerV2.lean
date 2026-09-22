module
public import FastConfirmation.Spec.Proof.Arms
public import FastConfirmation.Spec.Proof.Endpoint

@[expose] public section

/-!
# Spec / Proof / LedgerV2: enemy = `Bbad` + spent capacity

This is the head-safety ledger's corrected persistence invariant. Its enemy is
not the whole-window Byzantine set `Bval` (`Proof/Ledger.lean`) but the strictly
smaller **`Bbad(σ) + spent(σ)`**:

* `Bbad` (`BbadVal`) — the byz window members of `[lo, es]` that are already
  **sibling-ward recorded at `es`**: non-honest, non-equivocating (`v₀`-known
  equivocators relay out by `attester_slashing_relay`), and neither supporting
  `subtree(b′)` nor an ancestor of `b′`. This is the byz analog of `Xclass` at
  `es`; it excludes the byz `b′`-supporters (`Bsup`), the parent-stuck byz
  (`Bpar`, ancestor-voting), and the equivocators (`eq`) — exactly the
  `B₀ − Bsup − eq − Bpar` of the z3 accounting.
* `spent` (`SpentCap`) — the byz of the **tail** window `(es, σ]`: every later
  sibling-ward byz vote (a defection or a fresh arrival) is an attestation at the
  voter's own assignment slot `t ∈ (es, σ]`, so it pays per-slot `span_fraction`
  (F3) capacity fueled by that slot's honest recurrence. `SpentCap` grows
  pay-go and `SpentCap es = 0`.

`Enemy σ := weight (BbadSet ∪ SpentSet σ)` (`LedgerV2`/§9 union form; `≤ BbadVal + SpentCap
σ` via `Enemy_le_sum`, and the capacity cap `D·Enemy ≤ C·J` is now *derivable* from
`BbadSet ∪ SpentSet ⊆ Bwin lo σ` + `span_fraction`, counting each byz member once).
The invariant mirrors v1's `INVstar` but is
**floored** (an ℕ-division reserve: integer arrivals cannot consume
fractional slack) and carries `Enemy` in place of `Bval`:

  INV2(σ):  `x(σ) + Enemy(σ) + boost + 1`
            `+ min (⌊C·U(σ)/D⌋) (⌊C·J(σ)/D⌋ − Enemy(σ)) ≤ s(σ)`

with `C := confirmation_byzantine_threshold ≤ 25`, `D := 100 − C`. This module
delivers the **vocabulary** (`BbadSet`/`SpentSet`, their weights, `Enemy`,
`INV2`), the **set-level `span_fraction` facts** (`BbadVal ≤ Bval`,
`BbadVal ≤ ⌊C·J/D⌋`, `SpentCap` per-slot bound, monotonicity), the **base**
(`INV2(es)` from the `Arms` arms disjunction), the **endpoint strip**
(`INV2 ⟹` the plain per-`σ` inequality `Endpoint.lean` consumes) and its
**sibling bridge** (recorded sibling score `≤ Xval + Enemy`), the **pure-ℕ step**
(defections pay: `interval_cases C <;> omega` over floor witnesses), and the
**saturation** lemma consuming `committee_coverage`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the v2 enemy sets -/

open Classical in
/-- `BbadSet` — the base enemy in **recorded** form (`recorded-base reduction` reshape): non-honest,
`(v₀, n₀)`-non-equivocating members of the window `[lo, es]` whose **recorded** latest
message at `(v₀, n₀)` is **sibling-ward** — recorded neither `b′`-supporting
(`¬ lm.root ⪰ b′`) nor a `b′`-ancestor (`¬ b′ ⪰ lm.root`). Byzantine enemies are only
knowable through the store's recorded latest message (there is no
`HonestBehavior.no_forgery` for byz, so the ground `E.vote` and the recorded message
diverge); this is the recorded analog of `Xclass es`, definitionally equal to
`ByzVpre.RecByzSibBase cfg ext v₀ n₀ b′ lo es`. It still excludes `Bsup`, `Bpar` and
the relayed equivocators, and sits inside the window byz set `Bwin lo es` (only the
`span_committee`/`∉ honest` prefix is read by the accounting). -/
noncomputable def BbadSet (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo es).filter (fun i => i ∉ E.honest)).filter
    (fun i => i ∉ (E.store cfg ext v₀ n₀).equivocating_indices ∧
      ∀ lm : LatestMessage Root, (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        ¬ is_ancestor (E.store cfg ext v₀ n₀)
            (get_node_for_root lm.root) (get_node_for_root b') = true ∧
        ¬ is_ancestor (E.store cfg ext v₀ n₀)
            (get_node_for_root b') (get_node_for_root lm.root) = true)

/-- `SpentSet σ` — the byz of the tail window `(es, σ]`; their per-slot votes pay
`span_fraction` capacity. -/
def SpentSet (es σ : Slot) : Finset ValidatorIndex :=
  (E.span_committee (es + 1) σ).filter (fun i => i ∉ E.honest)

/-! ## Section 2 — weight accessors -/

/-- `Bbad` — base-enemy weight. -/
noncomputable def BbadVal (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) : Gwei :=
  E.weight (E.BbadSet cfg ext v₀ n₀ b' lo es)

/-- `spent(σ)` — tail-byz weight. -/
noncomputable def SpentCap (es σ : Slot) : Gwei :=
  E.weight (E.SpentSet es σ)

/-- `Enemy(σ) := weight (BbadSet ∪ SpentSet σ)` — the v2 enemy as a **union** weight
(`LedgerV2`, §9). A validator has one latest message, so the semantic enemy is a subset of
the union; counting members **once** is what makes the capacity cap `D·Enemy ≤ C·J`
derivable (`Enemy_capacity`) — the cross-epoch double-seat problem of the sum form
vanishes. `Enemy ≤ Bbad + spent` (`Enemy_le_sum`) keeps the step's additive arrival
accounting. -/
noncomputable def Enemy (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) : Gwei :=
  E.weight (E.BbadSet cfg ext v₀ n₀ b' lo es ∪ E.SpentSet es σ)

/-- **Sum-form upper bound.** `Enemy(σ) ≤ Bbad + spent(σ)` — subadditivity of
`E.weight` over the union. The step's arrival accounting (`hE' : Enemy σ' ≤ Enemy σ +
β`) is discharged additively through this bound; the union form is only needed for the
tight member cap. -/
theorem Enemy_le_sum (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) :
    E.Enemy cfg ext v₀ n₀ b' lo es σ ≤
      E.BbadVal cfg ext v₀ n₀ b' lo es + E.SpentCap es σ := by
  simp only [Execution.Enemy, Execution.BbadVal, Execution.SpentCap]
  exact weight_union_le _ _

/-! ## Section 3 — easy set-level facts -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The tail window is empty at `σ = es` (`Icc (es+1) es = ∅`), so `spent(es) = 0`. -/
theorem SpentCap_es_zero (es : Slot) : E.SpentCap es es = 0 := by
  simp only [Execution.SpentCap, Execution.SpentSet, Execution.span_committee]
  rw [Finset.Icc_eq_empty (Nat.not_succ_le_self es)]
  simp [Execution.weight]

omit [LinearOrder Root] [Inhabited Root] in
/-- The tail byz set is empty at `σ = es` (`Icc (es+1) es = ∅`). -/
theorem SpentSet_es_empty (es : Slot) : E.SpentSet es es = ∅ := by
  simp only [Execution.SpentSet, Execution.span_committee]
  rw [Finset.Icc_eq_empty (Nat.not_succ_le_self es)]
  simp

/-- `Enemy(es) = Bbad` (the tail set vanishes at the window start, so the union
collapses to `BbadSet`). -/
theorem Enemy_es_eq_BbadVal (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    E.Enemy cfg ext v₀ n₀ b' lo es es = E.BbadVal cfg ext v₀ n₀ b' lo es := by
  rw [Execution.Enemy, E.SpentSet_es_empty es, Finset.union_empty, Execution.BbadVal]

/-- `BbadSet ⊆ Bwin`: the base enemy is a subset of the window byz. -/
theorem BbadSet_subset_Bwin (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    E.BbadSet cfg ext v₀ n₀ b' lo es ⊆ E.Bwin lo es := by
  intro i hi
  simp only [Execution.BbadSet, Finset.mem_filter] at hi
  exact Finset.mem_filter.mpr ⟨hi.1.1, hi.1.2⟩

/-- `Bbad ≤ B(es)` — the base enemy weight is at most the window byz weight. -/
theorem BbadVal_le_Bval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    E.BbadVal cfg ext v₀ n₀ b' lo es ≤ E.Bval lo es :=
  E.weight_mono (E.BbadSet_subset_Bwin cfg ext v₀ n₀ b' lo es)

/-! ## Section 4 — the `span_fraction` capacity bounds on the enemy

The base enemy sits inside the window byz set, so `Rterm_nonneg`'s
`(100−C)·B(es) ≤ C·J(es)` passes to it: `D·Bbad ≤ C·J₀`, hence
`Bbad ≤ ⌊C·J₀/D⌋`. The tail byz `spent` is `span_fraction`-bounded on the tail
window directly. -/

/-- **`Bbad` sits under the F3 capacity**: `(100−C)·Bbad ≤ C·J(es)`. From
`Rterm_nonneg` on the window `[lo, es]` (`(100−C)·B(es) ≤ C·J(es)`) and
`BbadVal ≤ Bval`. -/
theorem BbadVal_capacity (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es) :
    (100 - cfg.confirmation_byzantine_threshold) * E.BbadVal cfg ext v₀ n₀ b' lo es ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo es := by
  refine le_trans ?_ (E.Rterm_nonneg cfg hbb lo es hloH hesH)
  gcongr
  exact E.BbadVal_le_Bval cfg ext v₀ n₀ b' lo es

/-- **`Bbad ≤ ⌊C·J(es)/D⌋`.** The floored form of `BbadVal_capacity` (`D > 0` from
`C ≤ 25`); lets the member-cap reserve `⌊C·J/D⌋ − Bbad` be un-truncated at the
base. -/
theorem BbadVal_le_floor_capacity (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es) :
    E.BbadVal cfg ext v₀ n₀ b' lo es ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo es
        / (100 - cfg.confirmation_byzantine_threshold) := by
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le; omega
  rw [Nat.le_div_iff_mul_le hDpos, Nat.mul_comm]
  exact E.BbadVal_capacity cfg ext hbb v₀ n₀ b' lo es hloH hesH

omit [LinearOrder Root] [Inhabited Root] in
/-- `spent(σ)` is exactly the window byz weight of the tail `(es, σ]`
(`SpentSet = Bwin (es+1) σ` definitionally). -/
theorem SpentCap_eq_Bval (es σ : Slot) : E.SpentCap es σ = E.Bval (es + 1) σ := by
  simp only [Execution.SpentCap, Execution.SpentSet, Execution.Bval, Execution.Bwin]

omit [LinearOrder Root] [Inhabited Root] in
/-- **The tail pays per-window `span_fraction`.** `(100−C)·spent(σ) ≤ C·J(es+1, σ)`
— `Rterm_nonneg` on the tail window `[es+1, σ]`, the F3 capacity that funds the
byz arrivals `spent` accrues from honest recurrence. -/
theorem SpentCap_capacity (hbb : ByzantineBound cfg E) (es σ : Slot)
    (hes1H : E.SlotWithinHorizon cfg (es + 1))
    (hσH : E.SlotWithinHorizon cfg σ) :
    (100 - cfg.confirmation_byzantine_threshold) * E.SpentCap es σ ≤
      cfg.confirmation_byzantine_threshold * E.Jspec (es + 1) σ := by
  rw [E.SpentCap_eq_Bval es σ]
  exact E.Rterm_nonneg cfg hbb (es + 1) σ hes1H hσH

/-- **The union enemy sits under the F3 capacity on `[lo, σ]`** (`LedgerV2`): the whole
enemy — counted once — is confined to the window byz `Bwin lo σ`, so `Rterm_nonneg`
on `[lo, σ]` gives `(100−C)·Enemy(σ) ≤ C·J(σ)`. This is the cap the step consumes at
both `σ` and `σ'`; the union form is what makes it hold *with members counted once*
(the sum form `Bbad + spent` double-counts the seam and does not close cross-epoch).
Needs `lo ≤ es + 1` (the tail `(es, σ]` starts inside the window) and `es ≤ σ` (the
base window `[lo, es]` lies inside `[lo, σ]`). -/
theorem Enemy_capacity (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (hloH : E.SlotWithinHorizon cfg lo) (hσH : E.SlotWithinHorizon cfg σ)
    (hlo : lo ≤ es + 1) (hes : es ≤ σ) :
    (100 - cfg.confirmation_byzantine_threshold) * E.Enemy cfg ext v₀ n₀ b' lo es σ ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo σ := by
  have hsub : E.Enemy cfg ext v₀ n₀ b' lo es σ ≤ E.Bval lo σ := by
    rw [Execution.Enemy, Execution.Bval]
    apply E.weight_mono
    apply Finset.union_subset
    · exact Finset.Subset.trans (E.BbadSet_subset_Bwin cfg ext v₀ n₀ b' lo es)
        (E.Bwin_mono lo hes)
    · rw [Execution.SpentSet, Execution.Bwin]
      exact Finset.filter_subset_filter _ (span_committee_mono_lo hlo)
  refine le_trans ?_ (E.Rterm_nonneg cfg hbb lo σ hloH hσH)
  gcongr

/-! ## Section 5 — monotonicity of the tail / enemy -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The tail byz set grows with the window end. -/
theorem SpentSet_mono (es : Slot) {σ σ' : Slot} (h : σ ≤ σ') :
    E.SpentSet es σ ⊆ E.SpentSet es σ' := by
  simp only [Execution.SpentSet]
  exact Finset.filter_subset_filter _ (E.span_committee_mono (es + 1) h)

omit [LinearOrder Root] [Inhabited Root] in
/-- Tail-byz weight `spent` is monotone in the window end. -/
theorem SpentCap_mono (es : Slot) {σ σ' : Slot} (h : σ ≤ σ') :
    E.SpentCap es σ ≤ E.SpentCap es σ' :=
  E.weight_mono (E.SpentSet_mono es h)

/-- The enemy `weight (Bbad ∪ spent)` is monotone in the window end (the tail set
`SpentSet` grows, so the union grows). -/
theorem Enemy_mono (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    {σ σ' : Slot} (h : σ ≤ σ') :
    E.Enemy cfg ext v₀ n₀ b' lo es σ ≤ E.Enemy cfg ext v₀ n₀ b' lo es σ' := by
  simp only [Execution.Enemy]
  exact E.weight_mono (Finset.union_subset_union (subset_refl _) (E.SpentSet_mono es h))

/-! ## Section 6 — the v2 invariant and the endpoint strip -/

/-- **INV2** at window end `σ` (floored, `C := confirmation_byzantine_threshold`,
`D := 100 − C`): the honest support `s(σ)` covers the sibling-stuck honest `x(σ)`,
the v2 enemy `Enemy(σ) = Bbad + spent(σ)`, the boost margin, and a floored `min`
reserve — the recurrence tax `⌊C·U(σ)/D⌋` on unrecurred base supporters and the
remaining member capacity `⌊C·J(σ)/D⌋ − Enemy(σ)`. Mirrors v1's `INVstar` with
`Bval` replaced by the smaller `Enemy` and the reserve floored. -/
def INV2 (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (boost : ℕ) : Prop :=
  E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
      + min (cfg.confirmation_byzantine_threshold * E.Uval cfg ext v₀ n₀ b' lo es σ
              / (100 - cfg.confirmation_byzantine_threshold))
          (cfg.confirmation_byzantine_threshold * E.Jspec lo σ
              / (100 - cfg.confirmation_byzantine_threshold)
            - E.Enemy cfg ext v₀ n₀ b' lo es σ)
    ≤ E.Sval cfg ext v₀ n₀ b' lo σ

/-- **The endpoint strip.** Dropping the nonnegative `min` reserve, `INV2` yields
the plain per-`σ` inequality the endpoint (`Endpoint.lean`) consumes, with the v2
enemy `Bbad + spent(σ)` in place of `Bval`:
`x(σ) + Enemy(σ) + boost + 1 ≤ s(σ)`. -/
theorem INV2_endpoint (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (boost : ℕ) (hinv : E.INV2 cfg ext v₀ n₀ b' lo es σ boost) :
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ :=
  le_trans (Nat.le_add_right _ _) hinv

/-! ## Section 7 — the base `INV2(es)` from the `Arms` arms -/

/-- Pure-ℕ base assembly: from the floored arms disjunction (tax arm
`X + Bbad + m₁ + rS ≤ S`, member arm `X + m₁ + rJ ≤ S`) and `Bbad ≤ rJ`, the
floored `min` invariant holds. The member arm folds `Bbad` back out of `rJ`
(un-truncated by `Bbad ≤ rJ`). -/
private theorem inv2_base_arith {X Bbad m1 rS rJ S : ℕ}
    (harm : X + Bbad + m1 + rS ≤ S ∨ X + m1 + rJ ≤ S) (hcap : Bbad ≤ rJ) :
    X + Bbad + m1 + min rS (rJ - Bbad) ≤ S := by
  rcases harm with h | h
  · exact le_trans (by have := min_le_left rS (rJ - Bbad); omega) h
  · have := min_le_right rS (rJ - Bbad); omega

/-- **INV2 at the window start `σ = es`** from the `Arms` base arms. At `es` the
unrecurred set is all of `Sclass es` (`U(es) = s₀`, `Base.Uval_es_eq_Sval`) and
`spent(es) = 0` (`Enemy(es) = Bbad`), so `INV2(es)` reduces to the floored `min`
over `⌊C·s₀/D⌋` and `⌊C·J₀/D⌋ − Bbad`, discharged by the arms disjunction
(`Arms.arms_of_confirmed`, in `Ledger`-accessor form) and `Bbad ≤ ⌊C·J₀/D⌋`. -/
theorem INV2_base_of_arms (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es)
    (harm :
      E.Xval cfg ext v₀ n₀ b' lo es + E.BbadVal cfg ext v₀ n₀ b' lo es + (boost + 1)
          + cfg.confirmation_byzantine_threshold * E.Sval cfg ext v₀ n₀ b' lo es
              / (100 - cfg.confirmation_byzantine_threshold)
        ≤ E.Sval cfg ext v₀ n₀ b' lo es
      ∨ E.Xval cfg ext v₀ n₀ b' lo es + (boost + 1)
          + cfg.confirmation_byzantine_threshold * E.Jspec lo es
              / (100 - cfg.confirmation_byzantine_threshold)
        ≤ E.Sval cfg ext v₀ n₀ b' lo es) :
    E.INV2 cfg ext v₀ n₀ b' lo es es boost := by
  simp only [Execution.INV2]
  rw [E.Enemy_es_eq_BbadVal cfg ext v₀ n₀ b' lo es, E.Uval_es_eq_Sval cfg ext v₀ n₀ b' lo es]
  exact inv2_base_arith harm
    (E.BbadVal_le_floor_capacity cfg ext hbb v₀ n₀ b' lo es hloH hesH)

private theorem reclassify_tax_arm
    {s xV xpre OV Opre X O B boost r : ℕ}
    (hX : xV + xpre = X) (hO : OV + Opre = O)
    (h : s ≥ (xV + OV) + (xpre + Opre) + B + (boost + 1) + r) :
    X + B + (boost + O + 1) + r ≤ s := by omega

private theorem reclassify_member_arm
    {s xV xpre OV Opre X O boost r : ℕ}
    (hX : xV + xpre = X) (hO : OV + Opre = O)
    (h : s ≥ (xV + OV) + (xpre + Opre) + (boost + 1) + r) :
    X + (boost + O + 1) + r ≤ s := by omega

/-- The payload-aware base potential charges the opposite ancestor votes in
the same `boost` position as a fixed debt. This is the invariant needed to
carry that debt through the existing `INV2_step` recurrence. -/
theorem INV2_base_of_confirmed_with_opposite (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b' : Root}
    (hconf : is_one_confirmed cfg ext store bs b' = true)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (lo es : Slot) (boost O : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es)
    {s0 aV xV G Opre OV apre xpre B_V B0 Bsup eqV Bpar Bbad qV : ℕ}
    (hboost : boost = compute_proposer_score cfg bs)
    (hS : get_attestation_score cfg store (get_node_for_root b') bs ≤ s0 + Bsup)
    (hd : get_support_discount cfg ext store bs b' ≤ G + Bpar)
    (hAhi : get_adversarial_weight cfg ext store bs b'
        ≤ qV * cfg.confirmation_byzantine_threshold)
    (hAlo : qV * cfg.confirmation_byzantine_threshold
        ≤ get_adversarial_weight cfg ext store bs b' + eqV)
    (hBsup : Bsup ≤ get_adversarial_weight cfg ext store bs b')
    (hR4b : Bsup + eqV ≤ B_V)
    (hR8aW : s0 + (aV + OV) + xV + B_V ≤ 100 * qV)
    (hR8cW : s0 + (aV + OV) + xV + (G + Opre + apre + xpre) + B0
        ≤ 100 * (estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b').parent_root).slot + 1)
            (get_current_slot cfg store - 1) / 100))
    (hBbad : Bbad + Bsup + eqV + Bpar ≤ B0)
    (hSval : s0 = E.Sval cfg ext v₀ n₀ b' lo es)
    (hXval : xV + xpre = E.Xval cfg ext v₀ n₀ b' lo es)
    (hBbadVal : Bbad = E.BbadVal cfg ext v₀ n₀ b' lo es)
    (hOval : OV + Opre = O)
    (hJval : s0 + (aV + OV) + xV + (G + Opre + apre + xpre) =
      E.Jspec lo es) :
    E.INV2 cfg ext v₀ n₀ b' lo es es (boost + O) := by
  have harm := arms_of_confirmed_with_opposite cfg ext hconf hS hd hAhi hAlo
    hBsup hR4b hR8aW hR8cW hBbad
  have hJval' : s0 + aV + (xV + OV) + (G + apre + (xpre + Opre)) =
      E.Jspec lo es := by omega
  rw [← hboost, hJval', hSval, hBbadVal] at harm
  have harm' :
      E.Xval cfg ext v₀ n₀ b' lo es + E.BbadVal cfg ext v₀ n₀ b' lo es +
          (boost + O + 1) +
          cfg.confirmation_byzantine_threshold * E.Sval cfg ext v₀ n₀ b' lo es /
            (100 - cfg.confirmation_byzantine_threshold) ≤
            E.Sval cfg ext v₀ n₀ b' lo es
      ∨ E.Xval cfg ext v₀ n₀ b' lo es + (boost + O + 1) +
          cfg.confirmation_byzantine_threshold * E.Jspec lo es /
            (100 - cfg.confirmation_byzantine_threshold) ≤
            E.Sval cfg ext v₀ n₀ b' lo es := by
    rcases harm with h | h
    · left; exact reclassify_tax_arm hXval hOval h
    · right; exact reclassify_member_arm hXval hOval h
  exact E.INV2_base_of_arms cfg ext hbb v₀ n₀ b' lo es (boost + O)
    hloH hesH harm'

/-! ## Section 8 — the v2 sibling bridge (endpoint result 5)

`Endpoint.recorded_sibling_le` bounds a sibling's recorded score by `Xval + Bval`
(the whole window byz). The v2 refinement confines the byz supporters to the
smaller v2 enemy sets `BbadSet ∪ SpentSet` (the store-dynamics fact the shell
supplies: a byz recorded as backing a sibling of `b′` at `(w, m)` is either
already sibling-recorded at `es` — in `BbadSet` — or defected/arrived after `es`,
so it has a tail assignment — in `SpentSet`; equivocators relay out and score
zero), giving the tighter `Xval + Enemy(σ)`. -/

/-- **Recorded sibling upper bound, v2.** With the honest sibling supporters
confined to `Xclass` (`hHon`, as in `Endpoint.recorded_sibling_le`) and the byz
sibling supporters confined to `BbadSet ∪ SpentSet` (`hByz`, the v2 byz
confinement), the recorded attestation score of a sibling `cc` is at most
`Xval(σ) + Enemy(σ)`. Subadditivity of `E.weight` over the three-way union. -/
theorem recorded_sibling_le_v2 {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' cc : Root} {lo es σ : Slot}
    (hHon : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∉ E.honest →
        i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ) :
    get_attestation_score cfg store (get_node_for_root cc) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ := by
  rw [attestation_score_eq_weight cfg hval, Execution.Xval, Execution.Enemy]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  intro i hi
  rw [List.mem_toFinset] at hi
  rw [Finset.mem_union]
  by_cases hh : i ∈ E.honest
  · exact Or.inl (hHon i hi hh)
  · exact Or.inr (Finset.mem_union.mpr (hByz i hi hh))

/-- The complete opposite resolved-status score is charged to the current
sibling class, the v2 enemy, and the fixed source opposite ancestor debt. -/
theorem recorded_opposite_status_le_v2
    {store source : Store Root} {bs bsSource : BeaconState Root}
    (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root}
    {lo es σ : Slot} {other : PayloadStatus}
    (hHon : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ ∨
          i ∈ OppositeAncestorClass cfg ext E source bsSource
            v₀ n₀ b' h lo es other)
    (hByz : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∉ E.honest →
        i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ) :
    get_attestation_score cfg store (ForkChoiceNode.mk h other) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ +
        E.weight (OppositeAncestorClass cfg ext E source bsSource
          v₀ n₀ b' h lo es other) := by
  rw [attestation_score_eq_weight cfg hval, Execution.Xval, Execution.Enemy]
  refine le_trans (E.weight_mono ?_)
    ((weight_union_le _ _).trans
      (Nat.add_le_add_right (weight_union_le _ _) _))
  intro i hi
  rw [List.mem_toFinset] at hi
  rw [Finset.mem_union]
  by_cases hh : i ∈ E.honest
  · rcases hHon i hi hh with hX | hO
    · exact Or.inl (Finset.mem_union.mpr (Or.inl hX))
    · exact Or.inr hO
  · exact Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (hByz i hi hh))))

private theorem inv2_opposite_margin_arith
    {X B boost O S opp selected : ℕ}
    (hstrip : X + B + (boost + O) + 1 ≤ S)
    (hopp : opp ≤ X + B + O) (hselected : S ≤ selected) :
    opp + boost < selected := by omega

/-- The strengthened `INV2` debt yields the required payload status margin
once each competing status score is confined to `X + Enemy + O`. -/
theorem pendingStatusMargin_of_INV2_opposite
    {store : Store Root} {blocks : List Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root}
    {lo es σ : Slot} {status : PayloadStatus} {boost O : ℕ}
    (hmem : ForkChoiceNode.mk h status ∈
      get_node_children store blocks (ForkChoiceNode.mk h .pending))
    (hnotPrev : is_previous_slot_payload_decision cfg store
      (ForkChoiceNode.mk h status) = false)
    (hselected : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (ForkChoiceNode.mk h status)
        (store.checkpoint_states store.justified_checkpoint))
    (hboost : boost = get_proposer_score cfg store)
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es σ (boost + O))
    (hopp : ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
      other ≠ ForkChoiceNode.mk h status →
      get_attestation_score cfg store other
        (store.checkpoint_states store.justified_checkpoint) ≤
          E.Xval cfg ext v₀ n₀ b' lo σ +
            E.Enemy cfg ext v₀ n₀ b' lo es σ + O) :
    PendingStatusMargin cfg store blocks h status := by
  refine ⟨hmem, ?_⟩
  intro other hm hne
  left
  constructor
  · have hstrip := E.INV2_endpoint cfg ext v₀ n₀ b' lo es σ
      (boost + O) hinv
    rw [hboost] at hstrip
    exact inv2_opposite_margin_arith hstrip (hopp other hm hne) hselected
  · exact hnotPrev

/-! ## Section 9 — the pure-ℕ v2 step ("defections pay")

The floored ledger step: `INV2(σ) ⟹ INV2(σ')` over the per-slot class deltas the
engine shell discharges (`ξ` = `x→s` migrants, `α` = `a→s` migrants, `φ` = fresh
honest joining `s`, `β` = new tail byz, `σt` = base supporters recurring off
`Unrec`). The reserve is floored (ℕ-division), so the step relies on the floor
witnesses' two-sided bounds; the byz arrival `β` pays the per-slot `span_fraction`
capacity `D·β ≤ C·(σt+ξ+α+φ)` (F3). Enemy caps `D·E ≤ C·J` at both ends keep the
member reserve un-truncated. `interval_cases C` turns every `C`/`D` product into a
literal-coefficient linear term and `omega` closes each of the 26 cases (the `min`
is split internally). -/

/-- **The v2 step, pure ℕ.** All floor terms are abstract witnesses `rU`, `rU'`,
`rJ`, `rJ'` with their two-sided division bounds. From `INV2(σ)` in the floored
`min` form, the per-slot deltas, F3, and the enemy caps, `INV2(σ')` follows.
Machine-checked by `interval_cases C <;> omega`. -/
private theorem inv2_step_arith
    {s s' x x' EE EE' J J' U U' boost ξ α φ β σt C rU rU' rJ rJ' : ℕ}
    (hC : C ≤ 25)
    (hINV : x + EE + boost + 1 + min rU (rJ - EE) ≤ s)
    (hs' : s + ξ + α + φ ≤ s')
    (hx' : x' + ξ ≤ x)
    (hE' : EE' ≤ EE + β)
    (hJ' : J' = J + φ)
    (hU' : U' + σt ≤ U)
    (hF3 : (100 - C) * β ≤ C * (σt + ξ + α + φ))
    (hEcap : (100 - C) * EE ≤ C * J)
    (hEcap' : (100 - C) * EE' ≤ C * J')
    (hrUlo : (100 - C) * rU ≤ C * U) (hrUhi : C * U < (100 - C) * (rU + 1))
    (hrU'lo : (100 - C) * rU' ≤ C * U') (hrU'hi : C * U' < (100 - C) * (rU' + 1))
    (hrJlo : (100 - C) * rJ ≤ C * J) (hrJhi : C * J < (100 - C) * (rJ + 1))
    (hrJ'lo : (100 - C) * rJ' ≤ C * J') (hrJ'hi : C * J' < (100 - C) * (rJ' + 1)) :
    x' + EE' + boost + 1 + min rU' (rJ' - EE') ≤ s' := by
  interval_cases C <;> omega

/-- Two-sided floor bounds of `n / m` (`0 < m`) as linear atoms (`omega` combines
`div_add_mod` with `mod_lt`). Local copy of `Arms.div_floor_bounds`. -/
private theorem div_floor_bounds (n m : ℕ) (hm : 0 < m) :
    m * (n / m) ≤ n ∧ n < m * (n / m + 1) := by
  have e := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  rw [Nat.mul_succ]
  omega

/-- **The v2 step over the ledger defs.** Given the per-slot class deltas as ℕ
relations between the accessor values at `σ` and `σ'` (the store-dynamics facts
the engine shell discharges from `votes_head` + IH + delivery +
`committee_assignment_unique`) and the per-slot F3 bound `hF3`, `INV2(σ)` propagates
to `INV2(σ')`. The enemy caps `D·Enemy ≤ C·J` at both `σ` and `σ'` are now **derived**
internally (`Enemy_capacity`, from the union confinement `BbadSet ∪ SpentSet ⊆ Bwin`
+ `span_fraction`) rather than assumed — the union `Enemy` counts each byz member
once, so the caps hold uniformly and the epoch-seam double-recurrence corner never arises. Gated by
`hlo : lo ≤ es + 1` and `hσ`/`hσ' : es ≤ σ, es ≤ σ'`. The reserve floor witnesses are
supplied from `div_floor_bounds`; the linear ledger arithmetic is handed to
`inv2_step_arith`. -/
theorem INV2_step (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) {σ σ' : Slot}
    (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ) (hσ'H : E.SlotWithinHorizon cfg σ')
    (boost ξ α φ β σt : ℕ)
    (hlo : lo ≤ es + 1) (hσ : es ≤ σ) (hσ' : es ≤ σ')
    (hs' : E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α + φ ≤ E.Sval cfg ext v₀ n₀ b' lo σ')
    (hx' : E.Xval cfg ext v₀ n₀ b' lo σ' + ξ ≤ E.Xval cfg ext v₀ n₀ b' lo σ)
    (hE' : E.Enemy cfg ext v₀ n₀ b' lo es σ' ≤ E.Enemy cfg ext v₀ n₀ b' lo es σ + β)
    (hJ' : E.Jspec lo σ' = E.Jspec lo σ + φ)
    (hU' : E.Uval cfg ext v₀ n₀ b' lo es σ' + σt ≤ E.Uval cfg ext v₀ n₀ b' lo es σ)
    (hF3 : (100 - cfg.confirmation_byzantine_threshold) * β ≤
      cfg.confirmation_byzantine_threshold * (σt + ξ + α + φ))
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es σ boost) :
    E.INV2 cfg ext v₀ n₀ b' lo es σ' boost := by
  simp only [Execution.INV2] at hinv ⊢
  have hEcap := E.Enemy_capacity cfg ext hbb v₀ n₀ b' lo es σ hloH hσH hlo hσ
  have hEcap' := E.Enemy_capacity cfg ext hbb v₀ n₀ b' lo es σ' hloH hσ'H hlo hσ'
  set C := cfg.confirmation_byzantine_threshold with hCdef
  have hC25 : C ≤ 25 := cfg.confirmation_byzantine_threshold_le
  have hDpos : 0 < 100 - C := by omega
  obtain ⟨hrUlo, hrUhi⟩ := div_floor_bounds (C * E.Uval cfg ext v₀ n₀ b' lo es σ) (100 - C) hDpos
  obtain ⟨hrU'lo, hrU'hi⟩ :=
    div_floor_bounds (C * E.Uval cfg ext v₀ n₀ b' lo es σ') (100 - C) hDpos
  obtain ⟨hrJlo, hrJhi⟩ := div_floor_bounds (C * E.Jspec lo σ) (100 - C) hDpos
  obtain ⟨hrJ'lo, hrJ'hi⟩ := div_floor_bounds (C * E.Jspec lo σ') (100 - C) hDpos
  exact inv2_step_arith hC25 hinv hs' hx' hE' hJ' hU' hF3 hEcap hEcap'
    hrUlo hrUhi hrU'lo hrU'hi hrJlo hrJhi hrJ'lo hrJ'hi

/-! ## Section 10 — saturation after `T1`, consuming `committee_coverage`

Beyond `T1 := end of epoch(es) + SLOTS_PER_EPOCH`, every honest active validator
has had an assignment in `(es, σ]` (`committee_coverage`: committees partition the
active set each epoch), so it has re-voted `desc(b′)` and left `Unrec`: `U(σ) = 0`,
the recurrence tax vanishes, and `INV2` collapses to its endpoint form — which the
window cap sustains. This section derives `U(σ) = 0` from `committee_coverage` (via
the epoch arithmetic) and shows `INV2` self-maintains from the endpoint margin. -/

/-- **`committee_coverage` gives a tail assignment.** An active validator (active
in `epoch(es) + 1`) has, once `σ` reaches two epochs past `es`
(`hσ : epoch(es) + 2 ≤ epoch(σ)` — one full epoch strictly inside `(es, σ]`), a
committee assignment at some slot `t ∈ (es, σ]`. The witnessing epoch is
`epoch(es) + 1`; slot monotonicity of `compute_epoch_at_slot` places its slot
above `es` and below `σ`. -/
theorem honest_active_tail_assignment (hec : ExternalsCoherence cfg ext E)
    {i : ValidatorIndex} {es σ : Slot}
    (hactive : is_active_validator (E.registry.getD i default)
      (compute_epoch_at_slot cfg es + 1) = true)
    (heH : compute_epoch_at_slot cfg es + 1 < E.verification_horizon)
    (hσ : compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ) :
    ∃ t : Slot, es < t ∧ t ≤ σ ∧ i ∈ E.committee t := by
  obtain ⟨s, _hsH, hep, hmem⟩ :=
    hec.committee_coverage i (compute_epoch_at_slot cfg es + 1) heH hactive
  refine ⟨s, ?_, ?_, hmem⟩
  · rcases Nat.lt_or_ge es s with h | h
    · exact h
    · exfalso
      have hmono : compute_epoch_at_slot cfg s ≤ compute_epoch_at_slot cfg es :=
        Nat.div_le_div_right h
      rw [hep] at hmono
      exact absurd hmono (Nat.not_succ_le_self _)
  · rcases le_or_gt s σ with h | h
    · exact h
    · exfalso
      have hmono : compute_epoch_at_slot cfg σ ≤ compute_epoch_at_slot cfg s :=
        Nat.div_le_div_right (le_of_lt h)
      rw [hep] at hmono
      exact absurd (le_trans hσ hmono) (Nat.not_succ_le_self _)

/-- Every window member is active at any epoch (committee membership ⟹ active at
the slot's epoch — `committee_members_active`; `registry_activity_constant` makes
it epoch-independent). -/
theorem span_member_active (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E) {i : ValidatorIndex} {lo es : Slot}
    (hi : i ∈ E.span_committee lo es)
    (hesH : E.SlotWithinHorizon cfg es)
    (e : Epoch) (heH : e < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) e = true := by
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hi
  obtain ⟨s, hs, hmem⟩ := hi
  have hsH : E.SlotWithinHorizon cfg s :=
    ⟨le_trans hs.2 hesH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hs.2) hesH.2⟩
  have h1 := hec.committee_members_active i s hsH hmem
  rw [← hsv.registry_activity_constant i (compute_epoch_at_slot cfg s) e hsH.2 heH]
  exact h1

/-- **`U(σ) = 0` when every base supporter re-assigns in `(es, σ]`.** The `Unrec`
filter (`Sclass es` members with no assignment in `(es, σ]`) is empty, so its
weight is `0`. -/
theorem Uval_eq_zero_of_all_assigned (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root)
    (lo es σ : Slot)
    (hassigned : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo es,
      ∃ t : Slot, es < t ∧ t ≤ σ ∧ i ∈ E.committee t) :
    E.Uval cfg ext v₀ n₀ b' lo es σ = 0 := by
  have hempty : E.Unrec cfg ext v₀ n₀ b' lo es σ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    simp only [Execution.Unrec, Finset.mem_filter] at hi
    obtain ⟨hsc, hpred⟩ := hi
    obtain ⟨t, ht1, ht2, htmem⟩ := hassigned i hsc
    exact hpred t ht1 ht2 htmem
  rw [Execution.Uval, hempty]
  simp [Execution.weight]

/-- **`U(σ) = 0` from `committee_coverage`.** In the saturated regime
(`hσ : epoch(es) + 2 ≤ epoch(σ)`) every base supporter — active by
`span_member_active` — has a tail assignment (`honest_active_tail_assignment`), so
`U(σ) = 0`. This is the structural input that collapses the tax reserve. -/
theorem Uval_eq_zero_of_coverage (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E) (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hσ : compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ) :
    E.Uval cfg ext v₀ n₀ b' lo es σ = 0 := by
  have hesσ : es ≤ σ := by
    by_contra hnot
    have hmono : compute_epoch_at_slot cfg σ ≤ compute_epoch_at_slot cfg es :=
      Nat.div_le_div_right (Nat.le_of_lt (Nat.lt_of_not_ge hnot))
    have hbad : compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg es :=
      le_trans hσ hmono
    exact (Nat.not_succ_le_self (compute_epoch_at_slot cfg es + 1))
      (le_trans hbad (Nat.le_succ _))
  have hesH : E.SlotWithinHorizon cfg es :=
    ⟨le_trans hesσ hσH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hesσ) hσH.2⟩
  have he1H : compute_epoch_at_slot cfg es + 1 < E.verification_horizon := by
    exact lt_trans
      (lt_of_lt_of_le (Nat.lt_succ_self (compute_epoch_at_slot cfg es + 1)) hσ) hσH.2
  apply E.Uval_eq_zero_of_all_assigned cfg ext v₀ n₀ b' lo es σ
  intro i hi
  have hspan : i ∈ E.span_committee lo es := by
    simp only [Execution.Sclass, Finset.mem_filter] at hi; exact hi.1.1
  exact E.honest_active_tail_assignment cfg ext hec
    (E.span_member_active cfg ext hec hsv hspan hesH _ he1H) he1H hσ

/-- **Saturation self-maintenance.** With `U(σ) = 0` (base fully recurred,
`Uval_eq_zero_of_coverage`) the tax reserve `⌊C·U(σ)/D⌋ = 0`, so the floored `min`
vanishes and `INV2(σ)` is exactly its endpoint form `x(σ) + Enemy(σ) + boost + 1 ≤
s(σ)` — supplied here as `hend` (the saturated honest majority the window cap
gives). No recurrence-tax bookkeeping is needed past `T1`. -/
theorem INV2_of_saturated (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (boost : ℕ) (hU0 : E.Uval cfg ext v₀ n₀ b' lo es σ = 0)
    (hend : E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ) :
    E.INV2 cfg ext v₀ n₀ b' lo es σ boost := by
  simp only [Execution.INV2, hU0, Nat.mul_zero, Nat.zero_div]
  rw [min_eq_left (Nat.zero_le _), Nat.add_zero]
  exact hend

end Execution

end FastConfirmation.Spec

end
