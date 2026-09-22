module
public import FastConfirmation.Spec.Proof.HeadSafetyEngine

@[expose] public section

/-!
# Spec / Proof / StepDischargeII: same-epoch closure of the INV2 ledger

This module implements the two interfaces needed to apply
`LedgerV2.INV2_step` after `StepDischarge`:

* **(A) class anchoring.** `Sclass`/`Aclass`/`Xclass` (and the base enemy
  `BbadSet`) anchor `is_ancestor` at a *parameter* `(v₀, n₀)` — nothing forces the
  confirming node. Late votes' blocks need not be in the
  confirming store, so support cannot grow there. §10-A's fix: run the whole `INV2`
  chain **per endpoint node** `(w, m)`, transporting only the base once. This module
  delivers the class transport at the cutoff `es` (`Sclass`/`Xclass`/`BbadSet`
  monotone under the forward `is_ancestor` transport of `EngineTransport.is_ancestor_transport`
  / `BlockAgreement.is_ancestor_congr`) and the headline `INV2_base_transport`:
  `INV2` at the confirming anchor `(v₀, n₀)` transports to `INV2` at any endpoint
  `(w, m)` at `σ = es` (both `min` branches close: the member arm rides
  `Xval`↓ + `Jspec` fixed, the tax arm the monotonicity of `s − ⌊C·s/D⌋`).

* **(B) `ρ = 0` in the same-epoch regime.** With the window `[lo, es]` inside
  `epoch(es)` (Arms' same-epoch hypothesis), a `LedgerV2.INV2_step` at a tail slot
  `σ + 1` has honest committee weight partitioning **exactly** into the migrant /
  fresh classes (no already-supporting recurrers `ρ`), so `span_fraction`-`[t,t]`
  (`StepDischarge.span_fraction_slot`) *is* the `hF3` funding. This module delivers
  `hF3_of_partition` (the `ρ = 0` reduction of `hF3` to the class partition of the
  slot committee) and `INV2_step_same_epoch`, the `INV2_step` wrapper that discharges
  the three **set-level** deltas (`hE'`/`hJ'`/`hU'`) from `StepDischarge`'s
  `Enemy_step`/`Jspec_step`/`Uval_step`, leaving only the two class-**migration**
  deltas `hs'`/`hx'` (the genuine store-dynamics residue) and `hF3` as inputs.

* **Composition.** `INV2_maintained_same_epoch` iterates the step from the
  transported base `INV2(es)` to every `σ`, routing pre-`T1` slots through the
  per-slot step functional and post-`T1` slots through `LedgerV2.INV2_of_saturated`
  (its `U(σ) = 0` discharged from `committee_coverage` via
  `LedgerV2.Uval_eq_zero_of_coverage`).

The genuine store-dynamics residue
(`hs'`/`hx'`; the `ρ = 0` partition itself) is taken as named hypotheses in the
existing `INV2_step` shapes.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — class base transport (§10-A)

At the cutoff `es`, every relevant vote is pre-`es`, its block known at both the
confirming store `(v₀, n₀)` and the endpoint store `(w, m)`. The forward
`is_ancestor` transport (`EngineTransport.is_ancestor_transport`, whose per-witness
instances the shell discharges from `block_relay` known-ness) makes the descent
predicates `SupportsDesc` / `AncestorOrVoteless` monotone `(v₀, n₀) → (w, m)`, hence:
`Sclass`/`Aclass` **grow** and `Xclass` **shrinks** across anchors. The base enemy
`BbadSet` shrinks too, given the equivocator containment `equivocating@(v₀,n₀) ⊆
equivocating@(w,m)` (`attester_slashing_relay`'s forward-evidence shape). The
transport implications are taken as the ∀-quantified `is_ancestor_transport`-shaped
hypotheses `hSt`/`hAt`; the shell instantiates them per supporter. -/

/-- **`Sclass` grows across anchors.** Under the forward `SupportsDesc` transport
`hSt` (the `is_ancestor_transport` conclusion, ∀-quantified over the window), the
confirming-anchor `Sclass` at `es` is contained in the endpoint-anchor `Sclass`. -/
theorem Sclass_subset_of_transport (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root)
    (lo es : Slot)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i) :
    E.Sclass cfg ext v₀ n₀ b' lo es ⊆ E.Sclass cfg ext w m b' lo es := by
  intro i hi
  simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hSt i hi.2⟩

/-- **`Xclass` shrinks across anchors.** With both descent predicates transporting
forward (`hSt`, `hAt`), the endpoint-anchor sibling-stuck class at `es` is contained
in the confirming-anchor one (`¬S`/`¬A` at `(w, m)` imply `¬S`/`¬A` at `(v₀, n₀)`). -/
theorem Xclass_subset_of_transport (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root)
    (lo es : Slot)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i) :
    E.Xclass cfg ext w m b' lo es ⊆ E.Xclass cfg ext v₀ n₀ b' lo es := by
  intro i hi
  simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, fun hS => hi.2.1 (hSt i hS), fun hA => hi.2.2 (hAt i hA)⟩

/-! ### Note (`recorded-base reduction`): the recorded base enemy does **not** transport across anchors.

With `LedgerV2.BbadSet` in its **recorded** form, its sibling-ward guard reads the
store's recorded latest message. A byzantine validator has no `no_forgery`, so its
recorded message at the endpoint `(w, m)` is unrelated to the one at the confirming
anchor `(v₀, n₀)` (targeted-gossip: a sibling-ward vote at a window slot `≤ es` may be
delivered to `w` but withheld from `v₀`). Hence `BbadVal@(w,m) ≤ BbadVal@(v₀,n₀)` is
**not derivable** from the ground descent transports `hSt`/`hAt` (which constrain
honest votes only) nor from the equivocator relay `hequiv`. The enemy-weight movement
is therefore carried as an explicit residual `hBb` on the base transport below (it
replaces the equivocator-relay slot the old ground-vote `BbadSet` consumed); only the
honest legs (`Sclass` grows, `Xclass` shrinks) transport from `hSt`/`hAt`. -/

/-! ## Section 2 — the `INV2` base transport (§10-A headline) -/

/-- Two-sided floor bounds of `n / m` (`0 < m`) as linear atoms. Local copy of
`Arms.div_floor_bounds` / `LedgerV2.div_floor_bounds`. -/
private theorem div_floor_bounds (n m : ℕ) (hm : 0 < m) :
    m * (n / m) ≤ n ∧ n < m * (n / m + 1) := by
  have e := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  rw [Nat.mul_succ]
  omega

/-- **Pure-ℕ base transport.** From `INV2(es)` at the confirming anchor (atoms
`X1`/`Bb1`/`S1`; the reserve caps at `es` are `⌊C·S1/D⌋` since `U(es) = s₀`, and
`⌊C·J/D⌋ − Bb1`), with `S1 ≤ S2`, `X2 ≤ X1`, `Bb2 ≤ Bb1` and the same window
`J`, `INV2(es)` at the endpoint anchor follows. Both `min` branches: the member arm
uses `X2 ≤ X1` + fixed `J`; the tax arm the monotonicity of `s − ⌊C·s/D⌋`
(`interval_cases C` makes it linear). -/
private theorem inv2_base_transport_arith
    {C X1 X2 Bb1 Bb2 S1 S2 J boost rU1 rU2 rJ : ℕ}
    (hC : C ≤ 25)
    (hINV1 : X1 + Bb1 + boost + 1 + min rU1 (rJ - Bb1) ≤ S1)
    (hS : S1 ≤ S2) (hX : X2 ≤ X1) (hBb : Bb2 ≤ Bb1)
    (hrU1lo : (100 - C) * rU1 ≤ C * S1) (hrU1hi : C * S1 < (100 - C) * (rU1 + 1))
    (hrU2lo : (100 - C) * rU2 ≤ C * S2) (hrU2hi : C * S2 < (100 - C) * (rU2 + 1))
    (hrJlo : (100 - C) * rJ ≤ C * J) (hrJhi : C * J < (100 - C) * (rJ + 1)) :
    X2 + Bb2 + boost + 1 + min rU2 (rJ - Bb2) ≤ S2 := by
  interval_cases C <;> omega

/-- **The `INV2` base transports across anchors.** `INV2` at the confirming anchor
`(v₀, n₀)` and cutoff `σ = es` transports to `INV2` at any endpoint anchor `(w, m)`,
given the class weight movements the base transport delivers: honest support grows
(`hS`), the sibling-stuck class shrinks (`hX`), the base enemy shrinks (`hBb`). The
window `Jspec lo es` is anchor-independent (identical term at both). This is §10-A's
"only the base transports once"; the shell instantiates `INV2` per `(w, m)` from
here. -/
theorem INV2_base_transport
    (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hS : E.Sval cfg ext v₀ n₀ b' lo es ≤ E.Sval cfg ext w m b' lo es)
    (hX : E.Xval cfg ext w m b' lo es ≤ E.Xval cfg ext v₀ n₀ b' lo es)
    (hBb : E.BbadVal cfg ext w m b' lo es ≤ E.BbadVal cfg ext v₀ n₀ b' lo es)
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es es boost) :
    E.INV2 cfg ext w m b' lo es es boost := by
  simp only [Execution.INV2] at hinv ⊢
  rw [E.Enemy_es_eq_BbadVal cfg ext v₀ n₀ b' lo es,
      E.Uval_es_eq_Sval cfg ext v₀ n₀ b' lo es] at hinv
  rw [E.Enemy_es_eq_BbadVal cfg ext w m b' lo es,
      E.Uval_es_eq_Sval cfg ext w m b' lo es]
  set C := cfg.confirmation_byzantine_threshold with hCdef
  have hC25 : C ≤ 25 := cfg.confirmation_byzantine_threshold_le
  have hDpos : 0 < 100 - C := by omega
  obtain ⟨hrU1lo, hrU1hi⟩ :=
    div_floor_bounds (C * E.Sval cfg ext v₀ n₀ b' lo es) (100 - C) hDpos
  obtain ⟨hrU2lo, hrU2hi⟩ :=
    div_floor_bounds (C * E.Sval cfg ext w m b' lo es) (100 - C) hDpos
  obtain ⟨hrJlo, hrJhi⟩ := div_floor_bounds (C * E.Jspec lo es) (100 - C) hDpos
  exact inv2_base_transport_arith hC25 hinv hS hX hBb hrU1lo hrU1hi hrU2lo hrU2hi hrJlo hrJhi

/-- **The two honest base weight movements.** Bundles the honest class-transport `⊆`'s
into the weight inequalities `INV2_base_transport` consumes: `Sval` grows, `Xval`
shrinks. Ground-truth weight is monotone under inclusion (`weight_mono`). The enemy leg
(`BbadVal`) does **not** transport (recorded byz, see the Section-1 note); it is supplied
separately to `INV2_base_transport_of_transport` as `hBb`. -/
theorem classes_base_transport (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root)
    (lo es : Slot)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i) :
    E.Sval cfg ext v₀ n₀ b' lo es ≤ E.Sval cfg ext w m b' lo es ∧
    E.Xval cfg ext w m b' lo es ≤ E.Xval cfg ext v₀ n₀ b' lo es :=
  ⟨E.weight_mono (E.Sclass_subset_of_transport cfg ext v₀ w n₀ m b' lo es hSt),
   E.weight_mono (E.Xclass_subset_of_transport cfg ext v₀ w n₀ m b' lo es hSt hAt)⟩

/-- Honest-window form of `classes_base_transport`.  `Sclass`/`Xclass`
already filter to `E.honest ∩ span_committee lo es`, so no transport statement
about Byzantine ground votes is needed (or implied by synchrony). -/
theorem classes_base_transport_honest
    (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root) (lo es : Slot)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v₀ n₀ b' es i →
        E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
        E.AncestorOrVoteless cfg ext w m b' es i) :
    E.Sval cfg ext v₀ n₀ b' lo es ≤ E.Sval cfg ext w m b' lo es ∧
      E.Xval cfg ext w m b' lo es ≤ E.Xval cfg ext v₀ n₀ b' lo es := by
  classical
  constructor
  · apply E.weight_mono
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  · apply E.weight_mono
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1,
      fun hS => hi.2.1 (hSt i hi.1.2 hi.1.1 hS),
      fun hA => hi.2.2 (hAt i hi.1.2 hi.1.1 hA)⟩

/-- **`INV2` base transport from the raw transport hypotheses.** Combines
`classes_base_transport` (honest legs) with `INV2_base_transport`: given the forward
descent transports `hSt`/`hAt` and the **recorded enemy-weight movement**
`hBb : BbadVal@(w,m) ≤ BbadVal@(v₀,n₀)` (`recorded-base reduction`: the residual replacing the old
equivocator-relay leg — see the Section-1 note), `INV2` at the confirming anchor
`(v₀, n₀)` and cutoff `es` yields `INV2` at the endpoint `(w, m)`. The shell wires the
honest legs with `is_ancestor_transport` + `block_relay`; `hBb` is the enumerated
recorded-enemy residue. -/
theorem INV2_base_transport_of_transport
    (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i)
    (hBb : E.BbadVal cfg ext w m b' lo es ≤ E.BbadVal cfg ext v₀ n₀ b' lo es)
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es es boost) :
    E.INV2 cfg ext w m b' lo es es boost := by
  obtain ⟨hS, hX⟩ := E.classes_base_transport cfg ext v₀ w n₀ m b' lo es hSt hAt
  exact E.INV2_base_transport cfg ext v₀ w n₀ m b' lo es boost hS hX hBb hinv

/-! ## Section 3 — the `ρ = 0` same-epoch step (§10-B)

`LedgerV2.INV2_step` takes six per-slot deltas. Three are **pure set algebra**
delivered by `StepDischarge`: `hE'` (`Enemy_step`, `β := Bval (σ+1) (σ+1)`),
`hJ'` (`Jspec_step`, `φ := honest committee growth`) and `hU'` (`Uval_step`,
`σt := base-supporter recurrence`). The `hF3` `span_fraction` funding needs, over
`β`, the slot committee's honest weight `≤ σt + ξ + α + φ` — i.e. no
already-supporting recurrer `ρ`. §10-B: in the same-epoch regime (`hsame`) each
window member's `epoch(es)` assignment is spent by `es`, so a tail slot's honest
committee partitions **exactly** into the migrants (`ξ`, `α`) / recurring base
supporters (`σt`) / fresh (`φ`), with `ρ = 0`; `hρ` captures that partition and
`span_fraction_slot` closes `hF3`. The two class-**migration** deltas `hs'`/`hx'`
remain the genuine store-dynamics residue (the honest committee members re-vote
`desc(b′)` under the engine IH + `votes_head` + delivery, landing at `(w, m)` by
slot `t + 1`) — taken as inputs. -/

/-- **`ρ = 0` reduces `hF3` to the slot-committee partition.** With the honest
committee weight of slot `σ+1` bounded by the migrant/recurrence/fresh weights
(`hρ`, the `ρ = 0` partition of §10-B), the per-slot `span_fraction`
(`StepDischarge.span_fraction_slot`) gives exactly `INV2_step`'s `hF3` funding
`(100−C)·β ≤ C·(σt + ξ + α + φ)` with `β := Bval (σ+1) (σ+1)`. -/
theorem hF3_of_partition (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) (ξ α : ℕ)
    (hσ1H : E.SlotWithinHorizon cfg (σ + 1))
    (hρ : E.weight ((E.span_committee (σ + 1) (σ + 1)).filter (fun i => i ∈ E.honest)) ≤
      E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ \ E.Unrec cfg ext v₀ n₀ b' lo es (σ + 1))
        + ξ + α +
        E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
          (fun i => i ∈ E.honest))) :
    (100 - cfg.confirmation_byzantine_threshold) * E.Bval (σ + 1) (σ + 1) ≤
      cfg.confirmation_byzantine_threshold *
        (E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ \ E.Unrec cfg ext v₀ n₀ b' lo es (σ + 1))
          + ξ + α +
          E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
            (fun i => i ∈ E.honest))) := by
  refine le_trans (E.span_fraction_slot cfg hbb (σ + 1) hσ1H) ?_
  gcongr

/-- **`INV2_step`, same-epoch specialisation.** Fixes the three set-level witnesses
`φ` (honest committee growth), `β` (new-slot byz), `σt` (base-supporter recurrence)
to the `StepDischarge` values and discharges `hE'`/`hJ'`/`hU'` from
`Enemy_step`/`Jspec_step`/`Uval_step`, leaving only the two class-migration deltas
`hs'`/`hx'` and the `ρ = 0` funding `hF3` (produced by `hF3_of_partition`). The
`INV2` at `σ` propagates to `σ + 1`. -/
theorem INV2_step_same_epoch (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) (boost ξ α : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ) (hσ1H : E.SlotWithinHorizon cfg (σ + 1))
    (hlo : lo ≤ es + 1) (hσ : es ≤ σ)
    (hs' : E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α +
        E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
          (fun i => i ∈ E.honest))
      ≤ E.Sval cfg ext v₀ n₀ b' lo (σ + 1))
    (hx' : E.Xval cfg ext v₀ n₀ b' lo (σ + 1) + ξ ≤ E.Xval cfg ext v₀ n₀ b' lo σ)
    (hF3 : (100 - cfg.confirmation_byzantine_threshold) * E.Bval (σ + 1) (σ + 1) ≤
      cfg.confirmation_byzantine_threshold *
        (E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ \ E.Unrec cfg ext v₀ n₀ b' lo es (σ + 1))
          + ξ + α +
          E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
            (fun i => i ∈ E.honest))))
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es σ boost) :
    E.INV2 cfg ext v₀ n₀ b' lo es (σ + 1) boost :=
  E.INV2_step cfg ext hbb v₀ n₀ b' lo es hloH hσH hσ1H boost ξ α
    (E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
      (fun i => i ∈ E.honest)))
    (E.Bval (σ + 1) (σ + 1))
    (E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ \ E.Unrec cfg ext v₀ n₀ b' lo es (σ + 1)))
    hlo hσ (le_trans hσ (Nat.le_succ σ)) hs' hx'
    (E.Enemy_step cfg ext v₀ n₀ b' lo es σ) (E.Jspec_step lo σ)
    (le_of_eq (E.Uval_step cfg ext v₀ n₀ b' lo es σ).symm) hF3 hinv

/-! ## Section 4 — the same-epoch maintenance composition (§10-3)

`INV2` at every window end `σ ≥ es` from the transported base `INV2(es)`, routing
each slot by its epoch: **pre-`T1`** (`epoch(σ+1) < epoch(es) + 2`) through the
per-slot step functional `hpre` (built from `INV2_step_same_epoch` + the class
deltas), and **post-`T1`** (`epoch(es) + 2 ≤ epoch(σ+1)`) through
`LedgerV2.INV2_of_saturated`, whose `U(σ+1) = 0` is discharged here from
`committee_coverage` (`LedgerV2.Uval_eq_zero_of_coverage`). The saturated endpoint
majority `hsat` is the functional the shell supplies past saturation. A single
`Nat.le_induction`; only the pre-`T1` step consumes the induction hypothesis. -/

/-- **Same-epoch `INV2` maintenance.** From the base `INV2(es)`, the pre-`T1` per-slot
step `hpre` (each `INV2(σ) ⟹ INV2(σ+1)` while `epoch(σ+1) < epoch(es) + 2`) and the
post-`T1` saturated endpoint `hsat` (the honest-majority endpoint form once
`epoch(es) + 2 ≤ epoch(σ)`), `INV2(σ)` holds for every `σ ≥ es`. The saturation
branch is self-contained: `Uval_eq_zero_of_coverage` collapses the tax reserve, so
`INV2_of_saturated` reads `hsat` directly (no step, no `ih`). This is §10-3's
"compose `INV2_step` pre-`T1` and `INV2_of_saturated` post-`T1`", with
`committee_coverage` wired in for the saturation discharge. -/
theorem INV2_maintained_same_epoch (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hbase : E.INV2 cfg ext v₀ n₀ b' lo es es boost)
    (hpre : ∀ σ : Slot, es ≤ σ →
      E.SlotWithinHorizon cfg σ → E.SlotWithinHorizon cfg (σ + 1) →
      compute_epoch_at_slot cfg (σ + 1) < compute_epoch_at_slot cfg es + 2 →
      E.INV2 cfg ext v₀ n₀ b' lo es σ boost → E.INV2 cfg ext v₀ n₀ b' lo es (σ + 1) boost)
    (hsat : ∀ σ : Slot, es ≤ σ →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ →
      E.SlotWithinHorizon cfg σ →
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
        ≤ E.Sval cfg ext v₀ n₀ b' lo σ) :
    ∀ σ : Slot, es ≤ σ → E.SlotWithinHorizon cfg σ →
      E.INV2 cfg ext v₀ n₀ b' lo es σ boost := by
  intro σ hσ
  induction σ, hσ using Nat.le_induction with
  | base => intro _; exact hbase
  | succ σ hσ ih =>
    intro hσ1H
    have hσH : E.SlotWithinHorizon cfg σ :=
      ⟨(Nat.le_succ σ).trans hσ1H.1,
        lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_succ σ)) hσ1H.2⟩
    by_cases hsatσ : compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg (σ + 1)
    · exact E.INV2_of_saturated cfg ext v₀ n₀ b' lo es (σ + 1) boost
        (E.Uval_eq_zero_of_coverage cfg ext hec hsv v₀ n₀ b' lo es (σ + 1)
          hσ1H hsatσ)
        (hsat (σ + 1) (le_trans hσ (Nat.le_succ σ)) hsatσ hσ1H)
    · exact hpre σ hσ hσH hσ1H (not_le.mp hsatσ) (ih hσH)

end Execution

end FastConfirmation.Spec

end
