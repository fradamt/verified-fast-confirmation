module
public import FastConfirmation.Spec.Proof.LedgerV2

@[expose] public section

/-!
# Spec / Proof / StepDischarge: the per-slot class deltas

This module isolates the per-slot maintenance inputs of the proof decomposition.
This module feeds the **store-dynamics inputs** the head-safety shell (`HeadSafetyEngine`) hands
to `LedgerV2.INV2_step` — the per-slot class-delta facts — plus the two `Bridge`
generalisations `Endpoint`/the shell need:

* `RecordedEpochMax_of_ubiquity` — discharge `Bridge.RecordedEpochMax` at any honest
  store from `Delivery.vote_ubiquity`'s ∀-quantified conclusion (the shape
  `EngineTransport.HS0_in_AttSupporters` already exposes it in).
* `recorded_lm_is_newest_at` — `Bridge.recorded_lm_is_newest` at an **arbitrary**
  honest node `(w, m)` (its proof uses only per-store facts; `Endpoint`'s flag).

The step-delta side delivers the **pure set-level** increments (`Jspec_step`,
`Uval_step`, `Enemy_step`) with their explicit witness weights, and the `hF3`
`span_fraction`-`[t,t]` ingredient (`span_fraction_slot`). The class-**migration**
deltas `hs'`/`hx'` and the exact `hF3` funding remain explicit inputs to
`INV2_step`; the `ρ` partition and `(v₀,n₀)` anchoring are described below.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the two `Bridge` generalisations

`Bridge.RecordedEpochMax` is the domination input `recorded_lm_is_newest` needs
(the recorded message dominates, in epoch, every one of the validator's votes
through `es`). It is exactly `Delivery.vote_ubiquity`'s conclusion, ∀-quantified
over the window — the shape `EngineTransport.HS0_in_AttSupporters` already takes
its `hubiq` in. `recorded_lm_is_newest_at` is `Bridge.recorded_lm_is_newest` with
the confirming node `(v₀, n₀)` replaced by an arbitrary honest `(w, m)`. -/

/-- **`RecordedEpochMax` from ubiquity.** Given `Delivery.vote_ubiquity`'s
∀-quantified conclusion at the store `(v₀, n₀)` — every honest validator's every
vote through `es` has a recorded message at `(v₀, n₀)` whose epoch dominates the
vote-slot epoch — `RecordedEpochMax` holds: the two recorded messages coincide by
`Option` injectivity. The shell produces `hubiq` from `vote_ubiquity` + the
head-known / walk well-formedness inputs it threads. -/
theorem RecordedEpochMax_of_ubiquity {v₀ : ValidatorIndex} {n₀ : ℕ} {es : Slot}
    (hubiq : ∀ i ∈ E.honest, ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (kk, a) →
      ∃ msg, (E.store cfg ext v₀ n₀).latest_messages i = some msg ∧
        compute_epoch_at_slot cfg t ≤ msg.epoch) :
    E.RecordedEpochMax cfg ext v₀ n₀ es := by
  intro i hi lm hlm t kk a htle hvt
  obtain ⟨msg, hmsg, hep⟩ := hubiq i hi t kk a htle hvt
  rw [hlm] at hmsg
  have hlmeq : lm = msg := Option.some.inj hmsg
  rw [hlmeq]; exact hep

/-- **`recorded_lm_is_newest` at an arbitrary honest `(w, m)`.** Verbatim port of
`Bridge.recorded_lm_is_newest` (its proof uses only per-store facts): at honest
`(w, m)`, an honest validator `i`'s recorded `latest_messages i = some lm` is set
by `i`'s ground newest-by-`es` vote (a vote at `t ≤ es`, no later vote through
`es`) whose LMD block is exactly `lm.root`. Existence + block-root from
`SchedLMProv` + `no_forgery`; `t ≤ es` from the provenance slot gate `hprov` +
`committee_assignment_unique`; the newest characterisation from the ubiquity
domination `hdom`. `Endpoint`'s flag (`Bridge.recorded_lm_is_newest at (w,m)`). -/
theorem recorded_lm_is_newest_at
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    {es : Slot} (hes : es = get_current_slot cfg (E.store cfg ext w m) - 1)
    {i : ValidatorIndex} (hi : i ∈ E.honest) {lm : LatestMessage Root}
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hdom : ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (k, a) → compute_epoch_at_slot cfg t ≤ lm.epoch) :
    ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = lm.root := by
  obtain ⟨a', u, tsc, ifb, hsched, hvin, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen w m i lm hlm
  obtain ⟨m1, a'', hvote', hdata'⟩ := hhb.no_forgery u tsc a' ifb hsched i hi hvin
  have hcomm0 : i ∈ E.committee a'.data.slot :=
    hhb.votes_assigned i hi a'.data.slot (by rw [hvote']; exact Option.some_ne_none _)
  obtain ⟨ap, _, _, _, h4, h5, h6, _, _⟩ := hprov i lm hlm
  have hepeq : compute_epoch_at_slot cfg a'.data.slot =
      compute_epoch_at_slot cfg ap.data.slot := by rw [hslotep, h4]
  have hslotdef : a'.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a'.data.slot ap.data.slot hcomm0 h6 hepeq
  have htle : a'.data.slot ≤ es := by
    rw [hslotdef, hes]; exact Nat.le_sub_one_of_lt h5
  have hbbr' : a''.data.beacon_block_root = lm.root := by rw [← hdata']; exact hbbr
  refine ⟨a'.data.slot, m1, a'', htle, hvote', ?_, hbbr'⟩
  intro t' hlt hle
  cases hvt : E.vote i t' with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨k', a3⟩ := p
    have hcomm' : i ∈ E.committee t' :=
      hhb.votes_assigned i hi t' (by rw [hvt]; exact Option.some_ne_none _)
    have heple : compute_epoch_at_slot cfg t' ≤ lm.epoch := hdom t' k' a3 hle hvt
    have hepmono : compute_epoch_at_slot cfg a'.data.slot ≤ compute_epoch_at_slot cfg t' :=
      Nat.div_le_div_right (le_of_lt hlt)
    have hle1 : compute_epoch_at_slot cfg t' ≤ compute_epoch_at_slot cfg a'.data.slot := by
      rw [hslotep]; exact heple
    have hepeq' : compute_epoch_at_slot cfg t' = compute_epoch_at_slot cfg a'.data.slot :=
      le_antisymm hle1 hepmono
    have hts : t' = a'.data.slot :=
      hec.committee_assignment_unique i t' a'.data.slot hcomm' hcomm0 hepeq'
    subst hts
    exact lt_irrefl _ hlt

/-! ## Section 2 — the pure set-level step deltas

`INV2_step` takes six per-slot deltas `hs'`/`hx'`/`hE'`/`hJ'`/`hU'`/`hF3` over the
ledger accessors at `σ` and `σ' = σ + 1`. Three of them are **pure `Finset`
algebra** with explicit witness weights (no store dynamics): `hJ'` (the honest
window grows by exactly the new honest committee members — `Jspec_eq_add_growth`),
`hU'` (the unrecurred base supporters lose those newly assigned at `σ+1` —
`Unrec_anti` + `sum_sdiff`), and `hE'` (the union enemy grows by at most the new
byzantine members of `committee(σ+1)` — `span_committee` split + subadditivity).
The `hF3` `span_fraction`-`[σ+1, σ+1]` ingredient is `span_fraction_slot`. The
class-**migration** deltas `hs'`/`hx'` and the exact `hF3` funding are the
store-dynamics inputs to the step. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hJ'`: the honest window grows by exactly the fresh honest members.**
`Jspec lo (σ+1) = Jspec lo σ + φ` with `φ` the honest weight of the committee
growth set `span_committee lo (σ+1) \ span_committee lo σ` (`= committee(σ+1)`'s
new members). Exact equality — `Fraction.Jspec_eq_add_growth`. -/
theorem Jspec_step (lo σ : Slot) :
    E.Jspec lo (σ + 1) = E.Jspec lo σ +
      E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
        (fun i => i ∈ E.honest)) :=
  E.Jspec_eq_add_growth lo (Nat.le_succ σ)

/-- **`hU'`: the unrecurred base supporters lose those newly assigned at `σ+1`.**
`Uval σ = Uval (σ+1) + σt` with `σt` the weight of `Sclass es` members that had no
assignment in `(es, σ]` but do at `σ+1` (`Unrec σ \ Unrec (σ+1)`, the base-supporter
recurrence). Exact equality via `Unrec_anti` + `Finset.sum_sdiff`; gives the
`INV2_step` hypothesis `Uval (σ+1) + σt ≤ Uval σ` (`le_of_eq`, `add_comm`). -/
theorem Uval_step (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) :
    E.Uval cfg ext v₀ n₀ b' lo es σ = E.Uval cfg ext v₀ n₀ b' lo es (σ + 1)
      + E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ \ E.Unrec cfg ext v₀ n₀ b' lo es (σ + 1)) := by
  simp only [Execution.Uval, Execution.weight]
  rw [← Finset.sum_sdiff (E.Unrec_anti cfg ext v₀ n₀ b' lo es (Nat.le_succ σ))]
  ring

/-- **`hE'`: the union enemy grows by at most the new slot's byzantine weight.**
`Enemy (σ+1) ≤ Enemy σ + β` with `β := Bval (σ+1) (σ+1)` the non-honest weight of
`committee(σ+1)`. A member of `SpentSet (σ+1)` sits in some `committee t`,
`t ∈ [es+1, σ+1]`: either `t ≤ σ` (already in `SpentSet σ`) or `t = σ+1` (in
`Bwin (σ+1) (σ+1)`); `BbadSet` is unchanged. Pointwise membership — no window
ordering hypothesis needed. -/
theorem Enemy_step (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) :
    E.Enemy cfg ext v₀ n₀ b' lo es (σ + 1) ≤
      E.Enemy cfg ext v₀ n₀ b' lo es σ + E.Bval (σ + 1) (σ + 1) := by
  simp only [Execution.Enemy, Execution.Bval]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  intro i hi
  rw [Finset.mem_union] at hi
  rw [Finset.mem_union]
  rcases hi with hb | hs
  · exact Or.inl (Finset.mem_union.mpr (Or.inl hb))
  · simp only [Execution.SpentSet, Finset.mem_filter] at hs
    obtain ⟨hspan, hnh⟩ := hs
    simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hspan
    obtain ⟨t, ⟨ht1, ht2⟩, hct⟩ := hspan
    rcases le_or_gt t σ with htσ | htσ
    · refine Or.inl (Finset.mem_union.mpr (Or.inr ?_))
      simp only [Execution.SpentSet, Finset.mem_filter]
      refine ⟨?_, hnh⟩
      simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨t, ⟨ht1, htσ⟩, hct⟩
    · have hteq : t = σ + 1 := le_antisymm ht2 htσ
      subst hteq
      refine Or.inr ?_
      simp only [Execution.Bwin, Finset.mem_filter]
      refine ⟨?_, hnh⟩
      simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨σ + 1, ⟨le_refl _, le_refl _⟩, hct⟩

/-- Pure-ℕ core (local copy of `Ledger.sub_mul_le_of_span`): from the
cross-multiplied `span_fraction` `100·B ≤ C·(J + B)` and `C ≤ 100`, the
`(100−C)·B ≤ C·J` rearrangement. Kept as a plain-ℕ lemma so `omega` atomizes
`(100−C)·B` rather than expanding it into a nonlinear product. -/
private theorem sub_mul_le_of_span {C B J : ℕ} (hC : C ≤ 100)
    (h : 100 * B ≤ C * (J + B)) : (100 - C) * B ≤ C * J := by
  have h1 : (100 - C) * B + C * B = 100 * B := by rw [← Nat.add_mul]; congr 1; omega
  rw [Nat.mul_add] at h
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hF3` ingredient: `span_fraction` at the singleton slot `[t, t]`.**
`(100−C)·Bval t t ≤ C·(honest weight of committee(t))` — the per-slot Byzantine
fraction bound of `ByzantineBound.span_fraction` on `span_committee t t =
committee(t)`, rearranged by `weight_split_honest` (the same algebra as
`Ledger.Rterm_nonneg`). This is the `β`-vs-honest-committee half of `hF3`; the
companion recurrence premise accounts for the excess over `σt + ξ + α + φ`
through the already-supporting recurrers (`ρ`). -/
theorem span_fraction_slot (hbb : ByzantineBound cfg E) (t : Slot)
    (htH : E.SlotWithinHorizon cfg t) :
    (100 - cfg.confirmation_byzantine_threshold) * E.Bval t t ≤
      cfg.confirmation_byzantine_threshold *
        E.weight ((E.span_committee t t).filter (fun i => i ∈ E.honest)) := by
  have hC : cfg.confirmation_byzantine_threshold ≤ 100 :=
    le_trans cfg.confirmation_byzantine_threshold_le (by norm_num)
  have hsf := hbb.span_fraction t t htH htH
  rw [E.weight_split_honest (E.span_committee t t)] at hsf
  rw [Execution.Bval, Execution.Bwin]
  exact sub_mul_le_of_span hC hsf

end Execution

end FastConfirmation.Spec

end
