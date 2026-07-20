import FastConfirmation.Spec.Proof.Remainder

/-!
# Spec / Proof / Growth: the aggregate window-growth facts

The three **aggregate window-growth facts** consumed by
`AnchorClose.ForkEdgeConfirmMarginSupply` — the residual interface of the confirm-margin
collapse (`Dominance.bval_strip_window_uniform`). At the Spec_Safety endpoint `(w, m)` the
fork-contest window is `[lo, σ]` with `σ = slot_at m − 1 ≥ es` (`es = slot_at n₀` the confirming
base). `Dominance.bval_strip_window_uniform` carries the plain confirm-margin strip from `es` to
`σ` in one **window-uniform** step, given exactly these three facts:

* **`hgrowS`** — honest-support growth: `Sval(es) + (Jspec σ − Jspec es) ≤ Sval(σ)`. Every fresh
  honest window entrant lands in `Sclass` under the head-safety IH. Delivered by
  **telescoping** `Remainder.hSmono_of_engine`'s per-slot delta over `[es, σ]`; each per-slot
  weight-growth is exactly the `Jspec`-difference (`Fraction.Jspec_eq_add_growth`), so the
  telescope collapses to `Jspec σ − Jspec es`.
* **`hgrowX`** — `Xclass` never grows post-`es`: `Xval(σ) ≤ Xval(es)`. Telescoping
  `Remainder.hXmono_of_engine`'s per-slot antitonicity.
* **`hbudget`** — the aggregate `span_fraction` on the growth span:
  `(100−C)·(Bval σ − Bval es) ≤ C·(Jspec σ − Jspec es)`. Delivered **unconditionally in the
  same-epoch regime** (`Dominance` Part 2b): under `committee_assignment_unique` seat-uniqueness
  the window growth `span lo σ \ span lo es` is exactly the disjoint span `span (es+1) σ`, so
  `ByzantineBound.span_fraction (es+1) σ` **is** the aggregate budget. The cross-epoch regime
  needs the `INVstar` min-reserve tax carried once (`Dominance` Part 3) — surfaced as a residual,
  not forced here.

`hgrowS`/`hgrowX` are IH-dependent: their per-slot supplier `Remainder.hSmono_of_engine` /
`hXmono_of_engine` consumes the head-safety induction hypothesis at each fresh entrant's voting
store. `AnchorClose.ForkEdgeConfirmMarginSupply` (and `DescendStepChainSupply`) **already**
carries that IH clause as a hypothesis field (the `∀ w' ∈ E.honest, … slot_at m' < slot_at m →
head(w',m') ⪰ b` premise), so no IH-carrying variant of the def is needed — the fold in
`advance_safe_of_descendStepChain` supplies it at the call site.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 0 — the pure-ℕ budget reduction -/

/-- Pure-ℕ core (a copy of `Ledger.sub_mul_le_of_span`, private there): from the
cross-multiplied `span_fraction` in set form `100·B ≤ C·(J + B)` and `C ≤ 100`, the R-term
subtraction is un-truncated, `(100−C)·B ≤ C·J`. -/
private theorem sub_mul_le_of_span {C B J : ℕ} (hC : C ≤ 100)
    (h : 100 * B ≤ C * (J + B)) : (100 - C) * B ≤ C * J := by
  have h1 : (100 - C) * B + C * B = 100 * B := by
    rw [← Nat.add_mul]; congr 1; omega
  rw [Nat.mul_add] at h
  omega

/-- **The pure-ℕ telescoping step for `hgrowS`.** Composing the inductive hypothesis at the window
end `es + d` (`Se + (Jd − Je) ≤ Sd`) with the single-slot growth step (`Sd + (Jd1 − Jd) ≤ Sd1`),
under the `Jspec`-monotonicity `Je ≤ Jd ≤ Jd1`, telescopes to `Se + (Jd1 − Je) ≤ Sd1` — the two
truncated `Jspec`-differences add across the endpoint. Kept over plain ℕ (`omega` is unreliable on
the `Slot`/`Gwei` abbrevs at the call site). -/
private theorem telescope_S {Se Sd Sd1 Je Jd Jd1 : ℕ}
    (hih : Se + (Jd - Je) ≤ Sd) (hs : Sd + (Jd1 - Jd) ≤ Sd1)
    (hm1 : Je ≤ Jd) (hm2 : Jd ≤ Jd1) :
    Se + (Jd1 - Je) ≤ Sd1 := by omega

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hgrowX`: `Xclass` antitonicity, telescoped

`Remainder.hXmono_of_engine` gives the single-slot antitonicity `Xval(σ'+1) ≤ Xval(σ')` under the
fresh-entrant engine inputs. Telescoping it over `[es, σ]` (induction on `σ − es`) yields the
aggregate `Xval(σ) ≤ Xval(es)`. -/

/-- Telescoping helper for `hgrowX`: induction on the window length `d = σ − es`. -/
private theorem hgrowX_aux (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    ∀ d : ℕ,
    (∀ σ' : Slot, es ≤ σ' → σ' < es + d →
      E.Xval cfg ext v₀ n₀ b' lo (σ' + 1) ≤ E.Xval cfg ext v₀ n₀ b' lo σ') →
    E.Xval cfg ext v₀ n₀ b' lo (es + d) ≤ E.Xval cfg ext v₀ n₀ b' lo es := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hstep
    have hih := ih (fun σ' h1 h2 => hstep σ' h1 (Nat.lt_succ_of_lt h2))
    have hs := hstep (es + d) (Nat.le_add_right es d) (Nat.lt_succ_self (es + d))
    exact le_trans hs hih

/-- **`hgrowX` from the per-slot antitonicity steps** — the pure telescoping. Given the single-slot
`Xval(σ'+1) ≤ Xval(σ')` for every `σ' ∈ [es, σ)`, `Xval(σ) ≤ Xval(es)`. -/
theorem hgrowX_of_steps (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo : Slot) {es σ : Slot}
    (hes : es ≤ σ)
    (hstep : ∀ σ' : Slot, es ≤ σ' → σ' < σ →
      E.Xval cfg ext v₀ n₀ b' lo (σ' + 1) ≤ E.Xval cfg ext v₀ n₀ b' lo σ') :
    E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es := by
  have h := E.hgrowX_aux cfg ext v₀ n₀ b' lo es (σ - es)
  rw [Nat.add_sub_cancel' hes] at h
  exact h hstep

/-- **`hgrowX` from the fresh-entrant engine inputs** — the deliverable. Telescopes
`Remainder.hXmono_of_engine` over `[es, σ]`. The single-epoch window hypothesis `hsame` (the
confinement flag the shell supplies) implies each per-slot same-epoch scoping; the head-safety IH
+ block-relay domain conditions enter through the per-slot `FreshEngineInputs`. -/
theorem hgrowX_of_engine (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hwf : WellFormedExecution E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo : Slot) {es σ : Slot}
    (hlo : lo ≤ es) (hes : es ≤ σ) (hσH : E.SlotWithinHorizon cfg σ)
    (hs0 : E.slot_at cfg 0 ≤ es)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hin : ∀ σ' : Slot, es ≤ σ' → σ' < σ → E.FreshEngineInputs cfg ext v₀ n₀ b' lo σ') :
    E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es := by
  refine E.hgrowX_of_steps cfg ext v₀ n₀ b' lo hes (fun σ' h1 h2 => ?_)
  have hσ1H : E.SlotWithinHorizon cfg (σ' + 1) :=
    E.slotWithinHorizon_mono cfg (Nat.succ_le_of_lt h2) hσH
  refine E.hXmono_of_engine cfg ext hhb hec hwf v₀ n₀ b' lo σ'
    hσ1H (le_trans hs0 (le_trans h1 (Nat.le_succ _)))
    (fun t htlo htσ' => ?_) (hin σ' h1 h2)
  have e1 := hsame t htlo (le_trans htσ' (le_of_lt h2))
  have e2 := hsame (σ' + 1) (le_trans hlo (le_trans h1 (Nat.le_succ _))) h2
  rw [e1, e2]

/-! ## Section 2 — `hgrowS`: honest-support growth, telescoped

`Remainder.hSmono_of_engine` gives the single-slot honest-support growth
`Sval(σ') + weight(fresh honest growth) ≤ Sval(σ'+1)` under the fresh-entrant engine inputs, and
`Fraction.Jspec_eq_add_growth` identifies that fresh honest weight with `Jspec(σ'+1) − Jspec(σ')`.
Telescoping the resulting per-slot step over `[es, σ]` collapses the sum of `Jspec`-differences to
`Jspec σ − Jspec es`, giving the aggregate `Sval(es) + (Jspec σ − Jspec es) ≤ Sval(σ)`. -/

/-- Telescoping helper for `hgrowS`: induction on the window length `d = σ − es`, composing each
per-slot `Jspec`-difference step with `telescope_S` under `Jspec`-monotonicity. -/
private theorem hgrowS_aux (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    ∀ d : ℕ,
    (∀ σ' : Slot, es ≤ σ' → σ' < es + d →
      E.Sval cfg ext v₀ n₀ b' lo σ' + (E.Jspec lo (σ' + 1) - E.Jspec lo σ')
        ≤ E.Sval cfg ext v₀ n₀ b' lo (σ' + 1)) →
    E.Sval cfg ext v₀ n₀ b' lo es + (E.Jspec lo (es + d) - E.Jspec lo es)
      ≤ E.Sval cfg ext v₀ n₀ b' lo (es + d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hstep
    have hih := ih (fun σ' h1 h2 => hstep σ' h1 (Nat.lt_succ_of_lt h2))
    have hs := hstep (es + d) (Nat.le_add_right es d) (Nat.lt_succ_self (es + d))
    have hm1 : E.Jspec lo es ≤ E.Jspec lo (es + d) := E.Jspec_mono lo (Nat.le_add_right es d)
    have hm2 : E.Jspec lo (es + d) ≤ E.Jspec lo (es + d + 1) :=
      E.Jspec_mono lo (Nat.le_succ (es + d))
    exact telescope_S hih hs hm1 hm2

/-- **`hgrowS` from the per-slot `Jspec`-difference growth steps** — the pure telescoping. Given the
single-slot `Sval(σ') + (Jspec(σ'+1) − Jspec(σ')) ≤ Sval(σ'+1)` for every `σ' ∈ [es, σ)`,
`Sval(es) + (Jspec σ − Jspec es) ≤ Sval(σ)`. -/
theorem hgrowS_of_steps (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo : Slot) {es σ : Slot}
    (hes : es ≤ σ)
    (hstep : ∀ σ' : Slot, es ≤ σ' → σ' < σ →
      E.Sval cfg ext v₀ n₀ b' lo σ' + (E.Jspec lo (σ' + 1) - E.Jspec lo σ')
        ≤ E.Sval cfg ext v₀ n₀ b' lo (σ' + 1)) :
    E.Sval cfg ext v₀ n₀ b' lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have h := E.hgrowS_aux cfg ext v₀ n₀ b' lo es (σ - es)
  rw [Nat.add_sub_cancel' hes] at h
  exact h hstep

/-- **The per-slot `Jspec`-difference growth step from the fresh-entrant engine inputs.** Turns
`Remainder.hSmono_of_engine`'s weight-form step into the `Jspec`-difference form by identifying the
fresh honest window growth with `Jspec(σ'+1) − Jspec(σ')` (`Fraction.Jspec_eq_add_growth`). -/
theorem hSstep_of_engine (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hwf : WellFormedExecution E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hσ1H : E.SlotWithinHorizon cfg (σ' + 1))
    (hs0 : E.slot_at cfg 0 ≤ σ' + 1)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hin : E.FreshEngineInputs cfg ext v₀ n₀ b' lo σ') :
    E.Sval cfg ext v₀ n₀ b' lo σ' + (E.Jspec lo (σ' + 1) - E.Jspec lo σ')
      ≤ E.Sval cfg ext v₀ n₀ b' lo (σ' + 1) := by
  have hw := E.hSmono_of_engine cfg ext hhb hec hwf v₀ n₀ b' lo σ'
    hσ1H hs0 hsame hin
  rw [E.Jspec_eq_add_growth lo (Nat.le_succ σ'), Nat.add_sub_cancel_left]
  exact hw

/-- **`hgrowS` from the fresh-entrant engine inputs** — the deliverable. Telescopes
`Remainder.hSmono_of_engine` (in `Jspec`-difference form) over `[es, σ]`. The single-epoch window
hypothesis `hsame` implies each per-slot same-epoch scoping; the head-safety IH + block-relay
domain conditions enter through the per-slot `FreshEngineInputs`. -/
theorem hgrowS_of_engine (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hwf : WellFormedExecution E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo : Slot) {es σ : Slot}
    (hlo : lo ≤ es) (hes : es ≤ σ) (hσH : E.SlotWithinHorizon cfg σ)
    (hs0 : E.slot_at cfg 0 ≤ es)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hin : ∀ σ' : Slot, es ≤ σ' → σ' < σ → E.FreshEngineInputs cfg ext v₀ n₀ b' lo σ') :
    E.Sval cfg ext v₀ n₀ b' lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  refine E.hgrowS_of_steps cfg ext v₀ n₀ b' lo hes (fun σ' h1 h2 => ?_)
  have hσ1H : E.SlotWithinHorizon cfg (σ' + 1) :=
    E.slotWithinHorizon_mono cfg (Nat.succ_le_of_lt h2) hσH
  refine E.hSstep_of_engine cfg ext hhb hec hwf v₀ n₀ b' lo σ'
    hσ1H (le_trans hs0 (le_trans h1 (Nat.le_succ _)))
    (fun t htlo htσ' => ?_) (hin σ' h1 h2)
  have e1 := hsame t htlo (le_trans htσ' (le_of_lt h2))
  have e2 := hsame (σ' + 1) (le_trans hlo (le_trans h1 (Nat.le_succ _))) h2
  rw [e1, e2]

/-! ## Section 3 — `hbudget`: the aggregate `span_fraction`, same-epoch regime

`Dominance` Part 2b: the confirm-margin strip's window growth needs the single aggregate budget
`(100−C)·(Bval σ − Bval es) ≤ C·(Jspec σ − Jspec es)`. In the **same-epoch regime**
`committee_assignment_unique` seat-uniqueness makes the window growth `span lo σ \ span lo es`
exactly the disjoint span `span (es+1) σ`, so the `Bval`/`Jspec` differences are the byz/honest
weights of that span and `ByzantineBound.span_fraction (es+1) σ` **is** the budget. The cross-epoch
regime — where recurring seats break the disjointness — needs the `INVstar` min-reserve tax carried
once (`Dominance` Part 3); it is surfaced as a residual, not delivered here. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **Growth decomposition of a filtered span weight**, for an arbitrary predicate `p` — the
`Fraction.Jspec_eq_add_growth` argument at predicate generality. As the window end grows `a → b`,
the `p`-filtered span weight splits as the value at `a` plus the `p`-weight of the committee
growth set. -/
theorem weight_filter_span_add_growth (p : ValidatorIndex → Prop) [DecidablePred p]
    (lo : Slot) {a b : Slot} (h : a ≤ b) :
    E.weight ((E.span_committee lo b).filter p)
      = E.weight ((E.span_committee lo a).filter p)
        + E.weight ((E.span_committee lo b \ E.span_committee lo a).filter p) := by
  simp only [Execution.weight]
  have hset : (E.span_committee lo b \ E.span_committee lo a).filter p
      = (E.span_committee lo b).filter p \ (E.span_committee lo a).filter p := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [add_comm, hset]
  exact (Finset.sum_sdiff (Finset.filter_subset_filter _ (E.span_committee_mono lo h))).symm

/-- **The window growth is a disjoint span, same-epoch.** Under a single-epoch window
(`hsame`: every slot of `[lo, σ]` shares `lo`'s epoch), `committee_assignment_unique`
seat-uniqueness identifies the window growth with the span `[es+1, σ]`: a validator in `(es, σ]`
cannot recur in `[lo, es]` (same epoch ⟹ one assignment), and every growth member is assigned
strictly past `es`. -/
theorem span_growth_eq_of_sameEpoch (hec : ExternalsCoherence cfg ext E) {lo es σ : Slot}
    (hlo : lo ≤ es) (hes : es ≤ σ)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo) :
    E.span_committee lo σ \ E.span_committee lo es = E.span_committee (es + 1) σ := by
  ext i
  simp only [Finset.mem_sdiff, Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨s, ⟨hslo, hshi⟩, hcomm⟩, hnot⟩
    refine ⟨s, ⟨?_, hshi⟩, hcomm⟩
    by_contra hc
    exact hnot ⟨s, ⟨hslo, Nat.lt_succ_iff.mp (not_le.mp hc)⟩, hcomm⟩
  · rintro ⟨s, ⟨hslo, hshi⟩, hcomm⟩
    have hlos : lo ≤ s := le_trans hlo (le_trans (Nat.le_succ es) hslo)
    refine ⟨⟨s, ⟨hlos, hshi⟩, hcomm⟩, ?_⟩
    rintro ⟨s', ⟨hs'lo, hs'hi⟩, hcomm'⟩
    have hep : compute_epoch_at_slot cfg s = compute_epoch_at_slot cfg s' :=
      (hsame s hlos hshi).trans (hsame s' hs'lo (le_trans hs'hi hes)).symm
    have heq := hec.committee_assignment_unique i s s' hcomm hcomm' hep
    exact absurd (le_trans (heq ▸ hslo) hs'hi) (Nat.not_succ_le_self es)

/-- **`hbudget` in the same-epoch regime** — the deliverable. The aggregate `span_fraction` budget
`(100−C)·(Bval σ − Bval es) ≤ C·(Jspec σ − Jspec es)`, unconditional under a single-epoch window
`hsame`. The window growth is the disjoint span `[es+1, σ]` (`span_growth_eq_of_sameEpoch`), so the
`Bval`/`Jspec` differences are that span's byz/honest weights (`weight_filter_span_add_growth` /
`Jspec_eq_add_growth`), and `ByzantineBound.span_fraction (es+1) σ` reduces (via
`sub_mul_le_of_span`, `C ≤ 25 ⟹ C ≤ 100`) to the budget. Cross-epoch is the `INVstar` min-reserve
residual (`Dominance` Part 3). -/
theorem hbudget_sameEpoch (hbb : ByzantineBound cfg E) (hec : ExternalsCoherence cfg ext E)
    {lo es σ : Slot} (hlo : lo ≤ es) (hes : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo) :
    (100 - cfg.confirmation_byzantine_threshold) * (E.Bval lo σ - E.Bval lo es)
      ≤ cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es) := by
  by_cases heq : es = σ
  · subst σ
    simp
  have heslt : es < σ := lt_of_le_of_ne hes heq
  have hes1H : E.SlotWithinHorizon cfg (es + 1) :=
    E.slotWithinHorizon_mono cfg (Nat.succ_le_of_lt heslt) hσH
  have hgeq := E.span_growth_eq_of_sameEpoch cfg ext hec hlo hes hsame
  have hJ : E.Jspec lo σ = E.Jspec lo es
      + E.weight ((E.span_committee (es + 1) σ).filter (fun i => i ∈ E.honest)) := by
    have hg := E.Jspec_eq_add_growth lo hes; rw [hgeq] at hg; exact hg
  have hB : E.Bval lo σ = E.Bval lo es
      + E.weight ((E.span_committee (es + 1) σ).filter (fun i => i ∉ E.honest)) := by
    have hg := E.weight_filter_span_add_growth (fun i => i ∉ E.honest) lo hes
    rw [hgeq] at hg; exact hg
  rw [hB, hJ, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  have hsf := hbb.span_fraction (es + 1) σ hes1H hσH
  rw [E.weight_split_honest (E.span_committee (es + 1) σ)] at hsf
  exact sub_mul_le_of_span
    (le_trans cfg.confirmation_byzantine_threshold_le (by norm_num)) hsf

end Execution

end FastConfirmation.Spec
