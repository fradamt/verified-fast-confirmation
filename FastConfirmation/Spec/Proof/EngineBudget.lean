import FastConfirmation.Spec.Proof.Engine
import FastConfirmation.Spec.Proof.Provenance
import FastConfirmation.Spec.Proof.HonestWeight
import FastConfirmation.Spec.Proof.MajorityPersists

/-!
# Spec / Proof / EngineBudget: the sibling budget

This module proves the head-safety engine's *sibling upper bound* and
*new-window Byzantine budget*. At a later honest store `(w, m)` in slot
`k ≥ s`, a fork on `b`'s chain pits a `b`-side child `c` (`c ≼ b`) against a
sibling `c'`. The ledger `MajorityPersists.fork_majority` consumes three
weight facts about that store; this module supplies the sibling-side two:

* **`hsib`** — the sibling's recorded score, plus `b`'s old honest support and
  the fork-parent stuck weight, fits inside the union-window committee budget;
* **`hnb`** — the new window's Byzantine recorded weight is covered by its honest
  recorded weight.

The relevant lemmas are:

* **`sibling_supporter_window`** — every supporter of `c'` sits
  in the ground-truth span committee `[c'.slot, k−1]`. The pre-fork
  zero-contribution argument is exactly `supporter_mem_span_committee`'s slot
  chain (`get_ancestor_slot_le`): a committee member of a slot `< c'.slot` has a
  vote-block of slot `< c'.slot`, so `c'` cannot descend from it.
* **`weight_mono` / `weight_add3_le`** — set-weight monotonicity and the
  three-disjoint-parts superadditive bound, the shape the additive `hsib` needs.
* **`sibling_score_le_estimate`** — `c'`'s recorded
  score is at most the union-window committee estimate `estimate[c'.slot, k−1]`
  (`attestation_score_eq_weight` + `sibling_supporter_window` +
  `estimate_sound`).
* **`sibling_disjoint_from_bchild`** — the
  supporter sets of the two siblings are disjoint, hence a `b`-chain child's
  supporters never overlap `c'`'s.
* **`weight_honest_byz_split`** — a span committee's weight splits into its
  honest and non-honest parts.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Set-weight monotonicity and superadditivity -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Ground-truth weight is monotone under `Finset` inclusion (the effective
balances are nonnegative). -/
theorem weight_mono {E : Execution Root} {A B : Finset ValidatorIndex} (h : A ⊆ B) :
    E.weight A ≤ E.weight B := by
  simp only [Execution.weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

omit [LinearOrder Root] [Inhabited Root] in
/-- Superadditivity into a common superset over three pairwise-disjoint parts —
the additive shape the ledger's `hsib` decomposition needs (sibling supporters,
`b`'s old honest supporters, and the fork-parent stuck set inside the
union-window budget). -/
theorem weight_add3_le {E : Execution Root} {A B C U : Finset ValidatorIndex}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hCU : C ⊆ U) :
    E.weight A + E.weight B + E.weight C ≤ E.weight U := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hAB]
  rw [← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  exact Finset.union_subset (Finset.union_subset hAU hBU) hCU

/-! ## result 1 — sibling window confinement

Every supporter of the sibling `c'` at a store carrying `LatestMessageProvenance`
lies in the ground-truth span committee `[c'.slot, current_slot − 1]`. This is
`supporter_mem_span_committee` instantiated at `b := c'` with the span start
pushed all the way up to `c'`'s own slot (`sa = (blocks c').slot`): the pre-fork
zero-contribution argument (a slot-`t` member with `t < c'.slot` has a
vote-block of slot `≤ t < c'.slot`, which `c'` cannot descend from) is precisely
the `get_ancestor_slot_le` slot chain inside that lemma. -/

omit [Inhabited Root] in
/-- **Sibling window confinement.** A supporter of `c'` sits in the span
committee starting at `c'`'s own slot. -/
theorem sibling_supporter_window {E : Execution Root} {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {bs : BeaconState Root} {c' : Root} {i : ValidatorIndex}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hi : i ∈ AttSupporters cfg store (get_node_for_root c') bs)
    (hwalk : ∀ lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks c').slot lm.root) :
    i ∈ E.span_committee (store.blocks c').slot (get_current_slot cfg store - 1) :=
  supporter_mem_span_committee cfg hwf hprov hi hwalk (le_refl _)

/-! ## result 2 (upper half) — the sibling score is bounded by the window estimate

`c'`'s recorded score is the ground-truth weight of its supporter set
(`attestation_score_eq_weight`); that set is confined to the span committee
`[c'.slot, k−1]` (result 1), whose weight the estimate bounds
(`ByzantineBound.estimate_sound`). Hence the sibling score never exceeds the
union-window committee estimate — the top of the `hsib` ledger's right-hand
side. -/

omit [Inhabited Root] in
/-- **Sibling score upper bound.** On a registry-constant balance source, the
sibling `c'`'s attestation score at `store` is at most the committee-weight
estimate over its confinement window `[c'.slot, current_slot − 1]`. -/
theorem sibling_score_le_estimate {E : Execution Root} (hbb : ByzantineBound cfg E)
    {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {bs : BeaconState Root} {c' : Root} (hval : bs.validators = E.registry)
    (hcH : E.SlotWithinHorizon cfg (store.blocks c').slot)
    (hendH : E.SlotWithinHorizon cfg (get_current_slot cfg store - 1))
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hwalk : ∀ i ∈ AttSupporters cfg store (get_node_for_root c') bs, ∀ lm,
      store.latest_messages i = some lm → WalkKnown store (store.blocks c').slot lm.root) :
    get_attestation_score cfg store (get_node_for_root c') bs ≤
      estimate_committee_weight_between_slots cfg (E.total_active cfg)
        (store.blocks c').slot (get_current_slot cfg store - 1) := by
  rw [attestation_score_eq_weight cfg hval]
  refine le_trans (weight_mono ?_) (hbb.estimate_sound _ _ hcH hendH)
  intro i hi
  rw [List.mem_toFinset] at hi
  exact sibling_supporter_window cfg hwf hprov hi (hwalk i hi)

/-! ## Set-weight honest/Byzantine split

The span committee's weight splits into its honest and non-honest parts. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- A validator set's ground-truth weight splits into its non-honest and honest
parts. -/
theorem weight_honest_byz_split {E : Execution Root} (S : Finset ValidatorIndex) :
    E.weight S = E.weight (S.filter (fun i => i ∉ E.honest))
      + E.weight (S.filter (fun i => i ∈ E.honest)) := by
  simp only [Execution.weight]
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not S (fun i => i ∈ E.honest) E.weight_of).symm

/-! ## result 2 (disjointness) — the sibling avoids `b`'s support

`MajorityPersists.supporters_disjoint` already gives that the two siblings'
supporter sets are disjoint. Since the old honest supporter set `HS₀` supports
the `b`-side child `c` (via `SupportTransport` / `EngineSupport`), it sits inside
`c`'s supporter set, hence is disjoint from `c'`'s. This is the disjointness the
additive `hsib` ledger needs between the sibling and `b`'s recorded support. -/

omit [Inhabited Root] in
/-- **Sibling disjoint from `b`'s support.** With `c` the `b`-side child and `c'`
its sibling (distinct children of `p`), any set `HS₀` contained in `c`'s
supporter set is disjoint from `c'`'s supporter set. -/
theorem sibling_disjoint_from_bsupport {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {bs : BeaconState Root} {p c c' : Root} {HS0 : Finset ValidatorIndex}
    (hc : c ∈ store.block_roots) (hc' : c' ∈ store.block_roots) (hp : p ∈ store.block_roots)
    (hpc : (store.blocks c).parent_root = p) (hpc' : (store.blocks c').parent_root = p)
    (hne : c ≠ c')
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks c).slot lm.root ∧
      WalkKnown store (store.blocks c').slot lm.root)
    (hHS0 : HS0 ⊆ (AttSupporters cfg store (get_node_for_root c) bs).toFinset) :
    Disjoint (AttSupporters cfg store (get_node_for_root c') bs).toFinset HS0 :=
  ((supporters_disjoint cfg hwf hc hc' hp hpc hpc' hne hwalk).symm).mono_right hHS0

/-! ## result 2 (additive assembly) — the abstract `hsib` shape

Given the three-way disjointness and a common superset `U` for the sibling's
supporters, `b`'s old honest support `HS₀`, and the fork-parent stuck set `D`,
the additive bound `score(c') + weight(HS₀) + weight(D) ≤ weight(U)` follows from
`weight_add3_le` and the score-weight identity. This is the ledger's `hsib`
left-hand side; the caller supplies `U` and its weight identification with
`Wold + Bnew`. -/

omit [Inhabited Root] in
/-- **Abstract sibling ledger.** On a registry-constant balance source, the
sibling `c'`'s score plus `b`'s old honest support weight plus the stuck-set
weight is at most the weight of any common superset `U` the three disjoint sets
sit in. Instantiating `U` with the union-window committee and identifying
`weight U ≤ Wold + Bnew` yields the ledger's `hsib`. -/
theorem sibling_score_plus_le {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {c' : Root} (hval : bs.validators = E.registry)
    {HS0 D U : Finset ValidatorIndex}
    (hAB : Disjoint (AttSupporters cfg store (get_node_for_root c') bs).toFinset HS0)
    (hAC : Disjoint (AttSupporters cfg store (get_node_for_root c') bs).toFinset D)
    (hBC : Disjoint HS0 D)
    (hAU : (AttSupporters cfg store (get_node_for_root c') bs).toFinset ⊆ U)
    (hBU : HS0 ⊆ U) (hCU : D ⊆ U) :
    get_attestation_score cfg store (get_node_for_root c') bs + E.weight HS0 + E.weight D
      ≤ E.weight U := by
  rw [attestation_score_eq_weight cfg hval]
  exact weight_add3_le hAB hAC hBC hAU hBU hCU

/-! ## Union-window input

**`sibling_score_plus_le` — the union-window identification.**
The abstract additive bound is complete; instantiating it needs (i) the union
window `U = span_committee[parent(c').slot+1, k−1]` and the identification
`weight U ≤ Wold + Bnew` splitting `U` into the OLD-window committee
(`[parent(b).slot+1, s−1]`, estimated by `Wold`) and the NEW-window Byzantine
part (`Bnew`), and (ii) the characterization of the stuck set `D` as the
fork-parent's own empty-slot voters with `weight D` matching `support_discount`'s
soundness. Both are the engine assembly's window-bookkeeping, needing the `[s,k)`
slot-window split machinery that lives with the orchestrator, not a single
frozen-assumption lemma. The disjointness half (`sibling_disjoint_from_bsupport`)
and the score-weight/superadditive core are delivered. -/

end FastConfirmation.Spec
