module
public import FastConfirmation.Spec.Proof.Engine
public import FastConfirmation.Spec.Proof.Provenance
public import FastConfirmation.Spec.Proof.HonestWeight
public import FastConfirmation.Spec.Proof.MajorityPersists

@[expose] public section

/-!
# Spec / Proof / EngineBudget

This module contains `weight_mono` and related declarations.
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


/-! ## result 1 — sibling window confinement

Every supporter of the sibling `c'` at a store carrying `LatestMessageProvenance`
lies in the ground-truth span committee `[c'.slot, current_slot − 1]`. This is
`supporter_mem_span_committee` instantiated at `b := c'` with the span start
pushed all the way up to `c'`'s own slot (`sa = (blocks c').slot`): the pre-fork
zero-contribution argument (a slot-`t` member with `t < c'.slot` has a
vote-block of slot `≤ t < c'.slot`, which `c'` cannot descend from) is precisely
the `get_ancestor_slot_le` slot chain inside that lemma. -/


/-! ## result 2 (upper half) — the sibling score is bounded by the window estimate

`c'`'s recorded score is the ground-truth weight of its supporter set
(`attestation_score_eq_weight`); that set is confined to the span committee
`[c'.slot, k−1]` (result 1), whose weight the estimate bounds
(`ByzantineBound.estimate_sound`). Hence the sibling score never exceeds the
union-window committee estimate — the top of the `hsib` ledger's right-hand
side. -/


/-! ## Set-weight honest/Byzantine split

The span committee's weight splits into its honest and non-honest parts. -/


/-! ## result 2 (disjointness) — the sibling avoids `b`'s support

`MajorityPersists.supporters_disjoint` already gives that the two siblings'
supporter sets are disjoint. Since the old honest supporter set `HS₀` supports
the `b`-side child `c` (via `SupportTransport` / `EngineSupport`), it sits inside
`c`'s supporter set, hence is disjoint from `c'`'s. This is the disjointness the
additive `hsib` ledger needs between the sibling and `b`'s recorded support. -/







end FastConfirmation.Spec

end
