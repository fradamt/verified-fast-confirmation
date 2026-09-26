module
public import FastConfirmationProofs.Discount.Confinement
public import FastConfirmationProofs.Discount.CommitteeWindowWeight

@[expose] public section

/-!
# Spec / Proof / ByzVpre

Bounds Byzantine and honest support of a sibling branch with committee estimates.

This module contains `Jspec_add_Bval_eq_weight_span`, `weight_span_le_estimate`, `ancestor_slot_le` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## Part A — the estimate-domination arms bridges (`hR8aW`/`hR8cW`)

Both `Arms.arms_of_confirmed` estimate bounds reduce to one fact: the honest window weight
(`Jspec`) plus the enemy weight (`Bval`) is exactly the span-committee weight, which
`ByzantineWeightPremises.estimate_dominates` bounds by `100 · (estimate // 100)`. `hR8aW`/`hR8cW` then
follow from the atom identities that split those class weights across the confirmation window
(the identities themselves — `s₀ = Sval`, `Jspec` partition — are the enumerated residues). -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **Honest + enemy = span weight.** The honest committee-union weight `Jspec a b` and the
enemy weight `Bval a b` partition the span committee `[a, b]` (`weight_split_honest`). -/
theorem Jspec_add_Bval_eq_weight_span (a b : Slot) :
    E.Jspec a b + E.Bval a b = E.weight (E.span_committee a b) := by
  simp only [Execution.Jspec, Execution.Bval, Execution.Bwin]
  exact (E.weight_split_honest (E.span_committee a b)).symm

omit [LinearOrder Root] [Inhabited Root] in
/-- **Span weight dominated by the estimate floor.** `ByzantineWeightPremises.estimate_dominates` at the
balance source's total active balance (`htab` matches the two readings). -/
theorem weight_span_le_estimate (hbb : ByzantineWeightPremises cfg E) {bs : BeaconState Root}
    (htab : get_total_active_balance cfg bs = E.total_active cfg) (a b : Slot)
    (haH : E.SlotWithinHorizon cfg a) (hbH : E.SlotWithinHorizon cfg b) :
    E.weight (E.span_committee a b) ≤
      100 * (estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) a b
        / 100) := by
  rw [htab]
  exact hbb.estimate_dominates a b haH hbH



/-! ## Part B — the pre/V-region accessors and the covering split

The confirmation window `[lo, es]` (`lo := parent(b').slot + 1`) splits at `mid := b'.slot`
into the pre-region `[lo, b'.slot − 1]` and the V-region `[b'.slot, es]`. The pre-region
accessors mirror `Discount.ParentStuck` (the honest parent-stuck weight `Hpar`, recorded) and
the `Ledger` classes over the pre-region (`xpre`/`apre`/`Bpre`, ground). The covering-split
inequalities — `Jspec`/`Bval` over the full window are at most the pre-region plus the V-region
value — are pure `Finset` subadditivity (`weight_span_committee_split`); they are what makes the
V/pre atom decomposition of `hR8aW`/`hR8cW`'s identities legitimate. -/







/-! ## Part C — the recorded byz sibling sets and the dichotomy

The `hByz` field asks for a Byzantine supporter of a sibling `c'` confined to
`LedgerV2.BbadSet ∪ SpentSet`, but `BbadSet` is **ground-vote**-based. For byzantine validators
the ground vote and the recorded latest message are independent (no `no_forgery`), so the only
provable statement is the **recorded** one. `RecByzSibBase` is the recorded analog of `BbadSet`
(byz, non-equivocating window members whose recorded latest message is sibling-ward — neither
recorded `b`-supporting nor recorded `b`-ancestor). The dichotomy places every byz sibling
supporter into `RecByzSibBase` (setting slot `≤ es`) or `SpentSet` (setting slot
`> es`) via the provenance setting-slot case split. -/

omit [Inhabited Root] in
/-- **Ancestor slot bound.** If `y` is an ancestor of `x` (`is_ancestor store ⟨x⟩ ⟨y⟩`) on the
known walk domain, then `y`'s slot does not exceed `x`'s (`get_ancestor_slot_le` at `⟨y⟩`'s
slot). -/
theorem ancestor_slot_le {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x y : Root} (hw : WalkKnown store (store.blocks y).slot x)
    (hanc : is_ancestor store (get_node_for_root x) (get_node_for_root y) = true) :
    (store.blocks y).slot ≤ (store.blocks x).slot := by
  have hsle := get_ancestor_slot_le hwf hw
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hanc
  rw [hanc] at hsle
  simpa using hsle

open Classical in
/-- `RecByzSibBase` — the **recorded** base enemy: byz, non-`(w, m)`-equivocating members of the
window `[lo, es]` whose recorded latest message is sibling-ward: recorded neither `b`-supporting
(`¬ ⟨lm.root⟩ ⪰ ⟨b⟩`) nor `b`-ancestor (`¬ ⟨b⟩ ⪰ ⟨lm.root⟩`). The recorded analog of
`LedgerV2.BbadSet`, provable for byz sibling supporters and disjoint (by construction) from the
recorded `b`-supporters and the recorded parent-stuck byz. -/
noncomputable def RecByzSibBase (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo es).filter (fun i => i ∉ E.honest)).filter
    (fun i => i ∉ (E.store cfg ext w m).equivocating_indices ∧
      ∀ lm : LatestMessage Root, (E.store cfg ext w m).latest_messages i = some lm →
        ¬ is_ancestor (E.store cfg ext w m)
            (get_node_for_root lm.root) (get_node_for_root b) = true ∧
        ¬ is_ancestor (E.store cfg ext w m)
            (get_node_for_root b) (get_node_for_root lm.root) = true)



/-- **The recorded byz sibling dichotomy** (`EdgeInputResidual.hByz`, recorded variant). A
byz supporter `i` of a sibling `c'` of the `b`-side child `c` at `(w, m)` lands in the recorded
base enemy `RecByzSibBase … lo es` (its provenance setting slot `≤ es`) or the frozen tail
`SpentSet es σ` (setting slot `> es`). The recorded sibling-ward conditions are closed by
`siblings_incompatible` on the recorded supported node — the same fork geometry as
`Confinement.honest_sibling_confinement`, but kept recorded throughout (no
`recorded_lm_is_newest`, which is honest-only). -/
theorem byz_sibling_recorded_dichotomy
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots, ∀ r ∈ (E.store cfg ext w m).block_roots,
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo es σ : Slot}
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hσcur : get_current_slot cfg (E.store cfg ext w m) - 1 ≤ σ)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c') bs)
    (hib : i ∉ E.honest) :
    i ∈ E.RecByzSibBase cfg ext w m b lo es ∨ i ∈ E.SpentSet es σ := by
  obtain ⟨lm, hlm, hnoneq, hanc⟩ := mem_AttSupporters cfg hi_supp
  have hancC' : is_ancestor (E.store cfg ext w m) (get_node_for_root lm.root)
      (get_node_for_root c') = true := by
    simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
  have hlmk : lm.root ∈ (E.store cfg ext w m).block_roots := hlmknown lm i hlm
  obtain ⟨a, _, _, _, _, hslt, hcomm, _, hblk, _⟩ := hprov i lm hlm
  -- lower bound: lo ≤ c'.slot ≤ lm.root.slot ≤ a.data.slot
  have hc'lm : ((E.store cfg ext w m).blocks c').slot ≤
      ((E.store cfg ext w m).blocks lm.root).slot :=
    ancestor_slot_le hwf (hwalkK c' hc' lm.root hlmk) hancC'
  have hloa : lo ≤ a.data.slot := le_trans hlo (le_trans hc'lm hblk)
  -- the recorded sibling-ward conditions, from `siblings_incompatible`
  have hcond : ∀ lm' : LatestMessage Root, (E.store cfg ext w m).latest_messages i = some lm' →
      ¬ is_ancestor (E.store cfg ext w m)
          (get_node_for_root lm'.root) (get_node_for_root b) = true ∧
      ¬ is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root lm'.root) = true := by
    intro lm' hlm'
    rw [hlm] at hlm'
    obtain rfl : lm = lm' := Option.some.injEq _ _ ▸ hlm'
    refine ⟨fun hsupp => ?_, fun hanc2 => ?_⟩
    · -- lm.root ⪰ b ⪰ c ⟹ lm.root ⪰ c; with lm.root ⪰ c' this contradicts siblings_incompatible
      have hlmc : is_ancestor (E.store cfg ext w m) (get_node_for_root lm.root)
          (get_node_for_root c) = true :=
        is_ancestor_trans (a := get_node_for_root lm.root) (b := get_node_for_root b)
        (c := get_node_for_root c) hwf (hwalkK c hc lm.root hlmk) (hwalkK c hc b hb) hsupp hbc
      exact siblings_incompatible hwf hc hc' hh hpc hpc' hne
        (hwalkK c hc lm.root hlmk) (hwalkK c' hc' lm.root hlmk) hlmc hancC'
    · -- b ⪰ lm.root ⪰ c' ⟹ b ⪰ c'; with b ⪰ c this contradicts siblings_incompatible
      have hbc' : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root c') = true :=
        is_ancestor_trans hwf (a := get_node_for_root b) (b := get_node_for_root lm.root)
          (c := get_node_for_root c') (hwalkK c' hc' b hb) (hwalkK c' hc' lm.root hlmk) hanc2 hancC'
      exact siblings_incompatible hwf hc hc' hh hpc hpc' hne
        (hwalkK c hc b hb) (hwalkK c' hc' b hb) hbc hbc'
  -- the setting-slot dichotomy
  rcases le_or_gt a.data.slot es with hle | hgt
  · refine Or.inl ?_
    have hspan : i ∈ E.span_committee lo es :=
      Finset.mem_biUnion.mpr ⟨a.data.slot, Finset.mem_Icc.mpr ⟨hloa, hle⟩, hcomm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hspan, hib⟩, hnoneq, hcond⟩
  · refine Or.inr ?_
    have hsleσ : a.data.slot ≤ σ := le_trans (Nat.le_sub_one_of_lt hslt) hσcur
    refine Finset.mem_filter.mpr ⟨?_, hib⟩
    exact Finset.mem_biUnion.mpr ⟨a.data.slot, Finset.mem_Icc.mpr ⟨hgt, hsleσ⟩, hcomm⟩

/-! ## Part D — `hByz` discharged: `BbadSet` is the recorded base enemy

After the `recorded-base reduction` reshape, `LedgerV2.BbadSet` is **definitionally** `RecByzSibBase` (both
are the recorded, sibling-ward, non-`(w,m)`-equivocating byz window set). Hence the
recorded dichotomy `byz_sibling_recorded_dichotomy` — proved above with no
`recorded_lm_is_newest` (byz have no `no_forgery`, so the ground↔recorded bridge is
honest-only and stays on `Confinement`) — now discharges the `hByz` obligation of
`EdgeDynamics.EdgeInputResidual` / `ForkAssembly.ForkEdgeInput` verbatim: a byz supporter
of a filtered sibling `c'` of the `b`-side child `c` lands in `BbadSet ∪ SpentSet`. -/


/-- **`hByz`, discharged** (`recorded-base reduction`). The per-`(c', i)` core of `EdgeInputResidual.hByz` /
`ForkEdgeInput.hByz`: a byzantine supporter `i` of a filtered sibling `c'` of the
`b`-side child `c` at `(w, m)` is confined to the recorded base enemy `BbadSet` (setting
slot `≤ es`) or the frozen tail `SpentSet es σ` (setting slot `> es`). This is
`byz_sibling_recorded_dichotomy` with `RecByzSibBase` rewritten to `BbadSet` — the byz
analog of `Confinement.honest_sibling_confinement`, closing the def-shape mismatch that
motivated the reshape. -/
theorem byz_sibling_confinement
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots, ∀ r ∈ (E.store cfg ext w m).block_roots,
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo es σ : Slot}
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hσcur : get_current_slot cfg (E.store cfg ext w m) - 1 ≤ σ)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c') bs)
    (hib : i ∉ E.honest) :
    i ∈ E.BbadSet cfg ext w m b lo es ∨ i ∈ E.SpentSet es σ :=
  E.byz_sibling_recorded_dichotomy cfg ext hprov hwf hwalkK hb hc hc' hh hpc hpc' hne hbc
    hlo hσcur hlmknown hi_supp hib

end Execution

end FastConfirmation.Spec

end
