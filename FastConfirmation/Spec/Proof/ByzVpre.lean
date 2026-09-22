module
public import FastConfirmation.Spec.Proof.Confinement
public import FastConfirmation.Spec.Proof.EngineWindows

@[expose] public section

/-!
# Spec / Proof / ByzVpre: the byz sibling reconciliation and the V/pre accessors

This module supplies two inputs of
`EdgeDynamics.EdgeInputResidual`:

* **the `hByz` Byzantine sibling confinement.** `LedgerV2.BbadSet` is a
  **ground-vote** set (`E.SupportsDesc` / `E.AncestorOrVoteless`
  over `E.vote`), while a byz supporter of a sibling is only known through the store's
  **recorded** latest message. For byzantine validators the two diverge (there is no
  `HonestBehavior.no_forgery`), so the recorded fact cannot be pushed into the ground set.
  This module defines the **recorded-based** byz sibling sets (`RecByzSib`), proves the
  recorded dichotomy (recorded-at-`es` vs post-`es`-vote, from the provenance setting-slot
  case split) — the tail half landing cleanly in `SpentSet` — and proves the
  arms-side enemy accounting against the recorded sets (disjoint from the recorded `Bsup` /
  equivocators / `ParentStuckByz`, all recorded). The ground `BbadSet` relation survives only
  for honest members (`StepDischarge.recorded_lm_is_newest_at`), which do not occur in the byz
  sets. The remaining mismatch is that `hByz`/`hBbadVal` are phrased over the
  ground `BbadSet`.

* **the V/pre accessor split** — `Confinement`'s undelivered Part-4 accessors. The confirmation
  window `[lo, es]` (`lo := parent(b').slot + 1`, `es := current − 1`) splits into the
  **pre-region** `[lo, b'.slot − 1]` and the **V-region** `[b'.slot, es]`. This module defines
  the pre-region accessors (`HparVal` = `Discount.ParentStuck` weight; `xPreVal`/`aPreVal`/
  `BpreVal` = the `Ledger` classes over the pre-region) and delivers the two estimate-domination
  bridges `Arms.arms_of_confirmed` consumes — `hR8aW` (V-span) and `hR8cW` (full window) — as
  inequalities anchored on `ByzantineBound.estimate_dominates`, with the atom identities
  (`s₀ = Sval`, `xV + xpre = Xval`, the honest-window partition `= Jspec`) reduced to precisely
  the shapes `DynamicsClosure.INV2_base_of_confirmed` needs. The pure-`Finset` split
  inequalities (`Jspec`/`Bval` subadditive covering, `Sval` supporter-into-V confinement) are
  proved; the recorded↔ground identity residues are enumerated.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Part A — the estimate-domination arms bridges (`hR8aW`/`hR8cW`)

Both `Arms.arms_of_confirmed` estimate bounds reduce to one fact: the honest window weight
(`Jspec`) plus the enemy weight (`Bval`) is exactly the span-committee weight, which
`ByzantineBound.estimate_dominates` bounds by `100 · (estimate // 100)`. `hR8aW`/`hR8cW` then
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
/-- **Span weight dominated by the estimate floor.** `ByzantineBound.estimate_dominates` at the
balance source's total active balance (`htab` matches the two readings). -/
theorem weight_span_le_estimate (hbb : ByzantineBound cfg E) {bs : BeaconState Root}
    (htab : get_total_active_balance cfg bs = E.total_active cfg) (a b : Slot)
    (haH : E.SlotWithinHorizon cfg a) (hbH : E.SlotWithinHorizon cfg b) :
    E.weight (E.span_committee a b) ≤
      100 * (estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) a b
        / 100) := by
  rw [htab]
  exact hbb.estimate_dominates a b haH hbH

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hR8cW` from the full-window identities.** With the full honest window
`s₀ + aV + xV + (Hpar + apre + xpre)` identified with `Jspec [lo, es]` (`lo := parent(b').slot+1`,
`es := current − 1`) and the enemy `B0` with `Bval [lo, es]`, the U-span estimate-domination
bound holds — exactly `arms_of_confirmed`'s `hR8cW`. -/
theorem hR8cW_of_identities (hbb : ByzantineBound cfg E) {bs : BeaconState Root}
    {store : Store Root} {b' : Root}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hstartH : E.SlotWithinHorizon cfg
      ((store.blocks (store.blocks b').parent_root).slot + 1))
    (hendH : E.SlotWithinHorizon cfg (get_current_slot cfg store - 1))
    {s0 aV xV Hpar apre xpre B0 : ℕ}
    (hJ : s0 + aV + xV + (Hpar + apre + xpre)
        = E.Jspec ((store.blocks (store.blocks b').parent_root).slot + 1)
            (get_current_slot cfg store - 1))
    (hB : B0 = E.Bval ((store.blocks (store.blocks b').parent_root).slot + 1)
            (get_current_slot cfg store - 1)) :
    s0 + aV + xV + (Hpar + apre + xpre) + B0
      ≤ 100 * (estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b').parent_root).slot + 1)
          (get_current_slot cfg store - 1) / 100) := by
  rw [hJ, hB, E.Jspec_add_Bval_eq_weight_span]
  exact E.weight_span_le_estimate cfg hbb htab _ _ hstartH hendH

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hR8aW` from the V-region identities.** With the V-region honest classes
`s₀ + aV + xV` identified with `Jspec [sa, es]` (`sa` the `get_adversarial_weight` span start —
`b'.slot` in the same-epoch case, `start_slot(epoch b')` in the crossing case) and the V-span
enemy `B_V` with `Bval [sa, es]`, the V-span estimate-domination bound holds — exactly
`arms_of_confirmed`'s `hR8aW` with `qV := estimate [sa, es] // 100`. -/
theorem hR8aW_of_identities (hbb : ByzantineBound cfg E) {bs : BeaconState Root}
    (htab : get_total_active_balance cfg bs = E.total_active cfg) (sa es : Slot)
    (hsaH : E.SlotWithinHorizon cfg sa) (hesH : E.SlotWithinHorizon cfg es)
    {s0 aV xV B_V : ℕ}
    (hJ : s0 + aV + xV = E.Jspec sa es)
    (hB : B_V = E.Bval sa es) :
    s0 + aV + xV + B_V
      ≤ 100 * (estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          sa es / 100) := by
  rw [hJ, hB, E.Jspec_add_Bval_eq_weight_span]
  exact E.weight_span_le_estimate cfg hbb htab _ _ hsaH hesH

/-! ## Part B — the pre/V-region accessors and the covering split

The confirmation window `[lo, es]` (`lo := parent(b').slot + 1`) splits at `mid := b'.slot`
into the pre-region `[lo, b'.slot − 1]` and the V-region `[b'.slot, es]`. The pre-region
accessors mirror `Discount.ParentStuck` (the honest parent-stuck weight `Hpar`, recorded) and
the `Ledger` classes over the pre-region (`xpre`/`apre`/`Bpre`, ground). The covering-split
inequalities — `Jspec`/`Bval` over the full window are at most the pre-region plus the V-region
value — are pure `Finset` subadditivity (`weight_span_committee_split`); they are what makes the
V/pre atom decomposition of `hR8aW`/`hR8cW`'s identities legitimate. -/

/-- `Hpar` — the recorded honest parent-stuck weight (`Discount.ParentStuck`). -/
noncomputable def HparVal (store : Store Root) (bs : BeaconState Root) (b : Root) : Gwei :=
  E.weight (ParentStuck cfg E store bs b)

/-- `xpre` — the pre-region sibling-stuck honest weight (`Ledger.Xval` over `[lo, b'.slot−1]`). -/
noncomputable def xPreVal (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo bslot : Slot) : Gwei :=
  E.Xval cfg ext v₀ n₀ b' lo (bslot - 1)

/-- `apre + Hpar` — the pre-region ancestor/voteless honest weight (`Ledger.Aval` over the
pre-region; its `ParentStuck` slice is `Hpar`, the remainder `apre`). -/
noncomputable def aPreVal (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo bslot : Slot) : Gwei :=
  E.Aval cfg ext v₀ n₀ b' lo (bslot - 1)

/-- `Bpre` — the pre-region enemy weight (`Ledger.Bval` over `[lo, b'.slot−1]`). -/
noncomputable def BpreVal (lo bslot : Slot) : Gwei :=
  E.Bval lo (bslot - 1)

omit [LinearOrder Root] [Inhabited Root] in
/-- **Honest-window covering split.** `Jspec [a, b]` is at most the pre-window plus the
V-window honest weight — the honest slice of `weight_span_committee_split`. -/
theorem Jspec_split_le (a mid b : Slot) :
    E.Jspec a b ≤ E.Jspec a (mid - 1) + E.Jspec mid b := by
  simp only [Execution.Jspec]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  rw [← Finset.filter_union]
  exact Finset.filter_subset_filter _ (span_committee_subset_union a mid b)

omit [LinearOrder Root] [Inhabited Root] in
/-- **Enemy covering split.** `Bval [a, b]` is at most the pre-window plus the V-window enemy
weight — the non-honest slice of `weight_span_committee_split`. -/
theorem Bval_split_le (a mid b : Slot) :
    E.Bval a b ≤ E.Bval a (mid - 1) + E.Bval mid b := by
  simp only [Execution.Bval, Execution.Bwin]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  rw [← Finset.filter_union]
  exact Finset.filter_subset_filter _ (span_committee_subset_union a mid b)

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

/-- `RecByzSibBase ⊆ Bwin`: the recorded base enemy sits inside the window byz set. -/
theorem RecByzSibBase_subset_Bwin (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot) :
    E.RecByzSibBase cfg ext w m b lo es ⊆ E.Bwin lo es := by
  intro i hi
  simp only [Execution.RecByzSibBase, Finset.mem_filter] at hi
  exact Finset.mem_filter.mpr ⟨hi.1.1, hi.1.2⟩

/-- `weight(RecByzSibBase) ≤ B(es)` — the recorded base enemy weight is at most the window byz
weight, the recorded-side analog of `LedgerV2.BbadVal_le_Bval`. -/
theorem weight_RecByzSibBase_le_Bval (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot) :
    E.weight (E.RecByzSibBase cfg ext w m b lo es) ≤ E.Bval lo es :=
  E.weight_mono (E.RecByzSibBase_subset_Bwin cfg ext w m b lo es)

/-- **The recorded byz sibling dichotomy** (`EdgeInputResidual.hByz`, recorded variant). A
byz supporter `i` of a sibling `c'` of the `b`-side child `c` at `(w, m)` lands in the recorded
base enemy `RecByzSibBase … lo es` (its provenance setting slot `≤ es`) or the frozen tail
`SpentSet es σ` (setting slot `> es`). The recorded sibling-ward conditions are closed by
`siblings_incompatible` on the recorded supported node — the same fork geometry as
`Confinement.honest_sibling_confinement`, but kept recorded throughout (no
`recorded_lm_is_newest_at`, which is honest-only). -/
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
  obtain ⟨a, _, _, _, _, hslt, hcomm, _, hblk⟩ := hprov i lm hlm
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
        is_ancestor_trans hwf (hwalkK c hc lm.root hlmk) (hwalkK c hc b hb) hsupp hbc
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
`recorded_lm_is_newest_at` (byz have no `no_forgery`, so the ground↔recorded bridge is
honest-only and stays on `Confinement`) — now discharges the `hByz` obligation of
`EdgeDynamics.EdgeInputResidual` / `ForkAssembly.ForkEdgeInput` verbatim: a byz supporter
of a filtered sibling `c'` of the `b`-side child `c` lands in `BbadSet ∪ SpentSet`. -/

/-- **`RecByzSibBase = BbadSet`** (`recorded-base reduction`). The recorded byz sibling base and the reshaped
`LedgerV2.BbadSet` are the same set (definitional). -/
theorem RecByzSibBase_eq_BbadSet (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot) :
    E.RecByzSibBase cfg ext w m b lo es = E.BbadSet cfg ext w m b lo es := rfl

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
