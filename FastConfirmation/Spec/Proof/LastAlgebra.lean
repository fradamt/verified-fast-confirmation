import FastConfirmation.Spec.Proof.Identities
import FastConfirmation.Spec.Proof.Reanchor
import FastConfirmation.Spec.Proof.ByzVpre
import FastConfirmation.Spec.Proof.IHMechanize

/-!
# Spec / Proof / LastAlgebra: the `VpreIdentities` class algebra + coverage/head/sat

This module supplies the final algebraic identities used by the proof decomposition.
`Identities.INV2_base_bridged_instantiated` reduces `INV2(es)` to the transparent
five-field `VpreIdentities` coherence bundle. This module discharges those five
fields (the carried `same-slot availability`-family class algebra) against a **single, uniform
`σ = es` window anchor**, plus the three companion residuals `hcov`/`hhead`/`hsat`
that the vote-landing / boost-dilution exports consume.

The uniform-anchor choice is the key simplification: all class weights are read at
`σ = es` (`aV := Aval sa es`, `xV := Xval sa es`, `xpre :=` the honest window
`Xclass` growth `lo → sa`, `apre :=` its `Aclass` growth minus the parent-stuck
slice), so the honest identities are pure `Finset` growth/`sdiff` algebra over the
`weight_partition`, and the supporter confinement `Sval lo es = Sval sa es` is
`Reanchor.Sval_anchor_invariant` verbatim.

Delivered, item by item:

* **`hJV`** (`hJV_of_anchor`) — supporter confinement: `Sval lo es + Aval sa es +
  Xval sa es = Jspec sa es`, from `Sval_anchor_invariant` + `weight_partition`.
* **`hXval`** (`hXval_of_growth`) — sibling-stuck split: `Xval sa es + xpre =
  Xval lo es`, `sdiff` over the `Xclass` window growth (`Xclass sa es ⊆ Xclass lo es`).
* **`hR4b`** (`hR4b_of_confinement`) — V-span byz partition: byz supporters +
  equivocation score `≤ Bval sa es`, the disjoint-into-`Bwin` half of
  `HonestWeight.byz_plus_equiv_le`.
* **`hJfull`** (`hJfull_of_parentStuck`) — the two-region honest partition, from
  `hJV`/`hXval` + `weight_partition lo es` + the parent-stuck honest slice
  `ParentStuck ⊆ Aclass lo es \ Aclass sa es` (the honest recorded↔ground bridge,
  taken as an input — see the residual note).
* **`hBbadfin`** (`hBbadfin_of_partition`) — the full-window byz partition, the
  four-disjoint-parts (`BbadSet`/byz-supporters/`EquivActive`/`ParentStuckByz`)
  bound into `Bwin lo es`, taking the pairwise disjointness/confinement as inputs.
* **`hcov`** (`hcov_of_coverage`) — the full-epoch coverage floor `total_active ≤
  2·Jspec lo σ'`, from the `span_fraction` half (proved) + the active-coverage
  weight identity `total_active ≤ weight (span_committee lo σ')` (explicit residual).
* **`hhead`** (`hhead_of_wellFormed`) — the head block-state slot `≤ s`, from
  `Delivery.store_blocks_slot_le_current` + `Preservation.block_state_slot_eq` +
  `HeadStack.head_root_known`.
* **`hsat`** — the post-`T1` saturation crux is a store-dynamics fact
  (`committee_coverage` + `votes_head` + landing); this module composes the
  `Sclass = window` collapse (`IHMechanize.hmaj_of_saturation`) but leaves the
  crux itself as the enumerated dynamics residual.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Set-weight `sdiff` algebra

The uniform-`σ = es` anchor makes every honest identity a growth split of the
window classes as `lo` widens from `sa` to `lo`. `weight_add_sdiff` is the single
`Finset.sum_sdiff` step it all rests on. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Weight splits as the base plus the growth (`sdiff`): `weight A + weight (B \ A)
= weight B` for `A ⊆ B`. -/
theorem weight_add_sdiff {A B : Finset ValidatorIndex} (h : A ⊆ B) :
    E.weight A + E.weight (B \ A) = E.weight B := by
  simp only [Execution.weight]
  rw [add_comm]
  exact Finset.sum_sdiff h

/-- `Xclass` is monotone in the lower anchor (`σ` fixed): widening `sa → lo` only
adds members. Both the span (`span_committee_mono_lo`) and the identical `σ`-fixed
`¬S ∧ ¬A` predicate ride the filter inclusion. -/
theorem Xclass_mono_lo (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) {lo sa σ : Slot}
    (h : lo ≤ sa) :
    E.Xclass cfg ext v₀ n₀ b' sa σ ⊆ E.Xclass cfg ext v₀ n₀ b' lo σ := by
  classical
  simp only [Execution.Xclass]
  exact Finset.filter_subset_filter _
    (Finset.filter_subset_filter _ (span_committee_mono_lo h))

/-- `Aclass` is monotone in the lower anchor (`σ` fixed). -/
theorem Aclass_mono_lo (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) {lo sa σ : Slot}
    (h : lo ≤ sa) :
    E.Aclass cfg ext v₀ n₀ b' sa σ ⊆ E.Aclass cfg ext v₀ n₀ b' lo σ := by
  classical
  simp only [Execution.Aclass]
  exact Finset.filter_subset_filter _
    (Finset.filter_subset_filter _ (span_committee_mono_lo h))

/-! ## `hJV` — supporter confinement -/

/-- **`hJV`** (VpreIdentities field 1). Supporter confinement: the honest window
`[lo, es]` supporters `Sval lo es` plus the V-span honest `Aval`/`Xval` at `sa`
partition `Jspec sa es`. The base honest support is anchor-invariant
(`Sval lo es = Sval sa es`, `Reanchor.Sval_anchor_invariant`), reducing the
identity to `weight_partition` at `[sa, es]`. `hslotcap` is the per-supporter
seat-cap store-dynamics fact (the L4 fold's `WellFormedExecution` discharge, the
shape `Sval_anchor_invariant` consumes). -/
theorem hJV_of_anchor (hhb : HonestBehavior cfg ext E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es sa : Slot}
    (hlo : lo ≤ sa)
    (hslotcap : ∀ i ∈ E.honest, E.SupportsDesc cfg ext v₀ n₀ b' es i →
      ∀ (t : Slot) (k : ℕ) (a : Attestation Root), t ≤ es →
        E.vote i t = some (k, a) →
        is_ancestor (E.store cfg ext v₀ n₀)
          (get_node_for_root a.data.beacon_block_root) (get_node_for_root b') = true →
        sa ≤ t) :
    E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' sa es
        + E.Xval cfg ext v₀ n₀ b' sa es
      = E.Jspec sa es := by
  rw [E.Sval_anchor_invariant cfg ext hhb hlo hslotcap]
  exact (E.weight_partition cfg ext v₀ n₀ b' sa es).symm

/-! ## `hXval` — the sibling-stuck window growth split -/

/-- **`hXval`** (VpreIdentities field 3). Sibling-stuck two-region split with the
pre-region weight taken as the `Xclass` window growth `Xclass lo es \ Xclass sa es`:
`Xval sa es + xpre = Xval lo es`. Pure `sdiff` algebra (`Xclass sa es ⊆ Xclass lo es`
at the fixed anchor `σ = es`). -/
theorem hXval_of_growth (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) {lo es sa : Slot}
    (hlo : lo ≤ sa) :
    E.Xval cfg ext v₀ n₀ b' sa es
        + E.weight (E.Xclass cfg ext v₀ n₀ b' lo es \ E.Xclass cfg ext v₀ n₀ b' sa es)
      = E.Xval cfg ext v₀ n₀ b' lo es := by
  simp only [Execution.Xval]
  exact E.weight_add_sdiff (E.Xclass_mono_lo cfg ext v₀ n₀ b' hlo)

/-! ## `hR4b` — the V-span byz partition -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Superadditivity into a common superset over disjoint parts (local copy of the
`HonestWeight`/`Discount` private helper). -/
theorem weight_add_le {A B C : Finset ValidatorIndex}
    (hdisj : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    E.weight A + E.weight B ≤ E.weight C := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAC hBC)
    (fun _ _ _ => Nat.zero_le _)

/-- **`hR4b`** (VpreIdentities field 4). V-span byz partition: the byzantine
supporters of `b` plus the V-span equivocation score are within the V-span enemy
weight `Bval sa es`. This is the disjoint-into-`Bwin` half of
`HonestWeight.byz_plus_equiv_le` (before `span_bound`): byz supporters are
non-equivocating (`AttSupporters` filter) and confined to `span_committee sa es`
(`hspan`, from `supporter_mem_span_committee`); active equivocators are
`hne`-non-honest span members; the two are disjoint, both inside `Bwin sa es`. -/
theorem hR4b_of_confinement (hec : ExternalsCoherence cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    {sa es : Slot}
    (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es ≤ E.Bval sa es := by
  rw [byz_score_eq_weight cfg hval,
    get_equivocation_score_eq_weight cfg ext hec hv n hnH hval sa es hesH]
  simp only [Execution.Bval, Execution.Bwin]
  refine E.weight_add_le ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨lm, _, hnoteq, _⟩ := mem_AttSupporters cfg hiBS.1
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnoteq hiEA.1.2
  · intro i hi
    simp only [List.mem_toFinset, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  · intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-! ## `hhead` — the head block-state slot bound -/

/-- **`hhead`** (`Remainder.hjc_le_of_store_epoch_bound`'s head-slot input). The
block-state slot of the store's current head is at most `s = slot_at n`:
`get_head` lands on a known block (`HeadStack.head_root_known`), whose block-state
slot equals its block slot (`Preservation.WellFormedStoreCore`, trajectory-level via
`store_wellFormedStore_core_plus`), which is at most the current slot
(`Delivery.store_blocks_slot_le_current`) `= s` (`store_current_slot`). -/
theorem hhead_of_wellFormed (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E) (hji : JustificationInterface cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n) {s : Slot} (hn : E.slot_at cfg n = s) :
    ((E.store cfg ext v n).block_states
        (get_head cfg (E.store cfg ext v n)).root).slot ≤ s := by
  obtain ⟨ast, ablk, hgeq, hslot, hpr⟩ := hgen
  have hknown : (get_head cfg (E.store cfg ext v n)).root ∈ (E.store cfg ext v n).block_roots :=
    E.head_root_known cfg ext hji hv n hnH
  have hcore := (E.store_wellFormedStore_core_plus cfg ext hwf hec
    ⟨ast, ablk, hgeq, hslot, hpr⟩ hwf.anchor_parent_unscheduled v n).1
  rw [hcore.2 _ hknown]
  refine le_trans
    (E.store_blocks_slot_le_current cfg ext hdiv ⟨ast, ablk, hgeq, hslot⟩ v n _ hknown)
    (le_of_eq ?_)
  rw [E.store_current_slot cfg ext v n, hn]

/-! ## `hcov` — the full-epoch coverage floor `total_active ≤ 2·Jspec` -/

/-- Pure-ℕ core of the coverage floor: with the honest/enemy split `J + B = W` and
the per-window `span_fraction` cap `100·B ≤ C·W` at `C ≤ 25`, the span weight is at
most twice the honest weight (`W ≤ 2·J`, i.e. `B ≤ J`). -/
private theorem cov_arith {W J B C : ℕ} (hsplit : J + B = W) (hfrac : 100 * B ≤ C * W)
    (hC : C ≤ 25) : W ≤ 2 * J := by
  have h25 : C * W ≤ 25 * W := by gcongr
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hcov`** (`Identities.hspan_of_coverage`'s coverage input). The saturated-span
honest-coverage floor `total_active ≤ 2·Jspec lo σ'`. The `span_fraction` half is
proved: `weight (span_committee) = Jspec + Bval` and `100·Bval ≤ C·weight` at
`C ≤ 25` give `weight ≤ 2·Jspec`. The active-coverage identity
`total_active ≤ weight (span_committee lo σ')` (a full epoch's committees cover the
active set, whose weight is `total_active`, above the `get_total_active_balance`
`max`-floor) is the **explicit tiny-`TAB` residual** `hcover`, taken as a hypothesis
(the same `committee_coverage` + registry-weight identification Section B of
`Identities` flags). -/
theorem hcov_of_coverage (hbb : ByzantineBound cfg E) {lo es : Slot}
    (hlo : lo ≤ es)
    (hcover : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.total_active cfg ≤ E.weight (E.span_committee lo σ')) :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.total_active cfg ≤ 2 * E.Jspec lo σ' := by
  intro σ' h1 h2 hσH
  refine le_trans (hcover σ' h1 h2 hσH) ?_
  have hsplit : E.Jspec lo σ' + E.Bval lo σ' = E.weight (E.span_committee lo σ') :=
    E.Jspec_add_Bval_eq_weight_span lo σ'
  have hfrac : 100 * E.Bval lo σ' ≤
      cfg.confirmation_byzantine_threshold * E.weight (E.span_committee lo σ') := by
    have hloH : E.SlotWithinHorizon cfg lo :=
      E.slotWithinHorizon_mono cfg (hlo.trans h1) hσH
    have h := hbb.span_fraction lo σ' hloH hσH
    simpa only [Execution.Bval, Execution.Bwin] using h
  exact cov_arith hsplit hfrac cfg.confirmation_byzantine_threshold_le

/-! ## `hJfull` — the two-region honest partition -/

/-- Pure-ℕ regrouping core of `hJfull` (`Gwei` atoms are opaque to inline `omega`;
extracted over plain `ℕ`). -/
private theorem jfull_arith {S As Xs P ap xp Al Xl : ℕ}
    (hA : As + (P + ap) = Al) (hX : Xs + xp = Xl) :
    S + As + Xs + (P + ap + xp) = S + Al + Xl := by omega

/-- **`hJfull`** (VpreIdentities field 2). The two-region honest window partition.
Given the honest `Aval`/`Xval` window-growth splits from the V-anchor `sa` to the
window anchor `lo` — with the parent-stuck honest slice `Hpar` carved out of the
`Aval` growth (`hAsplit : Aval sa es + (Hpar + apre) = Aval lo es`) and the
`Xval` growth `hXsplit : Xval sa es + xpre = Xval lo es` (`hXval_of_growth`) — the
identity is `weight_partition [lo, es]` plus pure-ℕ regrouping. `Hpar := weight
(ParentStuck …)`, `aV := Aval sa es`, `xV := Xval sa es`. -/
theorem hJfull_of_splits {v : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root}
    {lo es sa : Slot} {apre xpre : ℕ}
    (hAsplit : E.Aval cfg ext v n b sa es
        + (E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) + apre)
      = E.Aval cfg ext v n b lo es)
    (hXsplit : E.Xval cfg ext v n b sa es + xpre = E.Xval cfg ext v n b lo es) :
    E.Sval cfg ext v n b lo es + E.Aval cfg ext v n b sa es + E.Xval cfg ext v n b sa es
      + (E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) + apre + xpre)
    = E.Jspec lo es := by
  rw [E.weight_partition cfg ext v n b lo es]
  exact jfull_arith hAsplit hXsplit

/-- The `hAsplit` input of `hJfull_of_splits`, discharged from the honest bridge
subset `ParentStuck ⊆ Aclass lo es \ Aclass sa es` at `apre := weight ((Aclass lo es
\ Aclass sa es) \ ParentStuck)`. Two `sdiff` steps: `Hpar + apre = weight (Aclass lo
es \ Aclass sa es)` (`hPS`), and `Aval sa es + that = Aval lo es` (`Aclass_mono_lo`).
`hPS` is the parent-stuck honest slice residual: a parent-stuck honest validator
(recorded `lm.root = parent(b')`, newest by the honest recorded↔ground bridge) is
`AncestorOrVoteless` (its vote block `= parent(b') ⪯ b'`) and `¬ SupportsDesc`, hence
in `Aclass lo es`, and its seat `< sa` keeps it out of `Aclass sa es`. -/
theorem hAsplit_of_bridge {v : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root}
    {lo es sa : Slot} (hlo : lo ≤ sa)
    (hPS : ParentStuck cfg E (E.store cfg ext v n) bs b
      ⊆ E.Aclass cfg ext v n b lo es \ E.Aclass cfg ext v n b sa es) :
    E.Aval cfg ext v n b sa es
        + (E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b)
          + E.weight ((E.Aclass cfg ext v n b lo es \ E.Aclass cfg ext v n b sa es)
            \ ParentStuck cfg E (E.store cfg ext v n) bs b))
      = E.Aval cfg ext v n b lo es := by
  rw [E.weight_add_sdiff hPS]
  simp only [Execution.Aval]
  exact E.weight_add_sdiff (E.Aclass_mono_lo cfg ext v n b hlo)

/-! ## `hBbadfin` — the full-window byz partition -/

/-- **`hBbadfin`** (VpreIdentities field 5). The full-window byz partition: the base
recorded enemy `BbadVal`, the byz supporters of `b`, the V-span equivocation score,
and the byz parent-stuck weight are four pairwise-disjoint subsets of the window
enemy set `Bwin lo es`, so their weights sum to at most `Bval lo es`
(`EngineWindows.weight_add4_le`). The subset/disjointness facts are taken as clean
`Finset` inputs (the shape `EngineWindows`/`EngineWindows` scope them). The two byz-supporter
disjointness pairs (`d1` vs `BbadSet`, `d5` vs `ParentStuckByz`) are the recorded
`get_supported_node`-geometry residuals; the equiv-based pairs (`d2`/`d4`/`d6`) and
the `BbadSet`-vs-parent pair (`d3`, via `parent(b') ⪯ b'`) are the clean ones. -/
theorem hBbadfin_of_partition (hec : ExternalsCoherence cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry) {lo es sa : Slot}
    (hesH : E.SlotWithinHorizon cfg es)
    (hBB : E.BbadSet cfg ext v n b lo es ⊆ E.Bwin lo es)
    (hBS : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset) ⊆ E.Bwin lo es)
    (hEA : EquivActive cfg E (E.store cfg ext v n) bs sa es ⊆ E.Bwin lo es)
    (hPB : ParentStuckByz cfg E (E.store cfg ext v n) bs b ⊆ E.Bwin lo es)
    (d1 : Disjoint (E.BbadSet cfg ext v n b lo es)
      (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset))
    (d2 : Disjoint (E.BbadSet cfg ext v n b lo es)
      (EquivActive cfg E (E.store cfg ext v n) bs sa es))
    (d3 : Disjoint (E.BbadSet cfg ext v n b lo es)
      (ParentStuckByz cfg E (E.store cfg ext v n) bs b))
    (d4 : Disjoint (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset)
      (EquivActive cfg E (E.store cfg ext v n) bs sa es))
    (d5 : Disjoint (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset)
      (ParentStuckByz cfg E (E.store cfg ext v n) bs b))
    (d6 : Disjoint (EquivActive cfg E (E.store cfg ext v n) bs sa es)
      (ParentStuckByz cfg E (E.store cfg ext v n) bs b)) :
    E.BbadVal cfg ext v n b lo es
      + (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es
      + E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b) ≤ E.Bval lo es := by
  rw [byz_score_eq_weight cfg hval,
    get_equivocation_score_eq_weight cfg ext hec hv n hnH hval sa es hesH]
  simp only [Execution.BbadVal, Execution.Bval]
  exact weight_add4_le d1 d2 d3 d4 d5 d6 hBB hBS hEA hPB

/-! ## The composed `VpreIdentities` producer

Assembling the five field lemmas at the uniform `σ = es` anchor with the natural
class-weight choices `aV := Aval sa es`, `xV := Xval sa es`, `apre :=` the
`Aclass`-growth remainder after the parent-stuck slice, `xpre :=` the `Xclass`
growth. Feeds `Identities.INV2_base_bridged_instantiated` directly. The residual
inputs are: `hslotcap` (the store-dynamics seat-cap, the L4 fold's
`WellFormedExecution` discharge), `hne` (`HonestWeight.honest_not_equivocating`),
`hspan` (`QuorumAccounting.supporter_mem_span_committee`), `hPS` (the parent-stuck
honest slice — the honest recorded↔ground bridge residual), and the byz-partition
subset/disjointness facts (the recorded `get_supported_node`-geometry residuals). -/

/-- **The full `VpreIdentities`** (`LastAlgebra`), at the uniform-`σ = es` anchor. -/
theorem vpreIdentities_of (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    {lo es sa : Slot} (hlo : lo ≤ sa)
    (hesH : E.SlotWithinHorizon cfg es)
    (hslotcap : ∀ i ∈ E.honest, E.SupportsDesc cfg ext v n b es i →
      ∀ (t : Slot) (k : ℕ) (a : Attestation Root), t ≤ es →
        E.vote i t = some (k, a) →
        is_ancestor (E.store cfg ext v n)
          (get_node_for_root a.data.beacon_block_root) (get_node_for_root b) = true →
        sa ≤ t)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es)
    (hPS : ParentStuck cfg E (E.store cfg ext v n) bs b
      ⊆ E.Aclass cfg ext v n b lo es \ E.Aclass cfg ext v n b sa es)
    (hBB : E.BbadSet cfg ext v n b lo es ⊆ E.Bwin lo es)
    (hBS : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset) ⊆ E.Bwin lo es)
    (hEA : EquivActive cfg E (E.store cfg ext v n) bs sa es ⊆ E.Bwin lo es)
    (hPB : ParentStuckByz cfg E (E.store cfg ext v n) bs b ⊆ E.Bwin lo es)
    (d1 : Disjoint (E.BbadSet cfg ext v n b lo es)
      (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset))
    (d2 : Disjoint (E.BbadSet cfg ext v n b lo es)
      (EquivActive cfg E (E.store cfg ext v n) bs sa es))
    (d3 : Disjoint (E.BbadSet cfg ext v n b lo es)
      (ParentStuckByz cfg E (E.store cfg ext v n) bs b))
    (d4 : Disjoint (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset)
      (EquivActive cfg E (E.store cfg ext v n) bs sa es))
    (d5 : Disjoint (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset)
      (ParentStuckByz cfg E (E.store cfg ext v n) bs b))
    (d6 : Disjoint (EquivActive cfg E (E.store cfg ext v n) bs sa es)
      (ParentStuckByz cfg E (E.store cfg ext v n) bs b)) :
    VpreIdentities E cfg ext v n bs b lo es sa
      (E.Aval cfg ext v n b sa es) (E.Xval cfg ext v n b sa es)
      (E.weight ((E.Aclass cfg ext v n b lo es \ E.Aclass cfg ext v n b sa es)
        \ ParentStuck cfg E (E.store cfg ext v n) bs b))
      (E.weight (E.Xclass cfg ext v n b lo es \ E.Xclass cfg ext v n b sa es)) where
  hJV := E.hJV_of_anchor cfg ext hhb hlo hslotcap
  hJfull := E.hJfull_of_splits cfg ext (E.hAsplit_of_bridge cfg ext hlo hPS)
    (E.hXval_of_growth cfg ext v n b hlo)
  hXval := E.hXval_of_growth cfg ext v n b hlo
  hR4b := E.hR4b_of_confinement cfg ext hec hv hnH hval hne hesH hspan
  hBbadfin := E.hBbadfin_of_partition cfg ext hec hv hnH hval hesH
    hBB hBS hEA hPB d1 d2 d3 d4 d5 d6

/-! ## `hsat` — the saturated-majority composition

The post-`T1` saturation crux `hsat` (every honest window member re-votes
`desc(b')` two epochs past `es`) is a store-dynamics fact — `committee_coverage`
gives each honest active validator an assignment in the elapsed epoch, `votes_head`
+ the engine IH make that vote `desc(b')`, and it lands by `vote_ubiquity` — and is
**not** algebra; it stays the enumerated dynamics residual. This module closes the
*rest*: given the crux, the full saturated-majority field `x(σ') + ⌊C·J/(100−C)⌋ +
boost + 1 ≤ s(σ')` follows, with the `Jspec` lower bound discharged entirely by the
coverage floor (`hcov_of_coverage`) + `Identities.hspan_of_coverage` + the
nondegeneracy `hnondeg`. So the two explicit residuals — `hsat` and the coverage
identity `hcover` — are the *only* inputs to the saturated majority. -/

/-- **The saturated honest-majority field from the crux + coverage** (`LastAlgebra` item 4).
Composes `IHMechanize.hmaj_of_saturation` (via `VoteLanding.hmaj_of_saturation_lb`)
with the coverage-floor `Jspec` lower bound (`hspan_of_coverage ∘ hcov_of_coverage`).
`hsat` is the store-dynamics saturation crux (the enumerated residual); `hnondeg`
the tiny-`TAB` exclusion; `hcover` the active-coverage weight identity. -/
theorem saturated_majority_of_crux (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} {n : ℕ} {b : Root} {lo es : Slot} (boost : ℕ)
    (hlo : lo ≤ es)
    (hsat : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      ∀ i ∈ (E.span_committee lo σ').filter (fun i => i ∈ E.honest),
        E.SupportsDesc cfg ext v n b σ' i)
    (hnondeg : 4 * (boost + 1) ≤ E.total_active cfg)
    (hcover : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.total_active cfg ≤ E.weight (E.span_committee lo σ')) :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext v n b lo σ'
          + cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
              / (100 - cfg.confirmation_byzantine_threshold)
          + boost + 1 ≤ E.Sval cfg ext v n b lo σ' :=
  E.hmaj_of_saturation_lb cfg ext v n b lo es boost hsat
    (hspan_of_coverage E cfg lo es boost hnondeg
      (E.hcov_of_coverage cfg hbb hlo hcover))

end Execution

end FastConfirmation.Spec
