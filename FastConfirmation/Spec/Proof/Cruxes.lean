import FastConfirmation.Spec.Proof.LastAlgebra
import FastConfirmation.Spec.Proof.Bridge
import FastConfirmation.Spec.Proof.AnchorFacade
import FastConfirmation.Spec.Proof.ExportWiring

/-!
# Spec / Proof / Cruxes: store-dynamics lemmas

`LastCruxes` reduces `Spec_Safety` to `SameSlotFinalizedRootKnown` and
`EngineGroundResiduals`. This module proves four **store-dynamics** conditions that
`LastAlgebra` and `IHMechanize` consume as named hypotheses from the model and
`SpecAssumptions`:

* **Crux 3 — `hcov`** (`hcov_crux`): the full-epoch honest-coverage floor
  `total_active ≤ weight (span_committee lo σ')` on a span two epochs past `es`. Every
  active validator has a committee seat in epoch `CE(es)+1` (`committee_coverage`), and
  that seat lands in `[lo, σ']` (the epoch bounds), so the anchor's active set embeds in
  the span; `weight_mono` weighs the inclusion. The `get_total_active_balance` `max`-floor
  is the explicit tiny-`TAB` residual `hfloor` (active weight `≥ EFFECTIVE_BALANCE_INCREMENT`).
  Feeds `LastAlgebra.hcov_of_coverage`'s `hcover` input.

* **Crux 4 — `hsat`** (`hsat_crux`): the post-`T1` saturation crux — every honest window
  member `SupportsDesc b'` at `σ'`. The member is active (`committee_members_active`), so it
  has a seat in epoch `CE(es)+1` (`committee_coverage`) and votes there (`votes_head`); its
  newest vote through `σ'` (a `Nat.findGreatest` argument) sits in `(es, σ']`, and the engine
  IH clause `hIH` makes that vote's block descend from `b'` — so `SupportsDesc`. Feeds
  `LastAlgebra.saturated_majority_of_crux`'s `hsat`.

* **Crux 6 — `hrec`** (`hrec_crux`): every `Sclass` member records a `c`-supporting latest
  message at the endpoint `(w, m)`. Instantiates `IHMechanize.hrec_of_domain`, discharging its
  walk-domain premise `hwalk_wm` from `AnchorFacade.store_walkKnownK` (the recorded-root
  knownness input `hlm_known`), leaving the genuine per-endpoint residuals as inputs.

* **Crux 2 — `hPS`** (`hPS_crux`): the parent-stuck honest slice
  `ParentStuck ⊆ Aclass lo es \ Aclass sa es`. `Bridge.ParentStuck_subset_Aclass` gives the
  `⊆ Aclass lo es` half; the `sa`-slice exclusion is `votes_assigned` +
  `committee_assignment_unique` on the pre-region seat (`< b'.slot ≤ sa`) under the
  single-epoch window `hepoch` (the confinement flag). Feeds `LastAlgebra.hAsplit_of_bridge`.

The remaining explicit inputs are the active-balance floor `hfloor` and the single-epoch
window condition `hepoch`; the engine induction hypothesis is threaded as `hIH`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `compute_epoch_at_slot` is monotone (folded form, so `omega` sees the epochs as
consistent atoms — a bare `Nat.div_le_div_right` unfolds them). -/
theorem ce_mono {a b : Slot} (h : a ≤ b) :
    compute_epoch_at_slot cfg a ≤ compute_epoch_at_slot cfg b :=
  Nat.div_le_div_right h

namespace Execution

variable (E : Execution Root)

/-! ## Crux 3 — `hcov`: the full-epoch honest-coverage floor -/

/-- **`hcov`** (`LastAlgebra.hcov_of_coverage`'s `hcover` input). For a span end `σ'` at
least two epochs past `es`, the anchor's total active balance is at most the span-committee
weight `weight (span_committee lo σ')`.

*Proof.* Epoch `e := CE(es)+1` sits strictly between `CE(es)` and `CE(σ')` (two epochs
apart), so every validator active at the anchor epoch — active at `e` by
`registry_activity_constant` — has, by `committee_coverage`, a seat `s` with `CE(s) = e`,
hence `es < s < σ'` and `lo ≤ es < s`, placing `s ∈ [lo, σ']` and the validator in
`span_committee lo σ'`. The anchor active-index set thus embeds in the span; `weight_mono`
weighs it. The `get_total_active_balance` `max`-floor is absorbed by the explicit
nondegeneracy `hfloor` (`total_active ≤ weight (active set)`, i.e. the active weight meets
`EFFECTIVE_BALANCE_INCREMENT` — the tiny-`TAB` exclusion). -/
theorem hcov_crux (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    {lo es : Slot} (hlo : lo ≤ es)
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : E.total_active cfg ≤
      E.weight (get_active_validator_indices E.anchor_state
        (get_current_epoch cfg E.anchor_state)).toFinset) :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.total_active cfg ≤ E.weight (E.span_committee lo σ') := by
  intro σ' _hσ h2 hσH
  refine le_trans hfloor (E.weight_mono ?_)
  intro i hi
  rw [List.mem_toFinset, get_active_validator_indices, List.mem_filter, List.mem_range] at hi
  obtain ⟨_hlt, hact⟩ := hi
  have heH : compute_epoch_at_slot cfg es + 1 < E.verification_horizon := by
    exact (lt_of_lt_of_le (Nat.lt_succ_self _) h2).trans hσH.2
  have hact' : is_active_validator (E.registry.getD i default)
      (compute_epoch_at_slot cfg es + 1) = true := by
    rw [hsv.registry_activity_constant i (compute_epoch_at_slot cfg es + 1)
      (get_current_epoch cfg E.anchor_state) heH hanchorH]
    exact hact
  obtain ⟨s, _hsH, hse, hsi⟩ :=
    hec.committee_coverage i (compute_epoch_at_slot cfg es + 1) heH hact'
  have hes_lt_s : es < s := by
    by_contra hcon
    have hmono : compute_epoch_at_slot cfg s ≤ compute_epoch_at_slot cfg es :=
      ce_mono cfg (not_lt.mp hcon)
    rw [hse] at hmono
    exact Nat.lt_irrefl _ (Nat.lt_of_succ_le hmono)
  have hs_lt_σ : s < σ' := by
    by_contra hcon
    have hmono : compute_epoch_at_slot cfg σ' ≤ compute_epoch_at_slot cfg s :=
      ce_mono cfg (not_lt.mp hcon)
    rw [hse] at hmono
    exact Nat.lt_irrefl _ (Nat.lt_of_succ_le (Nat.le_trans h2 hmono))
  simp only [Execution.span_committee, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_Icc.mpr ⟨le_trans hlo (le_of_lt hes_lt_s), le_of_lt hs_lt_σ⟩, hsi⟩

/-! ## Crux 4 — `hsat`: the post-`T1` saturation crux -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **Newest vote through `σ'`.** Given a vote at some slot `s ≤ σ'`, there is a *newest*
vote slot `t ∈ [s, σ']` (a vote at `t`, none after `t` through `σ'`). A `Nat.findGreatest`
argument over the decidable predicate `(E.vote i ·).isSome`. -/
theorem exists_newest_vote {i : ValidatorIndex} {s σ' : Slot} (hs : s ≤ σ')
    (hvs : (E.vote i s).isSome = true) :
    ∃ t : Slot, s ≤ t ∧ t ≤ σ' ∧ (E.vote i t).isSome = true ∧
      (∀ t' : Slot, t < t' → t' ≤ σ' → E.vote i t' = none) := by
  classical
  refine ⟨Nat.findGreatest (fun u => (E.vote i u).isSome = true) σ', ?_, ?_, ?_, ?_⟩
  · exact Nat.le_findGreatest (P := fun u => (E.vote i u).isSome = true) hs hvs
  · exact Nat.findGreatest_le _
  · exact Nat.findGreatest_spec (P := fun u => (E.vote i u).isSome = true) hs hvs
  · intro t' hlt hle
    have hng := Nat.findGreatest_is_greatest (P := fun u => (E.vote i u).isSome = true) hlt hle
    cases hvt : E.vote i t' with
    | none => rfl
    | some x => exact absurd (show (E.vote i t').isSome = true by rw [hvt]; rfl) hng

/-- **`hsat`** (`LastAlgebra.saturated_majority_of_crux`'s `hsat` input). Two epochs past
`es`, every honest member of the window `span_committee lo σ'` supports `desc(b)` at `σ'`.

*Proof.* The member `i` is active (`committee_members_active` on any of its seats), so it has
a seat `s` in epoch `CE(es)+1` (`committee_coverage`, `registry_activity_constant`), with
`es < s < σ'` (the epoch bounds) and `slot_at 0 ≤ s` (from `hs0`); `votes_head` gives it a
vote at `s`. Its newest vote `t` through `σ'` (`exists_newest_vote`) then lies in `(es, σ']`,
and the engine IH clause `hIH` makes that vote's block descend from `b` at the endpoint store
— exactly `SupportsDesc`. `hIH` is the shell's head-safety IH threaded as everywhere; the
rest is `committee_coverage` + `votes_head`. -/
theorem hsat_crux (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    {v : ValidatorIndex} {n : ℕ} {b : Root} {lo es : Slot}
    (hs0 : E.slot_at cfg 0 ≤ es)
    (hIH : ∀ j ∈ E.honest, ∀ t : Slot, es < t → ∀ (k : ℕ) (a : Attestation Root),
      E.vote j t = some (k, a) →
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root a.data.beacon_block_root) (get_node_for_root b) = true) :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      ∀ i ∈ (E.span_committee lo σ').filter (fun i => i ∈ E.honest),
        E.SupportsDesc cfg ext v n b σ' i := by
  intro σ' _hσ h2 hσH i hi_mem
  rw [Finset.mem_filter] at hi_mem
  obtain ⟨hi_span, hih⟩ := hi_mem
  simp only [Execution.span_committee, Finset.mem_biUnion] at hi_span
  obtain ⟨t₀, ht0, hi_t0⟩ := hi_span
  have ht0_bounds : lo ≤ t₀ ∧ t₀ ≤ σ' := Finset.mem_Icc.mp ht0
  have ht0H : E.SlotWithinHorizon cfg t₀ :=
    ⟨le_trans ht0_bounds.2 hσH.1,
      lt_of_le_of_lt (Nat.div_le_div_right ht0_bounds.2) hσH.2⟩
  have heH : compute_epoch_at_slot cfg es + 1 < E.verification_horizon := by
    exact (lt_of_lt_of_le (Nat.lt_succ_self _) h2).trans hσH.2
  have hact' : is_active_validator (E.registry.getD i default)
      (compute_epoch_at_slot cfg es + 1) = true := by
    rw [hsv.registry_activity_constant i (compute_epoch_at_slot cfg es + 1)
      (compute_epoch_at_slot cfg t₀) heH ht0H.2]
    exact hec.committee_members_active i t₀ ht0H hi_t0
  obtain ⟨s, hsH, hse, hsi⟩ :=
    hec.committee_coverage i (compute_epoch_at_slot cfg es + 1) heH hact'
  have hes_lt_s : es < s := by
    by_contra hcon
    have hmono : compute_epoch_at_slot cfg s ≤ compute_epoch_at_slot cfg es :=
      ce_mono cfg (not_lt.mp hcon)
    rw [hse] at hmono
    exact Nat.lt_irrefl _ (Nat.lt_of_succ_le hmono)
  have hs_lt_σ : s < σ' := by
    by_contra hcon
    have hmono : compute_epoch_at_slot cfg σ' ≤ compute_epoch_at_slot cfg s :=
      ce_mono cfg (not_lt.mp hcon)
    rw [hse] at hmono
    exact Nat.lt_irrefl _ (Nat.lt_of_succ_le (Nat.le_trans h2 hmono))
  have hs0s : E.slot_at cfg 0 ≤ s := le_of_lt (lt_of_le_of_lt hs0 hes_lt_s)
  obtain ⟨n', index, _hnH, _hn', hvote_s⟩ := hhb.votes_head i hih s hsi hsH hs0s
  have hvs : (E.vote i s).isSome = true := by rw [hvote_s]; rfl
  obtain ⟨t, hst, htσ, hvt, hnewest⟩ := E.exists_newest_vote (le_of_lt hs_lt_σ) hvs
  obtain ⟨⟨k, a⟩, hva⟩ := Option.isSome_iff_exists.mp hvt
  have hes_lt_t : es < t := lt_of_lt_of_le hes_lt_s hst
  refine ⟨t, k, a, htσ, hva, ?_, hIH i hih t hes_lt_t k a hva⟩
  intro t' hlt hle
  exact hnewest t' hlt hle

/-! ## Crux 6 — `hrec`: every `Sclass` member records a `c`-supporting message -/

/-- **`hrec`** (`EdgeDynamics.EdgeInputResidual.hrec`). Every `Sclass w m b lo σ` member records
a `c`-supporting latest message at the endpoint `(w, m)`.

This instantiates `IHMechanize.hrec_of_domain`, additionally discharging its walk-domain premise
`hwalk_wm` from `AnchorFacade.store_walkKnownK` (the target `c` and the recorded root `lm.root`
are both known — `hc_wm`, `hlm_known` — so the walk from `lm.root` to `(blocks c).slot` stays
known). The genuine per-endpoint residuals stay as inputs: the engine IH `hIH`, the ubiquity
landing `hubiq`, the vote-block knownness `hbbr_known`, the recorded-root knownness `hlm_known`,
and the endpoint knownness/edge facts `hb_wm`/`hc_wm`/`hbc_wm`. -/
theorem hrec_crux (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b c : Root} {lo σ : Slot} (hw : w ∈ E.honest)
    (hb_wm : b ∈ (E.store cfg ext w m).block_roots)
    (hc_wm : c ∈ (E.store cfg ext w m).block_roots)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hIH : ∀ j ∈ E.honest, ∀ t' : Slot, σ + 1 ≤ t' → t' < E.slot_at cfg m →
      ∀ jj (a' : Attestation Root), E.vote j t' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hubiq : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) →
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        compute_epoch_at_slot cfg t ≤ lm.epoch)
    (hbbr_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) → a.data.beacon_block_root ∈ (E.store cfg ext w m).block_roots)
    (hlm_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ lm,
      (E.store cfg ext w m).latest_messages i = some lm →
      lm.root ∈ (E.store cfg ext w m).block_roots) :
    ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true := by
  obtain ⟨hgen, hwf, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  refine E.hrec_of_domain cfg ext ⟨hgen, hwf, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
    hw hb_wm hc_wm hbc_wm hIH hubiq hbbr_known ?_
  intro i hi lm hlm
  exact E.store_walkKnownK cfg ext hwf hec hgen w m c hc_wm lm.root (hlm_known i hi lm hlm)

/-! ## Crux 2 — `hPS`: the parent-stuck honest slice `⊆ Aclass lo es \ Aclass sa es` -/

/-- **`hPS`** (`LastAlgebra.hAsplit_of_bridge`'s input). The parent-stuck honest slice sits
in the `Aclass` window-growth `Aclass lo es \ Aclass sa es`.

The `⊆ Aclass lo es` half is `Bridge.ParentStuck_subset_Aclass`. For the `\ Aclass sa es`
exclusion: a parent-stuck member has a committee seat `t₀` in the pre-region `[lo, b.slot−1]`
(`mem_ParentSupport`), strictly below `b.slot ≤ sa`; were it also in `span_committee sa es`
(a seat `s' ∈ [sa, es]`), `committee_assignment_unique` — under the single-epoch window
`hepoch : CE(lo) = CE(es)`, which pins `CE(t₀) = CE(s')` — would force `t₀ = s'`, contradicting
`t₀ < sa ≤ s'`. So the member is not in `span_committee sa es`, hence not in `Aclass sa es`.
`hepoch` is the explicit single-epoch confinement (the confirmation window fits one epoch);
`hsa : b.slot ≤ sa` places the V-region above the block. -/
theorem hPS_crux (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} {lo es sa : Slot}
    (hlo : lo = ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hb'cur : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n))
    (hb'anc : is_ancestor (E.store cfg ext v n) (get_node_for_root b)
      (get_node_for_root ((E.store cfg ext v n).blocks b).parent_root) = true)
    (hdom : E.RecordedEpochMax cfg ext v n es)
    (hlosa : lo ≤ sa) (hsa : ((E.store cfg ext v n).blocks b).slot ≤ sa)
    (hepoch : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg es) :
    ParentStuck cfg E (E.store cfg ext v n) bs b
      ⊆ E.Aclass cfg ext v n b lo es \ E.Aclass cfg ext v n b sa es := by
  intro i hi
  rw [Finset.mem_sdiff]
  refine ⟨E.ParentStuck_subset_Aclass cfg ext hhb hec hgen hprov hlo hes hslotlt hb'cur hb'anc
    hdom hi, ?_⟩
  -- the pre-region seat `t₀`
  have hi' := hi
  simp only [ParentStuck, Finset.mem_filter] at hi'
  obtain ⟨hPSmem, _hih⟩ := hi'
  have hps_span := (mem_ParentSupport cfg hPSmem).1
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hps_span
  obtain ⟨t₀, ⟨ht0_lb, ht0_ub⟩, hi_t0⟩ := hps_span
  have hlo_t0 : lo ≤ t₀ := by rw [hlo]; exact ht0_lb
  have ht0_es : t₀ ≤ es := by
    rw [hes]; exact Nat.le_trans ht0_ub (Nat.sub_le_sub_right hb'cur 1)
  -- suppose it is also in `Aclass sa es`
  intro hiA
  simp only [Execution.Aclass, Finset.mem_filter] at hiA
  obtain ⟨⟨hi_span_sa, _⟩, _⟩ := hiA
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hi_span_sa
  obtain ⟨s', ⟨hs'_lb, hs'_ub⟩, hi_s'⟩ := hi_span_sa
  have hlo_s' : lo ≤ s' := le_trans hlosa hs'_lb
  have hbpos : 0 < ((E.store cfg ext v n).blocks b).slot :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hslotlt
  have ht0_lt_s' : t₀ < s' :=
    Nat.lt_of_le_of_lt ht0_ub
      (Nat.lt_of_lt_of_le (Nat.sub_lt hbpos Nat.one_pos) (le_trans hsa hs'_lb))
  -- both seats are in the same epoch (single-epoch window)
  have het0 : compute_epoch_at_slot cfg t₀ = compute_epoch_at_slot cfg s' :=
    le_antisymm
      (le_trans (ce_mono cfg ht0_es) (hepoch ▸ ce_mono cfg hlo_s'))
      (le_trans (ce_mono cfg hs'_ub) (hepoch ▸ ce_mono cfg hlo_t0))
  exact absurd (hec.committee_assignment_unique i t₀ s' hi_t0 hi_s' het0)
    (Nat.ne_of_lt ht0_lt_s')

end Execution

end FastConfirmation.Spec
