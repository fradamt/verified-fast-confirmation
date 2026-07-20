import FastConfirmation.Spec.Proof.ExportWiring
import FastConfirmation.Spec.Proof.HonestWeight

/-!
# Spec / Proof / EconomicCore: the economic-core closure

This module packages the economic inputs used by the proof decomposition.
This packages the inputs for `fork_edges`
(`ForkAssembly.ForkEdgeSupply` / `EdgeDynamics.EdgeInputResidual`). It **composes** the
bridges from `Confinement`, `ByzVpre`, `HonestWeight`, `Discount`,
`DynamicsClosure`, `IHMechanize`, `VoteLanding`, `HeadStack`, `ExportWiring` — into the
per-endpoint reductions consumed by the economic fields.

## Section 1 — `hbase`: the Arms accounting completion

`DynamicsClosure.INV2_base_of_confirmed` reduces `INV2(es)` to `Arms.arms_of_confirmed`'s
thirteen abstract atoms plus four Arms↔Ledger accessor identities. `INV2_base_bridged`
**discharges every proved atom bridge** — the adversarial-weight bounds
`hAhi`/`hAlo` (`Confinement.get_adversarial_weight_le_qV` / `qV_le_get_adversarial_add_eqV`),
the discount bound `hd` (`Confinement.hd_of_confirmed`), the honest-score bound `hS`
(`Confinement.hS_of_confirmed`), the byz-supporter bound `hBsup`
(`HonestWeight.byz_score_le_adversarial_weight`), and the two estimate-domination bounds
`hR8aW`/`hR8cW` (`ByzVpre.hR8aW_of_identities` / `hR8cW_of_identities`) — leaving as its sole
inputs the genuine **V/pre class-decomposition identities** (`ByzVpre`'s enumerated residue):
the window/V-region honest partitions (`hJfull`/`hJV`), the enemy identities
(`hBfull`/`hBV`), the byz-partition inequalities (`hR4b`/`hBbadfin`), and the two `Ledger`
accessor identities (`hXval`/`hBbadVal`). These inputs are collected here.

## Section 2 — the migration Finset algebra (`hSmono`/`hXmono`/`hsat`), reduced

The `IHMechanize`/`VoteLanding` reductions (`hdeltas_sameEpoch`, `hmaj_of_saturation_lb`)
close the pre-`T1` deltas and the post-`T1` majority **down to** the per-slot honest-support
growth `hSmono`, the sibling-stuck antitonicity `hXmono`, the saturation support crux `hsat`,
and the saturated committee-weight floor `hspan`. Those four are the genuine store-dynamics
content — the `Sclass`/`Xclass` Finset set-inclusion over the closed vote-landing bundle
(`ExportWiring.vote_ubiquity_export_closed`, whose only carried input is the epoch ordering
`hjc_le`). This section records the composed reductions and the exact set-inclusion cruxes.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hbase`: the Arms accounting completion

`INV2_base_bridged` composes every committed atom bridge into
`DynamicsClosure.INV2_base_of_confirmed`. The atom choices are the natural spec
quantities at the confirming store `(v, n)` / balance source `bs`:

* `s0 := Sval(lo, es)` (honest supporter weight), `Bsup :=` the byz-supporter list
  sum, `Hpar := weight(ParentStuck)`, `Bpar := weight(ParentStuckByz)`;
* `qV := estimate(advSpan)//100`, `eqV := get_equivocation_score(advSpan)` on the
  adversarial span `[sa, es]` (`sa` = the `get_adversarial_weight` start);
* `aV`/`xV`/`apre`/`xpre`/`B_V`/`B0`/`Bbad` are the V/pre class-decomposition atoms.

The seven atom-bridge hypotheses of `arms_of_confirmed` are discharged inline
(`Confinement.hAhi/hAlo/hd/hS`, `HonestWeight.hBsup`, `ByzVpre.hR8aW/hR8cW`); the
remaining inputs are exactly the **V/pre accounting identities** `ByzVpre` enumerated
as its residue (`hJV`/`hBV`/`hJfull`/`hBfull`/`hR4b`/`hBbadfin`/`hXval`/`hBbadVal`). -/

/-- **`INV2(es)` from a confirmed instance, bridges composed** (`EconomicCore`, item 1/`hbase`).
Every `Arms.arms_of_confirmed` atom bridge is discharged from the cited lemmas; the
only inputs are the per-store coherence package and the V/pre class-decomposition
identities. `es = current − 1`, `lo = parent(b).slot + 1`, `sa =` the adversarial-span
start — supplied definitionally (`hes`/`hlo`/`hsa`, `subst`-ed). -/
theorem INV2_base_bridged
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈ (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} {lo es sa : Slot}
    {aV xV apre xpre B_V B0 Bbad : ℕ}
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hlo : lo = ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hsa : sa =
      (if get_block_epoch cfg (E.store cfg ext v n) b >
          get_block_epoch cfg (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).parent_root
        then compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
        else ((E.store cfg ext v n).blocks b).slot))
    (hloH : E.SlotWithinHorizon cfg lo)
    (hesH : E.SlotWithinHorizon cfg es)
    (hsaH : E.SlotWithinHorizon cfg sa)
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root)
    (hdom : E.RecordedEpochMax cfg ext v n es)
    (hJV : E.Sval cfg ext v n b lo es + aV + xV = E.Jspec sa es)
    (hBV : B_V = E.Bval sa es)
    (hJfull : E.Sval cfg ext v n b lo es + aV + xV
        + (E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) + apre + xpre)
      = E.Jspec lo es)
    (hBfull : B0 = E.Bval lo es)
    (hR4b : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
        + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es ≤ B_V)
    (hBbadfin : Bbad
        + (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
            (fun i => i ∉ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum
        + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es
        + E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b) ≤ B0)
    (hXval : xV + xpre = E.Xval cfg ext v n b lo es)
    (hBbadVal : Bbad = E.BbadVal cfg ext v n b lo es) :
    E.INV2 cfg ext v n b lo es es (compute_proposer_score cfg bs) := by
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest :=
    fun i hi hih => Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n hi
  subst hlo hes hsa
  set sa : Slot :=
    (if get_block_epoch cfg (E.store cfg ext v n) b >
        get_block_epoch cfg (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).parent_root
      then compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
      else ((E.store cfg ext v n).blocks b).slot) with hsadef
  refine E.INV2_base_of_confirmed cfg ext hbb hconf v n _ _ (compute_proposer_score cfg bs)
    (s0 := E.Sval cfg ext v n b
      (((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
      (get_current_slot cfg (E.store cfg ext v n) - 1)) (aV := aV) (xV := xV)
    (Hpar := E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b))
    (apre := apre) (xpre := xpre) (B_V := B_V) (B0 := B0)
    (Bsup := (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map
      (fun i => (bs.validators.getD i default).effective_balance)).sum)
    (eqV := get_equivocation_score cfg ext (E.store cfg ext v n) bs sa
      (get_current_slot cfg (E.store cfg ext v n) - 1))
    (Bpar := E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b))
    (Bbad := Bbad)
    (qV := estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) sa
      (get_current_slot cfg (E.store cfg ext v n) - 1) / 100)
    (by simpa only using hloH) (by simpa only using hesH)
    rfl ?_ ?_ ?_ ?_ ?_ hR4b ?_ ?_ hBbadfin rfl hXval hBbadVal hJfull
  · exact E.hS_of_confirmed cfg ext hhb hec hgen hwf hprov hval rfl rfl hslotlt hwalk hdom
  · exact E.hd_of_confirmed cfg ext hec hbb hv hnH hval
      (by simpa only using hloH) hbH htab hne
  · exact get_adversarial_weight_le_qV cfg ext
  · exact qV_le_get_adversarial_add_eqV cfg ext
  · exact byz_score_le_adversarial_weight cfg ext hhb hec hbb hgen hv hnH hwf hbH
      hval htab hprov hwalk
  · exact E.hR8aW_of_identities cfg hbb htab sa
      (get_current_slot cfg (E.store cfg ext v n) - 1)
      (by simpa only using hsaH) (by simpa only using hesH) hJV hBV
  · exact E.hR8cW_of_identities cfg hbb htab
      (by simpa only using hloH) (by simpa only using hesH) hJfull hBfull

/-! ## Section 2 — the migration Finset algebra (`hSmono`/`hXmono`)

The pre-`T1` per-slot deltas of `IHMechanize.hdeltas_of_monotone` reduce, in the
same-epoch regime, to two Finset facts about the honest class sets as the window end
grows `σ' → σ' + 1`: `Sclass` grows by (at least) the fresh honest committee, and
`Xclass` never grows. This section **mechanizes that set algebra** down to the single
genuine store-dynamics crux — that every *fresh* honest window member of slot `σ' + 1`
supports `desc(b′)` (`hfresh`, from `votes_head` + the head-safety IH + the closed
vote-landing bundle). The same-epoch bookkeeping (`votes_assigned` +
`committee_assignment_unique`: a non-fresh window member casts no vote at `σ' + 1`, so its
class membership is preserved) is discharged here in full. -/

/-- **`SupportsDesc` is preserved by a no-vote step.** If `i` casts no vote at `σ' + 1`,
its newest-by-`σ'` supporting vote is still newest by `σ' + 1`, so `SupportsDesc σ'` lifts
to `SupportsDesc (σ' + 1)`. -/
theorem SupportsDesc_succ_of_novote (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ' : Slot)
    {i : ValidatorIndex} (hnovote : E.vote i (σ' + 1) = none)
    (h : E.SupportsDesc cfg ext v₀ n₀ b' σ' i) :
    E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i := by
  obtain ⟨t, k, a, htle, hvote, hnew, hanc⟩ := h
  refine ⟨t, k, a, le_trans htle (Nat.le_succ _), hvote, ?_, hanc⟩
  intro t' ht' ht'le
  rcases eq_or_lt_of_le ht'le with heq | hlt
  · rw [heq]; exact hnovote
  · exact hnew t' ht' (Nat.lt_succ_iff.mp hlt)

/-- **`AncestorOrVoteless` is preserved by a no-vote step.** As `SupportsDesc_succ_of_novote`
for the voteless / ancestor-voting predicate. -/
theorem AncestorOrVoteless_succ_of_novote (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ' : Slot)
    {i : ValidatorIndex} (hnovote : E.vote i (σ' + 1) = none)
    (h : E.AncestorOrVoteless cfg ext v₀ n₀ b' σ' i) :
    E.AncestorOrVoteless cfg ext v₀ n₀ b' (σ' + 1) i := by
  rcases h with hvoteless | ⟨t, k, a, htle, hvote, hnew, hanc⟩
  · refine Or.inl (fun t' ht'le => ?_)
    rcases eq_or_lt_of_le ht'le with heq | hlt
    · rw [heq]; exact hnovote
    · exact hvoteless t' (Nat.lt_succ_iff.mp hlt)
  · refine Or.inr ⟨t, k, a, le_trans htle (Nat.le_succ _), hvote, ?_, hanc⟩
    intro t' ht' ht'le
    rcases eq_or_lt_of_le ht'le with heq | hlt
    · rw [heq]; exact hnovote
    · exact hnew t' ht' (Nat.lt_succ_iff.mp hlt)

/-- **A non-fresh honest window member casts no vote at `σ' + 1`** (same-epoch). `i ∈
span lo σ'` is assigned at some slot `s ∈ [lo, σ']`; `committee_assignment_unique` (same
epoch) forbids a second assignment at `σ' + 1`, so `votes_assigned` (honest) forces
`vote i (σ' + 1) = none`. -/
theorem novote_succ_of_span (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    {i : ValidatorIndex} (hih : i ∈ E.honest) {lo σ' : Slot}
    (hmem : i ∈ E.span_committee lo σ')
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1)) :
    E.vote i (σ' + 1) = none := by
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hmem
  obtain ⟨s, ⟨hslo, hshi⟩, hcomm⟩ := hmem
  by_contra hne
  have hcomm' : i ∈ E.committee (σ' + 1) := hhb.votes_assigned i hih (σ' + 1) hne
  have hseq : s = σ' + 1 :=
    hec.committee_assignment_unique i s (σ' + 1) hcomm hcomm' (hsame s hslo hshi)
  subst hseq
  exact absurd hshi (Nat.not_succ_le_self σ')

omit [LinearOrder Root] [Inhabited Root] in
/-- **Disjoint-union weight.** `weight (A ∪ B) = weight A + weight B` for disjoint `A`, `B`. -/
theorem weight_union_disjoint {A B : Finset ValidatorIndex} (h : Disjoint A B) :
    E.weight (A ∪ B) = E.weight A + E.weight B := by
  simp only [Execution.weight]; exact Finset.sum_union h

/-- **`hSmono` from the fresh-support crux** (`EconomicCore`, item 1). In the same-epoch regime the
honest support grows by (at least) the fresh honest committee: `Sclass σ'` lifts into
`Sclass (σ' + 1)` (non-fresh members cast no vote, `SupportsDesc` preserved) and the fresh
honest window growth `G := (span lo (σ'+1) \ span lo σ').filter honest` lands in
`Sclass (σ' + 1)` by `hfresh`, disjointly. Hence
`Sval σ' + weight G ≤ Sval (σ' + 1)` — exactly `hdeltas_of_monotone`'s `hSmono`. -/
theorem hSmono_of_fresh (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hfresh : ∀ i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
        (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i) :
    E.Sval cfg ext v₀ n₀ b' lo σ' +
        E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
          (fun i => i ∈ E.honest))
      ≤ E.Sval cfg ext v₀ n₀ b' lo (σ' + 1) := by
  classical
  set G := (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter (fun i => i ∈ E.honest)
    with hGdef
  have hSsub : E.Sclass cfg ext v₀ n₀ b' lo σ' ⊆ E.Sclass cfg ext v₀ n₀ b' lo (σ' + 1) := by
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨hspan, hih⟩, hsupp⟩ := hi
    refine ⟨⟨E.span_committee_mono lo (Nat.le_succ _) hspan, hih⟩, ?_⟩
    exact E.SupportsDesc_succ_of_novote cfg ext v₀ n₀ b' σ'
      (E.novote_succ_of_span cfg ext hhb hec hih hspan hsame) hsupp
  have hGsub : G ⊆ E.Sclass cfg ext v₀ n₀ b' lo (σ' + 1) := by
    intro i hi
    have hi' := hi
    rw [hGdef, Finset.mem_filter, Finset.mem_sdiff] at hi'
    simp only [Execution.Sclass, Finset.mem_filter]
    exact ⟨⟨hi'.1.1, hi'.2⟩, hfresh i hi⟩
  have hdisj : Disjoint (E.Sclass cfg ext v₀ n₀ b' lo σ') G := by
    rw [Finset.disjoint_left]
    intro i hiS hiG
    simp only [Execution.Sclass, Finset.mem_filter] at hiS
    rw [hGdef, Finset.mem_filter, Finset.mem_sdiff] at hiG
    exact hiG.1.2 hiS.1.1
  simp only [Execution.Sval]
  rw [← E.weight_union_disjoint hdisj]
  exact E.weight_mono (Finset.union_subset hSsub hGsub)

/-- **`hXmono` from the fresh-support crux** (`EconomicCore`, item 1). In the same-epoch regime the
sibling-stuck honest class never grows: `Xclass (σ'+1) ⊆ Xclass σ'`. A member of
`Xclass (σ'+1)` cannot be fresh (`hfresh` would make it `SupportsDesc`, hence not `Xclass`),
so it is a non-fresh window member; as such it casts no vote at `σ' + 1`, so both class
predicates are preserved backwards. Hence `Xval (σ' + 1) ≤ Xval σ'` — `hdeltas_of_monotone`'s
`hXmono`. -/
theorem hXmono_of_fresh (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hfresh : ∀ i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
        (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i) :
    E.Xval cfg ext v₀ n₀ b' lo (σ' + 1) ≤ E.Xval cfg ext v₀ n₀ b' lo σ' := by
  classical
  have hsub : E.Xclass cfg ext v₀ n₀ b' lo (σ' + 1) ⊆ E.Xclass cfg ext v₀ n₀ b' lo σ' := by
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    obtain ⟨⟨hspan1, hih⟩, hnS, hnA⟩ := hi
    -- i is not fresh: freshness would give `SupportsDesc (σ'+1)`, contradicting `hnS`.
    have hspan0 : i ∈ E.span_committee lo σ' := by
      by_contra hnot
      exact hnS (hfresh i (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hspan1, hnot⟩, hih⟩))
    have hnovote := E.novote_succ_of_span cfg ext hhb hec hih hspan0 hsame
    refine ⟨⟨hspan0, hih⟩, ?_, ?_⟩
    · exact fun hS => hnS (E.SupportsDesc_succ_of_novote cfg ext v₀ n₀ b' σ' hnovote hS)
    · exact fun hA => hnA (E.AncestorOrVoteless_succ_of_novote cfg ext v₀ n₀ b' σ' hnovote hA)
  simp only [Execution.Xval]
  exact E.weight_mono hsub

end Execution

end FastConfirmation.Spec
