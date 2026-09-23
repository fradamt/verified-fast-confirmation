module
public import FastConfirmation.Spec.Proof.EdgeDynamics
public import FastConfirmation.Spec.Proof.StepDischarge
public import FastConfirmation.Spec.Proof.Discount

@[expose] public section

/-!
# Spec / Proof / Confinement: accounting and sibling-confinement lemmas

`EdgeDynamics.EdgeInputResidual` contains sibling-confinement and accounting
inputs used to construct a `ForkEdgeInput`. This module proves arithmetic bounds
for the adversarial-weight fields, connects the discount and supporter scores to
their specification definitions, and proves honest sibling confinement at the
base cutoff. Its lemmas use the endpoint store `(w, m)` and confirming store
`(vc, nc)` appearing in those definitions.

## Part 1 — the adversarial-weight bridges (`hAhi`/`hAlo`)

`compute_adversarial_weight = max(maxAdv − equiv, 0)` with `maxAdv = estimate//100 · C`.
`compute_adversarial_weight_le` / `_ge` are the two-sided bounds around it (pure
`split_ifs <;> omega`); `get_adversarial_weight_{le,ge}_qV` specialize them through
`Quorum.get_adversarial_weight_eq` to `get_adversarial_weight`, delivering
`arms_of_confirmed`'s `hAhi` (`≤ qV·C`) and `hAlo` (`qV·C ≤ · + eqV`) with
`qV := estimate(advSpan)//100`, `eqV := get_equivocation_score(advSpan)`.

## Part 2 — the discount bridge (`hd`)

`hd_of_confirmed` applies `Discount.support_discount_le_parent_stuck` to obtain
`d ≤ Hpar := weight(ParentStuck)` and weakens it to the `arms_of_confirmed`
shape `d ≤ Hpar + Bpar`, where `Bpar := weight(ParentStuckByz)`.

## Part 3 — the honest sibling confinement (`hHon`), reduced via `siblings_incompatible`

`honest_sibling_confinement`: at `(w, m)`, an honest recorded supporter of a sibling
`c'` of the `b`-side child `c` lands in `Xclass … es` — **at the base cutoff `es`**,
where the recorded newest-by-`es` message *is* the newest-by-`es` ground vote
(`StepDischarge.recorded_lm_is_newest_at`). The geometry shows that the supporter's
recorded block descends from `c'`; `Forks.siblings_incompatible` (with `c ⪯ b`) rules
out both `⪰ b` (would be a common descendant of `c`, `c'`) and `⪯ b` (would make `c'` a
second `h`-child ancestor of `b`). For a general `σ ≥ es`, a validator may record
`c'`-support at `es` yet have a later
`(es, σ]` vote that descends from `b` by the engine IH — it then sits in `Sclass σ`, not
`Xclass σ`. The corresponding cross-window migration statement is therefore a
separate input to `ForkEdgeInput`.

## Part 4 — the attestation-score bridge (`hS`)

`hS_of_confirmed` splits the attestation score into honest and Byzantine
supporter sums with `attestation_score_honest_split`, then bounds the honest sum
by `Sval` using `honest_supporters_sum_le_Sval`.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Part 1 — the adversarial-weight bridges (`hAhi`/`hAlo`) -/

/-- Pure-ℕ upper bound around the guarded difference. -/
private theorem guarded_sub_le {M eq : ℕ} : (if M > eq then M - eq else 0) ≤ M := by
  split_ifs <;> omega

/-- Pure-ℕ lower bound: the guarded difference plus the subtrahend dominates `M`. -/
private theorem le_guarded_sub_add {M eq : ℕ} : M ≤ (if M > eq then M - eq else 0) + eq := by
  split_ifs <;> omega

/-- **`compute_adversarial_weight ≤ maxAdv`** (`hAhi` core). The adversarial weight is
the equivocation-discounted budget `max(maxAdv − equiv, 0)`, at most `maxAdv =
estimate//100 · C`. Pure `split_ifs`. -/
theorem compute_adversarial_weight_le {store : Store Root} {bs : BeaconState Root}
    (a e : Slot) :
    compute_adversarial_weight cfg ext store bs a e ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) a e / 100
        * cfg.confirmation_byzantine_threshold := by
  simp only [compute_adversarial_weight]
  exact guarded_sub_le

/-- **`maxAdv ≤ compute_adversarial_weight + equiv`** (`hAlo` core). The budget net of the
equivocation score, plus that score back, recovers the full `maxAdv`. Pure `split_ifs`. -/
theorem le_compute_adversarial_weight_add_equiv {store : Store Root} {bs : BeaconState Root}
    (a e : Slot) :
    estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) a e / 100
        * cfg.confirmation_byzantine_threshold ≤
      compute_adversarial_weight cfg ext store bs a e
        + get_equivocation_score cfg ext store bs a e := by
  simp only [compute_adversarial_weight]
  exact le_guarded_sub_add

/-- **`hAhi` at the real spec quantity.** `get_adversarial_weight ≤ qV·C` with
`qV := estimate(advSpan)//100`, `advSpan := [start, current−1]` the
`get_adversarial_weight` span (`Quorum.get_adversarial_weight_eq`). Exactly
`arms_of_confirmed`'s `hAhi`. -/
theorem get_adversarial_weight_le_qV {store : Store Root} {bs : BeaconState Root} {b : Root} :
    get_adversarial_weight cfg ext store bs b ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (if get_block_epoch cfg store b >
              get_block_epoch cfg store (store.blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
          else (store.blocks b).slot)
          (get_current_slot cfg store - 1) / 100
        * cfg.confirmation_byzantine_threshold := by
  rw [get_adversarial_weight_eq]
  exact compute_adversarial_weight_le cfg ext _ _

/-- **`hAlo` at the real spec quantity.** `qV·C ≤ get_adversarial_weight + eqV` with
`qV := estimate(advSpan)//100`, `eqV := get_equivocation_score(advSpan)`. Exactly
`arms_of_confirmed`'s `hAlo`. -/
theorem qV_le_get_adversarial_add_eqV {store : Store Root} {bs : BeaconState Root} {b : Root} :
    estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (if get_block_epoch cfg store b >
              get_block_epoch cfg store (store.blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
          else (store.blocks b).slot)
          (get_current_slot cfg store - 1) / 100
        * cfg.confirmation_byzantine_threshold ≤
      get_adversarial_weight cfg ext store bs b
        + get_equivocation_score cfg ext store bs
          (if get_block_epoch cfg store b >
              get_block_epoch cfg store (store.blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
          else (store.blocks b).slot)
          (get_current_slot cfg store - 1) := by
  rw [get_adversarial_weight_eq]
  exact le_compute_adversarial_weight_add_equiv cfg ext _ _

/-! ## Part 2 — the discount bridge (`hd`), via `Discount.support_discount_le_parent_stuck` -/

namespace Execution

variable (E : Execution Root)

/-- **`hd` at the real spec quantities.** `d ≤ Hpar + Bpar` with `Hpar :=
weight(ParentStuck)`, `Bpar := weight(ParentStuckByz)`. `Discount.support_discount_le_parent_stuck`
delivers the stronger `d ≤ Hpar`; the byz slice `Bpar` only relaxes it. This is
`arms_of_confirmed`'s `hd` with the pre-region honest / byz split as the `Hpar` / `Bpar`
witnesses. -/
theorem hd_of_confirmed (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest) :
    get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b)
        + E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b) :=
  le_trans (support_discount_le_parent_stuck cfg ext hec hbb hv hnH hval hstartH hbH htab hne)
    (Nat.le_add_right _ _)

/-! ## Part 3 — the honest sibling confinement (`hHon`), at the base cutoff `es`

At the base cutoff `es = get_current_slot(store w m) − 1`, an honest recorded supporter of a
sibling `c'` of the `b`-side child `c` lands in `Xclass … es`. The recorded newest-by-`es`
message *is* the newest-by-`es` ground vote (`StepDischarge.recorded_lm_is_newest_at`), so the
recorded block `lm.root` is the sole newest vote block; `Forks.siblings_incompatible` (with
`c ⪯ b`) then rules out both class-membership branches:

* `¬SupportsDesc`: `lm.root ⪰ b` would make `lm.root` a common descendant of `c` (`c ⪯ b ⪯ lm.root`)
  and `c'` (`c' ⪯ lm.root`) — impossible for distinct `h`-children.
* `¬AncestorOrVoteless`: `b ⪰ lm.root` would give `c' ⪯ lm.root ⪯ b`, so `b` is a common
  descendant of `c` and `c'` — again impossible; and the voteless branch dies on the recorded vote.

The blanket walk domain `hwalkK` is the Layer-0 `AnchorFacade.store_walkKnownK` shape; `hdom` is
`Bridge.RecordedEpochMax` (the ubiquity domination); `hbc`/`hlo`/`hpc`/`hpc'`/`hne` are the fork
geometry. `hlmknown` (recorded message roots are known blocks) is the per-store knownness fact the
attestation-application block gate provides. -/

/-- **Honest sibling confinement at `es`** (`EdgeInputResidual.hHon`, `σ := es` slice). See the
section note for the geometry. -/
theorem honest_sibling_confinement
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots, ∀ r ∈ (E.store cfg ext w m).block_roots,
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo es : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    (hdom : E.RecordedEpochMax cfg ext w m es)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c') bs)
    (hih : i ∈ E.honest) :
    i ∈ E.Xclass cfg ext w m b lo es := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hi_supp
  have hanc' : is_ancestor (E.store cfg ext w m) (get_node_for_root lm.root)
      (get_node_for_root c') = true := by
    simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
  obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
    E.recorded_lm_is_newest_at cfg ext hhb hec hgen hprov hes hih hlm (hdom i hih lm hlm)
  have hlmk : lm.root ∈ (E.store cfg ext w m).block_roots := hlmknown lm i hlm
  have hmem : i ∈ E.span_committee lo es := by
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi_supp
      (fun lm2 hlm2 => hwalkK c' hc' lm2.root (hlmknown lm2 i hlm2)) hlo
  simp only [Execution.Xclass, Finset.mem_filter]
  refine ⟨⟨hmem, hih⟩, ?_, ?_⟩
  · rintro ⟨t1, k1, a1, ht1le, hvote1, hnew1, hanc1⟩
    have htt : t = t1 := newest_vote_unique
      (by rw [hvote]; exact Option.some_ne_none _) hnew
      (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
    rw [← htt, hvote] at hvote1
    simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
    obtain ⟨_, ha⟩ := hvote1
    rw [← ha, hbbreq] at hanc1
    have hlmc : is_ancestor (E.store cfg ext w m) (get_node_for_root lm.root)
        (get_node_for_root c) = true :=
      is_ancestor_trans (a := get_node_for_root lm.root) (b := get_node_for_root b)
        (c := get_node_for_root c) hwf (hwalkK c hc lm.root hlmk) (hwalkK c hc b hb) hanc1 hbc
    exact siblings_incompatible hwf hc hc' hh hpc hpc' hne
      (hwalkK c hc lm.root hlmk) (hwalkK c' hc' lm.root hlmk) hlmc hanc'
  · rintro (hvoteless | ⟨t1, k1, a1, ht1le, hvote1, hnew1, hanc1⟩)
    · exact absurd (hvoteless t htle) (by rw [hvote]; exact Option.some_ne_none _)
    · have htt : t = t1 := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnew
        (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
      rw [← htt, hvote] at hvote1
      simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
      obtain ⟨_, ha⟩ := hvote1
      rw [← ha, hbbreq] at hanc1
      have hbc' : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root c') = true :=
        is_ancestor_trans hwf (a := get_node_for_root b) (b := get_node_for_root lm.root)
          (c := get_node_for_root c') (hwalkK c' hc' b hb) (hwalkK c' hc' lm.root hlmk) hanc1 hanc'
      exact siblings_incompatible hwf hc hc' hh hpc hpc' hne
        (hwalkK c hc b hb) (hwalkK c' hc' b hb) hbc hbc'

/-! ## Part 4 — the `hS` bridge (score `≤ Sval + Bsup`)

`arms_of_confirmed`'s `hS` (`get_attestation_score ≤ s₀ + Bsup`) with the natural
choices `s₀ := Sval` and `Bsup := ` the byz-supporter list sum: the score splits into
its honest and byz sub-sums (`QuorumAccounting.attestation_score_honest_split`), and the
honest sub-sum is `≤ Sval` (`Bridge.honest_supporters_sum_le_Sval`). This makes the
`DynamicsClosure.INV2_base_of_confirmed` identity `hSval : s₀ = Sval` **definitional** and
its `hBsup` exactly `HonestWeight.byz_score_le_adversarial_weight` (`Bsup` = the same byz
sub-sum). The theorem states the required execution and store premises. -/

/-- **`hS` at the real spec quantities.** `get_attestation_score b' ≤ Sval + Bsup` with
`Bsup :=` the byz-supporter list sum — `arms_of_confirmed`'s `hS` under `s₀ := Sval`. The
score's honest/byz split plus `honest_supporters_sum_le_Sval` on the honest half. -/
theorem hS_of_confirmed (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈ (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {lo es : Slot}
    (hval : bs.validators = E.registry)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (hdom : E.RecordedEpochMax cfg ext v₀ n₀ es) :
    get_attestation_score cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs ≤
      E.Sval cfg ext v₀ n₀ b' lo es +
        (((AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs).filter
            (fun i => i ∉ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum := by
  rw [attestation_score_honest_split cfg E]
  exact Nat.add_le_add_right
    (E.honest_supporters_sum_le_Sval cfg ext hhb hec hgen hwf hprov hval hlo hes hslotlt hwalk hdom)
    _

end Execution

end FastConfirmation.Spec

end
