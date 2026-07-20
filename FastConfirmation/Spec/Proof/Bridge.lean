import FastConfirmation.Spec.Proof.Base
import FastConfirmation.Spec.Proof.Delivery
import FastConfirmation.Spec.Proof.EngineSupport
import FastConfirmation.Spec.Proof.FractionBase

/-!
# Spec / Proof / Bridge: the reverse-provenance bridge

`Proof/Base.lean`'s `weak_base_of_rule` reduces the INV\* endpoint-form margin to
two store-dynamics facts left as hypotheses `hHsup` / `hdisc` — the *reverse*
Provenance/Delivery bridge from **recorded latest messages** back to
**ground-truth newest votes** (the base and maintenance bridge; the
mirror of `EngineSupport.mem_AttSupporters_honest` in the opposite direction).
This module discharges both.

The core is `recorded_lm_is_newest`: at the confirming honest node `(v₀, n₀)`
(second of slot `es + 1`, `es = get_current_slot store − 1`), an honest
validator `i`'s recorded `latest_messages i = some lm` corresponds to `i`'s
ground newest-by-`es` vote — a vote at slot `t ≤ es`, no later vote through `es`,
whose LMD block is exactly `lm.root`. Its ingredients are all existing exports:

* **existence + block-root** — `Delivery.SchedLMProv` (schedule-connected
  setting attestation) + `HonestBehavior.no_forgery` (the attestation is `i`'s
  own vote), exactly the route `Delivery.latest_message_root` takes;
* **`t ≤ es`** — `LatestMessageProvenance`'s slot gate (`a.data.slot + 1 ≤
  current_slot`) + `committee_assignment_unique` (the setting slot is `i`'s vote
  slot), needing **no** new hypothesis (`hprov` is already in `weak_base_of_rule`);
* **newest** — a domination input `RecordedEpochMax` (the recorded message's
  epoch is at least every honest vote-slot epoch through `es`) rules out later
  displacing votes via `committee_assignment_unique`. This is exactly
  `Delivery.vote_ubiquity`'s conclusion, ∀-quantified over the window; the engine
  shell discharges it from `Synchrony`. No additional dynamics premise is used.

`recorded_supporter_mem_Sclass` / `ParentStuck_subset_Aclass` then place the
recorded honest supporters into `Sclass` and the parent-stuck honest weight into
`Aclass`, and `honest_supporters_sum_le_Sval` / `support_discount_le_Aval`
weigh those inclusions into `hHsup` / `hdisc`. `weak_base_discharged` assembles
the full weak base with the two bridges gone.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## The domination input (ubiquity's ∀-quantified conclusion)

`RecordedEpochMax` says the message recorded for an honest validator at the
confirming node dominates, in epoch, every one of that validator's own votes
through `es`. This is precisely what `Delivery.vote_ubiquity` establishes for a
single honest vote (recorded message epoch `≥` the delivered vote's target epoch,
`= compute_epoch_at_slot` of the vote slot for an honest attestation); the engine
shell instantiates it per honest voter over the window. -/

/-- The recorded latest message of an honest validator at `(v₀, n₀)` has epoch at
least the epoch of every vote that validator cast at a slot `≤ es`. -/
def RecordedEpochMax (v₀ : ValidatorIndex) (n₀ : ℕ) (es : Slot) : Prop :=
  ∀ i ∈ E.honest, ∀ lm : LatestMessage Root,
    (E.store cfg ext v₀ n₀).latest_messages i = some lm →
    ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (k, a) →
      compute_epoch_at_slot cfg t ≤ lm.epoch

/-- Model/domain adequacy for honest-attestation delivery. For an actual
post-anchor honest vote, the source head's walk down to its FFG target epoch
boundary stays in the source store's block domain. Source-head knownness is
kept separate and is derived by selected-margin consumers. -/
def PostAnchorHonestVoteTargetWalkDomain : Prop :=
  ∀ (i : ValidatorIndex), i ∈ E.honest →
    ∀ (s : Slot) (n : ℕ) (index : CommitteeIndex),
      E.slot_at cfg 0 ≤ s →
      E.WithinHorizon cfg n →
      E.slot_at cfg n = s →
      E.vote i s = some
        (n, honest_attestation cfg ext (E.store cfg ext i n) s index i) →
      WalkKnown (E.store cfg ext i n)
        (compute_start_slot_at_epoch cfg
          (honest_attestation cfg ext
            (E.store cfg ext i n) s index i).data.target.epoch)
        (get_head cfg (E.store cfg ext i n)).root

/-- Epoch domination restricted to post-anchor votes. Unlike
`RecordedEpochMax`, this predicate never reads the unconstrained pre-anchor
portion of `Execution.vote`. -/
def PostAnchorRecordedEpochMax
    (v : ValidatorIndex) (q : ℕ) (lo es : Slot) : Prop :=
  ∀ i ∈ E.honest, ∀ lm : LatestMessage Root,
    (E.store cfg ext v q).latest_messages i = some lm →
    ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      lo ≤ t → t ≤ es → E.vote i t = some (k, a) →
      compute_epoch_at_slot cfg t ≤ lm.epoch

/-- Domination for all votes through `es`, restricted to honest validators
proved to belong to the concrete ledger window `[lo, es]`. A window member's
post-anchor assignment makes the apparently broader vote quantifier sound. -/
def WindowRecordedEpochMax
    (v : ValidatorIndex) (q : ℕ) (lo es : Slot) : Prop :=
  ∀ i ∈ E.honest, i ∈ E.span_committee lo es →
    ∀ lm : LatestMessage Root,
      (E.store cfg ext v q).latest_messages i = some lm →
      ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
        t ≤ es → E.vote i t = some (k, a) →
        compute_epoch_at_slot cfg t ≤ lm.epoch

/-- The legacy all-validator domination implies the faithful window-scoped
form. -/
theorem RecordedEpochMax.toWindow {v : ValidatorIndex} {q : ℕ} {lo es : Slot}
    (h : E.RecordedEpochMax cfg ext v q es) :
    E.WindowRecordedEpochMax cfg ext v q lo es := by
  intro i hi _hiSpan lm hlm t k a ht hvote
  exact h i hi lm hlm t k a ht hvote

end Execution

/-! ## Newest-vote uniqueness -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Through a fixed window `[·, es]` an honest validator has at most one
"newest" vote: two slots each with no later vote through `es` coincide. -/
theorem newest_vote_unique {E : Execution Root} {i : ValidatorIndex} {es t₀ t₁ : Slot}
    (h0 : E.vote i t₀ ≠ none) (h0n : ∀ t' : Slot, t₀ < t' → t' ≤ es → E.vote i t' = none)
    (h1 : E.vote i t₁ ≠ none) (h1n : ∀ t' : Slot, t₁ < t' → t' ≤ es → E.vote i t' = none)
    (h0le : t₀ ≤ es) (h1le : t₁ ≤ es) : t₀ = t₁ := by
  rcases lt_trichotomy t₀ t₁ with h | h | h
  · exact absurd (h0n t₁ h h1le) h1
  · exact h
  · exact absurd (h1n t₀ h h0le) h0

namespace Execution

variable (E : Execution Root)

/-! ## The core bridge: recorded latest message ⟹ ground newest vote -/

/-- **The reverse-provenance bridge.** At the confirming honest node `(v₀, n₀)`,
an honest validator `i`'s recorded `latest_messages i = some lm` is set by `i`'s
ground **newest-by-`es`** vote (a vote at `t ≤ es`, no later vote through `es`)
whose LMD block is exactly `lm.root`. Existence + block-root from
`SchedLMProv` + `no_forgery`; `t ≤ es` from the provenance slot gate `hprov` +
`committee_assignment_unique`; the newest characterization from the ubiquity
domination `hdom`. -/
theorem recorded_lm_is_newest
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {es : Slot} (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    {i : ValidatorIndex} (hi : i ∈ E.honest) {lm : LatestMessage Root}
    (hlm : (E.store cfg ext v₀ n₀).latest_messages i = some lm)
    (hdom : ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (k, a) → compute_epoch_at_slot cfg t ≤ lm.epoch) :
    ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = lm.root := by
  -- existence of a setting vote with block `lm.root`
  obtain ⟨a', u, tsc, ifb, hsched, hvin, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen v₀ n₀ i lm hlm
  obtain ⟨m1, a'', hvote', hdata'⟩ := hhb.no_forgery u tsc a' ifb hsched i hi hvin
  -- `a'.data.slot` is `i`'s vote slot; identify it with the provenance slot `≤ es`
  have hcomm0 : i ∈ E.committee a'.data.slot :=
    hhb.votes_assigned i hi a'.data.slot (by rw [hvote']; exact Option.some_ne_none _)
  obtain ⟨ap, _, _, _, h4, h5, h6, _, _⟩ := hprov i lm hlm
  have hepeq : compute_epoch_at_slot cfg a'.data.slot = compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, h4]
  have hslotdef : a'.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a'.data.slot ap.data.slot hcomm0 h6 hepeq
  have htle : a'.data.slot ≤ es := by
    rw [hslotdef, hes]; exact Nat.le_sub_one_of_lt h5
  -- the block-root of the recovered vote
  have hbbr' : a''.data.beacon_block_root = lm.root := by rw [← hdata']; exact hbbr
  refine ⟨a'.data.slot, m1, a'', htle, hvote', ?_, hbbr'⟩
  -- newest: any later vote through `es` collides with `a'.data.slot`'s epoch
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

/-! ## `hHsup`: recorded honest supporters are `Sclass` members -/

/-- **Recorded supporter ⟹ `Sclass`.** An honest supporter of `b′` at `(v₀, n₀)`
sits in `Sclass lo es`: window membership from
`QuorumAccounting.supporter_mem_span_committee`, and the descent
`SupportsDesc` from the bridge (its newest vote's block is the recorded
`lm.root`, which supports `b′`). -/
theorem recorded_supporter_mem_Sclass
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
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
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (hdom : E.RecordedEpochMax cfg ext v₀ n₀ es)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs)
    (hih : i ∈ E.honest) :
    i ∈ E.Sclass cfg ext v₀ n₀ b' lo es := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hi_supp
  obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
    E.recorded_lm_is_newest cfg ext hhb hec hgen hprov hes hih hlm (hdom i hih lm hlm)
  have hsa : lo ≤ ((E.store cfg ext v₀ n₀).blocks b').slot := by rw [hlo]; exact hslotlt
  simp only [Execution.Sclass, Finset.mem_filter]
  refine ⟨⟨?_, hih⟩, ?_⟩
  · rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi_supp (hwalk i hi_supp) hsa
  · refine ⟨t, k, a, htle, hvote, hnew, ?_⟩
    rw [hbbreq]; simpa only [get_supported_node, get_node_for_root] using hanc

/-- **`hHsup` discharge.** The honest-supporter list-sum at `(v₀, n₀)` is at most
`Sval lo es`: `FractionBase.honest_score_eq_weight` turns the list-sum into a
`Finset` weight, `recorded_supporter_mem_Sclass` includes those supporters in
`Sclass`, and `weight_mono` weighs the inclusion. -/
theorem honest_supporters_sum_le_Sval
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
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
    (((AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ E.Sval cfg ext v₀ n₀ b' lo es := by
  rw [honest_score_eq_weight cfg E hval, Execution.Sval]
  apply E.weight_mono
  intro i hi
  rw [List.mem_toFinset, List.mem_filter] at hi
  exact E.recorded_supporter_mem_Sclass cfg ext hhb hec hgen hwf hprov hlo hes hslotlt hwalk
    hdom hi.1 (of_decide_eq_true hi.2)

/-! ## `hdisc`: parent-stuck honest weight is `Aclass` weight -/

/-- **`ParentStuck ⊆ Aclass`.** A parent-stuck honest validator (recorded
`lm.root = parent(b′)`) is an `Aclass lo es` member: window membership from the
pre-span inclusion (`b′.slot − 1 ≤ es`), and `AncestorOrVoteless` because its
newest vote's block is `parent(b′)`, an ancestor of `b′` (`hb'anc`); `¬SupportsDesc`
because the newest vote is unique and `parent(b′)` does not descend from `b′`
(`hslotlt`, via `get_ancestor_stop`). -/
theorem ParentStuck_subset_Aclass
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {lo es : Slot}
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hb'cur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hb'anc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.RecordedEpochMax cfg ext v₀ n₀ es) :
    ParentStuck cfg E (E.store cfg ext v₀ n₀) bs b'
      ⊆ E.Aclass cfg ext v₀ n₀ b' lo es := by
  intro i hi_ps
  simp only [ParentStuck, Finset.mem_filter] at hi_ps
  obtain ⟨hPS, hih⟩ := hi_ps
  have hspan := (mem_ParentSupport cfg hPS).1
  simp only [ParentSupport, Finset.mem_filter] at hPS
  obtain ⟨_, hany⟩ := hPS
  cases hlm : (E.store cfg ext v₀ n₀).latest_messages i with
  | none => rw [hlm] at hany; simp at hany
  | some lm =>
    rw [hlm] at hany
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hany
    obtain ⟨hroot, _⟩ := hany
    obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
      E.recorded_lm_is_newest cfg ext hhb hec hgen hprov hes hih hlm (hdom i hih lm hlm)
    have habbr : a.data.beacon_block_root =
        ((E.store cfg ext v₀ n₀).blocks b').parent_root := by rw [hbbreq]; exact hroot
    have hb'nanc : ¬ is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root ((E.store cfg ext v₀ n₀).blocks b').parent_root)
        (get_node_for_root b') = true := by
      simp only [is_ancestor, get_node_for_root, decide_eq_true_eq]
      rw [get_ancestor_stop (le_of_lt hslotlt)]
      intro hcon
      injection hcon with h
      rw [h] at hslotlt
      exact lt_irrefl _ hslotlt
    simp only [Execution.Aclass, Finset.mem_filter]
    refine ⟨⟨?_, hih⟩, ?_, ?_⟩
    · apply E.span_committee_mono lo
        (show ((E.store cfg ext v₀ n₀).blocks b').slot - 1 ≤ es by
          rw [hes]; exact Nat.sub_le_sub_right hb'cur 1)
      rw [hlo]; exact hspan
    · intro hsd
      obtain ⟨t₁, k₁, a₁, ht1le, hvote1, hnew1, hanc1⟩ := hsd
      have htt : t = t₁ := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnew
        (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
      rw [← htt, hvote] at hvote1
      simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
      obtain ⟨_, ha⟩ := hvote1
      rw [← ha, habbr] at hanc1
      exact hb'nanc hanc1
    · exact Or.inr ⟨t, k, a, htle, hvote, hnew, by rw [habbr]; exact hb'anc⟩

/-- **`hdisc` discharge.** The support discount at `(v₀, n₀)` is at most
`Aval lo es`: `Discount.support_discount_le_parent_stuck` bounds it by the
parent-stuck honest weight, `ParentStuck_subset_Aclass` includes those in
`Aclass`, and `weight_mono` weighs the inclusion. No honest equivocators
(`hne`) is `Execution.honest_not_equivocating`. -/
theorem support_discount_le_Aval
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} (hv₀ : v₀ ∈ E.honest) {n₀ : ℕ}
    (hnH : E.WithinHorizon cfg n₀)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {lo es : Slot}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hb'cur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hb'anc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.RecordedEpochMax cfg ext v₀ n₀ es) :
    get_support_discount cfg ext (E.store cfg ext v₀ n₀) bs b'
      ≤ E.Aval cfg ext v₀ n₀ b' lo es := by
  have hne : ∀ i ∈ (E.store cfg ext v₀ n₀).equivocating_indices, i ∉ E.honest :=
    fun i hi_eq hi_honest =>
      Execution.honest_not_equivocating cfg ext hhb hec hgen hi_honest v₀ n₀ hi_eq
  refine le_trans (support_discount_le_parent_stuck cfg ext hec hbb hv₀ hnH hval
    (hlo ▸ hloH) hbH htab hne) ?_
  rw [Execution.Aval]
  exact E.weight_mono
    (E.ParentStuck_subset_Aclass cfg ext hhb hec hgen hprov hlo hes hslotlt hb'cur hb'anc hdom)

/-! ## The assembled weak base — `hHsup` / `hdisc` discharged -/

/-- **`weak_base_of_rule` with the two store-dynamics bridges gone.** The INV\*
endpoint-form margin `x₀ + B(es) + boost + 1 ≤ s₀` from the confirmation rule,
now depending only on the standard assumption package + the confirmation fact +
three chain-geometry facts about `b′` (`hslotlt`/`hb'cur`/`hb'anc`, all supplied
by the L4 chain fold: `b′` is a known chain block above its parent and not in the
future) + the ubiquity domination `hdom` (`RecordedEpochMax`, the shell
discharges it from `Synchrony`/`Delivery.vote_ubiquity`). `hHsup`/`hdisc` are
supplied by `honest_supporters_sum_le_Sval` / `support_discount_le_Aval`. -/
theorem weak_base_discharged
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} (hv : v₀ ∈ E.honest) {n₀ : ℕ}
    (hnH : E.WithinHorizon cfg n₀)
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈ (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    {bs : BeaconState Root} {b' : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v₀ n₀) bs b' = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (lo es : Slot)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hb'cur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hb'anc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.RecordedEpochMax cfg ext v₀ n₀ es) :
    E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es + compute_proposer_score cfg bs + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es := by
  have hHsup := E.honest_supporters_sum_le_Sval cfg ext hhb hec hgen hwf hprov hval hlo hes
    hslotlt hwalk hdom
  have hdisc := E.support_discount_le_Aval cfg ext hhb hec hbb hgen hv hnH hprov
    hval htab hlo hloH hes hslotlt hb'cur hbH hb'anc hdom
  exact E.weak_base_of_rule cfg ext hhb hec hbb hgen hv hnH hwf hbH hval htab hprov
    hconf hwalk lo es hlo hes hloH hesH hHsup hdisc

end Execution

end FastConfirmation.Spec
