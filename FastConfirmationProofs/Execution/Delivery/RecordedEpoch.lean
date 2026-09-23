module
public import FastConfirmationProofs.LMD.SameSlotLMD

@[expose] public section

/-!
# Recorded-epoch domination at an arbitrary query

`Bridge.RecordedEpochMax` quantifies over every ground-truth `Execution.vote`
at a slot below the ledger cutoff.  That is too broad for a trusted-anchor
execution: `HonestBehavior.votes_head` deliberately constrains only votes at
or after `slot_at 0`, so a pre-anchor value of the totalized `Execution.vote`
function need not have been delivered to the query store.

This module exposes the faithful window-scoped replacement.  Delivery is
proved only for actual post-anchor honest votes.  A validator in
`span_committee lo es` has an honest post-anchor vote in that window; that
vote's delivered epoch also dominates any spurious pre-anchor vote epoch by
slot monotonicity.  Thus consumers may recover exactly the domination they
need, but only after proving that the validator belongs to their ledger
window.

There is one explicit model/domain-adequacy boundary.  The executable model's
abstract checkpoint writes do not prove that the target-boundary walk used by
`validate_on_attestation` is in-domain.  `PostAnchorHonestVoteTargetWalkDomain`
states precisely that walk, only for actual in-horizon post-anchor honest
votes.  Source-head knownness is *not* assumed: it follows from
`SelectedMarginDomain.justified_root_known` and `get_head`'s fallback.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Store-explicit recorded evidence

`Execution.WindowRecordedEpochMax` is intentionally tied to a completed
whole-second store.  A source-permitted query may instead observe an action
prefix inside that second.  The following predicate is the production
interface for that case: it names the exact store read by the query and says
only that latest-message cells actually used by the honest ledger window
dominate the relevant ground votes.
-/








namespace Execution

variable (E : Execution Root)

/-- Reverse provenance at the exact store read by a query.  Unlike the
historical `(v,q)` wrapper, this theorem needs no equality with
`Execution.store`; schedule-connected and ordinary provenance are stated
directly for `queryStore`. -/
theorem recorded_lm_is_newest_in_store
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    {queryStore : Store Root}
    (hsched : SchedLMProv E cfg queryStore)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg queryStore) queryStore)
    {es : Slot} (hes : es = get_current_slot cfg queryStore - 1)
    {i : ValidatorIndex} (hi : i ∈ E.honest) {lm : LatestMessage Root}
    (hlm : queryStore.latest_messages i = some lm)
    (hdom : ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (k, a) →
      compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)) :
    ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = lm.root := by
  obtain ⟨a', u, tsc, ifb, hschedule, hvin, hbbr, hslotep⟩ :=
    hsched i lm hlm
  obtain ⟨m1, a'', hvote', hdata'⟩ :=
    hhb.no_forgery u tsc a' ifb hschedule i hi hvin
  have hcomm0 : i ∈ E.committee a'.data.slot :=
    hhb.votes_assigned i hi a'.data.slot
      (by rw [hvote']; exact Option.some_ne_none _)
  obtain ⟨ap, _, _, _, h4, h5, h6, _, _, _⟩ := hprov i lm hlm
  have hepeq : compute_epoch_at_slot cfg a'.data.slot =
      compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, h4]
  have hslotdef : a'.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a'.data.slot ap.data.slot hcomm0 h6 hepeq
  have htle : a'.data.slot ≤ es := by
    rw [hslotdef, hes]
    exact Nat.le_sub_one_of_lt h5
  have hbbr' : a''.data.beacon_block_root = lm.root := by
    rw [← hdata']
    exact hbbr
  refine ⟨a'.data.slot, m1, a'', htle, hvote', ?_, hbbr'⟩
  intro t' hlt hle
  cases hvt : E.vote i t' with
  | none => rfl
  | some p =>
      exfalso
      obtain ⟨k', a3⟩ := p
      have hcomm' : i ∈ E.committee t' :=
        hhb.votes_assigned i hi t'
          (by rw [hvt]; exact Option.some_ne_none _)
      have heple : compute_epoch_at_slot cfg t' ≤ (get_latest_message_epoch cfg lm) :=
        hdom t' k' a3 hle hvt
      have hepmono : compute_epoch_at_slot cfg a'.data.slot ≤
          compute_epoch_at_slot cfg t' :=
        Nat.div_le_div_right (le_of_lt hlt)
      have hle1 : compute_epoch_at_slot cfg t' ≤
          compute_epoch_at_slot cfg a'.data.slot := by
        rw [hslotep]
        exact heple
      have hepeq' : compute_epoch_at_slot cfg t' =
          compute_epoch_at_slot cfg a'.data.slot :=
        le_antisymm hle1 hepmono
      have hts : t' = a'.data.slot :=
        hec.committee_assignment_unique i t' a'.data.slot
          hcomm' hcomm0 hepeq'
      subst hts
      exact lt_irrefl _ hlt

/-- A single actual post-anchor honest vote is recorded (or superseded by a
newer-epoch message) at an arbitrary later query.  This is the reusable
existence half of the supplier; unlike `PostAnchorRecordedEpochMax`, it does
not assume that the query already has a message for the validator.

Only the target-boundary walk comes from the explicit model/domain-adequacy
interface.  The source head is known from `SelectedMarginDomain`, and all
clock, horizon, validity, and synchrony premises are derived from
`SelectedMarginAssumptions`. -/
theorem honestVote_recorded_at_query_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hnH : E.WithinHorizon cfg n)
    (hnSlot : E.slot_at cfg n = s)
    (hvoteHead : E.vote i s = some
      (n, honest_attestation cfg ext (E.store cfg ext i n) s index i))
    (hsq : s < E.slot_at cfg q) :
    ∃ msg, (E.store cfg ext v q).latest_messages i = some msg ∧
      compute_epoch_at_slot cfg s ≤ (get_latest_message_epoch cfg msg) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    have hgws : WellFormedStore E.genesis_store := by
      rw [hgeq]
      exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
    exact hgws.time_ge_genesis
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_of_le cfg (le_of_eq hnSlot.symm) hnH
  have hheadKnown : (get_head cfg (E.store cfg ext i n)).root ∈
      (E.store cfg ext i n).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi n hnH
  have hheadWalk : WalkKnown (E.store cfg ext i n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext i n) s index i).data.target.epoch)
      (get_head cfg (E.store cfg ext i n)).root :=
    hwalkDomain i hi s n index hs0 hnH hnSlot hvoteHead
  have hdeliver : E.slot_start cfg (s + 1) ≤ q := by
    have hs1le : s + 1 ≤ E.slot_at cfg q := Nat.succ_le_of_lt hsq
    apply Nat.le_of_not_gt
    intro hqStart
    have hslotLt : E.slot_at cfg q < s + 1 :=
      (E.slot_at_lt_iff cfg hA.whole_seconds hgenTime).2 hqStart
    exact (Nat.not_lt_of_ge hs1le) hslotLt
  obtain ⟨msg, hmsg, htarget⟩ :=
    E.vote_ubiquity cfg ext hA.wellFormed hA.honest_behavior
      hA.synchrony hA.externals_coherence hA.whole_seconds hA.genesis
      hi hv hnSlot hnH hvoteHead hheadKnown hheadWalk hdeliver hqH
  have hheadStateSlot :
      ((E.store cfg ext i n).block_states
        (get_head cfg (E.store cfg ext i n)).root).slot ≤ s := by
    have hgws : WellFormedStore E.genesis_store := by
      rw [hgeq]
      exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
    have hcore := E.store_wellFormedStoreCore cfg ext
      hA.externals_coherence.state_transition_slot hgws.core i n
    rw [hcore.2 _ hheadKnown]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext
      hA.whole_seconds ⟨ast, ablk, hgeq, hslot⟩ i n _ hheadKnown
    rwa [E.store_current_slot cfg ext i n, hnSlot] at hblockSlot
  have htargetEpoch :
      (honest_attestation cfg ext
        (E.store cfg ext i n) s index i).data.target.epoch =
        compute_epoch_at_slot cfg s :=
    honest_attestation_data_target_epoch cfg ext
      (E.store cfg ext i n) s index
      hA.externals_coherence.process_slots_slot hheadStateSlot
  exact ⟨msg, hmsg, htargetEpoch ▸ htarget⟩

/-- Post-anchor vote domination at an arbitrary query.  Synchrony schedules
the honest attestation at the first second of `t+1`; cutoff geometry
`t ≤ slot_at(q)-1` puts that delivery second no later than `q`.

The target-boundary walk is the explicit model/domain-adequacy premise above;
source-head knownness and every remaining delivery premise are derived from
`SelectedMarginAssumptions`. -/
theorem postAnchorRecordedEpochMax_at_query_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {lo es : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (heslt : es < E.slot_at cfg q) :
    E.PostAnchorRecordedEpochMax cfg ext v q lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    have hgws : WellFormedStore E.genesis_store := by
      rw [hgeq]
      exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
    exact hgws.time_ge_genesis
  have hesle : es ≤ E.slot_at cfg q := by
    rw [hes, E.store_current_slot cfg ext v q]
    exact Nat.sub_le _ _
  have hesH : E.SlotWithinHorizon cfg es :=
    E.slotWithinHorizon_of_le cfg hesle hqH
  intro i hi lm hlm t k a hlot htes hvote
  have htH : E.SlotWithinHorizon cfg t :=
    E.slotWithinHorizon_mono cfg htes hesH
  have hiComm : i ∈ E.committee t :=
    hA.honest_behavior.votes_assigned i hi t
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨n, index, hnH, hnSlot, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi t hiComm htH (hlo0.trans hlot)
  have hheadKnown : (get_head cfg (E.store cfg ext i n)).root ∈
      (E.store cfg ext i n).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi n hnH
  have hheadWalk : WalkKnown (E.store cfg ext i n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext i n) t index i).data.target.epoch)
      (get_head cfg (E.store cfg ext i n)).root :=
    hwalkDomain i hi t n index (hlo0.trans hlot) hnH hnSlot hvoteHead
  have hdeliver : E.slot_start cfg (t + 1) ≤ q := by
    have ht1le : t + 1 ≤ E.slot_at cfg q :=
      Nat.succ_le_of_lt (htes.trans_lt heslt)
    apply Nat.le_of_not_gt
    intro hqStart
    have hslotLt : E.slot_at cfg q < t + 1 :=
      (E.slot_at_lt_iff cfg hA.whole_seconds hgenTime).2 hqStart
    exact (Nat.not_lt_of_ge ht1le) hslotLt
  obtain ⟨msg, hmsg, htarget⟩ :=
    E.vote_ubiquity cfg ext hA.wellFormed hA.honest_behavior
      hA.synchrony hA.externals_coherence hA.whole_seconds hA.genesis
      hi hv hnSlot hnH hvoteHead hheadKnown hheadWalk hdeliver hqH
  have hmsgEq : msg = lm := by
    rw [hlm] at hmsg
    exact Option.some.inj hmsg.symm
  have hheadStateSlot :
      ((E.store cfg ext i n).block_states
        (get_head cfg (E.store cfg ext i n)).root).slot ≤ t := by
    have hgws : WellFormedStore E.genesis_store := by
      rw [hgeq]
      exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
    have hcore := E.store_wellFormedStoreCore cfg ext
      hA.externals_coherence.state_transition_slot hgws.core i n
    rw [hcore.2 _ hheadKnown]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext
      hA.whole_seconds ⟨ast, ablk, hgeq, hslot⟩ i n _ hheadKnown
    rwa [E.store_current_slot cfg ext i n, hnSlot] at hblockSlot
  have htargetEpoch :
      (honest_attestation cfg ext
        (E.store cfg ext i n) t index i).data.target.epoch =
        compute_epoch_at_slot cfg t :=
    honest_attestation_data_target_epoch cfg ext
      (E.store cfg ext i n) t index
      hA.externals_coherence.process_slots_slot hheadStateSlot
  rw [← htargetEpoch, ← hmsgEq]
  exact htarget

/-- Faithful query supplier for the ledger's recorded-epoch domination.

For a window member `i`, choose its assignment `s ∈ [lo, es]`.  Its honest
post-anchor vote is delivered and therefore has epoch at most the query's
recorded epoch.  A vote at `t < lo` is older than `s`, so its epoch is bounded
by the delivered assignment's epoch; a vote at `lo ≤ t` is covered directly
by post-anchor delivery.  No condition is imposed on pre-anchor
`Execution.vote` values themselves. -/
theorem windowRecordedEpochMax_at_query_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {lo es : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (heslt : es < E.slot_at cfg q) :
    E.WindowRecordedEpochMax cfg ext v q lo es := by
  have hpost := E.postAnchorRecordedEpochMax_at_query_minimal cfg ext
    hA hwalkDomain hv hqH hlo0 hes heslt
  have hesle : es ≤ E.slot_at cfg q := by
    rw [hes, E.store_current_slot cfg ext v q]
    exact Nat.sub_le _ _
  have hesH : E.SlotWithinHorizon cfg es :=
    E.slotWithinHorizon_of_le cfg hesle hqH
  intro i hi hiSpan lm hlm t k a htes hvote
  by_cases hlot : lo ≤ t
  · exact hpost i hi lm hlm t k a hlot htes hvote
  · simp only [Execution.span_committee, Finset.mem_biUnion,
      Finset.mem_Icc] at hiSpan
    obtain ⟨s, ⟨hloS, hsEs⟩, hiS⟩ := hiSpan
    have hsH : E.SlotWithinHorizon cfg s :=
      E.slotWithinHorizon_mono cfg hsEs hesH
    obtain ⟨ns, indexS, hnsH, hnsSlot, hvoteS⟩ :=
      hA.honest_behavior.votes_head i hi s hiS hsH (hlo0.trans hloS)
    have hsDom : compute_epoch_at_slot cfg s ≤ (get_latest_message_epoch cfg lm) :=
      hpost i hi lm hlm s ns
        (honest_attestation cfg ext (E.store cfg ext i ns) s indexS i)
        hloS hsEs hvoteS
    have hts : t ≤ s := (Nat.lt_of_not_ge hlot).le.trans hloS
    exact (Nat.div_le_div_right hts).trans hsDom



/-- A recorded honest supporter belongs to `Sclass`, using domination only
after the supporter's concrete window membership has been established. -/
theorem recorded_supporter_mem_Sclass_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈
          (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {lo es : Slot}
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
        (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀)
          ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀ lo es)
    {i : ValidatorIndex}
    (hiSupp : i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
      (get_node_for_root b') bs)
    (hi : i ∈ E.honest) :
    i ∈ E.Sclass cfg ext v₀ n₀ b' lo es := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hiSupp
  have hsa : lo ≤ ((E.store cfg ext v₀ n₀).blocks b').slot := by
    rw [hlo]
    exact hslotlt
  have hiSpan : i ∈ E.span_committee lo es := by
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hiSupp
      (hwalk i hiSupp) hsa
  obtain ⟨t, k, a, htle, hvote, hnew, hroot⟩ :=
    E.recorded_lm_is_newest cfg ext hhb hec hgen hprov hes hi hlm
      (hdom i hi hiSpan lm hlm)
  simp only [Execution.Sclass, Finset.mem_filter]
  refine ⟨⟨hiSpan, hi⟩, ⟨t, k, a, htle, hvote, hnew, ?_⟩⟩
  rw [hroot]
  simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc

/-- Honest supporter score is bounded by `Sval`, with only window-scoped
recorded-epoch domination. -/
theorem honest_supporters_sum_le_Sval_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈
          (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {lo es : Slot}
    (hval : bs.validators = E.registry)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
        (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀)
          ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀ lo es) :
    (((AttSupporters cfg (E.store cfg ext v₀ n₀)
        (get_node_for_root b') bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      E.Sval cfg ext v₀ n₀ b' lo es := by
  rw [honest_score_eq_weight cfg E hval, Execution.Sval]
  apply E.weight_mono
  intro i hi
  rw [List.mem_toFinset, List.mem_filter] at hi
  exact E.recorded_supporter_mem_Sclass_window cfg ext hhb hec hgen hwf
    hprov hlo hes hslotlt hwalk hdom hi.1 (of_decide_eq_true hi.2)

/-- Parent-stuck honest validators belong to `Aclass`, with domination
specialized only after their parent-support span is widened to `[lo, es]`. -/
theorem ParentStuck_subset_Aclass_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {bs : BeaconState Root} {b' : Root} {lo es : Slot}
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hbcur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hbanc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root
        ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀ lo es) :
    ParentStuck cfg E (E.store cfg ext v₀ n₀) bs b' ⊆
      E.Aclass cfg ext v₀ n₀ b' lo es := by
  intro i hiPS
  simp only [ParentStuck, Finset.mem_filter] at hiPS
  obtain ⟨hPS, hi⟩ := hiPS
  have hspanBase := (mem_ParentSupport cfg hPS).1
  rw [← hlo] at hspanBase
  have hbaseEs :
      ((E.store cfg ext v₀ n₀).blocks b').slot - 1 ≤ es := by
    rw [hes]
    exact Nat.sub_le_sub_right hbcur 1
  have hiSpan : i ∈ E.span_committee lo es :=
    E.span_committee_mono lo hbaseEs hspanBase
  simp only [ParentSupport, Finset.mem_filter] at hPS
  obtain ⟨_, hany⟩ := hPS
  cases hlm : (E.store cfg ext v₀ n₀).latest_messages i with
  | none => rw [hlm] at hany; simp at hany
  | some lm =>
    rw [hlm] at hany
    simp only [Option.any_some, Bool.and_eq_true,
      decide_eq_true_eq] at hany
    obtain ⟨hroot, _⟩ := hany
    obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
      E.recorded_lm_is_newest cfg ext hhb hec hgen hprov hes hi hlm
        (hdom i hi hiSpan lm hlm)
    have habbr : a.data.beacon_block_root =
        ((E.store cfg ext v₀ n₀).blocks b').parent_root := by
      rw [hbbreq]
      exact hroot
    have hparentNotDesc : ¬ is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root
          ((E.store cfg ext v₀ n₀).blocks b').parent_root)
        (get_node_for_root b') = true := by
      simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
      rw [get_ancestor_stop (le_of_lt hslotlt)]
      intro hcon
      have heq : ((E.store cfg ext v₀ n₀).blocks b').parent_root = b' := hcon
      rw [heq] at hslotlt
      exact lt_irrefl _ hslotlt
    simp only [Execution.Aclass, Finset.mem_filter]
    refine ⟨⟨hiSpan, hi⟩, ?_, ?_⟩
    · intro hsd
      obtain ⟨t₁, k₁, a₁, ht1le, hvote1, hnew1, hanc1⟩ := hsd
      have htt : t = t₁ := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnew
        (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
      rw [← htt, hvote] at hvote1
      simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
      obtain ⟨_, ha⟩ := hvote1
      rw [← ha, habbr] at hanc1
      exact hparentNotDesc hanc1
    · exact Or.inr ⟨t, k, a, htle, hvote, hnew,
        by rw [habbr]; exact hbanc⟩

/-- Support discount is bounded by `Aval` using the window-scoped parent-
stuck inclusion. -/
theorem support_discount_le_Aval_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} (hv₀ : v₀ ∈ E.honest) {n₀ : ℕ}
    (hnH : E.WithinHorizon cfg n₀)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀))
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
    (hbcur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hbanc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root
        ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀ lo es) :
    get_support_discount cfg ext (E.store cfg ext v₀ n₀) bs b' ≤
      E.Aval cfg ext v₀ n₀ b' lo es := by
  have hne : ∀ i ∈ (E.store cfg ext v₀ n₀).equivocating_indices,
      i ∉ E.honest :=
    fun i hieq hi =>
      Execution.honest_not_equivocating cfg ext hhb hec hgen hi v₀ n₀ (by assumption) (by assumption) hieq
  refine le_trans (support_discount_le_parent_stuck cfg ext hec hbb hv₀ hnH
    hval (hlo ▸ hloH) hbH htab hne) ?_
  rw [Execution.Aval]
  exact E.weight_mono
    (E.ParentStuck_subset_Aclass_window cfg ext hhb hec hgen hprov hlo hes
      hslotlt hbcur hbanc hdom)

/-- Confirmation-rule base strip with the overbroad all-validator
`RecordedEpochMax` premise replaced by the faithful window-scoped form. -/
theorem weak_base_discharged_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} (hv : v₀ ∈ E.honest) {n₀ : ℕ}
    (hnH : E.WithinHorizon cfg n₀)
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈
          (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    {bs : BeaconState Root} {b' : Root}
    (hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v₀ n₀) bs b' = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀)
        (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀)
          ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (lo es : Slot)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hesH : E.SlotWithinHorizon cfg es)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hbcur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hbanc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root
        ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.WindowRecordedEpochMax cfg ext v₀ n₀ lo es) :
    E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es +
        compute_proposer_score cfg bs + 1 ≤
      E.Sval cfg ext v₀ n₀ b' lo es := by
  have hHsup := E.honest_supporters_sum_le_Sval_window cfg ext hhb hec
    hgen hwf hprov hval hlo hes hslotlt hwalk hdom
  have hdisc := E.support_discount_le_Aval_window cfg ext hhb hec hbb
    hgen hv hnH hprov hval htab hlo hloH hes hslotlt hbcur hbH hbanc hdom
  exact E.weak_base_of_rule cfg ext hhb hec hbb hgen hv hnH hwf hbH hval
    htab hprov hconf hwalk lo es hlo hes hloH hesH hHsup hdisc

/-- Honest sibling confinement with recorded-epoch domination restricted to
the sibling supporter's proved ledger-window membership. -/
theorem honest_sibling_confinement_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo es : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
      (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    (hdom : E.WindowRecordedEpochMax cfg ext w m lo es)
    {i : ValidatorIndex}
    (hiSupp : i ∈ AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root c') bs)
    (hi : i ∈ E.honest) :
    i ∈ E.Xclass cfg ext w m b lo es := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hiSupp
  have hanc' : is_ancestor (E.store cfg ext w m)
      (get_node_for_root lm.root) (get_node_for_root c') = true := by
    simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
  have hiSpan : i ∈ E.span_committee lo es := by
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hiSupp
      (fun lm2 hlm2 =>
        hwalkK c' hc' lm2.root (hlmknown lm2 i hlm2)) hlo
  obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
    E.recorded_lm_is_newest_at cfg ext hhb hec hgen hprov hes hi hlm
      (hdom i hi hiSpan lm hlm)
  have hlmk : lm.root ∈ (E.store cfg ext w m).block_roots :=
    hlmknown lm i hlm
  simp only [Execution.Xclass, Finset.mem_filter]
  refine ⟨⟨hiSpan, hi⟩, ?_, ?_⟩
  · rintro ⟨t1, k1, a1, ht1le, hvote1, hnew1, hanc1⟩
    have htt : t = t1 := newest_vote_unique
      (by rw [hvote]; exact Option.some_ne_none _) hnew
      (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
    rw [← htt, hvote] at hvote1
    simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
    obtain ⟨_, ha⟩ := hvote1
    rw [← ha, hbbreq] at hanc1
    have hlmc : is_ancestor (E.store cfg ext w m)
        (get_node_for_root lm.root) (get_node_for_root c) = true :=
      is_ancestor_trans (a := get_node_for_root lm.root) (b := get_node_for_root b)
          (c := get_node_for_root c) hwf (hwalkK c hc lm.root hlmk)
        (hwalkK c hc b hb) hanc1 hbc
    exact siblings_incompatible hwf hc hc' hh hpc hpc' hne
      (hwalkK c hc lm.root hlmk) (hwalkK c' hc' lm.root hlmk)
      hlmc hanc'
  · rintro (hvoteless | ⟨t1, k1, a1, ht1le, hvote1, hnew1, hanc1⟩)
    · exact absurd (hvoteless t htle)
        (by rw [hvote]; exact Option.some_ne_none _)
    · have htt : t = t1 := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnew
        (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
      rw [← htt, hvote] at hvote1
      simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
      obtain ⟨_, ha⟩ := hvote1
      rw [← ha, hbbreq] at hanc1
      have hbc' : is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root c') = true :=
        is_ancestor_trans hwf (a := get_node_for_root b)
          (b := get_node_for_root lm.root) (c := get_node_for_root c')
          (hwalkK c' hc' b hb) (hwalkK c' hc' lm.root hlmk)
          hanc1 hanc'
      exact siblings_incompatible hwf hc hc' hh hpc hpc' hne
        (hwalkK c hc b hb) (hwalkK c' hc' b hb) hbc hbc'

end Execution

/-! ## Completed-boundary adapters

These theorems keep the existing synchrony supplier useful without making a
completed store (or full map replay) the primary query-store contract.
-/




end FastConfirmation.Spec

end
