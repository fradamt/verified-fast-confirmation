module
public import FastConfirmationProofs.Weak.Certificates.WeakQuorumAccounting
public import FastConfirmationProofs.Weak.Safety.WeakConfirmedDissemination
public import FastConfirmationProofs.Weak.Replay.WeakRulePredicateBridge
public import FastConfirmationProofs.Discount.SelectedMarginConstruction

@[expose] public section

/-!
# Spec / Proof / WeakEndpointClasses

Margin-discharge wave, Stage H: **the endpoint-direct base strip**.

Every ledger class on the weak margin path is read at the *honest endpoint*
`(w, m)`, never at the observer `(obs, q)`.  The observer contributes only two
sums — the weak fresh attestation score and the weak fresh support discount —
and each is placed directly into `Sclass cfg ext w m` / `Aclass cfg ext w m`.

The query-side route (converting an observer-indexed `StoreSval`/`StoreAval`
strip to the endpoint through a `SupportsDesc` transport) does **not** close at
a non-honest observer: transporting `is_ancestor (E.store cfg ext obs q) …` to
`(w, m)` needs the vote root to be known in *both* stores, and an arbitrary
`Sclass cfg ext obs q` member's ground vote root need not be in the observer's
block map at all.  The endpoint-direct strip works precisely because the
observer contributes only the cells it actually recorded, and
`Execution.latestMessageProvenance`'s `hlmKnown` component guarantees
`lm.root ∈ (E.store cfg ext obs q).block_roots` for exactly those.

## Route for the support class (`freshSupporter_mem_endpoint_Sclass`)

1. `Weak.mem_FreshAttSupporters` extracts the recorded, non-equivocating,
   **duty-fresh** cell `lm` whose supported node descends from `b` in the
   observer's own store.
2. `Weak.epoch_le_of_duty_fresh_cell` supplies the `hdom` premise of
   `Execution.recorded_lm_is_newest_in_store` for completed assigned duties.
   The existing observer committee-readback contract and honest duty assignment
   connect the executable check to actual votes. No observer honesty, delivery
   to the observer, or `WindowRecordedEpochMax` is needed.
3. `Execution.recorded_lm_is_newest_in_store` (reused verbatim; it is already
   store-generic and honesty-free) returns the supporter's **ground** newest
   vote `a` through the cutoff, with `a.data.beacon_block_root = lm.root`.
4. `Execution.honest_newest_vote_source_minimal` identifies that ground vote
   with the supporter's own validator-spec head vote in its own store, placing
   `lm.root ∈ (E.store cfg ext i nu).block_roots`; honest→honest
   `NextSlotSynchronyPremises.block_relay` from `i` (never *to* the observer) puts
   `lm.root` at the endpoint.
5. `LatestMessageProvenance`'s knownness component puts `lm.root` in the
   observer's store as well, so `lm.root` is the doubly-known witness
   `Execution.is_ancestor_replay_closed` (`WeakAncestryEndpoint.lean`) needs to
   replay the observer-store ancestry `is_ancestor obs (node lm.root) (node b)`
   at `(w, m)` — with no store containment in either direction.

## Route for the ancestor class (`freshParentStuck_subset_endpoint_Aclass`)

Simpler: the fresh parent-stuck members vote for `b`'s *parent* `a`, and both
class conditions are then read entirely at the endpoint —
`¬ SupportsDesc` because `a` does not descend from `b` there
(`get_ancestor_stop` at `a.slot < b.slot`), and `AncestorOrVoteless` because
`a` is `b`'s parent there (`is_ancestor_of_parent`).  No replay is needed; only
steps 1–3 above are used, to turn the recorded cell into a ground newest vote.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Pure arithmetic core of the store-indexed weak base.  Restated locally:
`SelectedMarginConstruction.queryStore_weak_base_arith` is `private`. -/
private theorem weak_endpoint_base_arith
    {Hsup discount maximum boost s a x B J : ℕ}
    (hsm : maximum + boost + 1 ≤ 2 * Hsup + discount)
    (hHsup : Hsup ≤ s) (hdisc : discount ≤ a)
    (hMS : J + B ≤ maximum) (hpart : J = s + a + x) :
    x + B + boost + 1 ≤ s := by
  omega

/-- Pure arithmetic core of the crossing base charge.  Restated locally:
`CrossingCert.crossing_hbase_arith` is `private`. -/
private theorem weak_crossing_hbase_arith {H B d rhs S : ℕ}
    (h : 2 * (H + B) + d ≥ rhs) (hHS : H ≤ S) :
    2 * S + 2 * B + d ≥ rhs := by
  omega

namespace Weak

/-! ## 1. The counted fresh honest support lands in the endpoint's `Sclass` -/

/-- **A counted (fresh) honest supporter at the observer's store lands in the
HONEST ENDPOINT's support class.**  Delivery runs observer → endpoint through
the supporter's *own* store: freshness gives `hdom`,
`recorded_lm_is_newest_in_store` gives the ground newest vote with
`a.data.beacon_block_root = lm.root`, `honest_newest_vote_source_minimal` puts
`lm.root` in the voter's store, honest→honest `block_relay` puts it at the
endpoint, and `is_ancestor_replay_closed` replays the ancestry with no
containment in either direction. -/
theorem freshSupporter_mem_endpoint_Sclass {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root)
    {lo es : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hloMid : lo ≤ ((E.store cfg ext obs q).blocks b).slot)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    {i : ValidatorIndex}
    (hiFresh : i ∈ FreshAttSupporters cfg ext (E.store cfg ext obs q)
      (get_node_for_root b) bs)
    (hi : i ∈ E.honest) :
    i ∈ E.Sclass cfg ext w m b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparentne⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  obtain ⟨lm, hlm, _hnequiv, hfresh, hanc⟩ := mem_FreshAttSupporters cfg ext hiFresh
  have hiSupp : i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs :=
    mem_AttSupporters_of_mem_fresh cfg ext hiFresh
  -- (i) window membership, from the recorded cell's provenance
  have hiSpan : i ∈ E.span_committee lo es := by
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hiSupp (hwalk i hiSupp) hloMid
  -- (ii) freshness ⇒ the `hdom` premise of the reverse-provenance core
  have hdom : ∀ (t : Slot) (k : ℕ) (att : Attestation Root),
      t ≤ es → E.vote i t = some (k, att) →
      compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg lm :=
    fun t _ _ ht hvote => epoch_le_of_duty_fresh_cell cfg ext hfresh hes ht (by
      rw [hcomm t (E.slotWithinHorizon_of_le cfg (ht.trans (le_of_lt hesq)) hqH)]
      exact hA.honest_behavior.votes_assigned i hi t
        (by rw [hvote]; exact Option.some_ne_none _))
  obtain ⟨t, k, att, htle, hvote, hnew, hroot⟩ :=
    E.recorded_lm_is_newest_in_store cfg ext hA.honest_behavior
      hA.externals_coherence hsched hprov hes hi hlm hdom
  -- (iii) the ground newest vote is the supporter's own head vote in its own store
  have hesH : E.SlotWithinHorizon cfg es :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hesq) hqH
  obtain ⟨nu, index, hnuH, hnuSlot, hdue, hatt, hrootNu⟩ :=
    E.honest_newest_vote_source_minimal cfg ext hA hlo0 hesH hi hiSpan htle hvote hnew
  -- (iv) the signed head reaches the later honest endpoint.
  have hslot_lt : E.slot_at cfg nu < E.slot_at cfg m := by
    rw [hnuSlot]
    exact (lt_of_le_of_lt htle hesq).trans_le hslotQM
  have hheadM := E.honest_head_known_at_later_slot_minimal cfg ext hA
    hi hw hnuH hmH hdue hslot_lt
  have hrootEq : att.data.beacon_block_root =
      (get_head cfg (E.store cfg ext i nu)).root := by
    rw [hatt, honest_attestation_data_eq,
      honest_attestation_data_beacon_block_root]
  have hrootM : att.data.beacon_block_root ∈ (E.store cfg ext w m).block_roots := by
    rw [hrootEq]
    exact hheadM
  -- (v) the same root is known at the observer, by latest-message provenance
  obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
  have hrootQ : att.data.beacon_block_root ∈ (E.store cfg ext obs q).block_roots := by
    rw [hroot]; exact hlmKnown
  -- (vi) replay the observer-store ancestry at the endpoint
  have hancQ : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root att.data.beacon_block_root) (get_node_for_root b) = true := by
    rw [hroot]
    simpa only [is_ancestor_supported_pending, get_node_for_root] using hanc
  have hanchorB : ablk.message.slot ≤ ((E.store cfg ext obs q).blocks b).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne obs q b hbQ
  have hancM : is_ancestor (E.store cfg ext w m)
      (get_node_for_root att.data.beacon_block_root) (get_node_for_root b) = true :=
    E.is_ancestor_replay_closed cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne hanchorB hrootQ hrootM hbQ hancQ
  simp only [Execution.Sclass, Finset.mem_filter]
  exact ⟨⟨hiSpan, hi⟩, ⟨t, k, att, htle, hvote, hnew, hancM⟩⟩

/-- The whole fresh honest supporter sum read at the observer is bounded by the
endpoint's `Sval`: weight of a subset (`fresh_honest_score_eq_weight` +
`Execution.weight_mono`), exactly as `honest_supporters_sum_le_Sval_window`
bounds the strong sum. -/
theorem freshHonestSupport_le_endpoint_Sval {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root)
    {lo es : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hloMid : lo ≤ ((E.store cfg ext obs q).blocks b).slot)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m) :
    (((FreshAttSupporters cfg ext (E.store cfg ext obs q) (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ E.Sval cfg ext w m b lo es := by
  rw [fresh_honest_score_eq_weight cfg ext hval, Execution.Sval]
  apply E.weight_mono
  intro i hi
  rw [List.mem_toFinset, List.mem_filter] at hi
  exact freshSupporter_mem_endpoint_Sclass cfg ext hA hqH hcomm hval hbQ hparentQ hprov
    hsched hwalk hlo0 hloMid hes hesq hw hmH hslotQM hi.1 (of_decide_eq_true hi.2)

/-! ## 2. The fresh discount source lands in the endpoint's `Aclass` -/

/-- **The fresh parent-stuck set at the observer lands in the HONEST ENDPOINT's
ancestor/voteless class.**  `ParentStuck_subset_storeAclass`'s argument with its
`hdom` input replaced by freshness, and both class conditions read at `(w, m)`:
`¬ SupportsDesc` because `b`'s parent does not descend from `b` there, and
`AncestorOrVoteless` because it *is* `b`'s parent there. -/
theorem freshParentStuck_subset_endpoint_Aclass {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {bs : BeaconState Root} {a b : Root}
    (hval : bs.validators = E.registry)
    (haQ : a ∈ (E.store cfg ext obs q).block_roots)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root = a)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    {lo es : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hloLe : lo ≤ ((E.store cfg ext obs q).blocks a).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a) :
    FreshParentStuck cfg ext E (E.store cfg ext obs q) bs b
      ⊆ E.Aclass cfg ext w m b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hpslM : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparentne⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hslotltM : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks b).slot := by
    have hlt := hpslM b hbM (by rw [hparentM]; exact haM)
    rwa [hparentM] at hlt
  have hbcM : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
      (get_node_for_root a) = true :=
    is_ancestor_of_parent hpslM hbM haM hparentM
  have hparentNotDescM : ¬ is_ancestor (E.store cfg ext w m)
      (get_node_for_root a) (get_node_for_root b) = true := by
    simp only [is_ancestor, Bool.and_eq_true, decide_eq_true_eq,
      get_node_for_root]
    rw [get_ancestor_stop (le_of_lt hslotltM)]
    intro hcon
    have hab : a = b := by simpa only using hcon.1
    rw [hab] at hslotltM
    exact lt_irrefl _ hslotltM
  have hbcurQ : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q b hbQ
  have hbaseEs : ((E.store cfg ext obs q).blocks b).slot - 1 ≤ es := by
    rw [hes]
    exact Nat.sub_le_sub_right hbcurQ 1
  intro i hiPS
  simp only [FreshParentStuck, Finset.mem_filter] at hiPS
  obtain ⟨hiFPS, hih⟩ := hiPS
  obtain ⟨hspanBase, _hnequiv, lm, hlm, hlmRoot, hfresh⟩ :=
    mem_FreshParentSupport cfg ext hiFPS
  rw [hparentQ] at hspanBase
  have hiSpan : i ∈ E.span_committee lo es :=
    span_committee_mono_lo hloLe (E.span_committee_mono _ hbaseEs hspanBase)
  have hdom : ∀ (t : Slot) (k : ℕ) (att : Attestation Root),
      t ≤ es → E.vote i t = some (k, att) →
      compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg lm :=
    fun t _ _ ht hvote => epoch_le_of_duty_fresh_cell cfg ext hfresh hes ht (by
      rw [hcomm t (E.slotWithinHorizon_of_le cfg (ht.trans (le_of_lt hesq)) hqH)]
      exact hA.honest_behavior.votes_assigned i hih t
        (by rw [hvote]; exact Option.some_ne_none _))
  obtain ⟨t, k, att, htle, hvote, hnew, hattRoot⟩ :=
    E.recorded_lm_is_newest_in_store cfg ext hA.honest_behavior
      hA.externals_coherence hsched hprov hes hih hlm hdom
  have hrootA : att.data.beacon_block_root = a :=
    hattRoot.trans (hlmRoot.trans hparentQ)
  simp only [Execution.Aclass, Finset.mem_filter]
  refine ⟨⟨hiSpan, hih⟩, ?_, ?_⟩
  · rintro ⟨t₁, k₁, att₁, ht1le, hvote1, hnew1, hdesc⟩
    have htt : t = t₁ := newest_vote_unique
      (by rw [hvote]; exact Option.some_ne_none _) hnew
      (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
    rw [← htt, hvote] at hvote1
    simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
    obtain ⟨_, hattEq⟩ := hvote1
    rw [← hattEq, hrootA] at hdesc
    exact hparentNotDescM hdesc
  · exact Or.inr ⟨t, k, att, htle, hvote, hnew, by rw [hrootA]; exact hbcM⟩

/-- **The weak support discount is charged against the endpoint's `Aval`.**
`support_discount_le_fresh_parent_stuck_of_prefix` (the fresh, equivocation-free
discount bound) composed with the endpoint class placement above. -/
theorem support_discount_le_endpoint_Aval {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {bs : BeaconState Root} {a b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (haQ : a ∈ (E.store cfg ext obs q).block_roots)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root = a)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    {lo es : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hloLe : lo ≤ ((E.store cfg ext obs q).blocks a).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a) :
    Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b
      ≤ E.Aval cfg ext w m b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hpslQ : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparentne⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hslotltQ : ((E.store cfg ext obs q).blocks a).slot <
      ((E.store cfg ext obs q).blocks b).slot := by
    have hlt := hpslQ b hbQ (by rw [hparentQ]; exact haQ)
    rwa [hparentQ] at hlt
  have hbcurQ : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q b hbQ
  have hbH : E.SlotWithinHorizon cfg ((E.store cfg ext obs q).blocks b).slot := by
    rw [E.store_current_slot cfg ext obs q] at hbcurQ
    exact E.slotWithinHorizon_of_le cfg hbcurQ hqH
  have hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks b).parent_root).slot + 1) := by
    refine E.slotWithinHorizon_mono cfg
      (b := ((E.store cfg ext obs q).blocks b).slot) ?_ hbH
    rw [hparentQ]
    exact hslotltQ
  refine le_trans (support_discount_le_fresh_parent_stuck_of_prefix cfg ext
    hA.byzantine_bound hcomm hval hstartH hbH htab) ?_
  rw [Execution.Aval]
  exact E.weight_mono
    (freshParentStuck_subset_endpoint_Aclass cfg ext hA hqH hcomm hval haQ hbQ hparentQ
      hprov hsched hlo0 hloLe hes hesq hw hmH hslotQM haM hbM hparentM)

/-! ## 3. The weak-native base strip, read entirely at the honest endpoint -/

/-- **The weak-native base strip, read entirely at the honest endpoint.**
This is the rule-delta-3 payoff: no observer honesty, no synchrony to the
observer, no delivery to the observer, no `WindowRecordedEpochMax`, no
ground-vote replay premise.  The only observer-side inputs are the boolean
`Weak.is_one_confirmed` and the store-generic committee readback. -/
theorem base_strip_of_confirmed_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext obs)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {query : FastConfirmationStore Root}
    (hstore : query.store = E.store cfg ext obs q)
    {b : Root}
    (hb : b ∈ (E.store cfg ext obs q).block_roots)
    (hp : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hconf : Weak.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    {lo es : Slot}
    (hlo : lo = ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m) (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (haM : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root =
      ((E.store cfg ext obs q).blocks b).parent_root) :
    E.Xval cfg ext w m b lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext w m b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconfQ : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true := by
    simpa only [bs, hstore] using hconf
  have hconfStrong : Spec.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true :=
    Spec.is_one_confirmed_of_weak cfg ext _ _ _ hconfQ
  -- balance-source facts, through the strong rule predicate
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hstore]
  have hkey : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp b
    rw [← hbsEq]
    exact hconfStrong
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen obs q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen obs q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  -- store-side geometry at the observer
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparentne⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hprov := E.latestMessageProvenance_of_observer_validity cfg ext hA.wellFormed
    obs hvalid hgen q
  rw [← E.store_current_slot cfg ext obs q] at hprov
  have hsched : SchedLMProv E cfg (E.store cfg ext obs q) :=
    E.schedLMProv cfg ext hgen obs q
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparentne⟩ obs q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hslotlt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot := hwf b hb hp
  have hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q b hb
  have hbH : E.SlotWithinHorizon cfg ((E.store cfg ext obs q).blocks b).slot := by
    have hbcur' := hbcur
    rw [E.store_current_slot cfg ext obs q] at hbcur'
    exact E.slotWithinHorizon_of_le cfg hbcur' hqH
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext obs q)) := by
    rw [E.store_current_slot cfg ext obs q]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hqH
  have hloH : E.SlotWithinHorizon cfg lo := by
    refine E.slotWithinHorizon_mono cfg
      (b := ((E.store cfg ext obs q).blocks b).slot) ?_ hbH
    rw [hlo]
    exact hslotlt
  have hesH : E.SlotWithinHorizon cfg es := by
    refine E.slotWithinHorizon_mono cfg
      (b := get_current_slot cfg (E.store cfg ext obs q)) ?_ hcurH
    rw [hes]
    exact Nat.sub_le _ _
  -- the cutoff precedes the query slot (from the confirmed past descendant)
  have hesq : es < E.slot_at cfg q := by
    obtain ⟨_, _, _, _, _, hnuq, _, _, _⟩ :=
      E.confirmed_pastDescendant_at_observer cfg ext hA obs q hvalid hcomm query hstore b
        hqH hb hp (by rw [hstore]; exact hconfStrong)
    have hqpos : 0 < E.slot_at cfg q := lt_of_le_of_lt (Nat.zero_le _) hnuq
    rw [hes, E.store_current_slot cfg ext obs q]
    exact Nat.sub_lt hqpos Nat.one_pos
  -- the window's lower end is at or after the anchor
  have hlo0 : E.slot_at cfg 0 ≤ lo := by
    have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
      have ht := E.store_current_slot cfg ext obs 0
      rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
        get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
      rw [← ht, hslot]
    have hanchorP : ablk.message.slot ≤ ((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks b).parent_root).slot :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hslot hparentne obs q _ hp
    rw [hcur0, hlo]
    exact hanchorP.trans (Nat.le_succ _)
  -- the two endpoint-class bounds
  have hHsup := freshHonestSupport_le_endpoint_Sval cfg ext hA hqH hcomm hval hb hp hprov
    hsched hwalk hlo0 (by rw [hlo]; exact hslotlt) hes hesq hw hmH hslotQM
  have hdisc := support_discount_le_endpoint_Aval cfg ext hA hqH hcomm hval htab
    hp hb rfl hprov hsched hlo0 (by rw [hlo]) hes hesq hw hmH hslotQM haM hbM hparentM
  -- the observer-side majority, the budget charge and the partition
  have hsm := honest_support_majority_at_observer cfg ext hA.byzantine_bound hwf
    hval htab hbH hcurH hprov hconfQ hwalk
  rw [htab] at hsm
  rw [← hlo, ← hes] at hsm
  have hsplit : E.weight (E.span_committee lo es) = E.Jspec lo es + E.Bval lo es := by
    rw [Execution.Jspec, Execution.Bval, Execution.Bwin]
    exact E.weight_split_honest _
  have hMS := hA.byzantine_bound.estimate_sound lo es hloH hesH
  rw [hsplit] at hMS
  have hpart := E.weight_partition cfg ext w m b lo es
  -- proposer boost read at the endpoint
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  rw [← hboost]
  exact weak_endpoint_base_arith hsm hHsup hdisc hMS hpart

/-- **Weak, endpoint-anchored twin of `crossing_hbase_of_confirmed_window`.**
`hdom` is gone (freshness replaces it) and there is no base transport: the
honest support charge is already read at `(w, m)`. -/
theorem crossing_hbase_of_confirmed_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root)
    (hconf : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true)
    {es : Slot} (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hbM : b ∈ (E.store cfg ext w m).block_roots) :
    2 * E.Sval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es
        + 2 * (((FreshAttSupporters cfg ext (E.store cfg ext obs q)
              (get_node_for_root b) bs).filter (fun i => i ∉ E.honest)).map
            (fun i => (bs.validators.getD i default).effective_balance)).sum
        + Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (((E.store cfg ext obs q).blocks
            ((E.store cfg ext obs q).blocks b).parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext obs q) - 1)
        + compute_proposer_score cfg bs
        + 2 * Weak.get_adversarial_weight cfg (E.store cfg ext obs q) bs b + 1 := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext obs 0
    rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
    rw [← ht, hslot]
  have hlo0 : E.slot_at cfg 0 ≤ ((E.store cfg ext obs q).blocks b).slot := by
    rw [hcur0]
    exact E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne obs q b hbQ
  have hineq := is_one_confirmed_ineq cfg ext hconf
  rw [fresh_attestation_score_honest_split cfg ext E (E.store cfg ext obs q)
    (get_node_for_root b) bs] at hineq
  have hhonest := freshHonestSupport_le_endpoint_Sval cfg ext hA hqH hcomm hval hbQ
    hparentQ hprov hsched hwalk hlo0 (le_refl _) hes hesq hw hmH hslotQM
  exact weak_crossing_hbase_arith hineq hhonest

end Weak

end FastConfirmation.Spec

end
