module
public import FastConfirmationProofs.FFG.Certificates.QuorumAccounting
public import FastConfirmationProofs.Execution.Delivery.Registry
public import FastConfirmationProofs.Execution.StoreInvariants.StoreInvariants
public import FastConfirmationProofs.Execution.StoreInvariants.ValidationStateReachability

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / HonestWeight

`Proof/QuorumAccounting.lean` derives `honest_support_majority_of_byz_le` from
the Byzantine bound

`byz_score ≤ get_adversarial_weight`.

This module proves that bound and derives
`honest_support_majority`. The four steps mirror the `HonestWeight` spec:

* **Step 1** (`Execution.honest_not_equivocating`): a trajectory invariant —
  no honest validator ever appears in an honest node's `equivocating_indices`.
  Genesis has an empty set (`get_forkchoice_store`); only `on_attester_slashing`
  adds, and inverting it against `HonestBehavior.not_slashable` /
  `BeaconExternalsPremises.valid_attestation_honest` shows an honest validator is
  never among the added intersection.
* **Step 2** (`get_equivocation_score_eq_weight`): the equivocation score over an
  honest store's balance source equals the ground-truth `E.weight` of the
  active equivocating span members (registry constancy + `committees_agree`).
* **Step 3** (`byz_plus_equiv_le`): the Byzantine supporters and the equivocating
  span members are *disjoint* subsets of the non-honest span committee (Step 1
  places equivocators outside the honest set; supporters are non-equivocating by
  the score's own filter), so their combined weight is within
  `estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD` (`ByzantineWeightPremises.span_bound`).
* **Step 4** (`byz_score_le_adversarial_weight`, `honest_support_majority`): the
  arithmetic assembly — `byz + equiv ≤ max_adv` gives `byz ≤ compute_adversarial_weight`
  (= `get_adversarial_weight`), discharging `honest_support_majority_of_byz_le`'s
  hypothesis.

No new behavioral assumptions enter beyond the existing records
(`HonestBehavior`, `BeaconExternalsPremises`, `ByzantineWeightPremises`) and the sanctioned
`∃`-genesis form.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-! ## Step 1 — no honest validator equivocates

Only `on_attester_slashing` grows `equivocating_indices`; every other handler
leaves it untouched. We first record those field-preservation facts (mirroring
`Proof/Provenance.lean`'s `latest_messages` versions), then invert the slashing
handler. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The `update_latest_messages` fold only rewrites `latest_messages`, so it
leaves `equivocating_indices` fixed. -/
private theorem update_lm_foldl_equiv (slot : Slot) (beacon : Root) (payload_present : Bool) :
    ∀ (l : List ValidatorIndex) (s : Store Root),
      (l.foldl (fun st j =>
        if (match st.latest_messages j with
            | none => true
            | some lm => decide (slot > lm.slot)) then
          { st with latest_messages :=
              Function.update st.latest_messages j (some (LatestMessage.mk slot beacon payload_present)) }
        else st) s).equivocating_indices = s.equivocating_indices := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons j l ih =>
    intro s
    rw [List.foldl_cons, ih]
    split_ifs <;> rfl

omit [LinearOrder Root] [Inhabited Root] in
theorem update_latest_messages_equiv (store : Store Root)
    (attesting_indices : List ValidatorIndex) (a : Attestation Root) :
    (update_latest_messages store attesting_indices a).equivocating_indices =
      store.equivocating_indices := by
  simp only [update_latest_messages]
  exact update_lm_foldl_equiv a.data.slot a.data.beacon_block_root (decide (a.data.index = 1)) _ store

omit [Inhabited Root] in
theorem record_block_timeliness_equiv (store : Store Root) (root : Root) :
    (record_block_timeliness cfg store root).equivocating_indices =
      store.equivocating_indices := rfl

theorem update_proposer_boost_root_equiv (store : Store Root) (head root : Root) :
    (update_proposer_boost_root cfg store head root).equivocating_indices =
      store.equivocating_indices := by
  simp only [update_proposer_boost_root]; split_ifs <;> rfl

omit [Inhabited Root] in
theorem store_target_checkpoint_state_equiv (store : Store Root) (target : Checkpoint Root) :
    (store_target_checkpoint_state cfg ext store target).equivocating_indices =
      store.equivocating_indices := by
  simp only [store_target_checkpoint_state]; split_ifs <;> rfl

omit [Inhabited Root] in
theorem compute_pulled_up_tip_equiv (store : Store Root) (block_root : Root) :
    (compute_pulled_up_tip cfg ext store block_root).equivocating_indices =
      store.equivocating_indices := by
  simp only [compute_pulled_up_tip]; split_ifs <;> simp

omit [LinearOrder Root] in
theorem on_tick_per_slot_equiv (store : Store Root) (time : ℕ) :
    (on_tick_per_slot cfg store time).equivocating_indices = store.equivocating_indices := by
  simp only [on_tick_per_slot]; split_ifs <;> simp

omit [LinearOrder Root] in
theorem on_tick_aux_equiv (tick_slot fuel : ℕ) (store : Store Root) :
    (on_tick_aux cfg tick_slot fuel store).equivocating_indices =
      store.equivocating_indices := by
  induction fuel generalizing store with
  | zero => rfl
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · rw [ih, on_tick_per_slot_equiv]
    · rfl

omit [LinearOrder Root] in
theorem on_tick_equiv (store : Store Root) (time : ℕ) :
    (on_tick cfg store time).equivocating_indices = store.equivocating_indices := by
  simp only [on_tick]; rw [on_tick_per_slot_equiv, on_tick_aux_equiv]

theorem on_block_equiv {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (h : on_block cfg ext store sb = some store') :
    store'.equivocating_indices = store.equivocating_indices := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [on_block, if_pos hknown] at h
    cases h
    rfl
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h <;> try cases h
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at h; cases h
    | some state =>
      rw [hst] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i notified hnotify
        cases h
        rw [compute_pulled_up_tip_equiv, update_checkpoints_equivocating_indices,
          update_proposer_boost_root_equiv, record_block_timeliness_equiv]
        exact (notify_ptc_messages_frame cfg ext hnotify).equivocating_indices

omit [Inhabited Root] in
theorem on_attestation_equiv {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool}
    (h : on_attestation cfg ext store a ifb = some store') :
    store'.equivocating_indices = store.equivocating_indices := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  rw [update_latest_messages_equiv, store_target_checkpoint_state_equiv]

/-- Inverting `on_attester_slashing` at an honest validator: an honest `v` is
never among the added (equivocating) intersection. Both attestations validate
(handler guards) so, by `valid_attestation_honest`, they carry `v`'s own vote
data; `not_slashable` then contradicts the handler's slashable guard. -/
theorem on_attester_slashing_honest_not_added {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    {store store' : Store Root} {asl : AttesterSlashing Root}
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (hcausal : E.HonestPrefixStoreWithinHorizon cfg ext store)
    (hunknown : UnknownBlockStatesDefault store)
    (hh : on_attester_slashing ext store asl = some store')
    (hprev : v ∉ store.equivocating_indices) :
    v ∉ store'.equivocating_indices := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh with hslash hv1 hv2
  cases hh
  simp only [Finset.mem_union, Finset.mem_inter, List.mem_toFinset, not_or, not_and]
  refine ⟨hprev, fun hv1' hv2' => ?_⟩
  have hs1 : ext.is_valid_indexed_attestation
      (store.block_states store.justified_checkpoint.root) asl.attestation_1 = true := by
    simpa using hv1
  have hs2 : ext.is_valid_indexed_attestation
      (store.block_states store.justified_checkpoint.root) asl.attestation_2 = true := by
    simpa using hv2
  have hknown : store.justified_checkpoint.root ∈ store.block_roots := by
    by_contra hnot
    rw [hunknown _ hnot, hec.valid_attestation_default] at hs1
    contradiction
  have hstate := hcausal.blockState cfg ext hknown
  obtain ⟨m1, c1, hvote1, hdata1⟩ :=
    hec.valid_attestation_honest _ asl.attestation_1 hstate hs1 v hv hv1'
  obtain ⟨m2, c2, hvote2, hdata2⟩ :=
    hec.valid_attestation_honest _ asl.attestation_2 hstate hs2 v hv hv2'
  have hns := hhb.not_slashable v hv asl.attestation_1.data.slot asl.attestation_2.data.slot
    m1 m2 c1 c2 hvote1 hvote2
  have hslash' : is_slashable_attestation_data asl.attestation_1.data asl.attestation_2.data
      = true := by simpa using hslash
  rw [hdata1, hdata2, hns] at hslash'
  simp at hslash'

/-- One dispatched event preserves "honest `v` is not equivocating": block and
attestation events leave `equivocating_indices` fixed; attester slashings ride
across by `on_attester_slashing_honest_not_added`. -/
theorem apply_event_honest_not_equiv {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (store : Store Root) (e : Event Root) (hprev : v ∉ store.equivocating_indices)
    (hcausal : E.HonestPrefixStoreWithinHorizon cfg ext store)
    (hunknown : UnknownBlockStatesDefault store) :
    v ∉ ((apply_event cfg ext store e).getD store).equivocating_indices := by
  cases e with
  | block b =>
    simp only [apply_event]
    cases hb : on_block cfg ext store b with
    | none => simpa using hprev
    | some s' =>
      simp only [Option.getD_some]; rw [on_block_equiv cfg ext hb]; exact hprev
  | attestation a ifb =>
    simp only [apply_event]
    cases ha : on_attestation cfg ext store a ifb with
    | none => simpa using hprev
    | some s' =>
      simp only [Option.getD_some]; rw [on_attestation_equiv cfg ext ha]; exact hprev
  | attester_slashing asl =>
    simp only [apply_event]
    cases has : on_attester_slashing ext store asl with
    | none => simpa using hprev
    | some s' =>
      simp only [Option.getD_some]
      exact on_attester_slashing_honest_not_added cfg ext hhb hec hv
        hcausal hunknown has hprev
  | execution_payload_envelope envelope observation =>
    simp only [apply_event]
    cases he : on_execution_payload_envelope ext store envelope observation with
    | none => exact hprev
    | some next =>
      simp only [Option.getD_some]
      rw [(on_execution_payload_envelope_frame ext he).equivocating_indices]
      exact hprev
  | payload_attestation_message message fromBlock =>
    simp only [apply_event]
    cases he : on_payload_attestation_message cfg ext store message fromBlock with
    | none => exact hprev
    | some next =>
      simp only [Option.getD_some]
      rw [(on_payload_attestation_message_frame cfg ext he).equivocating_indices]
      exact hprev

/-- Folding a second's events preserves non-equivocation when each exact
prefix belongs to an honest node inside the horizon. -/
theorem honest_not_equiv_foldl {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    ∀ (l : List (Event Root)) (s : Store Root), v ∉ s.equivocating_indices →
      UnknownBlockStatesDefault s →
      (∀ k, k ≤ l.length → E.HonestPrefixStoreWithinHorizon cfg ext
        ((l.take k).foldl
          (fun store event => (apply_event cfg ext store event).getD store) s)) →
      v ∉ (l.foldl (fun store e => (apply_event cfg ext store e).getD store)
        s).equivocating_indices := by
  intro l
  induction l with
  | nil => intro s hs _ _; exact hs
  | cons e l ih =>
    intro s hs hunknown hcausal
    rw [List.foldl_cons]
    refine ih _ ?_ (apply_event_unknownBlockStatesDefault cfg ext s e hunknown) ?_
    · exact apply_event_honest_not_equiv cfg ext hhb hec hv s e hs
        (by simpa using hcausal 0 (Nat.zero_le _)) hunknown
    · intro k hk
      simpa only [List.take_succ_cons, List.foldl_cons] using
        hcausal (k + 1) (by simpa using Nat.succ_le_succ hk)

/-- No honest validator is marked equivocating at an honest node inside the
verification horizon. Genesis starts empty; each scheduled prefix supplies
its keyed validation-state reachability. -/
theorem Execution.honest_not_equivocating {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) (w : ValidatorIndex) (n : ℕ)
    (hw : w ∈ E.honest) (hn : E.WithinHorizon cfg n) :
    v ∉ (E.store cfg ext w n).equivocating_indices := by
  revert hn
  induction n with
  | zero =>
    intro hn
    obtain ⟨ast, ablk, hg⟩ := hgen
    have h0 : E.store cfg ext w 0 = E.genesis_store := rfl
    rw [h0, hg]
    simp [get_forkchoice_store]
  | succ n ih =>
    intro hn
    change v ∉ ((E.schedule w (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))).equivocating_indices
    refine honest_not_equiv_foldl cfg ext hhb hec hv _ _ ?_ ?_ ?_
    · rw [on_tick_equiv]
      exact ih (E.withinHorizon_mono cfg (Nat.le_succ n) hn)
    · exact on_tick_unknownBlockStatesDefault cfg _ _
        (E.unknownBlockStatesDefault_store cfg ext hgen w n)
    · intro k hk
      exact E.honestCausalStore_prefix cfg ext w hw n hn
        ((E.schedule w (n + 1)).take k) ((E.schedule w (n + 1)).drop k)
        (List.take_append_drop k _).symm

/-! ## Step 2 — the equivocation score is ground-truth span weight

At an honest node the store-computed slot committees agree with the ground-truth
assignment (`committees_agree`), so `get_equivocation_score`'s participant set is
`E.span_committee`; and registry constancy (`hval`) turns the balance-source
effective balances into `E.weight_of`. Hence the score equals the ground-truth
weight of the **active equivocating span members**. -/

/-- The active equivocating members of the span `[sa, es]`: the span committee's
equivocating validators that are active under the balance source. -/
def EquivActive (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (sa es : Slot) : Finset ValidatorIndex :=
  (E.span_committee sa es ∩ store.equivocating_indices).filter (fun i =>
    is_active_validator (bs.validators.getD i default) (get_current_epoch cfg bs))

/-- Step 2: at an honest node `(v, n)` on a registry-constant balance source, the
equivocation score of the span `[sa, es]` equals the ground-truth weight of the
active equivocating span members. -/
theorem get_equivocation_score_eq_weight {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest) (n : ℕ)
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} (hval : bs.validators = E.registry) (sa es : Slot)
    (hesH : E.SlotWithinHorizon cfg es) :
    get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es =
      E.weight (EquivActive cfg E (E.store cfg ext v n) bs sa es) := by
  have hce : (Finset.Icc sa es).biUnion
        (fun slot => get_slot_committee cfg ext (E.store cfg ext v n) slot) =
      (Finset.Icc sa es).biUnion E.committee := by
    apply Finset.biUnion_congr rfl
    intro slot hslot
    exact hec.committees_agree v hv n slot hnH
      ⟨(le_trans (Finset.mem_Icc.mp hslot).2 hesH.1),
        lt_of_le_of_lt
          (Nat.div_le_div_right (Finset.mem_Icc.mp hslot).2) hesH.2⟩
  simp only [get_equivocation_score, EquivActive, Execution.weight, Execution.weight_of,
    Execution.span_committee, hce]
  exact Finset.sum_congr rfl (fun i _ => by rw [hval])

/-! ## Step 3 — the Byzantine supporters and equivocators are disjoint

The Byzantine supporters (`AttSupporters ∩ non-honest`) and the active
equivocators (`EquivActive`) are *disjoint* — supporters are non-equivocating by
`AttSupporters`' own filter, equivocators are equivocating — and both sit inside
the non-honest span committee (supporters by `hspan`; equivocators by Step 1,
`hne`). So their combined ground-truth weight is within `ByzantineWeightPremises.span_bound`. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Weight is superadditive-into a common superset over disjoint parts. -/
private theorem weight_add_le {E : Execution Root} {A B C : Finset ValidatorIndex}
    (hdisj : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    E.weight A + E.weight B ≤ E.weight C := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAC hBC)
    (fun _ _ _ => Nat.zero_le _)

omit [Inhabited Root] in
/-- The Byzantine-supporter list sum equals the ground-truth weight of its
`toFinset` (registry constancy + the supporter list's `Nodup`). -/
theorem byz_score_eq_weight {E : Execution Root} {store : Store Root} {bs : BeaconState Root}
    {b : Root} (hval : bs.validators = E.registry) :
    (((AttSupporters cfg store (get_node_for_root b) bs).filter (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum =
      E.weight (((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset) := by
  have hLnodup : ((AttSupporters cfg store (get_node_for_root b) bs).filter
      (fun i => i ∉ E.honest)).Nodup := (AttSupporters_nodup cfg store _ bs).filter _
  have hmap : ((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map (fun i => (bs.validators.getD i default).effective_balance)
      = ((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  rw [hmap]
  exact (List.sum_toFinset E.weight_of hLnodup).symm

/-- Step 3: at an honest node with no honest equivocators (`hne`, Step 1) and the
supporters confined to the span (`hspan`), the Byzantine supporters' weight plus
the equivocation score of `[sa, es]` is within
`estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`. -/
theorem byz_plus_equiv_le {E : Execution Root} (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E) {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    {sa es : Slot}
    (hsaH : E.SlotWithinHorizon cfg sa) (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es
      ≤ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) sa es
          / 100 * cfg.confirmation_byzantine_threshold := by
  rw [byz_score_eq_weight cfg hval,
    get_equivocation_score_eq_weight cfg ext hec hv n hnH hval sa es hesH, htab]
  set BS := ((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
    (fun i => i ∉ E.honest)).toFinset with hBS
  set EA := EquivActive cfg E (E.store cfg ext v n) bs sa es with hEA
  refine weight_add_le ?_ ?_ ?_ |>.trans (hbb.span_bound sa es hsaH hesH)
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [hBS, List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨lm, _, hnoteq, _⟩ := mem_AttSupporters cfg hiBS.1
    simp only [hEA, EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnoteq hiEA.1.2
  · intro i hi
    simp only [hBS, List.mem_toFinset, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  · intro i hi
    simp only [hEA, EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-! ## Step 4 — the unconditional honest-support majority

`get_adversarial_weight` is `compute_adversarial_weight` over the span
`[sa, current_slot − 1]`, i.e. `max_adv − equiv_score` (guarded). Step 3 bounds
`byz + equiv_score ≤ max_adv`, so `byz ≤ get_adversarial_weight` — the missing
hypothesis of `honest_support_majority_of_byz_le`. Composing them delivers the
unconditional `honest_support_majority`. -/

/-- Pure `ℕ` core: `byz + equiv ≤ max_adv` gives `byz` within the
`compute_adversarial_weight` guard (both branches). -/
private theorem byz_le_adv_arith {byz equiv max_adv : ℕ} (h : byz + equiv ≤ max_adv) :
    byz ≤ if max_adv > equiv then max_adv - equiv else 0 := by
  split_ifs <;> omega

omit [LinearOrder Root] [Inhabited Root] in
/-- The start slot of a block's epoch is at most the block's slot. -/
theorem start_slot_at_block_epoch_le (store : Store Root) (b : Root) :
    compute_start_slot_at_epoch cfg (get_block_epoch cfg store b) ≤ (store.blocks b).slot := by
  simp only [get_block_epoch, compute_epoch_at_slot, compute_start_slot_at_epoch]
  exact Nat.div_mul_le_self _ _

/-- Step 4a: the Byzantine supporters' weight is within `get_adversarial_weight`.
The `get_adversarial_weight` span start is at or below `b`'s slot in both
branches (`start_slot_at_block_epoch_le`), so `supporter_mem_span_committee`
confines every non-honest supporter to it; Step 3 then bounds
`byz + equiv ≤ max_adv`, and the guard arithmetic gives `byz ≤ get_adversarial_weight`. -/
theorem byz_score_le_adversarial_weight {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈ (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    {bs : BeaconState Root} {b : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b := by
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest := by
    intro i hi hih
    exact Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n hv hnH hi
  have hsa : (if get_block_epoch cfg (E.store cfg ext v n) b >
        get_block_epoch cfg (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
      else ((E.store cfg ext v n).blocks b).slot) ≤ ((E.store cfg ext v n).blocks b).slot := by
    split_ifs
    · exact start_slot_at_block_epoch_le cfg (E.store cfg ext v n) b
    · exact le_refl _
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest →
      i ∈ E.span_committee
        (if get_block_epoch cfg (E.store cfg ext v n) b >
            get_block_epoch cfg (E.store cfg ext v n)
              ((E.store cfg ext v n).blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
          else ((E.store cfg ext v n).blocks b).slot)
        (get_current_slot cfg (E.store cfg ext v n) - 1) :=
    fun i hi _ => supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) hsa
  have hstartH : E.SlotWithinHorizon cfg
      (if get_block_epoch cfg (E.store cfg ext v n) b >
          get_block_epoch cfg (E.store cfg ext v n)
            ((E.store cfg ext v n).blocks b).parent_root then
          compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
        else ((E.store cfg ext v n).blocks b).slot) :=
    ⟨hsa.trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hsa) hbH.2⟩
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact ⟨hnH.2.1, hnH.2.2⟩
  have hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1) :=
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
  rw [get_adversarial_weight_eq]
  exact byz_le_adv_arith
    (byz_plus_equiv_le cfg ext hec hbb hv hnH hval htab hne hstartH hendH hspan)

/-- **Step 4 (headline).** The unconditional spec-side Lemma 3∘4: at an honest
node `(v, n)` with a confirmed block `b` (`is_one_confirmed = true`), twice the
HONEST supporters' weight plus the support discount dominates `maximum_support +
proposer_score + 1`. This closes `QuorumAccounting`'s obligation: the Byzantine bound
(`byz ≤ get_adversarial_weight`, `byz_score_le_adversarial_weight`) is now
discharged from the assumption records, so no `hbyz` hypothesis remains. -/
theorem honest_support_majority {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈ (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    {bs : BeaconState Root} {b : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root) :
    2 * (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext v n) - 1)
        + compute_proposer_score cfg bs + 1 :=
  honest_support_majority_of_byz_le cfg ext hconf
    (byz_score_le_adversarial_weight cfg ext hhb hec hbb hgen hv hnH hwf hbH
      hval htab hprov hwalk)

end FastConfirmation.Spec

end
