module
public import FastConfirmation.Spec.Proof.ArbitraryQueryMargin
public import FastConfirmation.Spec.Proof.RecordedEpochSupplier

@[expose] public section

/-!
# Concrete constructors for arbitrary-query selected margins

This module starts discharging the fields of `SelectedMarginSupplyAt` from the
actual confirmation query.  In particular, the confirmation-time margin strip
does not require the broad `JustificationInterface`: the selected-margin domain
already supplies the endpoint's cached justified state, and static-validator
coherence is enough to reconcile proposer boost.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Pure arithmetic core of the store-indexed weak base. -/
private theorem queryStore_weak_base_arith
    {Hsup discount maximum boost s a x B J : ℕ}
    (hsm : maximum + boost + 1 ≤ 2 * Hsup + discount)
    (hHsup : Hsup ≤ s) (hdisc : discount ≤ a)
    (hMS : J + B ≤ maximum) (hpart : J = s + a + x) :
    x + B + boost + 1 ≤ s := by
  omega

namespace Execution

variable (E : Execution Root)

/-! ## Base strip at the exact query store -/

/-- Store-local evidence needed in addition to recorded-epoch domination for
the confirmation base.  The two accounting fields are intentionally explicit:
the current execution-store theorems derive them from trajectory facts, while
an action-prefix adapter must establish them for its exact store.

No equality with `E.store v q` appears in this structure. -/
structure QueryStoreBaseStripEvidence
    (queryStore : Store Root) (bs : BeaconState Root)
    (b : Root) (lo es : Slot) : Prop where
  block_known : b ∈ queryStore.block_roots
  parent_known : (queryStore.blocks b).parent_root ∈ queryStore.block_roots
  parent_slot_lt : ParentSlotLt queryStore
  block_slot_le_current : (queryStore.blocks b).slot ≤
    get_current_slot cfg queryStore
  block_horizon : E.SlotWithinHorizon cfg (queryStore.blocks b).slot
  lo_horizon : E.SlotWithinHorizon cfg lo
  es_horizon : E.SlotWithinHorizon cfg es
  lo_eq : lo = (queryStore.blocks (queryStore.blocks b).parent_root).slot + 1
  cutoff_eq : es = get_current_slot cfg queryStore - 1
  balance_validators : bs.validators = E.registry
  total_active : get_total_active_balance cfg bs = E.total_active cfg
  scheduled_provenance : SchedLMProv E cfg queryStore
  latest_message_provenance : LatestMessageProvenance E cfg
    (get_current_slot cfg queryStore) queryStore
  supporter_walk : ∀ i ∈ AttSupporters cfg queryStore
      (get_node_for_root b) bs, ∀ lm,
    queryStore.latest_messages i = some lm →
      WalkKnown queryStore (queryStore.blocks b).slot lm.root
  confirmation : is_one_confirmed cfg ext queryStore bs b = true
  byzantine_support_le_adversarial :
    (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      get_adversarial_weight cfg ext queryStore bs b
  support_discount_le_parent_stuck :
    get_support_discount cfg ext queryStore bs b ≤
      E.weight (ParentStuck cfg E queryStore bs b)

/-- A recorded honest supporter at the exact query store belongs to its
store-indexed supporting class. -/
theorem recorded_supporter_mem_storeSclass
    (hA : SelectedMarginAssumptions cfg ext E)
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hdom : PrefixWindowRecordedEpochMax cfg E queryStore lo es)
    {i : ValidatorIndex}
    (hiSupp : i ∈ AttSupporters cfg queryStore (get_node_for_root b) bs)
    (hi : i ∈ E.honest) :
    i ∈ E.StoreSclass queryStore b lo es := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hiSupp
  have hsa : lo ≤ (queryStore.blocks b).slot := by
    rw [hev.lo_eq]
    exact hev.parent_slot_lt b hev.block_known hev.parent_known
  have hiSpan : i ∈ E.span_committee lo es := by
    rw [hev.cutoff_eq]
    exact supporter_mem_span_committee cfg hev.parent_slot_lt
      hev.latest_message_provenance hiSupp
      (hev.supporter_walk i hiSupp) hsa
  obtain ⟨t, k, a, htle, hvote, hnew, hroot⟩ :=
    E.recorded_lm_is_newest_in_store cfg ext hA.honest_behavior
      hA.externals_coherence hev.scheduled_provenance
      hev.latest_message_provenance hev.cutoff_eq hi hlm
      (hdom i hi hiSpan lm hlm)
  simp only [StoreSclass, Finset.mem_filter]
  refine ⟨⟨hiSpan, hi⟩, ⟨t, k, a, htle, hvote, hnew, ?_⟩⟩
  rw [hroot]
  simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc

/-- Honest recorded support is bounded by the store-indexed `S` value. -/
theorem honest_supporters_sum_le_storeSval
    (hA : SelectedMarginAssumptions cfg ext E)
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hdom : PrefixWindowRecordedEpochMax cfg E queryStore lo es) :
    (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      E.StoreSval queryStore b lo es := by
  rw [honest_score_eq_weight cfg E hev.balance_validators, StoreSval]
  apply E.weight_mono
  intro i hi
  rw [List.mem_toFinset, List.mem_filter] at hi
  exact E.recorded_supporter_mem_storeSclass cfg ext hA hev hdom
    hi.1 (of_decide_eq_true hi.2)

/-- Parent-stuck honest validators at the exact query store belong to its
store-indexed ancestor/voteless class. -/
theorem ParentStuck_subset_storeAclass
    (hA : SelectedMarginAssumptions cfg ext E)
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hdom : PrefixWindowRecordedEpochMax cfg E queryStore lo es) :
    ParentStuck cfg E queryStore bs b ⊆
      E.StoreAclass queryStore b lo es := by
  intro i hiPS
  simp only [ParentStuck, Finset.mem_filter] at hiPS
  obtain ⟨hPS, hi⟩ := hiPS
  have hspanBase := (mem_ParentSupport cfg hPS).1
  rw [← hev.lo_eq] at hspanBase
  have hbaseEs : (queryStore.blocks b).slot - 1 ≤ es := by
    rw [hev.cutoff_eq]
    exact Nat.sub_le_sub_right hev.block_slot_le_current 1
  have hiSpan : i ∈ E.span_committee lo es :=
    E.span_committee_mono lo hbaseEs hspanBase
  simp only [ParentSupport, Finset.mem_filter] at hPS
  obtain ⟨_, hany⟩ := hPS
  cases hlm : queryStore.latest_messages i with
  | none => rw [hlm] at hany; simp at hany
  | some lm =>
      rw [hlm] at hany
      simp only [Option.any_some, Bool.and_eq_true,
        decide_eq_true_eq] at hany
      obtain ⟨hroot, _⟩ := hany
      obtain ⟨t, k, a, htle, hvote, hnew, hbbreq⟩ :=
        E.recorded_lm_is_newest_in_store cfg ext hA.honest_behavior
          hA.externals_coherence hev.scheduled_provenance
          hev.latest_message_provenance hev.cutoff_eq hi hlm
          (hdom i hi hiSpan lm hlm)
      have habbr : a.data.beacon_block_root =
          (queryStore.blocks b).parent_root := by
        rw [hbbreq]
        exact hroot
      have hparentNotDesc : ¬ is_ancestor queryStore
          (get_node_for_root (queryStore.blocks b).parent_root)
          (get_node_for_root b) = true := by
        simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
        rw [get_ancestor_stop
          (le_of_lt (hev.parent_slot_lt b hev.block_known hev.parent_known))]
        intro hcon
        injection hcon with heq
        have hlt := hev.parent_slot_lt b hev.block_known hev.parent_known
        rw [heq] at hlt
        exact lt_irrefl _ hlt
      have hbanc : is_ancestor queryStore (get_node_for_root b)
          (get_node_for_root (queryStore.blocks b).parent_root) = true :=
        is_ancestor_of_parent hev.parent_slot_lt hev.block_known
          hev.parent_known rfl
      simp only [StoreAclass, Finset.mem_filter]
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

/-- Confirmation at an arbitrary query store yields the weak selected margin
from the exact prefix domination premise.  The query-store accounting fields
remain explicit adapter obligations; no completed-store replay is assumed. -/
theorem base_strip_of_confirmed_in_store_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {queryStore : Store Root} {bs : BeaconState Root} {b : Root}
    {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es)
    (hdom : PrefixWindowRecordedEpochMax cfg E queryStore lo es) :
    E.StoreXval queryStore b lo es + E.Bval lo es
        + compute_proposer_score cfg bs + 1 ≤
      E.StoreSval queryStore b lo es := by
  have hHsup := E.honest_supporters_sum_le_storeSval cfg ext hA hev hdom
  have hdisc : get_support_discount cfg ext queryStore bs b ≤
      E.StoreAval queryStore b lo es := by
    refine hev.support_discount_le_parent_stuck.trans ?_
    rw [StoreAval]
    exact E.weight_mono
      (E.ParentStuck_subset_storeAclass cfg ext hA hev hdom)
  have hsm := honest_support_majority_of_byz_le cfg ext hev.confirmation
    hev.byzantine_support_le_adversarial
  rw [hev.total_active] at hsm
  rw [← hev.lo_eq, ← hev.cutoff_eq] at hsm
  have hsplit : E.weight (E.span_committee lo es) =
      E.Jspec lo es + E.Bval lo es := by
    rw [Execution.Jspec, Execution.Bval, Execution.Bwin]
    exact E.weight_split_honest _
  have hMS := hA.byzantine_bound.estimate_sound lo es
    hev.lo_horizon hev.es_horizon
  rw [hsplit] at hMS
  have hpart := E.store_weight_partition queryStore b lo es
  exact queryStore_weak_base_arith hsm hHsup hdisc hMS hpart

/-- Feed the exact query-store base strip into the prefix direct-window
selected-margin consumer.  All cross-store facts remain explicit; in
particular this constructor has no `query.store = E.store v q` premise. -/
theorem prefixDirectWindowSelectedMarginInputsAt_of_confirmed_in_store_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {glc a c : Root} {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : ℕ} {lo es : Slot}
    (hev : E.QueryStoreBaseStripEvidence cfg ext query.store
      (get_current_balance_source query) c lo es)
    (hdom : PrefixWindowRecordedEpochMax cfg E query.store lo es)
    (hboost : compute_proposer_score cfg (get_current_balance_source query) =
      get_proposer_score cfg (E.store cfg ext w m))
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.StoreSupportsDesc query.store c es i →
        E.SupportsDesc cfg ext w m c es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.StoreAncestorOrVoteless query.store c es i →
        E.AncestorOrVoteless cfg ext w m c es i)
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c))))
    (hselected : E.Sval cfg ext w m c lo es ≤
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hsibling : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c))) → c' ≠ c →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint) ≤
        E.Xval cfg ext w m c lo es + E.Bval lo es) :
    E.PrefixDirectWindowSelectedMarginInputsAt cfg ext
      glc a c v q query w m lo es := by
  have hbase := E.base_strip_of_confirmed_in_store_minimal cfg ext hA hev hdom
  refine
    { support_transport := hSt
      ancestor_transport := hAt
      base_strip := ?_
      child_filtered := hchild
      selected_score := hselected
      sibling_score := hsibling }
  rwa [← hboost]

/-- The plain confirmation margin at an arbitrary real query, with proposer
boost read at a later honest endpoint.  Every premise is either an executable
query fact or the faithful window-scoped delivery fact needed to interpret
the relevant recorded latest messages as newest through the cutoff. -/
theorem base_strip_of_confirmed_at_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hstore : query.store = E.store cfg ext v q)
    {b : Root}
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hp : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    (lo es : Slot)
    (hlo : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hdom : E.WindowRecordedEpochMax cfg ext v q lo es)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m) :
    E.Xval cfg ext v q b lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
      E.Sval cfg ext v q b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext v q) bs b = true := by
    simpa only [bs, hstore] using hconf
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hstore]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp b
    rw [← hbsEq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      v hv q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext
      hA.static_validators hA.externals_coherence v hv q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hwf b hb hp
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v q b hb
  have hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v q).blocks b).slot := by
    rw [E.store_current_slot cfg ext v q] at hbcur
    exact E.slotWithinHorizon_of_le cfg hbcur hqH
  have hloH : E.SlotWithinHorizon cfg lo := by
    apply E.slotWithinHorizon_mono cfg (b := (E.store cfg ext v q).blocks b |>.slot)
    · rw [hlo]
      exact hslotlt
    · exact hbH
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v q)) := by
    rw [E.store_current_slot cfg ext v q]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hqH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg
      (b := get_current_slot cfg (E.store cfg ext v q))
    · rw [hes]
      exact Nat.sub_le _ _
    · exact hcurH
  have hbanc : is_ancestor (E.store cfg ext v q) (get_node_for_root b)
      (get_node_for_root ((E.store cfg ext v q).blocks b).parent_root) = true :=
    is_ancestor_of_parent hwf hb hp rfl
  have hstrip := E.weak_base_discharged_window cfg ext hA.honest_behavior
    hA.externals_coherence hA.byzantine_bound hgen hv hqH hwf hbH hval htab
    hprov hconf' hwalk lo es hlo hes hloH hesH hslotlt hbcur hbanc hdom
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
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
  rwa [hboost] at hstrip

end Execution

end FastConfirmation.Spec

end
