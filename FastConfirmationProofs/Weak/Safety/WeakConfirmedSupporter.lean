module
public import FastConfirmationProofs.FCRRule.MinimalSelectedDomain
public import FastConfirmationProofs.Weak.Discount.WeakEconomicReadback
public import FastConfirmationProofs.Weak.Safety.WeakObserverProvenance
public import FastConfirmationProofs.Execution.StoreInvariants.CheckpointDomain
public import FastConfirmationModel.Weak.WeakSynchrony

@[expose] public section

/-!
# Spec / Proof / WeakConfirmedSupporter

Stage 3 of the weak-synchrony migration: the honest-supporter extraction for a
confirmed block, read at a query store that need not belong to an honest
observer.

`MinimalSelectedDomain.honestSupporter_of_confirmed_known_at_minimal` derives
its conclusion from `SelectedMarginAssumptions` plus `hv : v ∈ E.honest`. That
membership fact is used in exactly one place in the whole proof: to specialize
`honest_support_majority` (via its own dependency on
`ExternalsCoherence.committees_agree`, routed through
`support_discount_le_parent_stuck`). Both of those have store-generic
`_of_prefix` clones in `WeakEconomicReadback.lean`, driven by an explicit
`E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)` fact instead of
observer honesty. Substituting them removes the only honesty dependency, so
`honestSupporter_of_confirmed_known_at_observer` below is otherwise a verbatim
clone of the minimal-domain theorem — including its uses of the (already
honesty-free, per the `refactor: drop vacuous honesty hypotheses from Registry
balance lemmas` commit) `Execution.registryConstant` and
`Execution.checkpoint_states_total_active_balance`, and of the (already
honesty-free) `Execution.checkpoint_state_key_of_one_confirmed`.

The second theorem, `Execution.checkpoint_state_key_of_broadcast_certificate`,
is the broadcast-certificate analogue of
`CheckpointDomain.checkpoint_state_key_of_one_confirmed`: a checkpoint state
that witnesses a successful `Weak.has_broadcast_certificate` call must be
cached in the store's `checkpoint_state_keys`, since an unkeyed lookup returns
the totalized-map default (`CheckpointStatesExact`), whose empty validator
list forces every summand of `Weak.get_broadcast_certificate_support` — and
hence the observed support itself — to be `0`, contradicting the certificate's
strict inequality against a `ℕ`-valued (hence nonnegative) adversarial budget.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Local restatements of `MinimalSelectedDomain`'s file-private helpers

`MinimalSelectedDomain.lean` declares `exists_mem_of_map_sum_pos_minimal` and
`honest_weight_pos_minimal` as `private`, hence invisible here. They carry no
honesty content — pure `List`/`ℕ` facts — so they are restated verbatim
(same pattern `WeakEconomicReadback.lean` uses for `Discount.lean`'s and
`HonestWeight.lean`'s private arithmetic helpers). -/

private theorem exists_mem_of_map_sum_pos_observer {Alpha : Type*}
    (l : List Alpha) (f : Alpha → ℕ) (h : 0 < (l.map f).sum) :
    ∃ x ∈ l, 0 < f x := by
  induction l with
  | nil => simp at h
  | cons a rest ih =>
      rw [List.map_cons, List.sum_cons] at h
      rcases Nat.eq_zero_or_pos (f a) with ha | ha
      · rw [ha, Nat.zero_add] at h
        obtain ⟨x, hx, hpos⟩ := ih h
        exact ⟨x, List.mem_cons_of_mem a hx, hpos⟩
      · exact ⟨a, List.mem_cons_self, ha⟩

private theorem honest_weight_pos_observer {H maximum boost discount : ℕ}
    (hmain : 2 * H + discount ≥ maximum + boost + 1)
    (hdiscount : discount ≤ maximum) : 0 < H := by
  omega

namespace Execution

variable (E : Execution Root)

/-! ## Deliverable 1 — honest supporter at an arbitrary (not necessarily
honest) observer's store -/

/-- A successful concrete confirmation exposes an honest recorded supporter,
read at an arbitrary node's store — including a non-honest observer's.

Verbatim clone of `honestSupporter_of_confirmed_known_at_minimal`
(`MinimalSelectedDomain.lean:217`) with the observer-honesty hypothesis
`hv : v ∈ E.honest` replaced by the explicit committee-readback fact
`hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)`: the sole
use of `hv` in the original proof was to specialize `honest_support_majority`
(via `support_discount_le_parent_stuck`'s own `ExternalsCoherence
.committees_agree` dependency); both calls are replaced here by their
store-generic `_of_prefix` clones from `WeakEconomicReadback.lean`, driven by
`hcomm` instead. Every other hypothesis, and the whole rest of the proof, is
unchanged. -/
theorem honestSupporter_of_confirmed_known_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ)
    (hvalid : E.ObserverValidity cfg ext v)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n) (b : Root)
    (hH : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hparent : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) b = true) :
    ∃ (i : ValidatorIndex) (lm : LatestMessage Root), i ∈ E.honest ∧
      (E.store cfg ext v n).latest_messages i = some lm ∧
      is_ancestor (E.store cfg ext v n)
        (get_supported_node (E.store cfg ext v n) lm)
        (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hA.genesis
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  set c := fcrStore.current_epoch_observed_justified_checkpoint
  set bs := get_current_balance_source fcrStore
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true := by
    have ht := hconf
    rw [hstore] at ht
    exact ht
  have hbseq : bs = (E.store cfg ext v n).checkpoint_states c := by
    simp only [bs, c, get_current_balance_source]
    rw [hstore]
  have hkey : c ∈ (E.store cfg ext v n).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen0 v n c b
    rw [← hbseq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbseq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen0
      v n).2 c hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbseq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence (hdiv := hA.whole_seconds) v n c hkey hH
  have hprov := E.latestMessageProvenance_of_observer_validity cfg ext
    hA.wellFormed v hvalid hgen0 n
  rw [← E.store_current_slot cfg ext v n] at hprov
  have hwf : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hroot⟩ hA.wellFormed.anchor_parent_unscheduled
      v n
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hroot⟩ v n
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root := by
    intro i _ lm hlm
    have hlmKnown :=
      E.latestMessageRootKnown cfg ext hgen0 v n i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hbslot : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v n b hb
  have hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v n).blocks b).slot := by
    apply E.slotWithinHorizon_of_le cfg
    · rw [E.store_current_slot cfg ext v n] at hbslot
      exact hbslot
    · exact hH
  have hstart : ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1 ≤
      ((E.store cfg ext v n).blocks b).slot :=
    Nat.succ_le_iff.mpr (hwf b hb hparent)
  have hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1) :=
    ⟨hstart.trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hstart) hbH.2⟩
  have hsm := honest_support_majority_of_prefix cfg ext hA.honest_behavior
    hA.externals_coherence hA.byzantine_bound hgen0 hvalid hH hcomm hwf hbH hval htab
    hprov hconf' hwalk
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest := fun i hi hih =>
    E.honest_not_equivocating_of_observer_validity cfg ext hA.honest_behavior
      hA.externals_coherence hvalid hgen0 hih n hi
  have hdisc := support_discount_le_parent_stuck_of_prefix cfg ext
    hA.byzantine_bound hcomm hval hstartH hbH htab hne
  have hsub : ParentStuck cfg E (E.store cfg ext v n) bs b ⊆
      E.span_committee
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1) := by
    simp only [ParentStuck, ParentSupport]
    exact (Finset.filter_subset _ _).trans
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have hmono := E.span_committee_mono
    (((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
    (Nat.sub_le_sub_right hbslot 1)
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact ⟨hH.2.1, hH.2.2⟩
  have hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1) :=
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
  have hdle : get_support_discount cfg ext (E.store cfg ext v n) bs b ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) := by
    refine le_trans hdisc (le_trans (E.weight_mono hsub)
      (le_trans (E.weight_mono hmono) (le_trans
        (hA.byzantine_bound.estimate_sound _ _ hstartH hendH) (le_of_eq ?_))))
    rw [htab]
  have hpos : 0 < (((AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs).filter (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum := by
    exact honest_weight_pos_observer hsm hdle
  obtain ⟨i, hi, _⟩ := exists_mem_of_map_sum_pos_observer _ _ hpos
  simp only [List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨hiAtt, hiHon⟩ := hi
  obtain ⟨lm, hlm, _, hsupp⟩ := mem_AttSupporters cfg hiAtt
  exact ⟨i, lm, hiHon, hlm, hsupp⟩

/-! ## Deliverable 2 — checkpoint-state keyedness from a broadcast
certificate -/

/-- An unkeyed checkpoint state contributes zero broadcast-certificate
support: `CheckpointStatesExact` forces it to be `(default : BeaconState
Root)`, whose validator list is `[]`, so every `List.getD` lookup in
`Weak.get_broadcast_certificate_support` falls back to the zero-`effective_
balance` default validator and every summand vanishes — independent of which
store, block, or slot span is queried. -/
private theorem broadcast_certificate_support_default_eq_zero
    (store : Store Root) (block_root : Root) (start_slot end_slot : Slot) :
    Weak.get_broadcast_certificate_support cfg ext store
        (default : BeaconState Root) block_root start_slot end_slot = 0 := by
  have hvalidators : (default : BeaconState Root).validators = [] := rfl
  simp only [Weak.get_broadcast_certificate_support]
  apply Finset.sum_eq_zero
  intro i _
  simp only [hvalidators, List.getD_nil]
  rfl

/-- Any checkpoint state that witnesses a successful `Weak
.has_broadcast_certificate` call must be in the executable store's
checkpoint-state dictionary. Otherwise (`CheckpointStatesExact`, i.e.
`Execution.checkpointStatesExact`) its observed support is zero
(`broadcast_certificate_support_default_eq_zero`), contradicting the
certificate's strict inequality against a `ℕ`-valued, hence nonnegative,
adversarial budget.

The `store`/`bs`/`hbs` hypothesis shape mirrors how `get_current_balance_
source` (`FastConfirmation/Spec/Model/FCRStore.lean:197`) produces its
balance source from a `FastConfirmationStore`: an arbitrary `store`, and a
balance source `bs` that is exactly `store.checkpoint_states cp` for the
target checkpoint `cp`. This matches the hypothesis shape of the sibling
`checkpoint_state_key_of_one_confirmed` (`CheckpointDomain.lean:272`), whose
`store` is likewise pinned to an `Execution` trajectory point via `hstore`. -/
theorem checkpoint_state_key_of_broadcast_certificate (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (cp : Checkpoint Root)
    (store : Store Root) (hstore : store = E.store cfg ext v n)
    (bs : BeaconState Root) (hbs : bs = store.checkpoint_states cp)
    (block_root : Root) (start_slot end_slot : Slot)
    (hcert : Weak.has_broadcast_certificate cfg ext store bs block_root
      start_slot end_slot = true) :
    cp ∈ store.checkpoint_state_keys := by
  by_contra hc
  have hc' : cp ∉ (E.store cfg ext v n).checkpoint_state_keys := by
    rw [hstore] at hc
    exact hc
  have hbsDefault : bs = default := by
    rw [hbs, hstore]
    exact E.checkpointStatesExact cfg ext hgen v n cp hc'
  simp only [Weak.has_broadcast_certificate] at hcert
  by_cases h0 : get_current_slot cfg store = 0
  · rw [if_pos h0] at hcert
    exact absurd hcert Bool.false_ne_true
  rw [if_neg h0] at hcert
  simp only [gt_iff_lt, decide_eq_true_eq] at hcert
  rw [hbsDefault,
    broadcast_certificate_support_default_eq_zero cfg ext store block_root
      start_slot end_slot] at hcert
  exact (Nat.not_lt_zero _ hcert).elim

end Execution

end FastConfirmation.Spec

end
