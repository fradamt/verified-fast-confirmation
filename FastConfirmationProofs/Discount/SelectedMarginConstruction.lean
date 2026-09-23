module
public import FastConfirmationProofs.Discount.ArbitraryQueryMargin
public import FastConfirmationProofs.Execution.Delivery.RecordedEpoch

@[expose] public section

/-!
# Concrete constructors for arbitrary-query selected margins

Constructs the selected-edge margin from the minimal confirmation base case.

This module contains `base_strip_of_confirmed_at_minimal` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)


namespace Execution

variable (E : Execution Root)

/-! ## Base strip at the exact query store -/







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
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
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
