module
public import FastConfirmation.Spec.Proof.MonotonicityLiveBridge

@[expose] public section

/-!
# Full-window one-confirmation inputs for live monotonicity

Recorded honest votes contribute their weight to the executable score.
The configured liveness margin then suffices when the confirmation window
has full-epoch estimate and the balance source uses the anchored registry.
The interval and balance-source equalities remain to be established at calls.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- An exact epoch window is recognized by the executable estimator as a
full validator-set window. -/
theorem full_epoch_estimate_eq (e : Epoch) (total : Gwei) :
    estimate_committee_weight_between_slots cfg total
      (compute_start_slot_at_epoch cfg e)
      (compute_start_slot_at_epoch cfg (e + 1) - 1) = total := by
  have hL : 0 < cfg.slots_per_epoch := cfg.slots_per_epoch_pos
  have hend : (e + 1) * cfg.slots_per_epoch - 1 =
      e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    simpa only [Nat.add_mul, one_mul] using
      (Nat.add_sub_assoc (show 1 ≤ cfg.slots_per_epoch from hL)
        (e * cfg.slots_per_epoch))
  have hfirst : (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) /
      cfg.slots_per_epoch = e := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) <
            e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
          Nat.add_lt_add_left (Nat.sub_lt hL (by omega)) _
        _ = (e + 1) * cfg.slots_per_epoch := by
          simp only [Nat.add_mul, one_mul]
  have hnext : (((e + 1) * cfg.slots_per_epoch - 1) + 1) /
      cfg.slots_per_epoch = e + 1 := by
    have hnum : ((e + 1) * cfg.slots_per_epoch - 1) + 1 =
        (e + 1) * cfg.slots_per_epoch :=
      Nat.sub_add_cancel (by
        simp only [Nat.add_mul, one_mul]
        exact (Nat.succ_le_of_lt hL).trans (Nat.le_add_left _ _))
    rw [hnum]
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_refl _
    · simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using
        (Nat.lt_add_of_pos_right hL :
          (e + 1) * cfg.slots_per_epoch <
            (e + 1) * cfg.slots_per_epoch + cfg.slots_per_epoch)
  have hfull : is_full_validator_set_covered cfg
      (compute_start_slot_at_epoch cfg e)
      (compute_start_slot_at_epoch cfg (e + 1) - 1) = true := by
    simp only [is_full_validator_set_covered, compute_epoch_at_slot,
      compute_start_slot_at_epoch, decide_eq_true_eq]
    rw [hfirst, hnext]
    exact Nat.lt_succ_self e
  have hordered : compute_start_slot_at_epoch cfg e ≤
      compute_start_slot_at_epoch cfg (e + 1) - 1 := by
    simp only [compute_start_slot_at_epoch, hend]
    exact Nat.le_add_right _ _
  simp [estimate_committee_weight_between_slots, hordered, hfull]

/-- Every window containing a whole epoch has exact total-balance estimate,
even if it begins before the epoch or ends after it. -/
theorem estimate_eq_total_of_full_epoch_inside
    (e : Epoch) (total : Gwei) (a b : Slot)
    (ha : a ≤ compute_start_slot_at_epoch cfg e)
    (hb : compute_start_slot_at_epoch cfg (e + 1) - 1 ≤ b) :
    estimate_committee_weight_between_slots cfg total a b = total := by
  have hL : 0 < cfg.slots_per_epoch := cfg.slots_per_epoch_pos
  have hend : (e + 1) * cfg.slots_per_epoch - 1 =
      e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    simpa only [Nat.add_mul, one_mul] using
      (Nat.add_sub_assoc (show 1 ≤ cfg.slots_per_epoch from hL)
        (e * cfg.slots_per_epoch))
  have hfirst : (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) /
      cfg.slots_per_epoch = e := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) <
            e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
          Nat.add_lt_add_left (Nat.sub_lt hL (by omega)) _
        _ = (e + 1) * cfg.slots_per_epoch := by
          simp only [Nat.add_mul, one_mul]
  have hnext : (((e + 1) * cfg.slots_per_epoch - 1) + 1) /
      cfg.slots_per_epoch = e + 1 := by
    have hnum : ((e + 1) * cfg.slots_per_epoch - 1) + 1 =
        (e + 1) * cfg.slots_per_epoch :=
      Nat.sub_add_cancel (by
        simp only [Nat.add_mul, one_mul]
        exact (Nat.succ_le_of_lt hL).trans (Nat.le_add_left _ _))
    rw [hnum]
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_refl _
    · simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using
        (Nat.lt_add_of_pos_right hL :
          (e + 1) * cfg.slots_per_epoch <
            (e + 1) * cfg.slots_per_epoch + cfg.slots_per_epoch)
  have hleft : compute_epoch_at_slot cfg (a + (cfg.slots_per_epoch - 1)) ≤ e := by
    calc
      compute_epoch_at_slot cfg (a + (cfg.slots_per_epoch - 1)) ≤
          compute_epoch_at_slot cfg
            (compute_start_slot_at_epoch cfg e + (cfg.slots_per_epoch - 1)) :=
        Nat.div_le_div_right (Nat.add_le_add_right ha _)
      _ = e := by simpa only [compute_epoch_at_slot, compute_start_slot_at_epoch]
        using hfirst
  have hright : e + 1 ≤ compute_epoch_at_slot cfg (b + 1) := by
    calc
      e + 1 = compute_epoch_at_slot cfg
          (compute_start_slot_at_epoch cfg (e + 1) - 1 + 1) := by
        simpa only [compute_epoch_at_slot, compute_start_slot_at_epoch] using hnext.symm
      _ ≤ compute_epoch_at_slot cfg (b + 1) :=
        Nat.div_le_div_right (Nat.add_le_add_right hb 1)
  have hfull : is_full_validator_set_covered cfg a b = true := by
    simp only [is_full_validator_set_covered, decide_eq_true_eq]
    exact lt_of_le_of_lt hleft (lt_of_lt_of_le (Nat.lt_succ_self e) hright)
  have hordered : a ≤ b := by
    calc
      a ≤ compute_start_slot_at_epoch cfg e := ha
      _ ≤ compute_start_slot_at_epoch cfg (e + 1) - 1 := by
        simp only [compute_start_slot_at_epoch, hend]
        exact Nat.le_add_right _ _
      _ ≤ b := hb
  simp [estimate_committee_weight_between_slots, hordered, hfull]

/-- A first block of an epoch uses that whole epoch as its adversarial
window at the next epoch start. The executable equivocation discount can
only reduce the configured budget. -/
theorem first_epoch_block_adversarial_bound
    (store : Store Root) (balanceSource : BeaconState Root)
    (r : Root) (e : Epoch)
    (hblockEpoch : get_block_epoch cfg store r = e)
    (hparentEpoch : get_block_epoch cfg store (store.blocks r).parent_root < e)
    (hcurrentSlot : get_current_slot cfg store =
      compute_start_slot_at_epoch cfg (e + 1)) :
    get_adversarial_weight cfg ext store balanceSource r ≤
      get_total_active_balance cfg balanceSource / 100 *
        cfg.confirmation_byzantine_threshold := by
  rw [get_adversarial_weight_eq]
  have hspan : (if get_block_epoch cfg store r >
      get_block_epoch cfg store (store.blocks r).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg store r)
      else (store.blocks r).slot) = compute_start_slot_at_epoch cfg e := by
    simp [hblockEpoch, hparentEpoch]
  rw [hspan, hcurrentSlot]
  have hle := compute_adversarial_weight_le cfg ext
    (store := store) (bs := balanceSource)
    (compute_start_slot_at_epoch cfg e)
    (compute_start_slot_at_epoch cfg (e + 1) - 1)
  simpa only [full_epoch_estimate_eq] using hle

namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- The initial active weight splits into honest and non-honest parts. -/
theorem initial_active_weight_partition :
    E.weight ((Finset.range E.registry.length).filter fun i =>
      i ∈ E.honest ∧
        is_active_validator (E.registry.getD i default)
          (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true) +
      E.activeNonHonestWeight cfg =
    E.weight ((Finset.range E.registry.length).filter fun i =>
      is_active_validator (E.registry.getD i default)
        (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true) := by
  let active := (Finset.range E.registry.length).filter fun i =>
    is_active_validator (E.registry.getD i default)
      (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true
  have hsplit := Finset.sum_filter_add_sum_filter_not active
    (fun i => i ∈ E.honest) E.weight_of
  simpa only [Execution.weight, Execution.activeNonHonestWeight,
    active, Finset.filter_filter, and_comm] using hsplit

/-- In an accepted execution, the anchor state and initial execution slot
name the same epoch. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.anchor_epoch_eq_initial
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext) :
    get_current_epoch cfg E.anchor_state =
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
  obtain ⟨ast, ablk, hgenEq, hslot, _⟩ := h.trajectory.genesis_structure
  have hanchorState : E.anchor_state = ast := by
    simp only [Execution.anchor_state, hgenEq, get_forkchoice_store,
      Function.update_self]
  have hslot0 : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext 0 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg
      h.trajectory.whole_seconds] at hcurrent0
    exact hcurrent0.symm
  rw [hanchorState, hslot0]
  rfl

/-- Every vote slot in a completed epoch has reached its next-slot delivery
deadline by the endpoint, including the last slot of that epoch. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.completed_epoch_vote_delivery
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {e : Epoch} {m : ℕ}
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    {t : Slot} (htEpoch : compute_epoch_at_slot cfg t = e) :
    E.slot_start cfg (t + 1) ≤ m := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have htNext : t + 1 ≤ compute_start_slot_at_epoch cfg (e + 1) := by
    have hlt := Nat.lt_mul_div_succ t cfg.slots_per_epoch_pos
    simp only [compute_epoch_at_slot] at htEpoch
    rw [htEpoch] at hlt
    simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlt
  apply Nat.le_of_not_gt
  intro htooLate
  have hslotLt : E.slot_at cfg m < t + 1 :=
    (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).2 htooLate
  exact (Nat.not_lt_of_ge (htNext.trans heDone)) hslotLt

/-- Any in-horizon balance source with the static registry has the anchor's
total balance and proposer boost. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_balance_source_accounting
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (bs : BeaconState Root)
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon) :
    get_total_active_balance cfg bs = E.total_active cfg ∧
      compute_proposer_score cfg bs =
        compute_proposer_score cfg E.anchor_state := by
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon := by
    rw [h.anchor_epoch_eq_initial cfg ext E]
    exact (h.completed_calls.static_validators.genesis_within_horizon).2.2
  have hact : ∀ i : ValidatorIndex,
      is_active_validator (bs.validators.getD i default)
        (get_current_epoch cfg bs) =
      is_active_validator (E.anchor_state.validators.getD i default)
        (get_current_epoch cfg E.anchor_state) := by
    intro i
    rw [hval]
    exact h.completed_calls.static_validators.activity_constant i
      (get_current_epoch cfg bs) (get_current_epoch cfg E.anchor_state)
      hbsH hanchorH
  have htotal := get_total_active_balance_congr cfg hval hact
  have hboost := compute_proposer_score_congr cfg hval hact
  exact ⟨htotal, hboost⟩

/-- With a nondegenerate active balance, the live margin's non-honest
weight is exactly the complement of the honest anchor active set. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.anchor_honest_weight_partition
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg)) :
    E.weight ((E.currentTargetAnchorActive cfg).filter fun i => i ∈ E.honest) +
      E.activeNonHonestWeight cfg = E.total_active cfg := by
  have hset : E.currentTargetAnchorActive cfg =
      (Finset.range E.registry.length).filter fun i =>
        is_active_validator (E.registry.getD i default)
          (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true := by
    ext i
    simp [Execution.currentTargetAnchorActive, get_active_validator_indices,
      Execution.registry, h.anchor_epoch_eq_initial cfg ext E]
  have hpart := E.initial_active_weight_partition cfg
  have htotal := E.total_active_eq_anchorActive_weight cfg hfloor
  rw [hset] at htotal
  simpa only [hset, Finset.filter_filter, and_comm] using
    hpart.trans htotal.symm

/-- Committee coverage places every honest anchor-active validator into
the completed epoch. Delivery of each such slot is stated separately so
this lemma can be used at the exact FCR call time. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.honest_full_epoch_assignments
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {e : Epoch} {m : ℕ}
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hdelivery : ∀ t : Slot, compute_epoch_at_slot cfg t = e →
      E.slot_start cfg (t + 1) ≤ m) :
    ∀ i ∈ (E.currentTargetAnchorActive cfg).filter (fun i => i ∈ E.honest),
      i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        compute_start_slot_at_epoch cfg e ≤ t ∧
        t < E.slot_at cfg m ∧ i ∈ E.committee t ∧
        E.slot_start cfg (t + 1) ≤ m := by
  intro i hiHS
  obtain ⟨hiActive, hiHonest⟩ := Finset.mem_filter.mp hiHS
  have hactiveAnchor : is_active_validator (E.registry.getD i default)
      (get_current_epoch cfg E.anchor_state) = true := by
    simp only [Execution.currentTargetAnchorActive,
      get_active_validator_indices, List.mem_toFinset, List.mem_filter,
      List.mem_range] at hiActive
    simpa only [Execution.registry] using hiActive.2
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon := by
    rw [h.anchor_epoch_eq_initial cfg ext E]
    exact (h.completed_calls.static_validators.genesis_within_horizon).2.2
  have heEpochLe : e + 1 ≤ compute_epoch_at_slot cfg (E.slot_at cfg m) := by
    simp only [compute_epoch_at_slot]
    exact (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mpr
      (by simpa only [compute_start_slot_at_epoch] using heDone)
  have heH : e < E.verification_horizon :=
    (Nat.lt_succ_self e).trans (heEpochLe.trans_lt hHm.2.2)
  have hactiveE : is_active_validator (E.registry.getD i default) e = true := by
    rw [← h.completed_calls.static_validators.activity_constant i
      (get_current_epoch cfg E.anchor_state) e hanchorH heH]
    exact hactiveAnchor
  obtain ⟨t, htH, htEpoch, hcommittee⟩ :=
    h.trajectory.externals_coherence.committee_coverage i e heH hactiveE
  have hstartT : compute_start_slot_at_epoch cfg e ≤ t := by
    simp only [compute_start_slot_at_epoch, compute_epoch_at_slot] at htEpoch ⊢
    rw [← htEpoch]
    exact Nat.div_mul_le_self t cfg.slots_per_epoch
  have hnextT : t < compute_start_slot_at_epoch cfg (e + 1) := by
    have hlt := Nat.lt_mul_div_succ t cfg.slots_per_epoch_pos
    simp only [compute_epoch_at_slot] at htEpoch
    rw [htEpoch] at hlt
    simpa only [compute_start_slot_at_epoch, Nat.mul_comm] using hlt
  exact ⟨hiHonest, t, htH, hstartT, hnextT.trans_le heDone,
    hcommittee, hdelivery t htEpoch⟩

/-- One-confirmation of a live block from a full-epoch set of delivered
honest assignments. The explicit equalities are accounting results about the
actual call window, not additional live assumptions. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.one_confirmed_of_full_window
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hHm : E.WithinHorizon cfg m)
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      s ≤ u → u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (balanceSource : BeaconState Root)
    (hval : balanceSource.validators = E.registry)
    (hbsH : get_current_epoch cfg balanceSource < E.verification_horizon)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        s ≤ t ∧ t < E.slot_at cfg m ∧ i ∈ E.committee t ∧
        E.slot_start cfg (t + 1) ≤ m)
    (hpartition : E.weight HS + E.activeNonHonestWeight cfg =
      E.total_active cfg)
    (hwindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      (((E.store cfg ext w m).blocks
        ((E.store cfg ext w m).blocks r).parent_root).slot + 1)
      (get_current_slot cfg (E.store cfg ext w m) - 1) ≤ E.total_active cfg)
    (hboost : compute_proposer_score cfg balanceSource ≤
      compute_proposer_score cfg E.anchor_state)
    (hadversarial : get_adversarial_weight cfg ext
      (E.store cfg ext w m) balanceSource r ≤
      E.total_active cfg / 100 * cfg.confirmation_byzantine_threshold) :
    is_one_confirmed cfg ext (E.store cfg ext w m) balanceSource r = true := by
  have hscore := h.fixed_live_block_score_lower cfg ext E hs0 hHm
    hsupport hw balanceSource hval hbsH HS hHS
  exact one_confirmed_of_bounded_window cfg ext
    (E.store cfg ext w m) balanceSource r hpartition
    live.configured_threshold_margin hscore hwindow hboost hadversarial

/-- A live epoch-entry block is one-confirmed at the next epoch start when
the endpoint balance source is the anchored registry and the entire epoch's
honest assignments have arrived. The parent-window and balance-floor facts
are kept explicit for the actual-call application. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.first_epoch_live_block_one_confirmed
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (heStart : E.slot_at cfg 0 ≤ compute_start_slot_at_epoch cfg e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hdelivery : ∀ t : Slot, compute_epoch_at_slot cfg t = e →
      E.slot_start cfg (t + 1) ≤ m)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      compute_start_slot_at_epoch cfg e ≤ u →
      u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (balanceSource : BeaconState Root)
    (hval : balanceSource.validators = E.registry)
    (hbsH : get_current_epoch cfg balanceSource < E.verification_horizon)
    (htab : get_total_active_balance cfg balanceSource = E.total_active cfg)
    (hboost : compute_proposer_score cfg balanceSource ≤
      compute_proposer_score cfg E.anchor_state)
    (hcurrentSlot : get_current_slot cfg (E.store cfg ext w m) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hparentWindow : ((E.store cfg ext w m).blocks
      ((E.store cfg ext w m).blocks r).parent_root).slot + 1 ≤
        compute_start_slot_at_epoch cfg e)
    (hblockEpoch : get_block_epoch cfg (E.store cfg ext w m) r = e)
    (hparentEpoch : get_block_epoch cfg (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks r).parent_root < e) :
    is_one_confirmed cfg ext (E.store cfg ext w m) balanceSource r = true := by
  let HS := (E.currentTargetAnchorActive cfg).filter fun i => i ∈ E.honest
  have hassign := h.honest_full_epoch_assignments cfg ext E
    heDone hHm hdelivery
  have hpartition := h.anchor_honest_weight_partition cfg ext E hfloor
  have hwindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      (((E.store cfg ext w m).blocks
        ((E.store cfg ext w m).blocks r).parent_root).slot + 1)
      (get_current_slot cfg (E.store cfg ext w m) - 1) ≤ E.total_active cfg := by
    rw [htab, hcurrentSlot]
    exact le_of_eq (estimate_eq_total_of_full_epoch_inside cfg e
      (E.total_active cfg) _ _ hparentWindow (Nat.le_refl _))
  have hadversarial := first_epoch_block_adversarial_bound cfg ext
    (E.store cfg ext w m) balanceSource r e
    hblockEpoch hparentEpoch hcurrentSlot
  rw [htab] at hadversarial
  exact h.one_confirmed_of_full_window cfg ext E live heStart hHm
    hsupport hw balanceSource hval hbsH HS hassign hpartition
    hwindow hboost hadversarial

/-- The accepted clock and static-balance laws discharge all accounting
inputs of the first-epoch-block confirmation lemma. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.first_epoch_live_block_one_confirmed_at_boundary
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (heStart : E.slot_at cfg 0 ≤ compute_start_slot_at_epoch cfg e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      compute_start_slot_at_epoch cfg e ≤ u →
      u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (balanceSource : BeaconState Root)
    (hval : balanceSource.validators = E.registry)
    (hbsH : get_current_epoch cfg balanceSource < E.verification_horizon)
    (hcurrentSlot : get_current_slot cfg (E.store cfg ext w m) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hparentWindow : ((E.store cfg ext w m).blocks
      ((E.store cfg ext w m).blocks r).parent_root).slot + 1 ≤
        compute_start_slot_at_epoch cfg e)
    (hblockEpoch : get_block_epoch cfg (E.store cfg ext w m) r = e)
    (hparentEpoch : get_block_epoch cfg (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks r).parent_root < e) :
    is_one_confirmed cfg ext (E.store cfg ext w m) balanceSource r = true := by
  obtain ⟨htab, hboost⟩ := h.live_balance_source_accounting cfg ext E
    balanceSource hval hbsH
  exact h.first_epoch_live_block_one_confirmed cfg ext E live
    heStart heDone hHm
    (fun t ht => h.completed_epoch_vote_delivery cfg ext E heDone ht)
    h.completed_calls.balance_floor hsupport hw balanceSource
    hval hbsH htab hboost.le hcurrentSlot hparentWindow
    hblockEpoch hparentEpoch

end Execution

end FastConfirmation.Spec

end
