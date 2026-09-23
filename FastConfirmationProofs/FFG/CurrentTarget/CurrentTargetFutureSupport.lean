module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetSupportAccounting

public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
@[expose] public section

/-!
# Future honest support for the current-target prediction

This module proves the economic meaning of
`will_current_target_be_justified`.  The current epoch is split at the store's
current slot.  Full-epoch committee coverage and the sound elapsed-committee
estimate lower-bound the weight still available in the future part; the
per-span Byzantine fraction then lower-bounds its honest part.

The one explicit economic nondegeneracy premise below is necessary only
because `get_total_active_balance` is `max EFFECTIVE_BALANCE_INCREMENT
active_balance`.  It says that the actual active balance reaches that floor.
It is not a quorum premise.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- First slot of the store's current epoch. -/
def currentTargetEpochStart (store : Store Root) : Slot :=
  compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store)

/-- Last slot of the store's current epoch. -/
def currentTargetEpochEnd (store : Store Root) : Slot :=
  currentTargetEpochStart cfg store + (cfg.slots_per_epoch - 1)

namespace Execution

variable (E : Execution Root)

/-- Committee union already elapsed when the prediction helper is evaluated. -/
def currentTargetElapsedSpan (store : Store Root) : Finset ValidatorIndex :=
  E.span_committee (currentTargetEpochStart cfg store)
    (get_current_slot cfg store - 1)

/-- Committee union from the current slot through the end of the current epoch. -/
def currentTargetFutureSpan (store : Store Root) : Finset ValidatorIndex :=
  E.span_committee (get_current_slot cfg store) (currentTargetEpochEnd cfg store)

/-- Honest validators already counted by `get_current_target_score`. -/
def currentTargetObservedHonestSupporters
    (store : Store Root) (state : BeaconState Root) : Finset ValidatorIndex :=
  ((CurrentTargetSupporters cfg store state).filter
    (fun i => i ∈ E.honest)).toFinset

/-- Non-honest validators already counted by `get_current_target_score`. -/
def currentTargetObservedNonhonestSupporters
    (store : Store Root) (state : BeaconState Root) : Finset ValidatorIndex :=
  ((CurrentTargetSupporters cfg store state).filter
    (fun i => i ∉ E.honest)).toFinset

omit [LinearOrder Root] [Inhabited Root] in
/-- A slot between the canonical first and last slots of epoch `e` has epoch
exactly `e`. -/
private theorem epoch_eq_of_epoch_bounds {e : Epoch} {s : Slot}
    (hlo : e * cfg.slots_per_epoch <= s)
    (hhi : s <= e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) :
    compute_epoch_at_slot cfg s = e := by
  simp only [compute_epoch_at_slot]
  apply Nat.div_eq_of_lt_le hlo
  calc
    s <= e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := hhi
    _ < e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
      Nat.add_lt_add_left
        (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
    _ = (e + 1) * cfg.slots_per_epoch := by
      simp only [Nat.add_mul, one_mul]

omit [LinearOrder Root] [Inhabited Root] in
/-- The current slot lies between the canonical first and last slots of its
epoch. -/
private theorem current_slot_epoch_bounds (store : Store Root) :
    currentTargetEpochStart cfg store <= get_current_slot cfg store /\
      get_current_slot cfg store <= currentTargetEpochEnd cfg store := by
  let s := get_current_slot cfg store
  let e := get_current_store_epoch cfg store
  have hlo : e * cfg.slots_per_epoch <= s := by
    exact Nat.div_mul_le_self s cfg.slots_per_epoch
  have hlt : s < e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
    have h := Nat.lt_mul_div_succ s cfg.slots_per_epoch_pos
    have hdiv : s / cfg.slots_per_epoch = e := by
      rfl
    rw [hdiv, Nat.mul_add] at h
    simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
  have hhi : s <= e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    have hpred := Nat.le_pred_of_lt hlt
    rw [Nat.pred_eq_sub_one,
      Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
    exact hpred
  simpa only [currentTargetEpochStart, currentTargetEpochEnd,
    compute_start_slot_at_epoch, e, s] using And.intro hlo hhi

omit [LinearOrder Root] [Inhabited Root] in
/-- The minimum-balance nondegeneracy identifies `total_active` with the
actual anchor active-set weight. -/
theorem total_active_eq_anchorActive_weight
    (hfloor : cfg.effective_balance_increment <=
      E.weight (E.currentTargetAnchorActive cfg)) :
    E.total_active cfg = E.weight (E.currentTargetAnchorActive cfg) := by
  simp only [Execution.total_active, Execution.currentTargetAnchorActive,
    get_total_active_balance, get_total_balance, Execution.weight,
    Execution.weight_of, Execution.registry]
  exact Nat.max_eq_right hfloor

/-- In a horizon-bounded epoch, committee coverage and committee-member
activity identify the full epoch committee union with the static anchor active
set. -/
theorem current_epoch_span_eq_anchorActive
    (hec : BeaconExternalsPremises cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    {store : Store Root}
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hendH : E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon) :
    E.span_committee (currentTargetEpochStart cfg store)
        (currentTargetEpochEnd cfg store) =
      E.currentTargetAnchorActive cfg := by
  let e := get_current_store_epoch cfg store
  have heH : e < E.verification_horizon := by
    simpa only [e, get_current_store_epoch] using hcurrentH.2
  apply Finset.Subset.antisymm
  . intro i hi
    simp only [Execution.span_committee, Finset.mem_biUnion,
      Finset.mem_Icc] at hi
    obtain ⟨s, hs, his⟩ := hi
    have hsH : E.SlotWithinHorizon cfg s :=
      And.intro (le_trans hs.2 hendH.1)
        (lt_of_le_of_lt (Nat.div_le_div_right hs.2) hendH.2)
    have hsEpoch : compute_epoch_at_slot cfg s = e := by
      apply epoch_eq_of_epoch_bounds cfg
      . simpa only [currentTargetEpochStart, compute_start_slot_at_epoch, e]
          using hs.1
      . simpa only [currentTargetEpochEnd, currentTargetEpochStart,
          compute_start_slot_at_epoch, e] using hs.2
    have hactiveAnchor : is_active_validator
        (E.anchor_state.validators.getD i default)
        (get_current_epoch cfg E.anchor_state) = true := by
      have hactiveS := hec.committee_members_active i s hsH his
      have hactiveGround : is_active_validator (E.registry.getD i default)
          e = true := by simpa only [hsEpoch] using hactiveS
      have := hsv.activity_constant i e
        (get_current_epoch cfg E.anchor_state) heH hanchorH
      rw [this] at hactiveGround
      simpa only [Execution.registry] using hactiveGround
    rw [Execution.currentTargetAnchorActive, List.mem_toFinset]
    exact mem_active_of_active hactiveAnchor
  . intro i hi
    rw [Execution.currentTargetAnchorActive, List.mem_toFinset] at hi
    have hactiveAnchor : is_active_validator
        (E.registry.getD i default) (get_current_epoch cfg E.anchor_state) = true := by
      simpa only [Execution.registry] using (List.mem_filter.mp hi).2
    have hactiveE : is_active_validator (E.registry.getD i default) e = true := by
      rw [hsv.activity_constant i e (get_current_epoch cfg E.anchor_state)
        heH hanchorH]
      exact hactiveAnchor
    obtain ⟨s, _hsH, hsEpoch, his⟩ :=
      hec.committee_coverage i e heH hactiveE
    have hlo : e * cfg.slots_per_epoch <= s := by
      have h := Nat.div_mul_le_self s cfg.slots_per_epoch
      have hdiv : s / cfg.slots_per_epoch = e := by
        simpa only [compute_epoch_at_slot] using hsEpoch
      rw [hdiv] at h
      exact h
    have hlt : s < e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
      have h := Nat.lt_mul_div_succ s cfg.slots_per_epoch_pos
      rw [show s / cfg.slots_per_epoch = e by
        simpa only [compute_epoch_at_slot] using hsEpoch, Nat.mul_add] at h
      simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
    have hhi : s <= e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
      have hpred := Nat.le_pred_of_lt hlt
      rw [Nat.pred_eq_sub_one,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
      exact hpred
    simp only [Execution.span_committee, Finset.mem_biUnion]
    exact ⟨s, Finset.mem_Icc.mpr (And.intro
      (by simpa only [currentTargetEpochStart, compute_start_slot_at_epoch, e]
          using hlo)
      (by simpa only [currentTargetEpochEnd, currentTargetEpochStart,
          compute_start_slot_at_epoch, e] using hhi)), his⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- Horizon guards for the elapsed estimate's two endpoints follow from the
current-slot guard. -/
private theorem elapsed_endpoints_within
    {store : Store Root}
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store)) :
    E.SlotWithinHorizon cfg (currentTargetEpochStart cfg store) /\
      E.SlotWithinHorizon cfg (get_current_slot cfg store - 1) := by
  have hstartLe := (current_slot_epoch_bounds cfg store).1
  constructor
  . exact And.intro (le_trans hstartLe hcurrentH.1)
      (lt_of_le_of_lt (Nat.div_le_div_right hstartLe) hcurrentH.2)
  . exact And.intro (le_trans (Nat.sub_le _ _) hcurrentH.1)
      (lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurrentH.2)

omit [LinearOrder Root] [Inhabited Root] in
/-- Arithmetic form of the per-span Byzantine fraction: if
`100 * B <= C * (H + B)` and `C <= 100`, then at least the complementary
fraction of the whole span is honest. -/
private theorem complementary_fraction {C H B : Nat}
    (hC : C <= 100) (hfrac : 100 * B <= C * (H + B)) :
    (100 - C) * (H + B) <= 100 * H := by
  have hbyz : (100 - C) * B <= C * H := by
    have hsum : (100 - C) * B + C * B = 100 * B := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [Nat.mul_add] at hfrac
    omega
  calc
    (100 - C) * (H + B) = (100 - C) * H + (100 - C) * B :=
      Nat.mul_add _ _ _
    _ <= (100 - C) * H + C * H := Nat.add_le_add_left hbyz _
    _ = 100 * H := by
      rw [← Nat.add_mul]
      congr 1
      omega

/-- Quantitative future-seat half of
`will_current_target_be_justified`'s prediction.  The only extra economic
premise is `hfloor`, excluding the artificial tiny-active-set branch of
`get_total_active_balance`'s minimum.

No desired quorum or honest-support conclusion is assumed. -/
theorem currentTarget_remaining_honest_le_future_weight
    (hec : BeaconExternalsPremises cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hbb : ByzantineWeightPremises cfg E)
    {store : Store Root}
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hendH : E.SlotWithinHorizon cfg (currentTargetEpochEnd cfg store))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment <=
      E.weight (E.currentTargetAnchorActive cfg)) :
    (E.total_active cfg -
          estimate_committee_weight_between_slots cfg (E.total_active cfg)
            (currentTargetEpochStart cfg store)
            (get_current_slot cfg store - 1)) /
        100 * (100 - cfg.confirmation_byzantine_threshold) <=
      E.weight ((E.currentTargetFutureSpan cfg store).filter
        (fun i => i ∈ E.honest)) := by
  let full := E.span_committee (currentTargetEpochStart cfg store)
    (currentTargetEpochEnd cfg store)
  let elapsed := E.currentTargetElapsedSpan cfg store
  let future := E.currentTargetFutureSpan cfg store
  let estimate := estimate_committee_weight_between_slots cfg (E.total_active cfg)
    (currentTargetEpochStart cfg store) (get_current_slot cfg store - 1)
  let honestFuture := future.filter (fun i => i ∈ E.honest)
  let byzFuture := future.filter (fun i => i ∉ E.honest)
  have hfull : E.total_active cfg = E.weight full := by
    rw [E.total_active_eq_anchorActive_weight cfg hfloor]
    exact congrArg E.weight
      (E.current_epoch_span_eq_anchorActive cfg ext hec hsv hcurrentH hendH hanchorH).symm
  have hwindow : E.weight full <= E.weight elapsed + E.weight future := by
    simpa only [full, elapsed, future, Execution.currentTargetElapsedSpan,
      Execution.currentTargetFutureSpan] using
      (weight_span_committee_split (E := E)
        (currentTargetEpochStart cfg store) (get_current_slot cfg store)
        (currentTargetEpochEnd cfg store))
  obtain ⟨hstartH, hfinishH⟩ := E.elapsed_endpoints_within cfg hcurrentH
  have helapsed : E.weight elapsed <= estimate := by
    simpa only [elapsed, estimate, Execution.currentTargetElapsedSpan] using
      hbb.estimate_sound (currentTargetEpochStart cfg store)
        (get_current_slot cfg store - 1) hstartH hfinishH
  have hremaining : E.total_active cfg - estimate <= E.weight future := by
    apply (Nat.sub_le_iff_le_add').2
    calc
      E.total_active cfg = E.weight full := hfull
      _ <= E.weight elapsed + E.weight future := hwindow
      _ <= estimate + E.weight future := Nat.add_le_add_right helapsed _
  have hweightSplit : E.weight future =
      E.weight honestFuture + E.weight byzFuture := by
    simpa only [honestFuture, byzFuture] using E.weight_split_honest future
  have hfrac : 100 * E.weight byzFuture <=
      cfg.confirmation_byzantine_threshold *
        (E.weight honestFuture + E.weight byzFuture) := by
    have h := hbb.span_fraction (get_current_slot cfg store)
      (currentTargetEpochEnd cfg store) hcurrentH hendH
    change 100 * E.weight byzFuture <=
      cfg.confirmation_byzantine_threshold * E.weight future at h
    rw [hweightSplit] at h
    exact h
  have hC : cfg.confirmation_byzantine_threshold <= 100 :=
    le_trans cfg.confirmation_byzantine_threshold_le (by norm_num)
  have hfutureHonest :
      (100 - cfg.confirmation_byzantine_threshold) * E.weight future <=
        100 * E.weight honestFuture := by
    rw [hweightSplit]
    exact complementary_fraction hC hfrac
  have hscaled :
      100 * ((E.total_active cfg - estimate) / 100 *
          (100 - cfg.confirmation_byzantine_threshold)) <=
        100 * E.weight honestFuture := by
    calc
      100 * ((E.total_active cfg - estimate) / 100 *
          (100 - cfg.confirmation_byzantine_threshold)) =
          (100 * ((E.total_active cfg - estimate) / 100)) *
            (100 - cfg.confirmation_byzantine_threshold) := by ring
      _ <= (E.total_active cfg - estimate) *
          (100 - cfg.confirmation_byzantine_threshold) :=
        Nat.mul_le_mul_right _ (Nat.mul_div_le _ _)
      _ <= E.weight future * (100 - cfg.confirmation_byzantine_threshold) :=
        Nat.mul_le_mul_right _ hremaining
      _ = (100 - cfg.confirmation_byzantine_threshold) * E.weight future :=
        Nat.mul_comm _ _
      _ <= 100 * E.weight honestFuture := hfutureHonest
  have hresult := Nat.le_of_mul_le_mul_left hscaled (by omega : 0 < 100)
  simpa only [estimate, future, honestFuture] using hresult

/-- Already-observed honest score contributors and future honest committee
members are disjoint.  The proof deliberately uses provenance's strict
`attestation_slot + 1 <= current_slot`, rather than disjointness of the
syntactic elapsed/future spans: at slot zero, natural-number subtraction makes
`current_slot - 1 = current_slot`. -/
theorem currentTarget_observed_future_disjoint
    (hec : BeaconExternalsPremises cfg ext E)
    {store : Store Root} {state : BeaconState Root}
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg store) store) :
    Disjoint (E.currentTargetObservedHonestSupporters cfg store state)
      ((E.currentTargetFutureSpan cfg store).filter
        (fun i => i ∈ E.honest)) := by
  rw [Finset.disjoint_left]
  intro i hiObserved hiFuture
  simp only [Execution.currentTargetObservedHonestSupporters,
    List.mem_toFinset, List.mem_filter] at hiObserved
  obtain ⟨_active, _unslashed, latestMessage, hlm, _notEquiv, htarget⟩ :=
    mem_CurrentTargetSupporters cfg hiObserved.1
  obtain ⟨a, _hiAttests, _htargetEpoch, _hroot, hattEpoch,
      happlied, hiCommittee, _hrootKnown, _hrootSlot⟩ :=
    hprov i latestMessage hlm
  have hcurrentEpoch : get_current_store_epoch cfg store =
      get_latest_message_epoch cfg latestMessage := by
    have hepoch := congrArg Checkpoint.epoch htarget
    simpa only [get_current_target, get_checkpoint_for_block] using hepoch
  have haEpoch : compute_epoch_at_slot cfg a.data.slot =
      get_current_store_epoch cfg store := by
    rw [hattEpoch, ← hcurrentEpoch]
  simp only [Finset.mem_filter, Execution.currentTargetFutureSpan,
    Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiFuture
  obtain ⟨⟨s, hs, hiCommitteeFuture⟩, _hiHonest⟩ := hiFuture
  have hsEpoch : compute_epoch_at_slot cfg s =
      get_current_store_epoch cfg store := by
    apply epoch_eq_of_epoch_bounds cfg
    . exact le_trans (current_slot_epoch_bounds cfg store).1 hs.1
    . simpa only [currentTargetEpochEnd, currentTargetEpochStart,
        compute_start_slot_at_epoch, get_current_store_epoch] using hs.2
  have hslots := hec.committee_assignment_unique i a.data.slot s
    hiCommittee hiCommitteeFuture (haEpoch.trans hsEpoch.symm)
  subst s
  exact (Nat.not_succ_le_self a.data.slot)
    (le_trans happlied hs.1)


end Execution

end FastConfirmation.Spec

end
