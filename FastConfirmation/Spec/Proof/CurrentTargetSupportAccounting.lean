import FastConfirmation.Spec.Proof.EconomicRounding
import FastConfirmation.Spec.Proof.HonestWeight
import FastConfirmation.Spec.Proof.SelectedA32Support

/-!
# Exact accounting for the current-target prediction score

The executable `will_current_target_be_justified` helper begins with
`get_current_target_score`.  This file exposes that score as the ground-truth
weight of a concrete, duplicate-free validator set and separates its honest
and non-honest parts.  It is deliberately only the accounting first step:
turning the honest members into received source-specific FFG attestations and
adding the remaining honest epoch seats are separate temporal obligations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The validator list summed by `get_current_target_score`, before mapping
indices to balances. -/
def CurrentTargetSupporters (store : Store Root) (state : BeaconState Root) :
    List ValidatorIndex :=
  ((get_active_validator_indices state (get_current_epoch cfg state)).filter
      (fun i => !(state.validators.getD i default).slashed)).filter
    (fun i =>
      match store.latest_messages i with
      | none => false
      | some latestMessage =>
          decide (i ∉ store.equivocating_indices) &&
            decide (get_current_target cfg store =
              get_checkpoint_for_block cfg store latestMessage.root
                (get_latest_message_epoch latestMessage)))

/-- Definitional score readback. -/
theorem get_current_target_score_eq_supporters_sum
    (store : Store Root) (state : BeaconState Root)
    (hstate : state = get_pulled_up_head_state cfg ext store) :
    get_current_target_score cfg ext store =
      ((CurrentTargetSupporters cfg store state).map
        (fun i => (state.validators.getD i default).effective_balance)).sum := by
  subst state
  rfl

/-- The score list is duplicate-free because it is a double filter of the
active-index range. -/
theorem CurrentTargetSupporters_nodup
    (store : Store Root) (state : BeaconState Root) :
    (CurrentTargetSupporters cfg store state).Nodup := by
  simp only [CurrentTargetSupporters, get_active_validator_indices]
  exact (((List.nodup_range).filter _).filter _).filter _

/-- Exact membership facts retained by a current-target score contributor. -/
theorem mem_CurrentTargetSupporters
    {store : Store Root} {state : BeaconState Root} {i : ValidatorIndex}
    (hi : i ∈ CurrentTargetSupporters cfg store state) :
    is_active_validator (state.validators.getD i default)
        (get_current_epoch cfg state) = true ∧
      (state.validators.getD i default).slashed = false ∧
      ∃ latestMessage : LatestMessage Root,
        store.latest_messages i = some latestMessage ∧
        i ∉ store.equivocating_indices ∧
        get_current_target cfg store =
          get_checkpoint_for_block cfg store latestMessage.root
            (get_latest_message_epoch latestMessage) := by
  simp only [CurrentTargetSupporters, List.mem_filter,
    get_active_validator_indices, List.mem_range] at hi
  obtain ⟨⟨⟨_hiRange, hactive⟩, hunslashed⟩, hscore⟩ := hi
  cases hlm : store.latest_messages i with
  | none =>
      rw [hlm] at hscore
      simp at hscore
  | some latestMessage =>
      rw [hlm] at hscore
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hscore
      exact ⟨hactive,
        (Bool.not_eq_true_eq_eq_false _).mp hunslashed,
        latestMessage, rfl,
        hscore.1, hscore.2⟩

/-- Split the score exactly into honest and non-honest list sums. -/
theorem current_target_score_honest_split
    (E : Execution Root) (store : Store Root) (state : BeaconState Root)
    (hstate : state = get_pulled_up_head_state cfg ext store) :
    get_current_target_score cfg ext store =
      (((CurrentTargetSupporters cfg store state).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (state.validators.getD i default).effective_balance)).sum +
      (((CurrentTargetSupporters cfg store state).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (state.validators.getD i default).effective_balance)).sum := by
  rw [get_current_target_score_eq_supporters_sum cfg ext store state hstate]
  exact (List.sum_map_filter_add_sum_map_filter_not
    (fun i => i ∈ E.honest)
    (fun i => (state.validators.getD i default).effective_balance)
    (CurrentTargetSupporters cfg store state)).symm

namespace Execution

variable (E : Execution Root)

/-- Every score contributor belongs to the already elapsed part of the
current epoch.  This is the target-score analogue of ordinary LMD supporter
span confinement, and follows directly from latest-message provenance plus
the equality of checkpoint epochs in the score predicate. -/
theorem currentTargetSupporter_mem_elapsed_span
    {store : Store Root} {state : BeaconState Root}
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg store) store)
    {i : ValidatorIndex}
    (hi : i ∈ CurrentTargetSupporters cfg store state) :
    i ∈ E.span_committee
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
      (get_current_slot cfg store - 1) := by
  obtain ⟨_hactive, _hunslashed, latestMessage, hlm, _hnoteq,
      htarget⟩ := mem_CurrentTargetSupporters cfg hi
  obtain ⟨a, hiAttests, htargetEpoch, _hroot, hattEpoch,
      happlied, hiCommittee, _hrootKnown, _hrootSlot⟩ :=
    hprov i latestMessage hlm
  have hcurrentEpoch : get_current_store_epoch cfg store = latestMessage.epoch := by
    have hepoch := congrArg Checkpoint.epoch htarget
    simpa only [get_current_target, get_checkpoint_for_block] using hepoch
  have haEpoch : compute_epoch_at_slot cfg a.data.slot =
      get_current_store_epoch cfg store := by
    rw [hattEpoch, ← hcurrentEpoch]
  refine Finset.mem_biUnion.mpr
    ⟨a.data.slot, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hiCommittee⟩
  · simp only [compute_start_slot_at_epoch]
    rw [← haEpoch]
    simp only [compute_epoch_at_slot]
    exact Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
  · exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le happlied)

/-- On a registry-coherent balance source, any filtered score-list sum is
exactly the execution weight of its finite index set. -/
theorem currentTargetSupporters_filter_sum_eq_weight
    {store : Store Root} {state : BeaconState Root}
    (hval : state.validators = E.registry)
    (p : ValidatorIndex → Bool) :
    ((((CurrentTargetSupporters cfg store state).filter p).map
        (fun i => (state.validators.getD i default).effective_balance)).sum) =
      E.weight (((CurrentTargetSupporters cfg store state).filter p).toFinset) := by
  have hnodup : ((CurrentTargetSupporters cfg store state).filter p).Nodup :=
    (CurrentTargetSupporters_nodup cfg store state).filter p
  have hmap :
      ((CurrentTargetSupporters cfg store state).filter p).map
          (fun i => (state.validators.getD i default).effective_balance) =
        ((CurrentTargetSupporters cfg store state).filter p).map E.weight_of :=
    List.map_congr_left (fun i _ => by
      rw [Execution.weight_of, hval])
  rw [hmap]
  exact (List.sum_toFinset E.weight_of hnodup).symm

/-- Exact ground-truth honest/non-honest decomposition of the executable
current-target score. -/
theorem current_target_score_eq_honest_add_nonhonest_weight
    {store : Store Root} {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext store)
    (hval : state.validators = E.registry) :
    get_current_target_score cfg ext store =
      E.weight (((CurrentTargetSupporters cfg store state).filter
        (fun i => i ∈ E.honest)).toFinset) +
      E.weight (((CurrentTargetSupporters cfg store state).filter
        (fun i => i ∉ E.honest)).toFinset) := by
  rw [current_target_score_honest_split cfg ext E store state hstate,
    E.currentTargetSupporters_filter_sum_eq_weight cfg hval,
    E.currentTargetSupporters_filter_sum_eq_weight cfg hval]

private theorem currentTarget_weight_add_le
    {A B C : Finset ValidatorIndex}
    (hdisjoint : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    E.weight A + E.weight B ≤ E.weight C := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hdisjoint]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.union_subset hAC hBC) (fun _ _ _ => Nat.zero_le _)

private theorem currentTarget_byz_le_net_of_add
    {byz equiv budget : ℕ} (hbudget : byz + equiv ≤ budget) :
    byz ≤ if budget > equiv then budget - equiv else 0 := by
  split_ifs <;> omega

/-- The non-honest current-target score contributors and the active
equivocators are disjoint subsets of the same elapsed-epoch Byzantine span.
Consequently their combined weight fits the prediction helper's pre-discount
Byzantine budget. -/
theorem currentTarget_nonhonest_add_equiv_le_budget
    (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n)) :
    E.weight (((CurrentTargetSupporters cfg (E.store cfg ext v n) state).filter
        (fun i => i ∉ E.honest)).toFinset) +
      get_equivocation_score cfg ext (E.store cfg ext v n) state
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg (E.store cfg ext v n)))
        (get_current_slot cfg (E.store cfg ext v n) - 1) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg state)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg (E.store cfg ext v n)))
          (get_current_slot cfg (E.store cfg ext v n) - 1) /
            100 * cfg.confirmation_byzantine_threshold := by
  let store := E.store cfg ext v n
  let start := compute_start_slot_at_epoch cfg
    (get_current_store_epoch cfg store)
  let finish := get_current_slot cfg store - 1
  have hcurrentH : E.SlotWithinHorizon cfg
      (get_current_slot cfg store) := by
    rw [show get_current_slot cfg store = E.slot_at cfg n by
      exact E.store_current_slot cfg ext v n]
    exact ⟨hnH.2.1, hnH.2.2⟩
  have hstartLe : start ≤ get_current_slot cfg store := by
    simp only [start, compute_start_slot_at_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_mul_le_self _ _
  have hstartH : E.SlotWithinHorizon cfg start :=
    ⟨hstartLe.trans hcurrentH.1,
      by
        simp only [start, compute_start_slot_at_epoch,
          get_current_store_epoch, compute_epoch_at_slot]
        calc
          get_current_slot cfg store / cfg.slots_per_epoch *
                cfg.slots_per_epoch / cfg.slots_per_epoch =
              get_current_slot cfg store / cfg.slots_per_epoch := by
            rw [Nat.mul_comm]
            exact Nat.mul_div_cancel_left _ cfg.slots_per_epoch_pos
          _ < E.verification_horizon := by
            simpa only [compute_epoch_at_slot] using hcurrentH.2⟩
  have hfinishH : E.SlotWithinHorizon cfg finish :=
    ⟨(Nat.sub_le _ _).trans hcurrentH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurrentH.2⟩
  rw [get_equivocation_score_eq_weight cfg ext hec hv n hnH hval
    start finish hfinishH, htab]
  let BS := ((CurrentTargetSupporters cfg store state).filter
    (fun i => i ∉ E.honest)).toFinset
  let EA := EquivActive cfg E store state start finish
  refine (currentTarget_weight_add_le E ?_ ?_ ?_).trans
    (hbb.span_bound start finish hstartH hfinishH)
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [BS, List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨_hactive, _hunslashed, _lm, _hlm, hnotEquiv, _htarget⟩ :=
      mem_CurrentTargetSupporters cfg hiBS.1
    simp only [EA, EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnotEquiv hiEA.1.2
  · intro i hi
    simp only [BS, List.mem_toFinset, List.mem_filter] at hi
    have hnonhonest : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr
      ⟨E.currentTargetSupporter_mem_elapsed_span cfg hprov hi.1,
        hnonhonest⟩
  · intro i hi
    simp only [EA, EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-- The actual non-honest score contribution is bounded by the helper's
post-equivocation `compute_adversarial_weight`. -/
theorem currentTarget_nonhonest_weight_le_adversarial
    (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n)) :
    E.weight (((CurrentTargetSupporters cfg (E.store cfg ext v n) state).filter
        (fun i => i ∉ E.honest)).toFinset) ≤
      compute_adversarial_weight cfg ext (E.store cfg ext v n) state
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg (E.store cfg ext v n)))
        (get_current_slot cfg (E.store cfg ext v n) - 1) := by
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest := by
    intro i hi hih
    exact Execution.honest_not_equivocating cfg ext hhb hec hgen
      hih v n (by assumption) (by assumption) hi
  have hbudget := E.currentTarget_nonhonest_add_equiv_le_budget cfg ext
    hec hbb hv hnH hval htab hne hprov
  let byz := E.weight
    (((CurrentTargetSupporters cfg (E.store cfg ext v n) state).filter
      (fun i => i ∉ E.honest)).toFinset)
  let equiv := get_equivocation_score cfg ext (E.store cfg ext v n) state
    (compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.store cfg ext v n)))
    (get_current_slot cfg (E.store cfg ext v n) - 1)
  let budget := estimate_committee_weight_between_slots cfg
    (get_total_active_balance cfg state)
    (compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.store cfg ext v n)))
    (get_current_slot cfg (E.store cfg ext v n) - 1) /
      100 * cfg.confirmation_byzantine_threshold
  change byz ≤ if budget > equiv then budget - equiv else 0
  change byz + equiv ≤ budget at hbudget
  exact currentTarget_byz_le_net_of_add hbudget

end Execution

end FastConfirmation.Spec
