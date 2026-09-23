module
public import FastConfirmationStatements.Weak.CompleteEvidence

@[expose] public section

/-! Consequences of the complete evidence premise. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

namespace CompleteEvidence

variable (cfg : Config) (ext : Externals Root) {f : FastConfirmationStore Root}

omit [Inhabited Root] in
/-- The frozen raw helper uses the same score as the common fork choice. -/
theorem raw_score_eq (s : Store Root) (n : ForkChoiceNode Root) (bs : BeaconState Root) :
    Strong.get_attestation_score cfg s n bs = get_attestation_score cfg s n bs := rfl

/-- Full freshness removes precisely the extra weak filter. -/
theorem attestation_score_eq (h : CompleteEvidence cfg ext f)
    (n : ForkChoiceNode Root) (bs : BeaconState Root) :
    Strong.get_attestation_score cfg f.store n bs =
      Weak.get_duty_fresh_attestation_score cfg ext f.store n bs := by
  unfold Strong.get_attestation_score Weak.get_duty_fresh_attestation_score
  apply congrArg List.sum
  apply congrArg (List.map _)
  apply List.filter_congr
  intro i _
  cases hlm : f.store.latest_messages i with
  | none => rfl
  | some lm => simp [h.fresh i lm hlm]

theorem block_support_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (b : Root) (a z : Slot) :
    Strong.get_block_support_between_slots cfg ext f.store bs b a z =
      Weak.get_duty_fresh_block_support_between_slots cfg ext f.store bs b a z := by
  have hp : (fun i => (f.store.latest_messages i).any (fun lm =>
      decide (lm.root = b) && decide (i ∉ f.store.equivocating_indices))) =
      (fun i => (f.store.latest_messages i).any (fun lm =>
      decide (lm.root = b) && Weak.is_duty_fresh_message cfg ext f.store i lm &&
        decide (i ∉ f.store.equivocating_indices))) := by
    funext i
    cases hlm : f.store.latest_messages i with
    | none => rfl
    | some lm => simp [h.fresh i lm hlm]
  simp only [Strong.get_block_support_between_slots,
    Weak.get_duty_fresh_block_support_between_slots]
  simp_rw [congrFun hp]

theorem parent_payload_support_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (b : Root) (status : PayloadStatus) (a z : Slot) :
    get_parent_payload_support_between_slots cfg ext f.store bs b status a z =
      Weak.get_duty_fresh_parent_payload_support_between_slots cfg ext f.store bs b status a z := by
  have hp : (fun i => (f.store.latest_messages i).any (fun lm =>
      decide (lm.root = b) && decide (i ∉ f.store.equivocating_indices) &&
        decide ((get_supported_node f.store lm).payload_status = status ∨
          (get_supported_node f.store lm).payload_status = .pending))) =
      (fun i => (f.store.latest_messages i).any (fun lm =>
      decide (lm.root = b) && Weak.is_duty_fresh_message cfg ext f.store i lm &&
        decide (i ∉ f.store.equivocating_indices) &&
        decide ((get_supported_node f.store lm).payload_status = status ∨
          (get_supported_node f.store lm).payload_status = .pending))) := by
    funext i
    cases hlm : f.store.latest_messages i with
    | none => rfl
    | some lm => simp [h.fresh i lm hlm]
  simp only [get_parent_payload_support_between_slots,
    Weak.get_duty_fresh_parent_payload_support_between_slots]
  simp_rw [congrFun hp]

theorem adversarial_weight_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (a z : Slot) :
    Strong.compute_adversarial_weight cfg ext f.store bs a z =
      Weak.compute_adversarial_weight cfg f.store bs a z := by
  simp only [Strong.compute_adversarial_weight, Strong.get_equivocation_score,
    h.no_equivocations, Finset.inter_empty, Finset.filter_empty, Finset.sum_empty,
    Nat.sub_zero, Weak.compute_adversarial_weight]
  change (if Weak.compute_adversarial_weight cfg f.store bs a z > 0 then
    Weak.compute_adversarial_weight cfg f.store bs a z else 0) =
      Weak.compute_adversarial_weight cfg f.store bs a z
  generalize Weak.compute_adversarial_weight cfg f.store bs a z = w
  by_cases hw : w > 0
  · exact if_pos hw
  · rw [if_neg hw]
    exact (Nat.eq_zero_of_not_pos hw).symm

theorem block_adversarial_weight_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (b : Root) :
    Strong.get_adversarial_weight cfg ext f.store bs b =
      Weak.get_adversarial_weight cfg f.store bs b := by
  simp only [Strong.get_adversarial_weight, Weak.get_adversarial_weight,
    adversarial_weight_eq cfg ext h]

theorem support_discount_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (b : Root) :
    Strong.get_support_discount cfg ext f.store bs b =
      Weak.get_support_discount cfg ext f.store bs b := by
  simp only [Strong.get_support_discount, Weak.get_support_discount,
    Strong.compute_empty_slot_support_discount, Weak.compute_empty_slot_support_discount,
    parent_payload_support_eq cfg ext h, adversarial_weight_eq cfg ext h]

theorem safety_threshold_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (b : Root) :
    Strong.compute_safety_threshold cfg ext f.store b bs =
      Weak.compute_safety_threshold cfg ext f.store b bs := by
  simp only [Strong.compute_safety_threshold, Weak.compute_safety_threshold,
    support_discount_eq cfg ext h, block_adversarial_weight_eq cfg ext h]
  rfl

theorem is_one_confirmed_eq (h : CompleteEvidence cfg ext f)
    (bs : BeaconState Root) (b : Root) :
    Strong.is_one_confirmed cfg ext f.store bs b =
      Weak.is_one_confirmed cfg ext f.store bs b := by
  simp only [Strong.is_one_confirmed, Weak.is_one_confirmed,
    attestation_score_eq cfg ext h, safety_threshold_eq cfg ext h]

/-- Complete evidence gives the same check on each root, using previous balances. -/
theorem is_confirmed_chain_safe_eq (h : CompleteEvidence cfg ext f) :
    Strong.is_confirmed_chain_safe cfg ext f =
      Weak.is_confirmed_chain_safe cfg ext f := by
  funext b
  simp only [Strong.is_confirmed_chain_safe, Weak.is_confirmed_chain_safe,
    is_one_confirmed_eq cfg ext h]

theorem honest_ffg_support_eq (h : CompleteEvidence cfg ext f) :
    Strong.compute_honest_ffg_support_for_current_target cfg ext f.store =
      Weak.compute_honest_ffg_support_for_current_target cfg ext f.store := by
  simp only [Strong.compute_honest_ffg_support_for_current_target,
    Weak.compute_honest_ffg_support_for_current_target, adversarial_weight_eq cfg ext h]
  rfl

theorem current_target_eq (h : CompleteEvidence cfg ext f) :
    Strong.will_current_target_be_justified cfg ext f.store =
      Weak.will_current_target_be_justified cfg ext f.store := by
  simp only [Strong.will_current_target_be_justified,
    Weak.will_current_target_be_justified, honest_ffg_support_eq cfg ext h]

theorem carrier_certificate (h : CompleteEvidence cfg ext f) :
    Weak.has_head_broadcast_certificate cfg ext f.store (get_current_balance_source f) =
      true := by
  have h0 : get_current_slot cfg f.store ≠ 0 := Nat.pos_iff_ne_zero.mp h.after_genesis
  simp only [Weak.has_head_broadcast_certificate, Weak.has_broadcast_certificate, h0,
    ↓reduceIte, decide_eq_true_eq]
  exact h.carrier_support

theorem witness_certificate (h : CompleteEvidence cfg ext f) :
    Weak.has_justification_witness_certificate cfg ext f = true := by
  have h0 : get_current_slot cfg f.store ≠ 0 := Nat.pos_iff_ne_zero.mp h.after_genesis
  simp only [Weak.has_justification_witness_certificate, Weak.has_broadcast_certificate, h0,
    ↓reduceIte, decide_eq_true_eq]
  exact h.witness_support

theorem no_conflict_eq (h : CompleteEvidence cfg ext f) :
    Strong.will_no_conflicting_checkpoint_be_justified cfg ext f.store =
      Weak.will_no_conflicting_checkpoint_be_justified cfg ext f.store
        (get_current_balance_source f) := by
  simp only [Strong.will_no_conflicting_checkpoint_be_justified,
    Weak.will_no_conflicting_checkpoint_be_justified, honest_ffg_support_eq cfg ext h,
    carrier_certificate cfg ext h, and_true]
  by_cases ht : get_current_target cfg f.store = f.store.unrealized_justified_checkpoint
  · rw [if_pos ht, if_pos ⟨ht, h.realized_target_carrier ht⟩]
  · simp [ht]

theorem prev_epoch_loop_eq (h : CompleteEvidence cfg ext f) (e : Epoch)
    (roots : List Root) (b : Root) :
    Strong.find_latest_confirmed_descendant_prev_epoch_loop cfg ext f e roots b =
      Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext f e roots b := by
  induction roots generalizing b with
  | nil => rfl
  | cons a roots ih =>
    simp only [Strong.find_latest_confirmed_descendant_prev_epoch_loop,
      Weak.find_latest_confirmed_descendant_prev_epoch_loop, is_one_confirmed_eq cfg ext h, ih]

theorem tentative_loop_eq (h : CompleteEvidence cfg ext f)
    (roots : List Root) (b : Root) :
    Strong.find_latest_confirmed_descendant_tentative_loop cfg ext f roots b =
      Weak.find_latest_confirmed_descendant_tentative_loop cfg ext f roots b := by
  induction roots generalizing b with
  | nil => rfl
  | cons a roots ih =>
    simp only [Strong.find_latest_confirmed_descendant_tentative_loop,
      Weak.find_latest_confirmed_descendant_tentative_loop, is_one_confirmed_eq cfg ext h,
      current_target_eq cfg ext h, ih]

/- The former `banking_eq` whole-store equality is false after the weak-only
checkpoint field was added. See docs/weak-synchrony.md. -/

/-- Conditional helper only: the after-head grid does not meet these premises. -/
theorem certified_head_eq_of_certificate (s : Store Root) (bs : BeaconState Root)
    (hk : (get_head cfg s).root ∈ s.block_roots)
    (ha : is_ancestor s (get_head cfg s) (get_node_for_root (get_head cfg s).root) = true)
    (hc : Weak.has_broadcast_certificate cfg ext s bs (get_head cfg s).root
      (get_block_slot s (get_head cfg s).root) (get_current_slot cfg s - 1) = true) :
    Weak.get_certified_head cfg ext s bs = (get_head cfg s).root := by
  simp [Weak.get_certified_head, Weak.certified_head_search, hk, ha, hc]

/-- Equality on the aligned-head subcase. The unqualified grid theorem is not
asserted: its after-head calls need a separate suffix rejection proof. -/
theorem descendant_eq_of_head_eq (h : CompleteEvidence cfg ext f)
    (hh : Weak.get_certified_head cfg ext f.store (get_current_balance_source f) =
      (get_head cfg f.store).root) (b : Root) :
    Strong.find_latest_confirmed_descendant cfg ext f b =
      Weak.find_latest_confirmed_descendant cfg ext f b := by
  simp only [Strong.find_latest_confirmed_descendant, Weak.find_latest_confirmed_descendant,
    hh, carrier_certificate cfg ext h, witness_certificate cfg ext h,
    and_true, true_and, no_conflict_eq cfg ext h,
    prev_epoch_loop_eq cfg ext h, tentative_loop_eq cfg ext h]

/- Historical getter and handler equalities were removed: the greatest-
unrealized reset can make their outputs differ. See docs/weak-synchrony.md. -/

end CompleteEvidence
end FastConfirmation.Spec

end
