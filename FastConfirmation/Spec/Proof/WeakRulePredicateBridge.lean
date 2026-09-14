import FastConfirmation.Spec.Proof.WeakCertificateDissemination

/-!
# Spec / Proof / WeakRulePredicateBridge

Weak ⇒ strong monotonicity of every rule predicate (B1–B8 of the one-shot
weak-safety design, docs/weak-synchrony.md): the weak budget drops the
equivocation discount and is therefore no smaller, the empty-slot support
discount is therefore no larger, the LMD safety threshold no smaller, and the
projected honest FFG support no larger — so `Weak.is_one_confirmed`,
`Weak.will_current_target_be_justified` and
`Weak.will_no_conflicting_checkpoint_be_justified` each imply their strong
counterparts on the same store. These bridges let the weak selector's trace
reuse strong predicate-level lemmas; only selector-mentioning lemmas need weak
twins.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

private theorem sub_guard_antitone {P A A' : ℕ} (h : A ≤ A') :
    (if P > A' then P - A' else 0) ≤ (if P > A then P - A else 0) := by
  split_ifs <;> omega

private theorem threshold_mono {M P A A' D D' : ℕ} (hA : A ≤ A') (hD : D' ≤ D) :
    (if D < M + P + 2 * A then (M + P + 2 * A - D) / 2 else 0) ≤
      (if D' < M + P + 2 * A' then (M + P + 2 * A' - D') / 2 else 0) := by
  split_ifs with h1 h2 h2
  · exact Nat.div_le_div_right (by omega)
  · omega
  · exact Nat.zero_le _
  · exact Nat.le_refl 0

private theorem ffg_antitone {F A A' R : ℕ} (h : A ≤ A') :
    F - min A' F + R ≤ F - min A F + R := by omega

theorem weak_adversarial_weight_ge (store : Store Root) (bs : BeaconState Root)
    (a b : Slot) :
    compute_adversarial_weight cfg ext store bs a b ≤
      Weak.compute_adversarial_weight cfg store bs a b := by
  unfold compute_adversarial_weight Weak.compute_adversarial_weight
  dsimp only
  split_ifs
  · exact Nat.sub_le _ _
  · exact Nat.zero_le _

theorem weak_get_adversarial_weight_ge (store : Store Root) (bs : BeaconState Root)
    (r : Root) :
    get_adversarial_weight cfg ext store bs r ≤
      Weak.get_adversarial_weight cfg store bs r := by
  unfold get_adversarial_weight Weak.get_adversarial_weight
  dsimp only
  split_ifs <;> exact weak_adversarial_weight_ge cfg ext store bs _ _

theorem weak_support_discount_le (store : Store Root) (bs : BeaconState Root)
    (r : Root) :
    Weak.get_support_discount cfg ext store bs r ≤
      get_support_discount cfg ext store bs r := by
  unfold Weak.get_support_discount get_support_discount
    Weak.compute_empty_slot_support_discount compute_empty_slot_support_discount
  dsimp only
  by_cases h : (store.blocks (store.blocks r).parent_root).slot + 1 = (store.blocks r).slot
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact sub_guard_antitone (weak_adversarial_weight_ge cfg ext store bs _ _)

theorem weak_safety_threshold_ge (store : Store Root) (r : Root) (bs : BeaconState Root) :
    compute_safety_threshold cfg ext store r bs ≤
      Weak.compute_safety_threshold cfg ext store r bs := by
  unfold compute_safety_threshold Weak.compute_safety_threshold
  dsimp only
  exact threshold_mono (weak_get_adversarial_weight_ge cfg ext store bs r)
    (weak_support_discount_le cfg ext store bs r)

theorem is_one_confirmed_of_weak (store : Store Root) (bs : BeaconState Root) (r : Root)
    (h : Weak.is_one_confirmed cfg ext store bs r = true) :
    is_one_confirmed cfg ext store bs r = true := by
  simp only [Weak.is_one_confirmed, decide_eq_true_eq] at h
  simp only [is_one_confirmed, decide_eq_true_eq]
  exact lt_of_le_of_lt (weak_safety_threshold_ge cfg ext store r bs) h

theorem weak_honest_ffg_support_le (store : Store Root) :
    Weak.compute_honest_ffg_support_for_current_target cfg ext store ≤
      compute_honest_ffg_support_for_current_target cfg ext store := by
  unfold Weak.compute_honest_ffg_support_for_current_target
    compute_honest_ffg_support_for_current_target
  dsimp only
  exact ffg_antitone (weak_adversarial_weight_ge cfg ext store _ _ _)

theorem will_current_target_be_justified_of_weak (store : Store Root)
    (h : Weak.will_current_target_be_justified cfg ext store = true) :
    will_current_target_be_justified cfg ext store = true := by
  have hm := weak_honest_ffg_support_le cfg ext store
  unfold Weak.will_current_target_be_justified at h
  unfold will_current_target_be_justified
  dsimp only at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  exact le_trans h (Nat.mul_le_mul_left 3 hm)

theorem will_no_conflicting_of_weak (store : Store Root)
    (h : Weak.will_no_conflicting_checkpoint_be_justified cfg ext store = true) :
    will_no_conflicting_checkpoint_be_justified cfg ext store = true := by
  have hm := weak_honest_ffg_support_le cfg ext store
  unfold Weak.will_no_conflicting_checkpoint_be_justified at h
  unfold will_no_conflicting_checkpoint_be_justified
  dsimp only at h ⊢
  split_ifs at h with hc
  · simp [hc]
  · rw [if_neg hc]
    simp only [decide_eq_true_eq] at h ⊢
    exact lt_of_lt_of_le h (Nat.mul_le_mul_left 3 hm)

end FastConfirmation.Spec
