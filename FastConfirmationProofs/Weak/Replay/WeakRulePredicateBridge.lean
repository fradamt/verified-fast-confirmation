module
public import FastConfirmationProofs.Weak.Certificates.WeakCertifiedHead
public import FastConfirmationProofs.Weak.Certificates.WeakCertificateDissemination

@[expose] public section

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

/-- Sum monotonicity under sublist for `ℕ`-valued lists (dropping elements can
only shrink the sum). Local restatement of the private helper at
`SupportTransport.lean:32`. -/
private theorem sum_le_sum_of_sublist {l₁ l₂ : List ℕ} (h : List.Sublist l₁ l₂) :
    l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => exact le_refl _
  | cons a _ ih => rw [List.sum_cons]; exact ih.trans (Nat.le_add_left _ _)
  | cons_cons a _ ih => rw [List.sum_cons, List.sum_cons]; exact Nat.add_le_add_left ih a

private theorem sub_guard_mono {P P' A A' : ℕ} (hP : P' ≤ P) (hA : A ≤ A') :
    (if P' > A' then P' - A' else 0) ≤ (if P > A then P - A else 0) := by
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
    F - min A' F + R ≤ F - A + R := by omega

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

/-- The weak fresh-gated discount support is no larger than the strong
discount support on the same span: the weak filter additionally requires
`is_duty_fresh_message`, so its counted set is a subset of the strong
filter's on the same underlying committee union (rule delta 3, module
docstring of `WeakSynchrony`: the discount must be fresh-gated, not just the
main scorer). -/
theorem weak_fresh_block_support_le (store : Store Root) (bs : BeaconState Root)
    (r : Root) (a b : Slot) :
    Weak.get_duty_fresh_block_support_between_slots cfg ext store bs r a b ≤
      get_block_support_between_slots cfg ext store bs r a b := by
  unfold Weak.get_duty_fresh_block_support_between_slots get_block_support_between_slots
  dsimp only
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.monotone_filter_right _ ?_) (fun i _ _ => Nat.zero_le _)
  intro i _hi hib
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hib; simp at hib
  | some lm =>
    rw [hlm] at hib
    simp only [Option.any_some, Bool.and_eq_true] at hib ⊢
    exact ⟨hib.1.1, hib.2⟩

theorem weak_fresh_parent_payload_support_le (store : Store Root) (bs : BeaconState Root)
    (r : Root) (status : PayloadStatus) (a b : Slot) :
    Weak.get_duty_fresh_parent_payload_support_between_slots cfg ext store bs r status a b ≤
      get_parent_payload_support_between_slots cfg ext store bs r status a b := by
  unfold Weak.get_duty_fresh_parent_payload_support_between_slots
    get_parent_payload_support_between_slots
  dsimp only
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.monotone_filter_right _ ?_) (fun i _ _ => Nat.zero_le _)
  intro i _hi hib
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hib; simp at hib
  | some lm =>
    rw [hlm] at hib
    simp only [Option.any_some, Bool.and_eq_true] at hib ⊢
    exact ⟨⟨hib.1.1.1, hib.1.2⟩, hib.2⟩

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
    exact sub_guard_mono (weak_fresh_parent_payload_support_le cfg ext store bs _ _ _ _)
      (weak_adversarial_weight_ge cfg ext store bs _ _)

theorem weak_safety_threshold_ge (store : Store Root) (r : Root) (bs : BeaconState Root) :
    compute_safety_threshold cfg ext store r bs ≤
      Weak.compute_safety_threshold cfg ext store r bs := by
  unfold compute_safety_threshold Weak.compute_safety_threshold
  dsimp only
  exact threshold_mono (weak_get_adversarial_weight_ge cfg ext store bs r)
    (weak_support_discount_le cfg ext store bs r)

/-- The weak fresh-gated attestation score is no larger than the strong score
at the same node: the weak filter additionally requires `is_duty_fresh_message`
(rule delta 3), so its counted set is a subset of the strong filter's, in the
same conjunct order `(equiv && fresh) && ancestor` against `equiv && ancestor`
— the idiom at `SupportTransport.lean:70-91`, without the ancestor-transport
step since the node is unchanged. -/
theorem weak_duty_fresh_attestation_score_le (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) :
    Weak.get_duty_fresh_attestation_score cfg ext store node state ≤
      get_attestation_score cfg store node state := by
  simp only [Weak.get_duty_fresh_attestation_score, get_attestation_score]
  refine sum_le_sum_of_sublist ?_
  refine List.Sublist.map _ ?_
  refine List.monotone_filter_right _ ?_
  intro i hib
  cases hlm : store.latest_messages i with
  | none => simp [hlm] at hib
  | some lm =>
    simp only [hlm, Bool.and_eq_true] at hib ⊢
    exact ⟨hib.1.1, hib.2⟩

theorem is_one_confirmed_of_weak (store : Store Root) (bs : BeaconState Root) (r : Root)
    (h : Weak.is_one_confirmed cfg ext store bs r = true) :
    is_one_confirmed cfg ext store bs r = true := by
  simp only [Weak.is_one_confirmed, decide_eq_true_eq] at h
  simp only [is_one_confirmed, decide_eq_true_eq]
  exact lt_of_le_of_lt (weak_safety_threshold_ge cfg ext store r bs)
    (lt_of_lt_of_le h (weak_duty_fresh_attestation_score_le cfg ext store _ bs))

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

/-- B8, rule delta 4. The weak short-circuit additionally requires
`Weak.has_head_broadcast_certificate`; the strong side does not. Casing on the
strong condition first (`heq`) handles this: when it holds the strong
`if_pos` closes the goal outright (`hc.1` in the weak-true sub-case just
witnesses the same fact), and when it fails, both sides fall through to their
(unchanged) arithmetic branch. -/
theorem will_no_conflicting_of_weak (store : Store Root) (bs : BeaconState Root)
    (h : Weak.will_no_conflicting_checkpoint_be_justified cfg ext store bs = true) :
    will_no_conflicting_checkpoint_be_justified cfg ext store = true := by
  have hm := weak_honest_ffg_support_le cfg ext store
  unfold Weak.will_no_conflicting_checkpoint_be_justified at h
  unfold will_no_conflicting_checkpoint_be_justified
  dsimp only at h ⊢
  by_cases heq : get_current_target cfg store = store.unrealized_justified_checkpoint
  · simp [heq]
  · rw [if_neg heq]
    rw [if_neg (fun hc => heq hc.1)] at h
    simp only [decide_eq_true_eq] at h ⊢
    exact lt_of_lt_of_le h (Nat.mul_le_mul_left 3 hm)

end FastConfirmation.Spec

end
