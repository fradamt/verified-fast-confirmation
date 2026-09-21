import FastConfirmation.Spec.Model.WeakSynchrony

/-!
# Duty-based vote freshness

The executable filter preserves a previous-epoch cell until a newer assigned
duty has completed. These lemmas establish completed-duty domination, retention
before the next duty, and exclusion after a newer completed duty. They require
no observer delivery assumption.
-/

namespace FastConfirmation.Spec.Weak

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Completed-duty domination

A duty-fresh cell dominates the epoch of every completed assigned duty of
its validator. Committee readback connects this executable fact to honest
votes. It does not require delivery to the observer.
-/

theorem epoch_le_of_duty_fresh_cell {store : Store Root} {i : ValidatorIndex}
    {lm : LatestMessage Root}
    (hfresh : Weak.is_duty_fresh_message cfg ext store i lm = true)
    {es : Slot} (hes : es = get_current_slot cfg store - 1)
    {t : Slot} (ht : t ≤ es)
    (hassigned : i ∈ get_slot_committee cfg ext store t) :
    compute_epoch_at_slot cfg t ≤ lm.epoch := by
  have hupper : compute_epoch_at_slot cfg t ≤ recorded_cutoff_epoch cfg store := by
    unfold recorded_cutoff_epoch
    rw [← hes]
    exact Nat.div_le_div_right ht
  have hf := hfresh
  simp only [Weak.is_duty_fresh_message, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, get_latest_message_epoch] at hf
  rcases hf with hcurrent | ⟨hprevious, hnone⟩
  · exact hupper.trans hcurrent
  · by_contra hlate
    have heq : compute_epoch_at_slot cfg t = recorded_cutoff_epoch cfg store :=
      le_antisymm hupper (hprevious ▸ Nat.succ_le_of_lt (Nat.lt_of_not_ge hlate))
    have hstart : compute_start_slot_at_epoch cfg (recorded_cutoff_epoch cfg store) ≤ t := by
      rw [← heq]
      exact Nat.div_mul_le_self t cfg.slots_per_epoch
    exact hnone (Finset.mem_biUnion.mpr
      ⟨t, Finset.mem_Icc.mpr ⟨hstart, hes ▸ ht⟩, hassigned⟩)

/-- Every cell admitted by the old epoch cutoff is admitted by the duty filter. -/
theorem duty_fresh_of_epoch_fresh {store : Store Root} {i : ValidatorIndex}
    {lm : LatestMessage Root}
    (hfresh : recorded_cutoff_epoch cfg store ≤ lm.epoch) :
    is_duty_fresh_message cfg ext store i lm = true := by
  simp only [is_duty_fresh_message, Bool.or_eq_true, decide_eq_true_eq,
    get_latest_message_epoch]
  exact Or.inl hfresh

/-- A previous-epoch vote remains usable before its validator's next duty. -/
theorem duty_fresh_of_no_completed_duty {store : Store Root} {i : ValidatorIndex}
    {lm : LatestMessage Root}
    (hepoch : lm.epoch + 1 = recorded_cutoff_epoch cfg store)
    (hno : ∀ s ∈ Finset.Icc
        (compute_start_slot_at_epoch cfg (recorded_cutoff_epoch cfg store))
        (get_current_slot cfg store - 1), i ∉ get_slot_committee cfg ext store s) :
    is_duty_fresh_message cfg ext store i lm = true := by
  simp only [is_duty_fresh_message, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, get_latest_message_epoch]
  refine Or.inr ⟨hepoch, ?_⟩
  intro hmem
  obtain ⟨s, hs, hi⟩ := Finset.mem_biUnion.mp hmem
  exact hno s hs hi

/-- The duty filter loses no recent cell whose epoch already covers every
completed assigned duty. Timely participation and receipt can supply this
condition; the safety theorem does not assume that receipt. -/
theorem duty_fresh_of_completed_duty_domination {store : Store Root}
    {i : ValidatorIndex} {lm : LatestMessage Root}
    (hrecent : recorded_cutoff_epoch cfg store ≤ lm.epoch + 1)
    (hdom : ∀ s : Slot, s ≤ get_current_slot cfg store - 1 →
      i ∈ get_slot_committee cfg ext store s → compute_epoch_at_slot cfg s ≤ lm.epoch) :
    is_duty_fresh_message cfg ext store i lm = true := by
  by_cases hfresh : recorded_cutoff_epoch cfg store ≤ lm.epoch
  · exact duty_fresh_of_epoch_fresh cfg ext hfresh
  have hepoch : lm.epoch + 1 = recorded_cutoff_epoch cfg store :=
    le_antisymm (Nat.succ_le_of_lt (Nat.lt_of_not_ge hfresh)) hrecent
  apply duty_fresh_of_no_completed_duty cfg ext hepoch
  intro s hs hi
  have hbounds := Finset.mem_Icc.mp hs
  have hstart : recorded_cutoff_epoch cfg store ≤ compute_epoch_at_slot cfg s :=
    (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2 hbounds.1
  exact hfresh (hstart.trans (hdom s hbounds.2 hi))

/-- A known completed duty in a later epoch excludes the recorded old cell. -/
theorem duty_fresh_false_of_newer_completed_duty {store : Store Root}
    {i : ValidatorIndex} {lm : LatestMessage Root} {t : Slot}
    (ht : t ≤ get_current_slot cfg store - 1)
    (hi : i ∈ get_slot_committee cfg ext store t)
    (hepoch : lm.epoch < compute_epoch_at_slot cfg t) :
    is_duty_fresh_message cfg ext store i lm = false := by
  cases h : is_duty_fresh_message cfg ext store i lm with
  | false => rfl
  | true =>
      exact False.elim ((Nat.not_le_of_lt hepoch)
        (epoch_le_of_duty_fresh_cell cfg ext h rfl ht hi))

end FastConfirmation.Spec.Weak
