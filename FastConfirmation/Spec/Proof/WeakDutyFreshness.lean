module
public import FastConfirmation.Spec.Model.WeakSynchrony

@[expose] public section

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
    compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg lm := by
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
    (hfresh : recorded_cutoff_epoch cfg store ≤ get_latest_message_epoch cfg lm) :
    is_duty_fresh_message cfg ext store i lm = true := by
  simp only [is_duty_fresh_message, Bool.or_eq_true, decide_eq_true_eq,
    get_latest_message_epoch]
  exact Or.inl hfresh

/-- At the first slot of a new epoch, every recorded message from the
completed epoch passes the weak duty filter. This is the freshness fact
needed by boundary reconfirmation. -/
theorem duty_fresh_previous_epoch_at_boundary {store : Store Root}
    {i : ValidatorIndex} {lm : LatestMessage Root} (e : Epoch)
    (hslot : get_current_slot cfg store =
      compute_start_slot_at_epoch cfg (e + 1))
    (hepoch : get_latest_message_epoch cfg lm = e) :
    is_duty_fresh_message cfg ext store i lm = true := by
  have hL := cfg.slots_per_epoch_pos
  have hmul : (e + 1) * cfg.slots_per_epoch =
      e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
    simp [Nat.add_mul]
  have hend : (e + 1) * cfg.slots_per_epoch - 1 =
      e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    rw [hmul]
    exact Nat.add_sub_assoc (show 1 ≤ cfg.slots_per_epoch from hL) _
  have hle : e * cfg.slots_per_epoch ≤
      (e + 1) * cfg.slots_per_epoch - 1 := by
    rw [hend]
    exact Nat.le_add_right _ _
  have hlt : (e + 1) * cfg.slots_per_epoch - 1 <
      (e + 1) * cfg.slots_per_epoch := by
    rw [hend, hmul]
    exact Nat.add_lt_add_left (Nat.sub_lt hL (by omega)) _
  have hcutoff : recorded_cutoff_epoch cfg store = e := by
    rw [recorded_cutoff_epoch, hslot]
    exact Nat.div_eq_of_lt_le hle hlt
  apply duty_fresh_of_epoch_fresh cfg ext
  rw [hcutoff, hepoch]

/-- A recorded vote cast in the completed epoch is fresh at the next
epoch's first slot. This form uses the vote slot directly. -/
theorem duty_fresh_vote_slot_at_boundary {store : Store Root}
    {i : ValidatorIndex} {lm : LatestMessage Root} (e : Epoch)
    (hslot : get_current_slot cfg store =
      compute_start_slot_at_epoch cfg (e + 1))
    (hlo : compute_start_slot_at_epoch cfg e ≤ lm.slot)
    (hhi : lm.slot < compute_start_slot_at_epoch cfg (e + 1)) :
    is_duty_fresh_message cfg ext store i lm = true := by
  have hepoch : get_latest_message_epoch cfg lm = e := by
    simp only [get_latest_message_epoch, compute_epoch_at_slot]
    apply Nat.div_eq_of_lt_le
    · simpa only [compute_start_slot_at_epoch] using hlo
    · simpa only [compute_start_slot_at_epoch] using hhi
  exact duty_fresh_previous_epoch_at_boundary cfg ext e hslot hepoch

/-- A previous-epoch vote remains usable before its validator's next duty. -/
theorem duty_fresh_of_no_completed_duty {store : Store Root} {i : ValidatorIndex}
    {lm : LatestMessage Root}
    (hepoch : get_latest_message_epoch cfg lm + 1 = recorded_cutoff_epoch cfg store)
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
    (hrecent : recorded_cutoff_epoch cfg store ≤ get_latest_message_epoch cfg lm + 1)
    (hdom : ∀ s : Slot, s ≤ get_current_slot cfg store - 1 →
      i ∈ get_slot_committee cfg ext store s → compute_epoch_at_slot cfg s ≤ get_latest_message_epoch cfg lm) :
    is_duty_fresh_message cfg ext store i lm = true := by
  by_cases hfresh : recorded_cutoff_epoch cfg store ≤ get_latest_message_epoch cfg lm
  · exact duty_fresh_of_epoch_fresh cfg ext hfresh
  have hepoch : get_latest_message_epoch cfg lm + 1 = recorded_cutoff_epoch cfg store :=
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
    (hepoch : get_latest_message_epoch cfg lm < compute_epoch_at_slot cfg t) :
    is_duty_fresh_message cfg ext store i lm = false := by
  cases h : is_duty_fresh_message cfg ext store i lm with
  | false => rfl
  | true =>
      exact False.elim ((Nat.not_le_of_lt hepoch)
        (epoch_le_of_duty_fresh_cell cfg ext h rfl ht hi))

end FastConfirmation.Spec.Weak

end
