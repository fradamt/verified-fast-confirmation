module
public import FastConfirmationWitnesses.NonVacuity.FullTwelve

@[expose] public section

/-! The twelve-second execution satisfies operational premises through a finite slot table. -/

namespace FastConfirmation.Spec.FullTwelveWitness

open AcceptedActualFCRJointNonVacuityBase


/-- Ordinary boundary events plus three within-slot receipts. -/
def slotEvents (w s o : ℕ) : List (Event R) :=
  if s = 0 ∧ o = 4 ∧ w = 0 then [.attestation vote0 false]
  else if s = 0 ∧ o = 6 ∧ w = 1 then [.attestation vote0 false]
  else if s = 1 ∧ o = 2 ∧ w = 1 then [.block childSignedBlock]
  else if o = 0 then
    if s = 1 ∧ w = 1 then [.attestation vote0 false]
    else witnessSchedule w s
  else []

private theorem schedule_at_slot (w s o : ℕ) (ho : o < 12) :
    schedule w (12 * s + o) = slotEvents w s o := by
  by_cases hs : s ≤ 16
  · interval_cases s <;> interval_cases o <;>
      simp [schedule, slotEvents, witnessSchedule, vote0, vote1, vote2,
        vote3, vote4, vote5, vote6, vote7, vote8, vote9, vote10,
        vote11, vote12, vote13, vote14, vote15]
  · have hlarge : 192 < 12 * s + o := by omega
    have h0 : s ≠ 0 := by omega
    have h1 : s ≠ 1 := by omega
    have h7 : s ≠ 7 := by omega
    have hnot : ¬ (2 ≤ s ∧ s ≤ 16) := by omega
    simp [schedule, slotEvents, witnessSchedule, h0, h1, h7, hnot,
      show 12 * s + o ≠ 4 by omega, show 12 * s + o ≠ 6 by omega,
      show 12 * s + o ≠ 12 by omega, show 12 * s + o ≠ 14 by omega,
      show 12 * s + o ≠ 84 by omega, show 12 * s + o ≠ 24 by omega,
      show 12 * s + o ≠ 36 by omega, show 12 * s + o ≠ 48 by omega,
      show 12 * s + o ≠ 60 by omega, show 12 * s + o ≠ 72 by omega,
      show 12 * s + o ≠ 96 by omega, show 12 * s + o ≠ 108 by omega,
      show 12 * s + o ≠ 120 by omega, show 12 * s + o ≠ 132 by omega,
      show 12 * s + o ≠ 144 by omega, show 12 * s + o ≠ 156 by omega,
      show 12 * s + o ≠ 168 by omega, show 12 * s + o ≠ 180 by omega,
      show 12 * s + o ≠ 192 by omega]

theorem schedule_by_slot (w n : ℕ) :
    run.schedule w n = slotEvents w (n / 12) (n % 12) := by
  change schedule w n = _
  have h := schedule_at_slot w (n / 12) (n % 12) (Nat.mod_lt _ (by decide))
  simpa only [Nat.div_add_mod] using h

private theorem boundary_vote_before {w q a ifb}
    (h : Event.attestation a ifb ∈ witnessSchedule w q) :
    ∃ s, s < 16 ∧ a = vote s ∧ s < q := by
  unfold witnessSchedule at h
  split_ifs at h with h1 h7 hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Event.attestation.injEq] at h
    rcases h with h | h | h | h
    · refine ⟨6, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
    · refine ⟨4, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
    · refine ⟨5, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
    · refine ⟨6, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨q - 1, ?_, h.1, ?_⟩ <;> (simp only [Slot] at *; omega)
  · simp at h

theorem scheduled_attestation {w n a ifb}
    (h : Event.attestation a ifb ∈ run.schedule w n) :
    ∃ s, s < 16 ∧ a = vote s ∧ 12 * s + 3 ≤ n := by
  rw [schedule_by_slot] at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 ho h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · obtain ⟨s, hs, ha, hsq⟩ := boundary_vote_before h
    refine ⟨s, hs, ha, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h

theorem honest_behavior : HonestBehavior cfg ext run := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := horizon_slot hs
    have hvmod : v = s % 4 := by
      simpa [run, witnessCommittee] using hcommittee
    subst v
    refine ⟨12 * s + 3, 0, time_within ?_, ?_,
      vote_head_at_deadline hslt⟩
    · (simp only [Slot] at *; omega)
    · rw [slot_at_eq]
      (simp only [Slot] at *; omega)
  · intro v hv s n a hvote
    obtain ⟨_, _, rfl, _⟩ := recorded_vote_some_iff.mp hvote
    rw [slot_start_eq, due_eq]
    (simp only [Slot] at *; omega)
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨⟨n, a⟩, hna⟩
    obtain ⟨hs, hvmod, _, _⟩ := recorded_vote_some_iff.mp hna
    simpa [run, witnessCommittee, hvmod]
  · intro w n a ifb hschedule v hv hvin
    obtain ⟨s, hs, rfl, hsent⟩ := scheduled_attestation hschedule
    have hvmod : v = s % 4 := by simpa [vote] using hvin
    refine ⟨12 * s + 3, vote s, hsent, ?_, rfl⟩
    rw [vote_data_slot]
    exact recorded_vote_some_iff.mpr ⟨hs, hvmod, rfl, rfl⟩
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hs, hvmod, _, rfl⟩ := recorded_vote_some_iff.mp hvote
    obtain ⟨hs', hvmod', _, rfl⟩ := recorded_vote_some_iff.mp hvote'
    exact witnessHonestBehavior.not_slashable v hv s s' s s'
      (vote s) (vote s') (witness_vote_some_iff.mpr ⟨hs, hvmod, rfl, rfl⟩)
      (witness_vote_some_iff.mpr ⟨hs', hvmod', rfl, rfl⟩)
  · intro v hv
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by simpa [run] using hv) with
      rfl | rfl | rfl | rfl <;> decide

end FastConfirmation.Spec.FullTwelveWitness
end
