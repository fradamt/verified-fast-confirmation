module
public import FastConfirmationProofs.FFG.Concrete.TransitionFrames

@[expose] public section

/-! Proves the guards of a successful concrete `process_attestation` call that
the canonical inclusion evidence reads: the target epoch is the epoch of the
vote slot, the inclusion delay has passed, the call keeps the state slot, and
every attester is a member of a scheduled committee of the vote slot whose
index is below the committee count of the target epoch. Python:
`specs/gloas/beacon-chain.md:2336-2420`, `process_attestation`;
`specs/electra/beacon-chain.md:801-819`, `get_attesting_indices`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-- A list loop in `Except` whose body always continues checks a property of
each element when it succeeds. -/
theorem forIn_except_ok_mem {ε σ α : Type} (P : α → Prop)
    {f : α → σ → Except ε (ForInStep σ)}
    (hf : ∀ a s r, f a s = .ok r → P a ∧ ∃ s', r = .yield s') :
    ∀ (L : List α) (s s' : σ), forIn L s f = .ok s' → ∀ a ∈ L, P a
  | [], _, _, _, a, ha => absurd ha List.not_mem_nil
  | x :: L, s, s', h, a, ha => by
    simp only [List.forIn_cons, except_bind_eq_ok] at h
    obtain ⟨r, hr, hrest⟩ := h
    obtain ⟨hx, t, rfl⟩ := hf x s r hr
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx
    · exact forIn_except_ok_mem P hf L t s' hrest a ha

theorem process_attestation_guards [DecidableEq Root] {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {vote : FFGWireAttestation Root} {parentSlot : Slot}
    (h : process_attestation cfg preset schedule state vote parentSlot = .ok next) :
    vote.data.target.epoch = compute_epoch_at_slot cfg vote.data.slot ∧
      vote.data.slot + preset.min_attestation_inclusion_delay ≤ state.slot ∧
      next.slot = state.slot ∧
      ∃ count, schedule.count vote.data.target.epoch = some count ∧
        ∀ ci ∈ get_committee_indices vote.committee_bits, ci < count := by
  unfold process_attestation at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨_, -, _, hepoch, _, hdelay, _, -, _, -, count, hcount, _, hloop, _, -, flags, -, _, -,
    _, -, h⟩ := h
  refine ⟨?_, ?_, ?_, count, ?_, ?_⟩
  · simpa only [beq_iff_eq] using guard_eq_ok.mp hepoch
  · simpa only [decide_eq_true_eq] using guard_eq_ok.mp hdelay
  · split at h <;> (obtain rfl := except_pure_eq_ok.mp h; rfl)
  · cases hc : schedule.count vote.data.target.epoch with
    | none => simp [hc] at hcount
    | some n =>
      simp only [hc] at hcount
      rw [except_pure_eq_ok.mp hcount]
  · refine forIn_except_ok_mem (· < count) ?_ _ 0 _ hloop
    intro a s r hr
    simp only [except_bind_eq_ok] at hr
    obtain ⟨_, hg, _, -, _, -, _, -, _, -, _, -, hr⟩ := hr
    exact ⟨by simpa only [decide_eq_true_eq] using guard_eq_ok.mp hg, _,
      (except_pure_eq_ok.mp hr).symm⟩

end FastConfirmation.Spec.ConcreteFFG

end
