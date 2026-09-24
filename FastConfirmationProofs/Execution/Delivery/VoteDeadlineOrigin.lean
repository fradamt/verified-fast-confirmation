module
public import FastConfirmationStatements.Premises.Behavior

@[expose] public section

/-! Honest vote roots have a source observation no later than the attestation deadline. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The honest vote itself supplies a deadline-bounded origin for every root
already in the voter's store when the vote is made. -/
theorem honest_vote_root_before_deadline
    (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {s n : ℕ} {a : Attestation Root} {r : Root}
    (hvote : E.vote v s = some (n, a))
    (hroot : r ∈ (E.store cfg ext v n).block_roots) :
    ∃ origin : ℕ,
      E.slot_start cfg s ≤ origin ∧
      origin ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 ∧
      r ∈ (E.store cfg ext v origin).block_roots := by
  refine ⟨n, ?_, ?_, hroot⟩
  · exact (hhb.vote_deadline v hv s n a hvote).1
  · exact (hhb.vote_deadline v hv s n a hvote).2

/-- The paper's strict `A + Δ < S` bound places a message sent by the vote
deadline in the receiver's store before the next slot's first second. The
genuine-boundary guard handles executions whose anchor begins mid-slot. -/
theorem deadline_relay_before_next_slot
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    {s n delta : ℕ}
    (hboundary : E.genesis_store.time ≤ E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000))
    (hdeadline : n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000)
    (hdelta : 0 < delta)
    (hfit : get_attestation_due_ms cfg / 1000 + delta <
      cfg.slot_duration_ms / 1000) :
    n + delta ≤ E.slot_start cfg (s + 1) - 1 ∧
      n < E.slot_start cfg (s + 1) - 1 := by
  obtain ⟨seconds, hseconds⟩ := hdiv
  have hsecondsDiv : cfg.slot_duration_ms / 1000 = seconds := by
    rw [hseconds]
    exact Nat.mul_div_cancel_left seconds (by decide : 0 < (1000 : ℕ))
  have hmul (x : ℕ) :
      x * cfg.slot_duration_ms / 1000 = x * seconds := by
    rw [hseconds, Nat.mul_left_comm x 1000 seconds]
    exact Nat.mul_div_cancel_left (x * seconds) (by decide : 0 < (1000 : ℕ))
  have hslot : E.slot_start cfg (s + 1) =
      E.slot_start cfg s + seconds := by
    simp only [Execution.slot_start]
    rw [hmul (s + 1), hmul s, Nat.add_mul, one_mul]
    have hbound : E.genesis_store.time ≤
        E.genesis_store.genesis_time + s * seconds := by
      simpa only [hsecondsDiv] using hboundary
    omega
  rw [hsecondsDiv] at hfit
  omega

end Execution
end FastConfirmation.Spec

end
