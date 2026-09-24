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

end Execution
end FastConfirmation.Spec

end
