module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-! Defines honest validator vote production, assignment, and non-forgery conditions over scheduled executions. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution
/-- Honest validator behavior (validator.md "Attesting", plus the
no-equivocation/no-forgery discipline the slashing rules enforce). -/
structure HonestBehavior (E : Execution Root) : Prop where
  /-- vote-your-head: an honest validator assigned to slot `s` casts, at a
      voting second within slot `s`, exactly the validator-spec attestation
      computed from its own store at that second. -/
  votes_head : ∀ v ∈ E.honest, ∀ s : Slot, v ∈ E.committee s →
    E.SlotWithinHorizon cfg s →
    E.slot_at cfg 0 ≤ s →
    ∃ n index, E.WithinHorizon cfg n ∧ E.slot_at cfg n = s ∧
      E.vote v s =
        some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v)
  /-- An honest slot-`s` vote is sent between the slot start and its attestation
      due time. Phase0 `validator.md` (Attesting) sends on receipt of a valid
      expected proposal or at `get_attestation_due_ms`, whichever is first;
      Gloas `validator.md` sets that due time with `attestation_due_bps`.
      Whole-second execution uses the Python millisecond due time rounded
      down to seconds. -/
  vote_deadline : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.vote v s = some (n, a) →
      E.slot_start cfg s ≤ n ∧
      n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000
  /-- honest validators vote only for slots they are assigned to. -/
  votes_assigned : ∀ v ∈ E.honest, ∀ s : Slot,
    E.vote v s ≠ none → v ∈ E.committee s
  /-- no forgery / no equivocation: every attestation naming an honest
      validator, anywhere in any node's schedule, carries the data of that
      validator's own recorded vote for that slot, sent no later than the
      receiving schedule event (BLS unforgeability and send causality). -/
  no_forgery : ∀ w : ValidatorIndex, ∀ n : ℕ, ∀ (a : Attestation Root)
      (is_from_block : Bool),
    Event.attestation a is_from_block ∈ E.schedule w n →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', m ≤ n ∧
        E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  /-- honest votes are pairwise non-slashable ("How to avoid slashing",
      validator.md — honest source epochs are monotone in target epochs, so
      no double or surround vote): without this a surround pair of genuine
      honest votes would enable an `on_attester_slashing` that erases the
      validator's LMD weight. -/
  not_slashable : ∀ v ∈ E.honest, ∀ s s' : Slot, ∀ n n' : ℕ,
    ∀ a a' : Attestation Root,
    E.vote v s = some (n, a) → E.vote v s' = some (n', a') →
      is_slashable_attestation_data a.data a'.data = false
  /-- Honest validators are unslashed in the ground-registry snapshot; the
      honest set excludes validators with prior slashable offenses. -/
  honest_unslashed : ∀ v ∈ E.honest, (E.registry.getD v default).slashed = false

end FastConfirmation.Spec

end
