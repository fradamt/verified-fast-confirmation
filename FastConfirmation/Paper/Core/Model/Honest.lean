import FastConfirmation.Paper.Core.Model.ForkChoice

/-!
# Core / Model / Honest

The honest-validator **voting behavior** — this is *definitional* (what it means
to be an honest validator running the protocol), **not** an environmental
assumption. It is deliberately separate from `Synchrony` (the network/timing
model) and from the economic *Assumptions* (the `β`-bound, static balances).

An honest validator, in each slot whose committee it belongs to, casts exactly
one GHOST vote — for its own (filtered) LMD-GHOST fork-choice head at that slot —
and never equivocates. This is the sole driver that makes honest support of the
safe block accumulate (the engine of Lemmas 1–2).
-/

namespace FastConfirmation

variable {n : ℕ} {P : Type}

/-- The honest-validator voting protocol (definitional honest behavior). -/
structure HonestBehavior (τ : Timing) (fm : FaultModel n) (cm : Committees n)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) (boost : ProposerBoost n P)
    (pb : Weight) (flt : BlockFilter n P) (𝒱 : ViewFamily n P) : Prop where
  /-- An honest committee member of slot `s` casts a vote, in its own view at `st s`,
      for its own fork-choice head at `st s`. -/
  votesHead : ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃s : Slot⦄, v ∈ cm.member s →
    ∃ gv ∈ (𝒱 v (τ.st s)).votesOf v, gv.slot = s ∧
      gv.block = forkChoiceHead τ (gj 𝒱 v (τ.st s)) boost pb flt (𝒱 v (τ.st s)) (τ.st s)
  /-- Honest validators vote only in slots whose committee they belong to. -/
  votesInCommittee : ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃w : Validator n⦄ ⦃t : Time⦄
      ⦃gv : GhostVote n⦄, gv ∈ (𝒱 w t).votesOf v → v ∈ cm.member gv.slot
  /-- Honest validators never equivocate (in any honest view). -/
  noEquivocation : ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃w : Validator n⦄ ⦃t : Time⦄,
    ¬ (𝒱 w t).equivocator v

end FastConfirmation
