module
public import FastConfirmation.Paper.HFC.Model.FFGFilter
public import FastConfirmation.Paper.HFC.Model.Rule

@[expose] public section

/-!
# HFC / Model / HonestFFG

The honest-validator **FFG non-equivocation** discipline — the §4 mirror of the §3.1
`HonestBehavior.noEquivocation`
(`FastConfirmation/Paper/Core/Model/Honest.lean`). It is *definitional* (what it
means to be an honest validator running FFG-Casper), **not** an environmental assumption:
an honest committee member casts at most one FFG link vote per slot — its prescribed
head-vote — whose **source** is the AU-based voting source of its own head and whose **target** is
the checkpoint (at the slot's epoch) of its own LMD-GHOST-HFC
fork-choice head. Paired with `HonestNoForgery` (which delivers `HonestCast` for honest-
attributed messages in honest views), it pins every honest FFG message in an honest view to
that prescribed cast — exactly what the cross-epoch never-filter argument consumes.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **Honest FFG non-equivocation** (definitional; the FFG mirror of
    `HonestBehavior.noEquivocation`,
    `FastConfirmation/Paper/Core/Model/Honest.lean`). An honest validator
    casts **at most one FFG vote per slot** — namely its prescribed head-vote — so any
    FFG message attributed to an honest `i` that appears in *any* honest view (and is a
    `HonestCast`, i.e. genuinely `i`'s own vote at the slot it acts) **is** that prescribed
    cast: its **target** is the checkpoint, at the slot's epoch, of `i`'s own
    `ffgFilter` LMD-GHOST-HFC fork-choice head at `st(slot)`, and its **source** is the
    **voting source** of that head (`ruleVotingSource`) — chain-relative to the head, computed from
    block-contained AU votes, NOT the global greatest-justified. Equivalently: an honest
    validator's per-slot FFG vote is uniquely determined by its own protocol computation,
    so no two distinct FFG targets can be attributed to it at one slot.

    This is **definitional honest behavior**, not a new economic assumption: exactly as
    GHOST `noEquivocation` says an honest validator casts a single GHOST vote per slot
    (its fork-choice head), this says an honest validator casts a single FFG vote per
    slot (its head-checkpoint link). It is what "honest validator running FFG-Casper"
    *means*. It pairs with `HonestNoForgery` (which delivers `HonestCast` for honest-
    attributed messages in honest views): together they pin every honest FFG message in
    an honest view to the validator's prescribed head-checkpoint cast. -/
def HonestFFGNoEquivocation (τ : Timing) (fm : FaultModel n) (_cm : Committees n)
    (bal₀ : Stakes n) (boost : ProposerBoost n (FFGVote n)) (pb : Weight)
    (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  ∀ ⦃m : Message n (FFGVote n)⦄, HonestCast fm 𝒱 τ m →
    m.extra.target = checkpointOf τ
      (forkChoiceHead τ (gjFFG bal₀ 𝒱 m.ghost.validator (τ.st m.ghost.slot)) boost pb
        (ffgFilter bal₀ τ) (𝒱 m.ghost.validator (τ.st m.ghost.slot)) (τ.st m.ghost.slot))
      (τ.epochOf m.ghost.slot) ∧
    m.extra.source = ruleVotingSource bal₀ τ
      (forkChoiceHead τ (gjFFG bal₀ 𝒱 m.ghost.validator (τ.st m.ghost.slot)) boost pb
        (ffgFilter bal₀ τ) (𝒱 m.ghost.validator (τ.st m.ghost.slot)) (τ.st m.ghost.slot))
      (τ.st m.ghost.slot)

end FastConfirmation.HFC

end
