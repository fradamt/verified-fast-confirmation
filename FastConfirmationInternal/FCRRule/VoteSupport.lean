module
public import FastConfirmationStatements.Premises.FCRCallPremises
public import FastConfirmationStatements.Premises.LiveMonotonicity

@[expose] public section

/-! Vote-support predicates derived by the joint safety proof. -/

section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- Exact target support from the spec note on both `will_*` predictions
("This function assumes that all honest validators will be voting in support of the current epoch
target"): from second `n` on, every honest vote of a slot in the target's
epoch carries target `T`.

Honest validators vote the target derived from their own head
(validator.md over fork-choice.md). But that per-validator fact yields
support for *`v`'s* target `T` only under **cross-validator head/boundary
agreement** (every honest head's epoch-boundary block is `T.root`), which is
exactly what the FCR's preceding checks are mid-way through establishing
when the gates are consulted. The joint safety proof derives current-epoch target support at guarded
in-horizon FCR calls. For a previous-epoch result, it derives descendant
target support. The guards matter:
the `will_*` booleans are arithmetically true early in every epoch (the
elapsed-committee estimate is still small) even while honest heads — and
hence honest targets — are split across an adversarial boundary proposal. -/
def HonestVotesSupportTarget (E : Execution Root) (T : Checkpoint Root) (n : ℕ) :
    Prop :=
  E.WithinHorizon cfg n ∧
    ∀ v ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = T.epoch → E.slot_at cfg n ≤ s →
      ∀ k a, E.vote v s = some (k, a) → a.data.target = T

end FastConfirmation.Spec
end

section

/-! ## Selected call support -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- From the call slot on, each honest vote of epoch `e` targets a root
that descends from `result` in the execution's parent graph. This is the
support needed by paper Lemma 42 for a previous-epoch selected result. It
allows honest voters to use different epoch-boundary checkpoints. -/
def HonestVotesTargetDescendFrom (E : Execution Root)
    (result : Root) (e : Epoch) (q : ℕ) : Prop :=
  E.WithinHorizon cfg q ∧
    ∀ w ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = e → E.slot_at cfg q ≤ s →
      ∀ k a, E.vote w s = some (k, a) →
        a.data.target.epoch = e ∧ E.RootDescends a.data.target.root result


end FastConfirmation.Spec

end

end
