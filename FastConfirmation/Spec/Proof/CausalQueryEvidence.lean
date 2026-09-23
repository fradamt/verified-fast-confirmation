module
public import FastConfirmation.Spec.Proof.AllowedFCRCallTrace
public import FastConfirmation.Spec.Proof.CurrentTargetFutureSupport

@[expose] public section

/-!
# Causal query evidence

This module contains the safety-free evidence adapters needed by a query that
occurs at an exact global action position.  In particular, execution seconds
do not order a vote and a query that occur in the same second.  The production
interface therefore keeps the cast materialization/order obligation explicit.

The conclusion is the existing whole-slot `HonestVotesSupportTarget` premise;
no head-safety or strict-selection result is claimed here.
-/

namespace FastConfirmation.Spec
namespace CausalQueryEvidence

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

open AllowedFCRCalls


/-- The exact complementary half: relevant honest votes cast before the query
also support `target`. -/
def PreexistingRelevantHonestVotesSupportTarget
    (E : Execution Root) (target : Checkpoint Root) (querySecond : ℕ) : Prop :=
  ∀ validator ∈ E.honest, ∀ slot : Slot, E.SlotWithinHorizon cfg slot →
    compute_epoch_at_slot cfg slot = target.epoch →
    E.slot_at cfg querySecond ≤ slot →
    ∀ castSecond attestation,
      E.vote validator slot = some (castSecond, attestation) →
      castSecond < querySecond →
      attestation.data.target = target


/-- The unresolved low-to-high adapter obligation at a query: every relevant
ground vote cast in an earlier execution second is materialized by a matching
global cast observation before the exact query action position.

`GlobalRuntime` alone does not imply this predicate; an implementation trace
adapter must establish it. -/
def PreexistingVoteActionCoverage
    (E : Execution Root) (runtime : GlobalRuntime Root)
    (queryPosition querySecond : ℕ) : Prop :=
  ∀ validator ∈ E.honest, ∀ slot : Slot, E.SlotWithinHorizon cfg slot →
    ∀ castSecond attestation,
      E.vote validator slot = some (castSecond, attestation) →
      castSecond < querySecond →
      ∃ cast ∈ runtime.voteCasts,
        cast.validator = validator ∧ cast.slot = slot ∧
        cast.executionSecond = castSecond ∧
        cast.actionPosition < queryPosition




end CausalQueryEvidence
end FastConfirmation.Spec

end
