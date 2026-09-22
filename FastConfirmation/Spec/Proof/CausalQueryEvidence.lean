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

/-- Literal cast-time reading of support "from the query moment": relevant
votes cast at or after `querySecond` support `target`. -/
def HonestVotesSupportTargetFromMoment
    (E : Execution Root) (target : Checkpoint Root) (querySecond : ℕ) : Prop :=
  E.WithinHorizon cfg querySecond ∧
    ∀ validator ∈ E.honest, ∀ slot : Slot, E.SlotWithinHorizon cfg slot →
      compute_epoch_at_slot cfg slot = target.epoch →
      E.slot_at cfg querySecond ≤ slot →
      ∀ castSecond attestation,
        E.vote validator slot = some (castSecond, attestation) →
        querySecond ≤ castSecond →
        attestation.data.target = target

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

omit [LinearOrder Root] [Inhabited Root] in
/-- The existing whole-slot support premise is exactly the conjunction of its
from-moment and already-cast halves. -/
theorem honestVotesSupportTarget_iff_fromMoment_and_preexisting
    (E : Execution Root) (target : Checkpoint Root) (querySecond : ℕ) :
    HonestVotesSupportTarget cfg E target querySecond ↔
      HonestVotesSupportTargetFromMoment cfg E target querySecond ∧
      PreexistingRelevantHonestVotesSupportTarget cfg E target querySecond := by
  constructor
  · intro hsupport
    refine ⟨⟨hsupport.1, ?_⟩, ?_⟩
    · intro validator hhonest slot hslotH hepoch hqueryLe
        castSecond attestation hvote _hcast
      exact hsupport.2 validator hhonest slot hslotH hepoch hqueryLe
        castSecond attestation hvote
    · intro validator hhonest slot hslotH hepoch hqueryLe
        castSecond attestation hvote _hcast
      exact hsupport.2 validator hhonest slot hslotH hepoch hqueryLe
        castSecond attestation hvote
  · rintro ⟨⟨hqueryH, hfuture⟩, hpast⟩
    refine ⟨hqueryH, ?_⟩
    intro validator hhonest slot hslotH hepoch hqueryLe
      castSecond attestation hvote
    by_cases hcast : querySecond ≤ castSecond
    · exact hfuture validator hhonest slot hslotH hepoch hqueryLe
        castSecond attestation hvote hcast
    · exact hpast validator hhonest slot hslotH hepoch hqueryLe
        castSecond attestation hvote (Nat.lt_of_not_ge hcast)

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

/-- Target agreement attached only to relevant cast actions preceding the
query. -/
def PreexistingRelevantVoteActionsSupportTarget
    (E : Execution Root) (target : Checkpoint Root)
    (runtime : GlobalRuntime Root)
    (queryPosition querySecond : ℕ) : Prop :=
  ∀ cast ∈ runtime.voteCasts,
    cast.actionPosition < queryPosition →
    cast.validator ∈ E.honest →
    E.SlotWithinHorizon cfg cast.slot →
    compute_epoch_at_slot cfg cast.slot = target.epoch →
    E.slot_at cfg querySecond ≤ cast.slot →
    ∀ attestation,
      E.vote cast.validator cast.slot =
        some (cast.executionSecond, attestation) →
      attestation.data.target = target

omit [LinearOrder Root] [Inhabited Root] in
/-- Action coverage/order plus action-level target agreement gives the
already-cast half of whole-slot support. -/
theorem preexistingRelevantHonestVotesSupportTarget_of_actions
    (E : Execution Root) (target : Checkpoint Root)
    (runtime : GlobalRuntime Root)
    (queryPosition querySecond : ℕ)
    (hcoverage : PreexistingVoteActionCoverage cfg E runtime
      queryPosition querySecond)
    (hsupport : PreexistingRelevantVoteActionsSupportTarget cfg E target
      runtime queryPosition querySecond) :
    PreexistingRelevantHonestVotesSupportTarget cfg E target querySecond := by
  intro validator hhonest slot hslotH hepoch hqueryLe
    castSecond attestation hvote hcast
  obtain ⟨cast, hcastMem, hvalidator, hslot, hsecond, hposition⟩ :=
    hcoverage validator hhonest slot hslotH castSecond attestation hvote hcast
  apply hsupport cast hcastMem hposition
  · simpa only [hvalidator] using hhonest
  · simpa only [hslot] using hslotH
  · simpa only [hslot] using hepoch
  · simpa only [hslot] using hqueryLe
  · simpa only [hvalidator, hslot, hsecond] using hvote

omit [LinearOrder Root] [Inhabited Root] in
/-- Literal from-moment support plus exact already-cast action evidence yields
the existing whole-slot support premise.  This theorem is evidence-only. -/
theorem fromMoment_and_preexisting_actions_implies_formal
    (E : Execution Root) (target : Checkpoint Root)
    (runtime : GlobalRuntime Root)
    (queryPosition querySecond : ℕ)
    (hmoment : HonestVotesSupportTargetFromMoment cfg E target querySecond)
    (hcoverage : PreexistingVoteActionCoverage cfg E runtime
      queryPosition querySecond)
    (hsupport : PreexistingRelevantVoteActionsSupportTarget cfg E target
      runtime queryPosition querySecond) :
    HonestVotesSupportTarget cfg E target querySecond := by
  rw [honestVotesSupportTarget_iff_fromMoment_and_preexisting]
  exact ⟨hmoment,
    preexistingRelevantHonestVotesSupportTarget_of_actions cfg E target runtime
      queryPosition querySecond hcoverage hsupport⟩

end CausalQueryEvidence
end FastConfirmation.Spec

end
