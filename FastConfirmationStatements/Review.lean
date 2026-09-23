module
public import FastConfirmationStatements.Claims

@[expose] public section

/-!
# Public FCR review claims

The three fields claim that a confirmed root is safe from the next slot,
that live confirmed roots remain monotone, and that the result of a scheduled
descendant-helper call is safe from the next slot. The first and third fields
use `Execution.NextSlotSafetyPremises`; the second also uses
`LiveMonotonicityPremises` through `LiveConfirmedRootMonotonicity`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The scheduled helper result has the exact hypotheses and conclusion of
`Execution.NextSlotSafetyPremises.selected_result_safe_from_next_slot_of_scheduled_call`. -/
def SelectedResultSafeFromNextSlotOfScheduledCall : Prop :=
  ∀ (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext)
    {v : ValidatorIndex}, v ∈ E.honest → ∀ {n : ℕ},
    E.IsScheduledFCRCallAt cfg ext v n →
    E.WithinHorizon cfg (n + 1) →
    getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved →
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
      (n + 1)

/-- The three public executable FCR claims reviewed together. -/
structure ReviewClaims : Prop where
  confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot cfg ext
  live_confirmed_root_monotonicity : LiveConfirmedRootMonotonicity cfg ext
  selected_result_safe_from_next_slot_of_scheduled_call :
    SelectedResultSafeFromNextSlotOfScheduledCall cfg ext

end FastConfirmation.Spec

end
