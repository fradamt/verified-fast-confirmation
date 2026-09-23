module
public import FastConfirmationStatements.Review
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Monotonicity.LiveConfirmation

@[expose] public section

/-!
# Single review entry point

This theorem proves the three fields of `ReviewClaims` from the public safety,
live monotonicity, and scheduled descendant-helper theorems.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The public safety, live monotonicity, and scheduled call guarantees. -/
theorem review_claims : ReviewClaims cfg ext := by
  refine ⟨confirmed_root_safe_from_next_slot cfg ext,
    live_confirmed_root_monotonicity cfg ext, ?_⟩
  have hshape : SelectedResultSafeFromNextSlotOfScheduledCall cfg ext =
      (∀ (E : Execution Root) (h : E.NextSlotSafetyPremises cfg ext)
        {v : ValidatorIndex}, v ∈ E.honest → ∀ {n : ℕ},
        E.IsScheduledFCRCallAt cfg ext v n →
        E.WithinHorizon cfg (n + 1) →
        getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved →
        E.SafeFrom cfg ext
          (find_latest_confirmed_descendant cfg ext (E.fcrStoreAtCall cfg ext v n)
            (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
          (n + 1)) := rfl
  rw [hshape]
  intro E h v hv n hcall hHn1 hselector
  exact Execution.NextSlotSafetyPremises.selected_result_safe_from_next_slot_of_scheduled_call
    (E := E) cfg ext h hv hcall hHn1 hselector

end FastConfirmation.Spec

end
