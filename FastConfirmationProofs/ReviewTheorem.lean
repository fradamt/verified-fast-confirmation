module
public import FastConfirmationStatements.Review
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.FFG.Concrete.SafetyTranslation

@[expose] public section

/-!
# Single review entry point

This theorem proves the safety field of `ReviewClaims`. The premise of a run
with the concrete bridge translates to the internal premise record
(`ConcreteBridge.SafetyPremises.nextSlotSafetyPremises`), and
`accepted_confirmed_root_safe_from_next_slot` proves the conclusion from it.
-/

namespace FastConfirmation.Spec

variable (Root : Type) [LinearOrder Root] [Inhabited Root]

/-- Stored-output safety theorem at the following-slot deadline, for every
run with the concrete bridge. -/
theorem confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot Root := by
  intro B E h v hv n w hw m hnm hnext hHm
  have hHn : E.WithinHorizon B.setup.cfg n := E.withinHorizon_mono B.setup.cfg hnm hHm
  exact accepted_confirmed_root_safe_from_next_slot B.setup.cfg B.interface E
    (h.nextSlotSafetyPremises hv hHn) v hv n w hw m hnm hnext hHm

/-- The public safety guarantee. -/
theorem review_claims : ReviewClaims Root := by
  exact ⟨confirmed_root_safe_from_next_slot Root⟩

end FastConfirmation.Spec

end
