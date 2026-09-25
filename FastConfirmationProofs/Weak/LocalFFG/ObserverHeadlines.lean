module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverConditionalHeadlines
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunPaperA32

/-! Non-honest observer safety follows from shared network and local input contracts. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root) (E : Execution Root)

/-- A non-honest observer's weak confirmed root is safe from the next slot.
All actual-run FFG laws are derived from the restricted premises. -/
theorem nonhonest_weak_confirmed_root_safe_from_next_slot
    {obs : ValidatorIndex} (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n :=
  E.nonhonest_weak_confirmed_root_safe_from_next_slot_of_trustedInterpretation cfg ext
    hobs premises (ActualRunFFG.exactInterpretation hobs premises) rfl
    (ActualRunFFG.exactInterpretation_finalizationDelay hobs premises)
    (ActualRunFFG.exactInterpretation_paperA32 hobs premises)
    (ActualRunFFG.exactInterpretation_checkpointClosure hobs premises)
    (ActualRunFFG.exactInterpretation_exactLinkValidity hobs premises)

/-- Every honest endpoint's head contains the weak confirmed root from the
following slot. No timed receipt at the observer is a premise. -/
theorem nonhonest_weak_confirmed_root_on_honest_heads_from_next_slot
    {obs : ValidatorIndex} (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs)
    {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakConfirmed cfg ext obs n)) = true :=
  E.nonhonest_weak_confirmed_root_on_honest_heads_from_next_slot_of_trustedInterpretation
    cfg ext hobs premises (ActualRunFFG.exactInterpretation hobs premises) rfl
    (ActualRunFFG.exactInterpretation_finalizationDelay hobs premises)
    (ActualRunFFG.exactInterpretation_paperA32 hobs premises)
    (ActualRunFFG.exactInterpretation_checkpointClosure hobs premises)
    (ActualRunFFG.exactInterpretation_exactLinkValidity hobs premises)
    hw hnm hnext hHm

end Execution
end FastConfirmation.Spec
end
