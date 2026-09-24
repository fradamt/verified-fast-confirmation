import FastConfirmationInternal.Weak.ObserverIndependence
import FastConfirmationProofs.ForkChoice.Head.HeadMembership

open FastConfirmation.Spec FastConfirmation.Spec.Execution

section
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E E' : Execution Root} {obs : ValidatorIndex}

example (hobs : obs ∉ E.honest) (h : E.SameOutsideObserver E' obs)
    (hP : E.WeakObserverRestrictedPremises cfg ext obs)
    (hlocal : E'.ObserverLocalInputs cfg ext obs) :
    Nonempty (E'.WeakObserverRestrictedPremises cfg ext obs) :=
  (weakObserverRestrictedPremises_observer_independent cfg ext hobs h hP hlocal).2

/-- Any replacement input schedule is in the oracle's change domain. -/
example (replacement : ℕ → List (Event Root))
    (hobs : obs ∉ E.honest)
    (hP : E.WeakObserverRestrictedPremises cfg ext obs)
    (hlocal : ({ E with schedule := fun w n =>
      if w = obs then replacement n else E.schedule w n } : Execution Root).ObserverLocalInputs cfg ext obs) :
    Nonempty (({ E with schedule := fun w n =>
      if w = obs then replacement n else E.schedule w n } : Execution Root).WeakObserverRestrictedPremises cfg ext obs) := by
  apply (weakObserverRestrictedPremises_observer_independent cfg ext hobs _ hP hlocal).2
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro w hw
  funext n
  simp only [if_neg hw]

/-- The one live weak-path hji projection is replaced by the existing domain. -/
theorem h5_head_known_without_hji
    (hP : E.WeakObserverRestrictedPremises cfg ext obs)
    {w : ValidatorIndex} (hw : w ∈ E.honest.erase obs) (n : ℕ)
    (hn : E.WithinHorizon cfg n) :
    (get_head cfg (E.store cfg ext w n)).root ∈ (E.store cfg ext w n).block_roots := by
  have hwne : w ≠ obs := (Finset.mem_erase.mp hw).1
  have hk := hP.core.base.domain.justified_root_known w hw n hn
  rw [withoutObserver_store cfg ext E obs w hwne n] at hk
  rcases get_head_root_mem_or cfg (E.store cfg ext w n) with hm | heq
  · exact hm
  · exact heq ▸ hk

end

#print axioms FastConfirmation.Spec.Execution.SameOutsideObserver.withoutObserver_eq
#print axioms FastConfirmation.Spec.Execution.WeakObserverRestrictedCore.transport
#print axioms FastConfirmation.Spec.Execution.withoutObserver_honest
#print axioms FastConfirmation.Spec.Execution.WeakObserverRestrictedPremises.observer_independent
#print axioms FastConfirmation.Spec.Execution.weakObserverRestrictedPremises_observer_independent
#print axioms FastConfirmation.Spec.Execution.withoutObserver_store
#print axioms FastConfirmation.Spec.Execution.withoutObserver_weakFcr
#print axioms FastConfirmation.Spec.Execution.ObserverLocalInputs.wellFormed
#print axioms h5_head_known_without_hji
