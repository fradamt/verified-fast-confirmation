import FastConfirmationProofs.Weak.LocalFFG

open FastConfirmation.Spec FastConfirmation.Spec.Execution

section
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E E' : Execution Root} {obs : ValidatorIndex}

example (h : E.SameOutsideObserver E' obs)
    (hP : E.WeakObserverRestrictedPremises cfg ext obs)
    (hlocal : E'.ObserverLocalInputs cfg ext obs) :
    Nonempty (E'.WeakObserverRestrictedPremises cfg ext obs) :=
  weakObserverRestrictedPremises_observer_independent cfg ext h hP hlocal

example (replacement : ℕ → List (Event Root))
    (hP : E.WeakObserverRestrictedPremises cfg ext obs)
    (hlocal : ({ E with schedule := fun w n =>
      if w = obs then replacement n else E.schedule w n } : Execution Root).ObserverLocalInputs cfg ext obs) :
    Nonempty (({ E with schedule := fun w n =>
      if w = obs then replacement n else E.schedule w n } : Execution Root).WeakObserverRestrictedPremises cfg ext obs) := by
  apply weakObserverRestrictedPremises_observer_independent cfg ext _ hP hlocal
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro w hw
  funext n
  simp only [if_neg hw]

/-- The new premise record derives observer coherence; no such field is assumed. -/
theorem h6_observer_coherence (hP : E.WeakObserverRestrictedPremises cfg ext obs) :
    E.ObserverCoherence cfg ext obs := by
  obtain ⟨B⟩ := hP.local_inputs.ffg
  exact B.observerCoherence hP.core hP.local_inputs

end

#print axioms weakObserverRestrictedPremises_observer_independent
#print axioms ObserverIncludedEvidence.base_valid
#print axioms ObserverIncludedEvidence.honest_signed
#print axioms ObserverIncludedEvidence.committee
#print axioms restricted_no_forgery
#print axioms ObserverLocalFFG.link_honest_signer
#print axioms ObserverLocalFFG.link_root_eq_shared
#print axioms ObserverLocalFFG.link_signed_origin
#print axioms ObserverLocalFFG.formed_signed_origin
#print axioms ObserverLocalFFG.store_projection
#print axioms ObserverLocalFFG.global_origins
#print axioms ObserverLocalFFG.justified_AU
#print axioms ObserverLocalFFG.unrealized_justified_AU
#print axioms ObserverLocalFFG.finalized_certificate
#print axioms ObserverLocalFFG.checkpoint_root_known
#print axioms ObserverLocalFFG.justified_root_known
#print axioms ObserverLocalFFG.included_slot_before_tip
#print axioms ObserverLocalFFG.pulled_finalized_lag
#print axioms ObserverLocalFFG.shared_selectors_agree
#print axioms ObserverLocalFFG.shared_checkpoint_agree
#print axioms ObserverFFG.Execution.observerCausalStore_finalizationLag
#print axioms h6_observer_coherence
#print axioms ObserverFFGCounterexample.accepts
#print axioms ObserverFFGCounterexample.readback
#print axioms ObserverFFGCounterexample.restricted_absent
#print axioms ObserverFFGCounterexample.no_bad_certificate
#print axioms ObserverFFGCounterexample.authenticity
#print axioms ObserverFFGCounterexample.no_local_extension
