module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGAuthenticity

/-! Honest behavior restored from the shared core and local authenticity. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution

section
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}

/-- Non-honest observer inputs do not change honest behavior or vote delivery.
The all-receiver no-forgery law splits at the observer. -/
theorem nonhonest_honestBehavior
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) :
    HonestBehavior cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  have hB := core.base.honest_behavior
  refine {
    votes_head := ?_
    vote_deadline := ?_
    votes_assigned := ?_
    no_forgery := ?_
    not_slashable := ?_
    honest_unslashed := ?_ }
  · intro v hv s hs hsh hstart
    have hvR : v ∈ R.honest := hh.symm ▸ hv
    have hne : v ≠ obs := by
      intro heq
      subst v
      exact hobs hv
    obtain ⟨n, i, hn, hslot, hvote⟩ := hB.votes_head v hvR s hs hsh hstart
    exact ⟨n, i, hn, hslot, by
      change E.vote v s = some
        (n, honest_attestation cfg ext (R.store cfg ext v n) s i v) at hvote
      rw [withoutObserver_store cfg ext E obs v hne n] at hvote
      exact hvote⟩
  · intro v hv s n a hvote
    exact hB.vote_deadline v (hh.symm ▸ hv) s n a hvote
  · intro v hv s hvote
    exact hB.votes_assigned v (hh.symm ▸ hv) s hvote
  · intro w n a fb ha v hv hia
    have hvR : v ∈ E.honest.erase obs :=
      Finset.mem_erase.mpr ⟨by intro heq; subst v; exact hobs hv, hv⟩
    simpa only [withoutObserver] using
      restricted_no_forgery core localInputs.toObserverInputAuthenticity
        w n a fb ha hvR hia
  · intro v hv s s' n n' a a' hvs hvs'
    exact hB.not_slashable v (hh.symm ▸ hv) s s' n n' a a' hvs hvs'
  · intro v hv
    exact hB.honest_unslashed v (hh.symm ▸ hv)

/-- Vote receipt at the horizon boundary transfers because both the sender
and receiver are honest, hence distinct from the observer. -/
theorem nonhonest_deliveryLookahead
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    HorizonVoteDeliveryLookahead cfg E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  refine ⟨?_⟩
  intro v hv s n a hs hn hvote hcut w hw
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwR : w ∈ R.honest := hh.symm ▸ hw
  have hwr : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  have hr := core.delivery_lookahead.attestation_delivery v hvR s n a hs hn
    hvote hcut w hwR
  simpa only [R, withoutObserver, if_neg hwr] using hr

/-- The completed-call supplement uses the same anchor balances and the
transported honest-vote lookahead. -/
def nonhonest_completedCalls
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    E.WeakCompletedFCRCallSupplement cfg ext where
  phase0_source := core.completed_calls.phase0_source
  phase0_boundary_source := core.completed_calls.phase0_boundary_source
  balance_floor := by
    simpa only [withoutObserver, Execution.weight,
      Execution.currentTargetAnchorActive] using core.completed_calls.balance_floor
  delivery_lookahead := nonhonest_deliveryLookahead hobs core

end
end Execution
end FastConfirmation.Spec
end
