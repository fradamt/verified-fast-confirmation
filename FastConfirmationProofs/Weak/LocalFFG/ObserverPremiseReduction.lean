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

/-- The permanent-exclusion test agrees when its source and receiver are
honest. It reads only their stores and the common horizon. -/
theorem nonhonest_permanentBlockExclusion_iff
    (hobs : obs ∉ E.honest)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (n m : ℕ) (r : Root) :
    PermanentBlockExclusion cfg ext (E.withoutObserver obs) v n r w m ↔
      PermanentBlockExclusion cfg ext E v n r w m := by
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hwne : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  unfold PermanentBlockExclusion
  simp only [withoutObserver_store cfg ext E obs v hne,
    withoutObserver_store cfg ext E obs w hwne]
  rfl

/-- An admissible honest-to-honest vote path in the restricted view is the
same path in the actual execution. -/
theorem nonhonest_votePathAdmissible
    (hobs : obs ∉ E.honest)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {n boundary : ℕ} {slot : Slot} {r : Root}
    (h : VotePathAdmissible cfg ext (E.withoutObserver obs)
      v n w boundary slot r) :
    VotePathAdmissible cfg ext E v n w boundary slot r := by
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  induction h with
  | stop hr hnot hle =>
    exact .stop
      (by simpa only [withoutObserver_store cfg ext E obs v hne n] using hr)
      ((nonhonest_permanentBlockExclusion_iff hobs hv hw n boundary _).not.mp hnot)
      (by simpa only [withoutObserver_store cfg ext E obs v hne n] using hle)
  | step hr hnot hgt _ ih =>
    rw [withoutObserver_store cfg ext E obs v hne n] at ih
    exact .step
      (by simpa only [withoutObserver_store cfg ext E obs v hne n] using hr)
      ((nonhonest_permanentBlockExclusion_iff hobs hv hw n boundary _).not.mp hnot)
      (by simpa only [withoutObserver_store cfg ext E obs v hne n] using hgt)
      ih

/-- The G4 path contract transfers for honest endpoints. Its original
all-receiver form is not asserted for the actual non-honest observer. -/
theorem nonhonest_headPaths_honestEndpoints
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    ∀ v ∈ E.honest, ∀ n, E.WithinHorizon cfg n →
      ∀ w ∈ E.honest, ∀ slot,
        E.WithinHorizon cfg (E.slot_start cfg (E.slot_at cfg n + 1)) →
        WalkKnown (E.store cfg ext v n) slot
          (get_head cfg (E.store cfg ext v n)).root →
        VotePathAdmissible cfg ext E v n w
          (E.slot_start cfg (E.slot_at cfg n + 1) - 1) slot
          (get_head cfg (E.store cfg ext v n)).root := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  intro v hv n hn w hw slot hb hwalk
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwalkR : WalkKnown (R.store cfg ext v n) slot
      (get_head cfg (R.store cfg ext v n)).root := by
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hwalk
  have hR := core.base.domain.honest_head_paths v hvR n hn w slot hb hwalkR
  change VotePathAdmissible cfg ext R v n w
    (E.slot_start cfg (E.slot_at cfg n + 1) - 1) slot
    (get_head cfg (R.store cfg ext v n)).root at hR
  rw [withoutObserver_store cfg ext E obs v hne n] at hR
  exact nonhonest_votePathAdmissible hobs hv hw hR

end
end Execution
end FastConfirmation.Spec
end
