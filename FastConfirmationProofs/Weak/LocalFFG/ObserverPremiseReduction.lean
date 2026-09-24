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

/-- Cutoff block relay keeps both endpoints in the unchanged honest set. -/
theorem nonhonest_deadlineBlockRelay
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    DeadlineBlockRelay cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  intro v hv n r hn hr hcut w hw m hm hboundary hnm
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwR : w ∈ R.honest := hh.symm ▸ hw
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hwne : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  have hrR : r ∈ (R.store cfg ext v n).block_roots := by
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hr
  have hrelay := core.base.synchrony.deadline_block_relay
    v hvR n r hn hrR hcut w hwR m hm hboundary hnm
  rcases hrelay with hk | hex
  · left
    simpa only [R, withoutObserver_store cfg ext E obs w hwne m] using hk
  · right
    exact (nonhonest_permanentBlockExclusion_iff hobs hv hw n
      (E.slot_start cfg (E.slot_at cfg n + 1) - 1) r).1 hex

/-- Ready cutoff blocks precede the honest receiver's boundary vote in the
actual run because that receiver has the same schedule and stores. -/
theorem nonhonest_deadlineBoundaryBlockPrefix
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    DeadlineBoundaryBlockPrefix cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  intro v hv n r hn hr hcut w hw boundary hb hnb a before after hsched hnot
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwR : w ∈ R.honest := hh.symm ▸ hw
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hwne : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  have hrR : r ∈ (R.store cfg ext v n).block_roots := by
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hr
  have hschedR : R.schedule w (E.slot_start cfg (E.slot_at cfg n + 1)) =
      before ++ Event.attestation a false :: after := by
    simpa only [R, withoutObserver, if_neg hwne] using hsched
  have hnotR : ¬ PermanentBlockExclusion cfg ext R v n r w
      (E.slot_start cfg (E.slot_at cfg n + 1) - 1) :=
    (nonhonest_permanentBlockExclusion_iff hobs hv hw n
      (E.slot_start cfg (E.slot_at cfg n + 1) - 1) r).not.mpr hnot
  have hp := core.base.synchrony.boundary_block_prefix
    v hvR n r hn hrR hcut w hwR hb hnb a before after hschedR hnotR
  simpa only [R, withoutObserver_store cfg ext E obs w hwne] using hp

/-- Verified envelope delivery transfers across the two unchanged honest
event schedules and stores. -/
theorem nonhonest_deadlineEnvelopeDelivery
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    DeadlineEnvelopeDelivery cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  intro v hv n r hn hp hr hcut w hw m hm hb hnm
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwR : w ∈ R.honest := hh.symm ▸ hw
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hwne : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  have hpR : is_payload_verified (R.store cfg ext v n) r = true := by
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hp
  have hrR : r ∈ (R.store cfg ext v n).block_roots := by
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hr
  have hdelivery := core.base.synchrony.envelope_delivery
    v hvR n r hn hpR hrR hcut w hwR m hm hb hnm
  rcases hdelivery with hex | ⟨d, k, signed, source, receiver,
      before, after, hdata⟩
  · left
    exact (nonhonest_permanentBlockExclusion_iff hobs hv hw n
      (E.slot_start cfg (E.slot_at cfg n + 1) - 1) r).1 hex
  · right
    refine ⟨d, k, signed, source, receiver, before, after, ?_⟩
    simp only [withoutObserver_store cfg ext E obs v hne,
      withoutObserver_store cfg ext E obs w hwne] at hdata
    simp only [withoutObserver, if_neg hne, if_neg hwne] at hdata
    exact hdata

/-- Honest data-service observations use the same scheduled envelopes. -/
theorem nonhonest_dataAvailabilityRelay
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    DeadlineDataAvailabilityRelay cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  intro v hv k n signed source hk hn hs hda hcut w hw m hm hb hnm
    received observation hroot hreceived
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwR : w ∈ R.honest := hh.symm ▸ hw
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hwne : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  have hsR : Event.execution_payload_envelope signed source ∈ R.schedule v k := by
    simpa only [R, withoutObserver, if_neg hne] using hs
  have hreceivedR : Event.execution_payload_envelope received observation ∈
      R.schedule w m := by
    simpa only [R, withoutObserver, if_neg hwne] using hreceived
  exact core.base.synchrony.data_availability_relay v hvR k n signed source
    hk hn hsR hda hcut w hwR m hm hb hnm received observation hroot hreceivedR

/-- Cutoff evidence relay also has only honest endpoints. -/
theorem nonhonest_attesterSlashingRelay
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    DeadlineAttesterSlashingRelay cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  intro v hv n i hn hi hcut w hw m hm hb hnm
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hwR : w ∈ R.honest := hh.symm ▸ hw
  have hne : v ≠ obs := by
    intro heq
    subst v
    exact hobs hv
  have hwne : w ≠ obs := by
    intro heq
    subst w
    exact hobs hw
  have hiR : i ∈ (R.store cfg ext v n).equivocating_indices := by
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hi
  have hR := core.base.synchrony.attester_slashing_relay
    v hvR n i hn hiR hcut w hwR m hm hb hnm
  simpa only [R, withoutObserver_store cfg ext E obs w hwne m] using hR

/-- The complete timed network contract for honest nodes follows from the
restricted core. Every source and receiver remains in `E.honest`. -/
def nonhonest_synchrony
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    NextSlotSynchronyPremises cfg ext E where
  delta := core.base.synchrony.delta
  delta_pos := core.base.synchrony.delta_pos
  deadline_fits := core.base.synchrony.deadline_fits
  attestation_delivery := by
    intro v hv s n a hs hn hva hcut _ w hw
    exact (nonhonest_deliveryLookahead hobs core).attestation_delivery
      v hv s n a hs hn hva hcut w hw
  deadline_block_relay := nonhonest_deadlineBlockRelay hobs core
  boundary_block_prefix := nonhonest_deadlineBoundaryBlockPrefix hobs core
  envelope_delivery := nonhonest_deadlineEnvelopeDelivery hobs core
  data_availability_relay := nonhonest_dataAvailabilityRelay hobs core
  attester_slashing_relay := nonhonest_attesterSlashingRelay hobs core

/-- Every honest causal store of the actual run is the same exact prefix in
the restricted view. The observer is outside the honest set. -/
theorem nonhonest_honestCausalStore
    (hobs : obs ∉ E.honest) {store : Store Root}
    (h : E.HonestCausalStore cfg ext store) :
    (E.withoutObserver obs).HonestCausalStore cfg ext store := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  cases h with
  | genesis hnonempty hhorizon =>
    exact .genesis (hh.symm ▸ hnonempty) hhorizon
  | scheduledPrefix p hp hn =>
    have hne : p.node ≠ obs := by
      intro heq
      exact hobs (heq ▸ hp)
    let q : R.ScheduledEventPrefix := {
      node := p.node
      previousSecond := p.previousSecond
      processedCount := p.processedCount
      count_le := by
        simpa only [R, withoutObserver, if_neg hne] using p.count_le }
    have htime : R.time_at (p.previousSecond + 1) =
        E.time_at (p.previousSecond + 1) := by rfl
    have hstore : q.store cfg ext = p.store cfg ext := by
      simp only [ScheduledEventPrefix.store, q]
      rw [withoutObserver_store cfg ext E obs p.node hne p.previousSecond]
      rw [htime]
      simp only [R, withoutObserver, if_neg hne]
    rw [← hstore]
    exact .scheduledPrefix q (hh.symm ▸ hp) hn

/-- The honest keyed-validation domain is unchanged by observer erasure. -/
theorem nonhonest_reachableValidationState
    (hobs : obs ∉ E.honest) {state : BeaconState Root}
    (h : E.ReachableValidationState cfg ext state) :
    (E.withoutObserver obs).ReachableValidationState cfg ext state := by
  obtain ⟨store, hs, hk⟩ := h
  exact ⟨store, nonhonest_honestCausalStore hobs hs, hk⟩

/-- External validation laws on honest keyed states transfer to the actual
execution. The observer's own keyed states remain in local input contracts. -/
def nonhonest_externals
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    BeaconExternalsPremises cfg ext E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  let hB := core.base.externals_coherence
  refine {
    process_slots_slot := hB.process_slots_slot
    process_slots_registry := hB.process_slots_registry
    state_transition_slot := hB.state_transition_slot
    state_transition_registry := hB.state_transition_registry
    state_transition_pre_slot_lt := hB.state_transition_pre_slot_lt
    state_transition_checkpoint_epoch := hB.state_transition_checkpoint_epoch
    pjf_checkpoint_epoch := hB.pjf_checkpoint_epoch
    committees_agree := ?_
    honest_attestation_valid := ?_
    valid_attestation_honest := ?_
    valid_attestation_committee := ?_
    committee_assignment_unique := hB.committee_assignment_unique
    committee_coverage := hB.committee_coverage
    committee_members_active := hB.committee_members_active
    valid_attestation_default := hB.valid_attestation_default
    process_slots_attestation_valid := ?_
    verify_envelope_deterministic := hB.verify_envelope_deterministic }
  · intro v hv n s hn hs
    have hvR : v ∈ R.honest := hh.symm ▸ hv
    have hne : v ≠ obs := by
      intro heq
      subst v
      exact hobs hv
    have hc := hB.committees_agree v hvR n s hn hs
    simpa only [R, withoutObserver_store cfg ext E obs v hne n] using hc
  · intro state a hs v hv ha hvcom hvote
    exact hB.honest_attestation_valid state a
      (nonhonest_reachableValidationState hobs hs)
      v (hh.symm ▸ hv) ha hvcom hvote
  · intro state a hs hvalid v hv hia
    exact hB.valid_attestation_honest state a
      (nonhonest_reachableValidationState hobs hs)
      hvalid v (hh.symm ▸ hv) hia
  · intro state a hs hvalid i hi
    exact hB.valid_attestation_committee state a
      (nonhonest_reachableValidationState hobs hs) hvalid i hi
  · intro state slot a hs hslot
    exact hB.process_slots_attestation_valid state slot a
      (nonhonest_reachableValidationState hobs hs) hslot

/-- Registry and horizon data are fixed by observer erasure. -/
def nonhonest_staticValidators
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    StaticValidatorSet cfg E where
  genesis_within_horizon := core.base.static_validators.genesis_within_horizon
  activity_constant := core.base.static_validators.activity_constant

/-- A non-honest observer contributes to the same unknown stake on both
views. Committee spans and balances are unchanged. -/
def nonhonest_byzantineBound
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    ByzantineWeightPremises cfg E := by
  let R := E.withoutObserver obs
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  refine {
    effective_balance_quantized := core.base.byzantine_bound.effective_balance_quantized
    estimate_sound := core.base.byzantine_bound.estimate_sound
    span_fraction := ?_ }
  intro a b ha hb
  have h := core.base.byzantine_bound.span_fraction a b ha hb
  have hspan : R.span_committee a b = E.span_committee a b := rfl
  have hweight : ∀ S, R.weight S = E.weight S := by intro S; rfl
  change 100 * R.weight ((R.span_committee a b).filter
      (fun i => i ∉ R.honest)) ≤
    cfg.confirmation_byzantine_threshold * R.weight (R.span_committee a b) at h
  rw [hh, hspan, hweight, hweight] at h
  exact h

end
end Execution
end FastConfirmation.Spec
end
