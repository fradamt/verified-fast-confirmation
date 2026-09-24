module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32CallSupplier
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetGateGeometry
public import FastConfirmationProofs.Execution.History.TrustedCompletedPrefixCallsBase

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

noncomputable def trusted_observerCall_acceptedTargetGateProducerAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (_hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n) := by
  intro hgate hsupport
  let p := E.completedScheduledEventPrefix obs n
  have hpstore : p.store cfg ext = E.store cfg ext obs (n + 1) := by
    simpa only [p] using E.completedScheduledEventPrefix_store cfg ext obs n
  have hevidenceBoundary :=
    E.completedScheduledEventPrefix_accountingEvidence_at_observer
      cfg ext hT hcoh n hHn1
  have hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1) := by
    rw [hpstore]
    change E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext obs (n + 1)) (n + 1)
    exact hevidenceBoundary
  let state := get_pulled_up_head_state cfg ext
    (E.store cfg ext obs (n + 1))
  have hstate : state = get_pulled_up_head_state cfg ext
      (p.store cfg ext) := by
    rw [hpstore]
  have hval : state.validators = E.registry := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_validators_at_observer cfg ext hT hcoh hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_totalActive_at_observer cfg ext hT
        hC.static_validators hcoh hHn1
  have hgateBoundary : will_current_target_be_justified cfg ext
      (E.store cfg ext obs (n + 1)) = true := by
    simpa only [E.weakFcrStep_store] using hgate
  have hsupportBoundary : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext obs (n + 1))) (n + 1) := by
    simpa only [E.weakFcrStep_store] using hsupport
  have hendH := E.currentTargetEpochEnd_within_of_epochEndsFitUint64
    cfg ext hfit (v := obs) (q := n + 1) hHn1
  have hanchorH := E.trusted_completedPrefix_anchor_epoch_within cfg ext hT
    hC.static_validators
  have hendHP : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)) := by
    rw [hpstore]
    exact hendH
  have hgateP : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true := by
    rw [hpstore]
    exact hgateBoundary
  have hsupportP : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1) := by
    rw [hpstore]
    change HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext obs (n + 1))) (n + 1)
    exact hsupportBoundary
  have hrealized :=
    E.trusted_scheduledEventPrefix_acceptedTargetA32GateRealization_core_of_operationalEvidence
    cfg ext B hT hC.static_validators
      hC.byzantine_bound
      hC.phase0_source hC.phase0_boundary_source hanchor hboundary p hHn1
      hevidence hstate hval htab hendHP
      (fun Q => Q.scheduledDelivery_of_lookahead cfg ext E hC.delivery_lookahead)
      hanchorH hC.balance_floor
      hgateP hsupportP
  rw [hpstore] at hrealized
  simpa only [E.weakFcrStep_store] using hrealized

end Execution
end FastConfirmation.Spec
end
