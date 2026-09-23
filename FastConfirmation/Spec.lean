module
public import FastConfirmation.Spec.Model
public import FastConfirmation.Spec.Proof.CompleteEvidenceWitness
public import FastConfirmation.Spec.Proof.Containment
public import FastConfirmation.Spec.ProvenTheorems
public import FastConfirmation.Spec.Proof.PayloadStoreInvariants
public import FastConfirmation.Spec.Proof.PayloadSupport
public import FastConfirmation.Spec.Proof.PayloadPersistence
public import FastConfirmation.Spec.Proof.OancTransport
public import FastConfirmation.Spec.Proof.MonotonicityTrace
public import FastConfirmation.Spec.Proof.MonotonicityLiveGates
public import FastConfirmation.Spec.Proof.MonotonicityLiveBridge
public import FastConfirmation.Spec.Proof.MonotonicityLiveConfirmation
public import FastConfirmation.Spec.Proof.MonotonicityLiveRestart
public import FastConfirmation.Spec.Proof.MonotonicityLiveAssemble
public import FastConfirmation.Spec.Proof.MonotonicityLiveHeadCounterexample
public import FastConfirmation.Spec.Proof.MonotonicityLiveFinalizationCounterexample
public import FastConfirmation.Spec.Proof.AcceptedStrictPrefixExtraQueryCounterexample
public import FastConfirmation.Spec.Proof.AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample
public import FastConfirmation.Spec.Proof.WeakOneShotSafety
public import FastConfirmation.Spec.Proof.WeakFinalizedInput
public import FastConfirmation.Spec.Proof.WeakFreshSupport
public import FastConfirmation.Spec.Proof.WeakQuorumAccounting
public import FastConfirmation.Spec.Proof.WeakEndpointClasses
public import FastConfirmation.Spec.Proof.WeakCrossingSets
public import FastConfirmation.Spec.Proof.WeakSiblingScore
public import FastConfirmation.Spec.Proof.WeakSelectorBetween
public import FastConfirmation.Spec.Proof.WeakSelectedEdgeGeometry
public import FastConfirmation.Spec.Proof.WeakSelectedMarginInputs
public import FastConfirmation.Spec.Proof.WeakStatusMarginConstruction
public import FastConfirmation.Spec.Proof.WeakCoveredMarginConstruction
public import FastConfirmation.Spec.Proof.WeakOneShotSafetyNative
public import FastConfirmation.Spec.Proof.WeakObserverDomain
public import FastConfirmation.Spec.Proof.WeakSourceHistory
public import FastConfirmation.Spec.Proof.WeakSelectedTrace
public import FastConfirmation.Spec.Proof.WeakCertificateMonotone
public import FastConfirmation.Spec.Proof.WeakFCRCallContracts
public import FastConfirmation.Spec.Proof.WeakObserverReplay
public import FastConfirmation.Spec.Proof.WeakReplayRelation
public import FastConfirmation.Spec.Proof.WeakBankedJustification
public import FastConfirmation.Spec.Proof.WeakJustificationTiming
public import FastConfirmation.Spec.Proof.WeakSeedDissemination
public import FastConfirmation.Spec.Proof.WeakEarlyPhaseSourceWiring
public import FastConfirmation.Spec.Proof.WeakCandidateHistoryRecurrence
public import FastConfirmation.Spec.Proof.WeakCandidateSourceHistory
public import FastConfirmation.Spec.Proof.WeakHistoricalA32OriginCall
public import FastConfirmation.Spec.Proof.WeakSelectedStrictEdgeFilterSupply
public import FastConfirmation.Spec.Proof.WeakPreQuerySIR
public import FastConfirmation.Spec.Proof.WeakHistoricalA32Geometry
public import FastConfirmation.Spec.Proof.WeakHistoricalA32Step
public import FastConfirmation.Spec.Proof.WeakHistoricalA32CallSupplier
public import FastConfirmation.Spec.Proof.WeakHistoricalA32LazyCrossing
public import FastConfirmation.Spec.Proof.WeakHistoricalA32OneStep
public import FastConfirmation.Spec.Proof.WeakHistoricalA32Induction
public import FastConfirmation.Spec.Proof.WeakSelectedJustifiedOrientation
public import FastConfirmation.Spec.Proof.WeakHistoricalA32PayloadProducer
public import FastConfirmation.Spec.Proof.WeakObserverStrictCallFilterInputs
public import FastConfirmation.Spec.Proof.WeakOneShotSafetyClosed
public import FastConfirmation.Spec.Proof.WeakObservedRestartAdoption
public import FastConfirmation.Spec.Proof.WeakObservedRestartDynamicSafety
public import FastConfirmation.Spec.Proof.WeakTrajectorySafety
public import FastConfirmation.Spec.Proof.WeakObservedResetSeedSafety
public import FastConfirmation.Spec.Proof.HonestTargetAgreement
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OriginCall
public import FastConfirmation.Spec.Proof.EndpointQuorumCausality
public import FastConfirmation.Spec.Proof.SelectedTraceFilterPipeline


@[expose] public section

/-!
# Spec — facade

The consensus-spec model of the Fast Confirmation Rule: executable rule and
fork-choice functions, scheduled multi-node executions, explicit assumptions,
and the primary accepted-execution theorem
`acceptedSpec_safety_next_slot : AcceptedSpec_Safety_next_slot`. Its premise
surface is `AcceptedActualFCRNextSlotSafetyAssumptions`; finalized and observed
reset safety are derived rather than assumed.

This development is mechanically independent of the abstract paper model in
`FastConfirmation/Paper/`: it imports none of those modules, and no formal
refinement theorem between the two models is claimed.

The facade also exports strict-prefix counterexamples delimiting the theorem.
A source-permitted pre-update query can return a root which is not on another
honest endpoint's head at that exact global action position, even under the
proved structural, honest-behavior, synchrony, and Byzantine-bound packages.
The second finite regression uses the pinned proposer-boost and confirmation-
Byzantine-threshold values `40`/`25`; it deliberately remains a small
four-slot preset rather than claiming to instantiate every field of
`mainnet_config`. These counterexamples do not touch the accepted mandatory
boundary-call proof path: the primary stored-output theorem starts at the next
slot, after the modeled synchrony deadline.
-/

end
