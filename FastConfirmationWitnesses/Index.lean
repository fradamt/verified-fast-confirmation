module
public import FastConfirmationWitnesses.Counterexamples.PinnedEconomicsExtraQuery
public import FastConfirmationWitnesses.Counterexamples.StrictPrefixExtraQuery
public import FastConfirmationWitnesses.NonVacuity.NextSlotPremises

/-!
# Witness index

This page names the finite execution that satisfies the next-slot premise
bundle and the two executions that refute strict-prefix safety variants.

## Premise bundles

* `Execution.NextSlotSafetyPremises`:
  `NextSlotPremiseWitness.finite_execution_satisfies_premises` and
  `NextSlotPremiseWitness.next_slot_premises_nonempty`. The execution has four
  honest validators, four slots per epoch, an anchor, a slot-one child, and a
  slot-seven FFG carrier. Its scheduled FCR call changes the confirmed root.
  The final in-horizon vote is delivered one second beyond the horizon.
* `Execution.ScheduledPrefixPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessScheduledPrefixTrajectoryAssumptions`.
  The same execution has whole-second scheduling, honest votes, a valid genesis
  store, and well-formed external functions.
* `Execution.WellFormedExecution`:
  `AcceptedActualFCRJointNonVacuityBase.witnessWellFormedExecution`. The four
  honest nodes start from one valid anchor store and process finite schedules.
* `HonestBehavior`:
  `AcceptedActualFCRJointNonVacuityBase.witnessHonestBehavior`. Every scheduled
  honest vote belongs to its assigned slot committee and meets the
  attestation due time in that execution.
* `Execution.CompletedFCRCallPremises`:
  `NextSlotPremiseWitness.witnessCompletedPrefixCallAssumptions`. The same
  execution has synchronized votes and blocks, stable validators and weights,
  and a scheduled descendant-helper call.
  Its selector guard excludes selected current-target accepted edges, so this
  witness does not exercise their support premise.
* `NextSlotSynchronyPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessPaperSafetySynchrony`.
  The same execution satisfies the delivery and relay laws. It contains no
  execution payload envelope, so its envelope laws are vacuous.
* `Synchrony`:
  `AcceptedActualFCRJointNonVacuityBase.witnessSynchrony`. The same finite
  schedule delivers each honest vote to all four honest nodes.
* `BeaconExternalsPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessExternalsCoherence`. The same
  execution uses deterministic slot processing and envelope verification.
* `ByzantineWeightPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessByzantineBound`. The same
  execution has four equal-weight honest validators and no Byzantine weight.
* `StaticValidatorSet`:
  `AcceptedActualFCRJointNonVacuityBase.witnessStaticValidatorSet`. All four
  validators remain active throughout the finite horizon.
* `Phase0SourceCoherence`:
  `AcceptedActualFCRJointNonVacuityBase.witnessPhase0SourceCoherence`. Slot
  processing preserves the chosen source within an epoch.
* `Phase0BoundarySourceCoherence`:
  `AcceptedActualFCRJointNonVacuityBase.witnessPhase0BoundarySourceCoherence`.
  The same finite state transition supplies the epoch-boundary source law.
* `HorizonVoteDeliveryLookahead`:
  `AcceptedActualFCRJointNonVacuityBase.witnessHorizonVoteDeliveryLookahead`.
  The slot-fifteen vote reaches every honest node at second sixteen, outside
  the verification horizon.
* `CausalPrefixFFGInterpretation`:
  `AcceptedActualFCRJointNonVacuityFFG.witnessAcceptedSemantics`. The child
  and carrier in the same execution have an accepted FFG interpretation at
  every causal schedule prefix.
* `EpochCheckpointClosure`:
  `AcceptedActualFCRJointNonVacuityFFG.witnessAcceptedEpochCheckpointProjection`.
  The anchor, child, and carrier give concrete epoch checkpoint roots.
* `CausalCarrierFFGState.ExactLinkValidity`:
  `AcceptedActualFCRJointNonVacuityFFG.witnessExactLinkValidity`. Included
  attestations on the carrier support its exact checkpoint link.
* `CausalCarrierFFGState.PaperA32Inclusion`:
  `NextSlotPremiseWitness.witnessPaperA32Inclusion`. The slot-seven carrier
  includes the vote evidence for the slot-one child.
* `Execution.RealizedFinalizationDelay`:
  `NextSlotPremiseWitness.witnessAcceptedRealizedFinalizationDelay`. The
  finite FFG state meets the delay bound over the horizon.
* `EpochEndsFitUint64`:
  `AcceptedActualFCRJointNonVacuityBase.witnessEpochEndsFitUint64`. The
  four-slot epochs fit the execution's integer bounds.
* `TrustedAnchorBoundaryAligned`:
  `AcceptedActualFCRJointNonVacuityBase.witnessTrustedAnchorBoundaryAligned`.
  The trusted anchor lies at its declared epoch boundary.

## Counterexamples

* `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` refutes
  exact-current safety at every legal in-second query position: the querying
  actor confirms a candidate while another honest node's head is its sibling.
* `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` refutes
  the same strict-prefix variant with proposer boost 40 and Byzantine allowance
  25. Its computed safety threshold is 95.

## Known gaps

* No witness shows that `LiveMonotonicityPremises` can hold together with
  `Execution.NextSlotSafetyPremises` (audit a5 A5-2).
* Envelope premises are exercised only through the next-slot bundle witness.
  Its execution contains no payload envelope, so envelope delivery and data
  relay hold vacuously.
-/
