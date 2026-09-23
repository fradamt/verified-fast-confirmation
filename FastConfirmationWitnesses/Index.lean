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
* `Execution.CompletedFCRCallPremises`:
  `NextSlotPremiseWitness.witnessCompletedPrefixCallAssumptions`. The same
  execution has synchronized votes and blocks, stable validators and weights,
  and a scheduled descendant-helper call.
* `NextSlotSynchronyPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessPaperSafetySynchrony`.
  The same execution satisfies the delivery and relay laws. It contains no
  execution payload envelope, so its envelope laws are vacuous.
* `BeaconExternalsPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessExternalsCoherence`. The same
  execution uses deterministic slot processing and envelope verification.
* `ByzantineWeightPremises`:
  `AcceptedActualFCRJointNonVacuityBase.witnessByzantineBound`. The same
  execution has four equal-weight honest validators and no Byzantine weight.

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
