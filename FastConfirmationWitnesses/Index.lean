module
public import FastConfirmationWitnesses.Counterexamples.DeadlineVotePathCandidate
public import FastConfirmationWitnesses.Counterexamples.PinnedEconomicsExtraQuery
public import FastConfirmationWitnesses.Counterexamples.StrictPrefixExtraQuery
public import FastConfirmationWitnesses.NonVacuity.NextSlotPremises
public import FastConfirmationWitnesses.NonVacuity.LiveMonotonicity
public import FastConfirmationWitnesses.NonVacuity.TwelveSecondSynchrony
public import FastConfirmationWitnesses.NonVacuity.FullTwelve
public import FastConfirmationWitnesses.NonVacuity.FullTwelveOperational
public import FastConfirmationWitnesses.NonVacuity.FullTwelveFFG
public import FastConfirmationWitnesses.NonVacuity.FullTwelvePremises
public import FastConfirmationWitnesses.NonVacuity.TargetEdgePremises
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopePremises
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopeBranches
public import FastConfirmationWitnesses.NonVacuity.ByzantinePremises

/-!
# Witness index

`ReviewClaims` contains only the safety theorem. Its result gives observer-store
membership and executable ancestry from the next slot. The public
`live_confirmed_root_monotonicity` theorem is a separate conditional result
under `LiveMonotonicityPremises`. Its timely FFG store outcomes close
previous_epoch_greatest_unrealized_checkpoint,
is_head_unrealized_justified_ok, and the previous-slot-head voting-source
recency guard.

This page names the finite runs that satisfy the premise bundles: a short
joint live run, a next-slot safety run with one-second slots and a 500 ms delay,
a one-second target-edge run,
a one-second run with Byzantine weight and a slashing, a 12-second
full-bundle run, and a 12-second run with an accepted payload envelope. It
also names two counterexamples to same-second head agreement at mid-second
prefixes under the older synchrony record.

## Premise bundles

* `LiveMonotonicityWitness.joint_witness`: one accepted two-slot-epoch run
  satisfies the full next-slot safety bundle and both live fields with two
  honest validators. The interval from second one to second two crosses the
  completed first epoch. Its stored confirmed root advances strictly from
  the anchor to the child. `joint_monotonicity` applies the public live theorem
  to that same strict interval. The FFG timing field holds at epoch 0
  through the genesis anchor; no vote-driven justification occurs.

* `Execution.NextSlotSafetyPremises`:
  `NextSlotPremiseWitness.finite_execution_satisfies_premises` and
  `NextSlotPremiseWitness.next_slot_premises_nonempty`. The execution has four
  honest validators, four slots per epoch, an anchor, a slot-one child, and a
  slot-seven FFG carrier. Its scheduled FCR call changes the confirmed root.
  The final in-horizon vote is delivered one second beyond the horizon.
* Guarded current-target edge:
  `TargetEdgePremiseWitness.full_bundle_witness` supplies the full next-slot
  bundle for a one-second run. `target_edge_support_exercised` proves the
  selector guard and the accepted anchor-to-child epoch crossing at the call
  from second six to seven. `target_edge_call_snapshot` checks positive vote
  weight and a remaining honest target vote. `target_edge_safe_from_next_slot`
  applies the public safety theorem from second eight onward.
* Byzantine weight and slashing relay:
  `ByzantinePremiseWitness.full_bundle_witness` supplies the full next-slot
  bundle for a one-second run with non-honest validator 4 of weight 200 out of
  4000. `byzantine_weight_exercised` proves positive non-honest weight in an
  in-horizon span. Validator 4 signs two slot-four votes with the same target
  epoch. `slashing_relay_exercised` proves the relay antecedent for the
  slashing that every node applies at second five. `equivocation_read_at_call`
  shows that the call from second six to seven reads the evidence and confirms
  the child. `previous_result_proviso_exercised` proves the antecedent of the
  selected previous-result guard at the call from second eight to nine.
  `previous_result_descendant_support_exercised` proves that its later honest
  epoch-two targets descend from the selected carrier.
* Twelve-second synchrony and behavior:
  `TwelveSecondSynchronyWitness.joint_witness` proves `WellFormedExecution`,
  `HonestBehavior`, `Synchrony`, and `NextSlotSynchronyPremises` for a second
  finite run. Its four honest validators share an anchor and accept a slot-one
  child. The slot is 12 seconds, the vote deadline is 3 seconds, and the
  positive delay is 2 seconds. Node 1 receives the child block at second 14
  while node 0 receives it at second 12; it receives the slot-zero vote at
  second 6 while node 0 receives it at second 4. The early vote copies are
  received inside the slot and are scheduled again for handler service at the
  next slot boundary. `delayed_block_in_stores` checks the real block-store
  difference. This run has no envelope or equivocation evidence, so those
  synchrony fields hold vacuously.
  The same run proves `HorizonVoteDeliveryLookahead`, `StaticValidatorSet`,
  `ByzantineWeightPremises`, `Phase0SourceCoherence`,
  `Phase0BoundarySourceCoherence`, the balance floor, `EpochEndsFitUint64`,
  and `InitialAnchorAtEpochBoundary` for its concrete anchor.
* Twelve-second full bundle:
  `FullTwelveWitness.full_bundle_witness` proves the full
  `Execution.NextSlotSafetyPremises` for the four-epoch trace, with
  12,000 ms slots, a 3,000 ms vote deadline, and a positive 2,000 ms delay.
  `FullTwelveWitness.delayed_receipts_are_first` proves the real block and
  vote receipt delays. The scheduled call at second 24 changes the anchor
  to the child. `FullTwelveWitness.changed_root_safe_from_next_slot` applies
  `confirmed_root_safe_from_next_slot` to this output. The accepted slot-seven
  carrier supports the FFG interpretation and Paper A3.2. Envelope service
  remains vacuous; the selector has no current-target accepted edge.
* Twelve-second envelope bundle:
  `FullTwelveEnvelopeWitness.full_bundle_witness` proves the full safety
  premises in a run with an accepted child payload envelope. Node 1 first
  receives it two seconds after node 0. The envelope and data relay
  antecedents hold at second 168, with boundary service at second 180.
  `FullTwelveEnvelopeWitness.changed_root_safe_from_next_slot` applies the
  public safety theorem. `payload_status_branches` checks the FULL choice
  and its Gloas weight beside the EMPTY choice. `gloas_discount_sample`
  computes zero carrier discount after verification. `fcr_branch_samples`
  checks selection, finalized reset, and late selector bypass.
* `Execution.ScheduledExecutionPremises`:
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
* `Execution.ScheduledFCRCallPremises`:
  `NextSlotPremiseWitness.witnessCompletedPrefixCallAssumptions`. The same
  execution has synchronized votes and blocks, stable validators and weights,
  and a scheduled descendant-helper call.
  Its selector guard excludes selected current-target accepted edges, so this
  witness does not exercise these support branches.
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
  `ByzantinePremiseWitness.byzantine_weight_exercised` has positive
  non-honest weight under the full safety bundle.
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
  the verification horizon. This stronger law is the `delivery_lookahead`
  field of `NextSlotSynchronyPremises`; it supplies in-horizon vote delivery.
* `ScheduledFFGInterpretation`:
  `AcceptedActualFCRJointNonVacuityFFG.witnessAcceptedSemantics`. The child
  and carrier in the same execution have an accepted FFG interpretation at
  every causal schedule prefix.
* `FFGInterpretationFidelity` (outside the safety premise):
  `NextSlotPremiseWitness.ffg_interpretation_fidelity`,
  `FullTwelveWitness.ffg_interpretation_fidelity`,
  `TargetEdgePremiseWitness.ffg_interpretation_fidelity`,
  `FullTwelveEnvelopeWitness.ffg_interpretation_fidelity`,
  `ByzantinePremiseWitness.ffg_interpretation_fidelity`, and
  `LiveMonotonicityWitness.ffg_interpretation_fidelity`. Each proves the
  fidelity record for the interpretation of its premise bundle. In the runs
  with a carrier, the included votes are valid members of the accepted
  carrier body. The live run includes no vote.
* `EpochCheckpointProjectionLaws`:
  `AcceptedActualFCRJointNonVacuityFFG.witnessAcceptedEpochCheckpointProjection`.
  The anchor, child, and carrier give concrete epoch checkpoint roots.
* `AcceptedBlockFFGState.LinkCheckpointAgreement`:
  `AcceptedActualFCRJointNonVacuityFFG.witnessExactLinkValidity`. Included
  attestations on the carrier support its exact checkpoint link.
* `AcceptedBlockFFGState.EventualCheckpointInclusion`:
  `NextSlotPremiseWitness.witnessPaperA32Inclusion`. The slot-seven carrier
  includes the vote evidence for the slot-one child.
* `Execution.ImportedBlockFinalizationLag`:
  `NextSlotPremiseWitness.witnessAcceptedRealizedFinalizationDelay`. The
  finite FFG state meets the delay bound over the horizon.
* `EpochEndsFitUint64`:
  `AcceptedActualFCRJointNonVacuityBase.witnessEpochEndsFitUint64`. The
  four-slot epochs fit the execution's integer bounds.
* `InitialAnchorAtEpochBoundary`:
  `AcceptedActualFCRJointNonVacuityBase.witnessTrustedAnchorBoundaryAligned`.
  The trusted anchor lies at its declared epoch boundary.

## Counterexamples

* `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` refutes
  same-second head agreement at a mid-second prefix under the older synchrony
  record. The querying actor confirms a candidate while another honest node's
  head is its sibling.
* `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` refutes
  the same same-second claim under the older synchrony record. It uses proposer
  boost 40 and Byzantine allowance 25. Its computed safety threshold is 95.
  These counterexamples do not refute next-slot safety of an in-slot query.
  That question remains open.

## Known gaps

* The shorter `TwelveSecondSynchronyWitness` run does not establish
  `Execution.NextSlotSafetyPremises`.
  It has no FFG carrier. Its `ScheduledFFGInterpretation`,
  `ScheduledExecutionPremises` (in particular `BeaconExternalsPremises`), and
  `ScheduledFCRCallPremises` are not proved.
  The bundle's semantic anchor equality, `ImportedBlockFinalizationLag`,
  `EventualCheckpointInclusion`, `EpochCheckpointProjectionLaws`, and `LinkCheckpointAgreement`
  are also not re-established for this run. The slot count bound and the
  concrete anchor boundary alignment are proved separately.

The short joint live run has a strict root advance. Its FFG timing uses only
the genesis anchor. The 1 s safety run (delay 500 ms) changes a stored root. The 12-second
full-bundle run adds real delayed block and vote receipts. The target-edge run
checks current-target support as a fact about the run. The envelope run
exercises envelope delivery and data relay through
`FullTwelveEnvelopeWitness.envelope_relay_exercised` and
`FullTwelveEnvelopeWitness.data_relay_exercised`. The Byzantine run exercises
positive non-honest weight, the slashing relay, and the selected
previous-result guard through
`ByzantinePremiseWitness.byzantine_weight_exercised`,
`ByzantinePremiseWitness.slashing_relay_exercised`, and
`ByzantinePremiseWitness.previous_result_proviso_exercised`.
`ByzantinePremiseWitness.previous_result_descendant_support_exercised` checks
the descendant conclusion. Both support forms are now derived by the joint
call and endpoint-slot induction. The six full-bundle constructors no longer
contain support fields. The witness support lemmas remain facts about the runs.
The historical certificate and quorum are produced from earlier votes when
needed. No external law or live-only premise was added. The shorter
synchrony-only run does not prove the full safety bundle.
Every positive run has proposer boost zero. The proposer-score term and
should_apply_proposer_boost are not exercised positively. The one-second
runs set `attestation_due_bps` to zero. The main safety runs have four or five
validators and one validator per slot committee. The joint live run has two
validators. Included slashing does not mark a validator slashed in state.
`DeadlineVotePathCandidate` checks that a skipped-boundary schedule fails the
pre-tick relay. The audited public theorem set has 43 entries.
-/
