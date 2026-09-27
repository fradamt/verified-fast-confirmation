module
public import FastConfirmationWitnesses.Counterexamples.CheckpointSyncFilter
public import FastConfirmationWitnesses.Counterexamples.DeadlineVotePathCandidate
public import FastConfirmationWitnesses.Counterexamples.PinnedEconomicsExtraQuery
public import FastConfirmationWitnesses.Counterexamples.StrictPrefixExtraQuery
public import FastConfirmationWitnesses.NonVacuity.NextSlotPremises
public import FastConfirmationWitnesses.NonVacuity.GenesisStubPremises
public import FastConfirmationWitnesses.NonVacuity.FullTwelvePremises
public import FastConfirmationWitnesses.NonVacuity.TargetEdgePremises
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopePremises
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopeBranches
public import FastConfirmationWitnesses.NonVacuity.ByzantinePremises

/-!
# Witness index

`ReviewClaims` contains only the safety theorem. Its result gives observer-store
membership and executable ancestry from the next slot. These finite witnesses
show that the full premise bundle is consistent. They do not establish Python
faithfulness; the contract suite, projection harness, and concrete differential
check test that behavior. Their PJF returns early in epochs 0 and 1, as Python does.

This page names the finite runs that satisfy the premise bundles: a short
next-slot safety run with one-second slots and a 500 ms delay, the same run
with the real genesis stub,
a one-second target-edge run,
a one-second run with Byzantine weight and a slashing, a 12-second
full-bundle run, and a 12-second run with an accepted payload envelope. It
also names two counterexamples to same-second head agreement at mid-second
prefixes under the counterexample synchrony record, and a raw checkpoint-sync filter
regression. The latter confirms a child at slot 14 and loses it at slot 20.
See `CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample`. It has no
attestation inclusion for two epochs. The regression does not assert the full safety
bundle or its `EventualCheckpointInclusion` premise (paper Assumption 3.2
(explicit)). It shows why that premise matters;
it is not an FCR safety failure.

`NextSlotSafetyPremises.anchor_state_checkpoints` covers a genesis anchor whose state
has the zero-root stub. It also covers a normalized anchor state whose current justified
and finalized checkpoints equal the anchor. At the FFG interpretation boundary,
`CheckpointReadsAs` reads a raw genesis stub as the genesis anchor because both
checkpoints have `GENESIS_EPOCH`. Executable handlers and wire attestations keep the raw
checkpoint. Checkpoint-sync anchors with older state checkpoints are outside this
condition. The raw source age and the filter's `+2` rule need an inclusion argument.
That argument is not formalized.
`CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample` has no attestation
inclusion for two epochs, so it is outside `EventualCheckpointInclusion` (paper Assumption 3.2
(explicit)). It shows why
that premise matters; it is not an FCR safety failure.

`Phase0BoundarySourceCoherence` has five fields. `process_slots_one_boundary` equates
one boundary with eager PJF. `process_slots_same_target_epoch` equates target slots in
one epoch. `state_transition_process_slots` equates a crossing block transition with
slot processing. `process_slots_checkpoint_epoch` bounds the output checkpoint if every
intermediate slot-processed state satisfies `3 * effective_balance_increment < 2 *
get_total_active_balance`. This guard is exact because an empty vote set can pass the
two-thirds test at a total balance of at most one and a half increments.
`process_slots_two_boundaries` equates two or more boundaries from a start epoch of at
least `GENESIS_EPOCH + 2` with eager PJF, if the registry and the total active balance
are unchanged and the same guard holds at every intermediate state.
`ScheduledFCRCallPremises.balance_floor` requires two increments of anchor active
weight. With `registry_static_in_horizon`, this floor supplies the guard on in-horizon
reads. The concrete transition rejects blocks with slashings, voluntary exits, or parent
execution requests (`FFGWireBlock.InFixedScope`), and a Python run with an epoch-step
registry change is outside the scope (`FixedFFGScope`).
`on_attestation_committee` confines successful delivered attestations in honest
in-horizon prefixes to their slot committee. Attester-slashing evidence can name
off-committee validators.

## Premise bundles

Every full-bundle witness is a finite run with a concrete bridge: one
concrete setup, a finite state table, and a finite block table. The state
functions of the run are the bridge interface, and its FFG content is the
canonical content of the bridge, not a hand-made interpretation. The proofs
evaluate stores with a computable copy of the interface (`lookupInterface`)
and rewrite by `interface_eq_lookupInterface`. The concrete child and carrier
states are literals that the pointwise concrete transition checks by kernel
reduction.

Five families take `zeroRoot := anchorRoot`: the next-slot, target-edge,
Byzantine, twelve-second, and twelve-second envelope runs. Python cannot make
this choice, because `ZERO_HASH` is not the genesis root. With it, the genesis
stub reads as the anchor checkpoint in the honest votes. The genesis-stub run
keeps a separate `zeroRoot`, as Python does. It is still not a
Python-faithful execution: it uses one-second slots, four validators and four
slots per epoch, `attestation_due_bps = 0`, zero proposer boost, an oracle that
accepts every block, a base signature check that accepts exactly the ground
votes, and the genesis payload fields of `FFGBeaconState.genesis`. Every
full-bundle run makes the same kind of choices: the twelve-second runs use
twelve-second slots and a 2500 basis-point attestation due time, and the
Byzantine run has five validators.

* `ConcreteBridge.SafetyPremises`, the public premise:
  `NextSlotPremiseWitness.finite_execution_satisfies_premises` and
  `NextSlotPremiseWitness.next_slot_premises_nonempty`. The run uses the
  concrete bridge `NextSlotBridgeRun.witnessBridge`. It has four honest
  validators, four slots per epoch, an anchor, a slot-one child, and a
  slot-eight carrier whose body has the votes of slots four to six. Its
  scheduled FCR call changes the confirmed root, and
  `finite_execution_satisfies_premises` applies
  `confirmed_root_safe_from_next_slot` to the changed root. The final
  in-horizon vote is delivered one second beyond the horizon.
* Real Phase0 genesis anchor:
  `GenesisStubPremiseWitness.genesis_stub_full_bundle_witness` is the same
  one-second run with a real genesis anchor state. Its current justified and
  finalized checkpoints are the stub `(GENESIS_EPOCH, zeroRoot)`, and the stub
  root is not the anchor root. Honest votes before slot 12 carry the stub as
  their source. The public premise holds, the FCR call confirms the child, and
  the anchor state's justified checkpoint differs from the genesis store's
  justified checkpoint.
* Guarded current-target edge:
  `TargetEdgePremiseWitness.full_bundle_witness` proves the public premise
  for a one-second run with a slot-four child. `target_edge_support_exercised`
  proves the selector guard and the accepted anchor-to-child epoch crossing at
  the call from second six to seven. `target_edge_call_snapshot` checks
  positive vote weight and a remaining honest target vote.
  `target_edge_safe_from_next_slot` applies the public safety theorem from
  second eight onward.
* Byzantine weight and slashing relay:
  `ByzantinePremiseWitness.full_bundle_witness` proves the public premise for
  a one-second run with non-honest validator 4 of weight 200 out of 4000.
  Validator 4 shares every committee of validator 3.
  `byzantine_weight_exercised` proves positive non-honest weight in an
  in-horizon span. Validator 4 signs two slot-four votes with the same target
  epoch. `slashing_relay_exercised` proves the relay antecedent for the
  slashing that every node applies at second five. `equivocation_read_at_call`
  shows that the call from second six to seven reads the evidence and confirms
  the child. The call from second nine to ten confirms the epoch-two carrier
  in its own epoch. Block D at slot 11 extends the carrier; its body has the
  votes of slots 8 to 10. `previous_result_proviso_exercised` shows that the
  call from second 12 to 13, in the non-start slot 13 of epoch 3, selects D
  from the confirmed carrier. `previous_result_descendant_support_exercised`
  proves the descendant target support of this selection.
* Twelve-second full bundle:
  `FullTwelveWitness.full_bundle_witness` proves the public premise for the
  run `FullTwelveBridgeRun`, with 12,000 ms slots, a 3,000 ms vote deadline,
  and a positive 2,000 ms delay. It has the concrete setup, blocks, and states
  of the next-slot run. `FullTwelveWitness.delayed_receipts_are_first` proves
  the real block and vote receipt delays: node 1 receives the child block at
  second 14 while node 0 receives it at second 12, and the slot-zero vote at
  second 6 while node 0 receives it at second 4.
  `FullTwelveWitness.delayed_block_in_stores` checks the block-store
  difference. The scheduled call at second 24 changes the anchor to the child.
  `FullTwelveWitness.changed_root_safe_from_next_slot` applies
  `confirmed_root_safe_from_next_slot` to this output. Envelope service is
  vacuous.
* Twelve-second envelope bundle:
  `FullTwelveEnvelopeWitness.full_bundle_witness` proves the public premise
  in a run with an accepted child payload envelope. The base interface of the
  bridge reports the child data as available and accepts exactly the child
  envelope. Node 1 receives the envelope two seconds after node 0. Each node
  receives it once, before the boundary at second 180, and keeps the payload
  (`single_early_envelope_receipt`). The envelope delivery, envelope prefix,
  and data relay antecedents hold at second 168.
  `FullTwelveEnvelopeWitness.changed_root_safe_from_next_slot` applies the
  public safety theorem. `payload_status_branches` checks the FULL choice and
  its Gloas weight beside the EMPTY choice. `gloas_discount_sample` computes
  zero carrier discount after verification. `fcr_branch_samples` checks
  selection, finalized reset, and late selector bypass.
* The internal record `Execution.NextSlotSafetyPremises` follows from the
  public premise by `ConcreteBridge.SafetyPremises.nextSlotSafetyPremises`.
  The bridge proves the Phase0 source laws
  (`ConcreteBridge.phase0SourceCoherence` and
  `ConcreteBridge.phase0BoundarySourceCoherence`), the balance floor
  (`ConcreteBridge.balance_floor`), the anchor fields, the FFG interpretation
  (`ConcreteBridge.canonicalScheduledFFGInterpretation`), the checkpoint
  projection (`ConcreteBridge.canonical_checkpoint_projection`), and the link
  agreement (`ConcreteBridge.canonical_link_checkpoint_agreement`) for every
  bridge.
* The run fields of the public premise, for the next-slot run:
  `NextSlotBridgeRun.witnessWellFormedExecution`,
  `NextSlotBridgeRun.witnessHonestBehavior`,
  `NextSlotBridgeRun.witnessExternalsCoherence` (the internal record; the
  public field is its residual part),
  `NextSlotBridgeRun.witnessPaperSafetySynchrony`,
  `NextSlotBridgeRun.witnessByzantineBound` (it meets the cross-boundary
  part of the committee-sampling idealization only through the 1000-Gwei
  rounding of `adjust_committee_weight_estimate_to_ensure_safety`: every
  estimate is at least 1005 Gwei, more than the total stake of 400 Gwei; a
  witness at realistic scale with a mixed schedule is deferred), and
  `NextSlotPremiseWitness.witnessEpochEndsFitUint64`. The four honest nodes
  start from one anchor store and process finite schedules. Every honest vote
  belongs to its slot committee and meets the attestation due time. The run
  contains no execution payload envelope, so its envelope laws are vacuous.
  `NextSlotBridgeRun.witnessHorizonVoteDeliveryLookahead` delivers the
  slot-fifteen vote to every honest node at second sixteen, outside the
  verification horizon.
* Concrete FFG fixtures outside the safety bundle:
  `ConcreteJustificationWitness.concrete_certificate_extraction` extracts the
  supermajority certificate of the end-of-epoch-2 justification of epoch 1 in
  a two-slot-per-epoch concrete run, and
  `ConcreteJustificationWitness.wrong_target_vote_not_counted` shows that
  `process_attestation` accepts a wrong-target vote that does not count.
  `ConcreteFinalityWitness.k2_certificate_extraction` finalizes epoch 2
  through the two-epoch link 2 -> 4 with no link 2 -> 3
  (`ConcreteFinalityWitness.no_adjacent_link`), the pattern of the pyspec
  two-step-finality run, and
  `ConcreteFinalityWitness.adjacent_certificate_extraction` finalizes epoch 4
  through an adjacent link. These fixtures show concrete non-anchor finality;
  no full-bundle run has it.
* Fixed-scope guard regression:
  `ScopeGuardRegression.registry_changing_block_out_of_scope` and
  `ScopeGuardRegression.parent_request_block_out_of_scope` reject a genesis
  child with slashings and an exit, or with a parent execution request;
  `ScopeGuardRegression.in_scope_child_accepted` accepts the same child
  without them.
* `FFGInterpretationFidelity` (outside the safety premise):
  `NextSlotPremiseWitness.ffg_interpretation_fidelity`,
  `FullTwelveWitness.ffg_interpretation_fidelity`,
  `TargetEdgePremiseWitness.ffg_interpretation_fidelity`,
  `FullTwelveEnvelopeWitness.ffg_interpretation_fidelity`,
  `ByzantinePremiseWitness.ffg_interpretation_fidelity`. Each proves the
  fidelity record for the canonical interpretation of its run: the included
  votes are valid members of the accepted carrier body.
* `EventualCheckpointInclusion` (paper Assumption 3.2 (explicit)) over the
  view of the bridge:
  `NextSlotPremiseWitness.witnessPaperA32Inclusion`. The slot-eight carrier
  carries the unrealized justification of the slot-one child in epoch 1. It is
  in epoch 2, because Python justification returns early in epochs 0 and 1.
  Each full-bundle family proves the first case of the consequent
  (`AvailableCheckpointOrExtension`): a carrier carries `C(b, e)` itself.

## Counterexamples

* `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` refutes
  same-second head agreement at a mid-second prefix under the counterexample synchrony
  record. The querying actor confirms a candidate while another honest node's
  head is its sibling.
* `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` refutes
  the same same-second claim under the counterexample synchrony record. It uses proposer
  boost 40 and Byzantine allowance 25. Its computed safety threshold is 95.
  These counterexamples do not refute next-slot safety of an in-slot query.
  That question remains open.

## Notes

The 1 s safety run (delay 500 ms) changes a stored root. The 12-second
full-bundle run adds real delayed block and vote receipts. The target-edge run
checks current-target support as a fact about the run. The envelope run
exercises envelope delivery, the envelope prefix, and data relay through
`FullTwelveEnvelopeWitness.envelope_relay_exercised` and
`FullTwelveEnvelopeWitness.data_relay_exercised`. The Byzantine run exercises
positive non-honest weight and the slashing relay through
`ByzantinePremiseWitness.byzantine_weight_exercised` and
`ByzantinePremiseWitness.slashing_relay_exercised`. The Byzantine run
exercises the previous-result proviso through
`ByzantinePremiseWitness.previous_result_proviso_exercised`. Both support forms
are derived by the joint call and endpoint-slot induction. The witness support
lemmas remain facts about the runs.
No full-bundle run exercises non-anchor finality, positive Gloas discount, a
PTC event, or positive proposer boost.
Every positive run has proposer boost zero. The proposer-score term and
should_apply_proposer_boost are not exercised positively. The one-second
runs set `attestation_due_bps` to zero. The main safety runs have four or five
validators. Each slot committee has one validator, except in the Byzantine run,
where validator 4 joins the committees of validator 3. Included slashing does
not mark a validator slashed in state.
`DeadlineVotePathCandidate` checks that a skipped-boundary schedule fails the
pre-tick relay. The audited public theorem set has 46 entries. Four regression checks are:
`CheckpointSyncFilterWitness.normalized_anchor_run_keeps_child`,
`CheckpointSyncFilterWitness.anchor_only_view_satisfies_inclusion`,
`EarlyEpochBoundaryWitness.epoch_one_boundary_regression`, and
`EarlyEpochBoundaryWitness.epoch_one_fixture_satisfies_boundary_laws`. They
check the normalized-state control, the strict-link inclusion antecedent, the
certified epoch-1 source after two boundaries, and that this epoch-1 behavior
satisfies the boundary laws. They are not full-bundle runs. The epoch-1
regression certifies its link with the votes in the body of the next-slot
carrier (`ConcreteBridge.BodyIncludedAt`).

Paper references use arXiv:2405.00549v4 (https://arxiv.org/abs/2405.00549v4).
-/
