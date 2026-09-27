# Review guide

`ReviewClaims` has one safety field. `review_claims` proves it. The field states observer-store membership and executable ancestry from the next slot. The trust audit checks 46 public theorems: 39 executable-side and seven paper-side. [Former live theorem history](history/live-monotonicity-removed.md).

The premise `ConcreteBridge.SafetyPremises` starts the run from the Python genesis
store of the bridge setup (`ConcreteBridge.ConcreteGenesis`). The genesis state has
the zero-root stub. The translation proves the internal anchor condition
`NextSlotSafetyPremises.anchor_state_checkpoints` from this genesis. At the FFG
interpretation boundary,
`CheckpointReadsAs` reads a raw genesis stub as the genesis anchor because both
checkpoints have `GENESIS_EPOCH`. Executable handlers and wire attestations keep the raw
checkpoint. Checkpoint-sync anchors with older state checkpoints are outside this
condition. The raw source age and the filter's `+2` rule need an inclusion argument.
That argument is not formalized.
`CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample` has no attestation
inclusion for two epochs, so it is outside `EventualCheckpointInclusion`. It shows why
that premise matters; it is not an FCR safety failure.

The translation proves `Phase0SourceCoherence` and `Phase0BoundarySourceCoherence` for
the concrete transition of the bridge. `Phase0BoundarySourceCoherence` has five fields.
`process_slots_one_boundary` equates
one boundary with eager PJF. `process_slots_same_target_epoch` equates target slots in
one epoch. `state_transition_process_slots` equates a crossing block transition with
slot processing. `process_slots_checkpoint_epoch` bounds the output checkpoint if every
intermediate slot-processed state satisfies `3 * effective_balance_increment < 2 *
get_total_active_balance`. This guard is exact because an empty vote set can pass the
two-thirds test at a total balance of at most one and a half increments.
`process_slots_two_boundaries` equates two or more boundaries from a start epoch of at
least `GENESIS_EPOCH + 2` with eager PJF, if the registry and the total active balance
are unchanged and the same guard holds at every intermediate state.
The admissible setup (`FFGSetup.Admissible`) requires two increments of active weight,
and the translation gives `ScheduledFCRCallPremises.balance_floor`. With
`registry_static_in_horizon`, this floor supplies the guard on in-horizon reads. The
concrete transition rejects blocks with slashings, voluntary exits, or parent execution
requests, and a Python run with an epoch-step registry change (effective-balance update,
activation, ejection, or pending deposit) is outside the scope (`FixedFFGScope`).
`on_attestation_committee` confines successful delivered attestations in honest
in-horizon prefixes to their slot committee. Attester-slashing evidence can name
off-committee validators.

A `ConcreteBridge` fixes one concrete setup (configuration, fixed scope, committee
schedule, genesis state, and block-validity oracle) and the state and block
commitments. Its interface runs the concrete Gloas FFG transition for `process_slots`,
`state_transition`, and PJF. The block-validity oracle is opaque (class I). It can
reject a block but supplies no FFG state, and the theorem holds for every oracle.
`ConcreteBridge.StateRootsCommit` (class I) is not a premise; with it, the bridge
accepts each in-scope block that Python accepts. The proof computes the FFG
interpretation from the bridge (`SafetyPremises.nextSlotSafetyPremises`). The
inclusion relation counts the body votes of accepted blocks that set the timely-target
flag. Python `process_attestation` accepts some votes without a target-root check;
such votes do not count. An included aggregate stands for one single-validator vote of
each signer, with the same data. The premise keeps eventual checkpoint inclusion (paper
Assumption 3.2) over the view of the bridge. The projection harness checks the
interpretation laws on real pyspec runs. It reports `EventualCheckpointInclusion.included` as NOT_ESTABLISHED; the every-view antecedent and A3.2 implication remain assumed. The concrete FFG state and
34 Gloas functions agree with 59 Python differential cases and with the retained fields
of 48 accepted blocks of a 100-validator pyspec run.

## Operational obligations

`DeadlineBlockRelay` is an operational store-retention premise close to the membership part of the conclusion. The network must deliver each cutoff block and its parents before the next boundary. Each honest client must service ready blocks, accept a valid block with a known parent, and retain accepted blocks. Only a permanent finalized-guard rejection before the tick is exempt. The proof excludes that branch for the confirmed root and proves head ancestry.
`DeadlineBoundaryBlockPrefix` requires the block before a boundary vote handler.
Envelope, data-availability, vote, and slashing relay fields require timely
receipt and handler service. The positive delay bound alone does not give
these events.

## Short glossary

- **FCR:** Fast Confirmation Rule. It selects a confirmed root from fork-choice state.
- **Beacon function interface:** `BeaconFunctionInterface` supplies the opaque beacon, committee, signature, and payload functions.
- **FFG:** Casper Friendly Finality Gadget. It supplies checkpoint justification and finalization state.
- **LMD-GHOST:** Latest Message Driven Greedy Heaviest Observed SubTree. It selects a fork-choice head from latest votes.
- **Gloas:** The consensus fork that separates beacon blocks from execution payloads.
- **Available checkpoint:** `AcceptedBlockFFGState.AvailableCheckpoint` holds when an accepted block on the tip's chain has checkpoint evidence. `CheckpointInclusionView.AvailableCheckpoint` is the paper view.
- **PTC:** Payload Timeliness Committee. It supplies payload timeliness votes in Gloas.
- **GST:** Global stabilization time. The paper's synchrony assumptions apply after this point.
- **Scheduled prefix:** `Execution.ScheduledPrefixStore` is a store from the exact event fold. `Execution.RootKnownInScheduledPrefix` also covers the initial store.
- **Selected vote support:** `SelectedPredictionVoteSupport` is an internal derived fact. Current-edge votes use the exact target. Previous-result votes may use different targets below the selected root.
- **FFG interpretation:** `ScheduledFFGInterpretation` holds the accepted block state and its checkpoint read agreement. The translation computes it from the concrete bridge. `FFGInterpretationFidelity` checks real included votes and the external validity function.
- **A, Δ, S:** A is the attestation deadline offset. Δ is the positive message delay. S is the slot duration. The execution premise requires `A + Δ < S`.

## Review status

```text
┌─────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Finding                 │ Status and evidence                                                                                          │
├─────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Stored next-slot safety │ The root is in each honest observer's block store and on its head from the next slot, within the horizon.    │
│ Selected result         │ A spec-correspondence lemma covers the find_latest_confirmed_descendant note. It is not a review claim.      │
│ Optional in-slot query  │ Next-slot safety remains open. The counterexamples refute same-second head agreement under the               │
│                         │ counterexample synchrony record.                                                                             │
│ Payload envelope        │ Exercised by FullTwelveEnvelopeWitness.envelope_relay_exercised and data_relay_exercised under the full      │
│                         │ safety bundle, with an accepted envelope that one node receives two seconds late.                            │
│ Guarded target edge     │ Exercised by TargetEdgePremiseWitness.target_edge_support_exercised under the full safety bundle.            │
│ Byzantine weight        │ Exercised by ByzantinePremiseWitness.byzantine_weight_exercised: non-honest weight 200 of 4000 under the     │
│                         │ full safety bundle.                                                                                          │
│ Slashing relay          │ Exercised by ByzantinePremiseWitness.slashing_relay_exercised; the call at second six reads the evidence.    │
│ Previous-result guard   │ Exercised by ByzantinePremiseWitness.previous_result_proviso_exercised and                                   │
│                         │ previous_result_descendant_support_exercised: the call at slot 13 selects an epoch-2 block.                  │
│ Included carrier votes  │ The canonical relation counts body votes of accepted blocks that set the timely-target flag. Body membership │
│                         │ and validity are also in FFGInterpretationFidelity, outside the premise.                                     │
│ Block validity          │ The block-validity oracle is opaque (class I) and supplies no FFG state. The theorem holds for every oracle. │
│                         │ No oracle can accept a block outside the fixed scope.                                                        │
│ Interpretation fidelity │ Each full-bundle witness proves FFGInterpretationFidelity for its interpretation. Validation uses a prepared │
│                         │ target checkpoint state from a reachable keyed target block state.                                           │
│ Committee span bound    │ The fault fraction applies to every in-horizon span, including one slot. A global fault share does not       │
│                         │ establish it.                                                                                                │
│ Opaque validation       │ BeaconExternalsPremises and verified envelope events supply the engine verdict and deterministic behavior.   │
│ Static registry         │ The registry is fixed in the horizon. The transition rejects blocks with slashings, exits, or parent         │
│                         │ execution requests (scope error). A Python run with an epoch-step registry change is outside the scope.      │
│ Paper Algorithm 1       │ SafeConfirmedAlg1Inputs requires future rule confirmation for each honest-view-safe block. This is stronger  │
│                         │ than paper Assumption 6.                                                                                     │
│ Gloas discount          │ The pinned fork counts matching-status or PENDING parent votes. Upstream can count opposite resolved-status  │
│                         │ votes.                                                                                                       │
└─────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

`scripts/ReviewSurfaceShape.lean` pins field names and field types for 18
reviewed records and the definition of the safety claim.

## Audit path

1. **Model:** Read `FastConfirmationModel/`. Compare `Spec/` with the pinned Python fork. Check the Gloas discount, finite maps, loop fuel, and arithmetic. Check schedules and accepted handler results in `Execution/`.
2. **Statements premises:** Read the safety field of `ReviewClaims`. Expand each record in `FastConfirmationStatements/Premises/`. Check the observer, time, horizon, and successful-prefix ranges.
3. **Externals:** Check the table below against `BeaconFunctionInterface` and `BeaconExternalsPremises`. Check the concrete bridge in `FastConfirmationModel/Execution/ConcreteBridge.lean`, its canonical inclusion relation, and its block-validity oracle. The slashing relay is a separate premise over the literal Python handler.
4. **Claims:** Read the proof terms in `FastConfirmationProofs/`. Check `confirmed_root_safe_from_next_slot` and `review_claims`. Read the independent Paper library with [the paper map](PAPER_MAP.md).
5. **Witnesses:** Read `FastConfirmationWitnesses/Index.lean`. Check each run's true guards and vacuous branches. Check the 46 audited public theorems in `scripts/Audit.lean`.

## Trusted boundary

`BeaconFunctionInterface` has 11 functions or relations. The bridge fixes seven of
them: the committee reads from its schedule, the three state functions from the
concrete transition, the structural part of the indexed check, and the anchor relation.
The base interface of the bridge supplies the others. The table distinguishes
constrained externals, whose contracts are premises, from unconstrained externals. The theorem holds for every choice of an unconstrained
function. A source or client interpretation must justify the constrained
contracts and the intended behavior of any unconstrained function it uses.

```text
┌──────────────────────────────────────┬────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│External field                        │Constraining premise and limit                                                                          │
├──────────────────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────────────────┤
│get_beacon_committee                  │Fixed by the bridge: the committee schedule of the setup (class I).                                     │
│                                      │BeaconExternalsPremises.committees_agree, committee_assignment_unique, committee_coverage, and          │
│                                      │committee_members_active constrain the union read. Ordered committee tables in BeaconState are          │
│                                      │unconstrained: the theorem holds for every choice of these tables.                                      │
│get_committee_count_per_slot          │Fixed by the bridge: the schedule count. No count contract is a premise.                                │
│process_slots                         │Fixed by the bridge: the concrete process_slots on the decoded state.                                   │
│                                      │BeaconExternalsPremises.process_slots_slot, registry_static_in_horizon, and                             │
│                                      │process_slots_attestation_valid constrain used outputs. The translation proves both Phase0 source-      │
│                                      │coherence records. FFGInterpretationFidelity constrains target-state origin outside safety.             │
│state_transition                      │Fixed by the bridge: the concrete state_transition with the opaque validity oracle and the state        │
│                                      │commitment. BeaconExternalsPremises.state_transition_slot, state_transition_pre_slot_lt, and            │
│                                      │state_transition_checkpoint_epoch constrain imports; the last one only from a pre-state whose           │
│                                      │checkpoints are not in a future epoch (anchor_state_checkpoint_epoch starts that invariant). The        │
│                                      │translation proves the Phase0 source records, the FFG state laws, and ImportedBlockFinalizationLag.     │
│process_justification_and_finalization│Fixed by the bridge: the concrete PJF. BeaconExternalsPremises.pjf_checkpoint_epoch (for a state whose  │
│                                      │justified checkpoint is not in a future epoch) constrains checkpoint outputs. The translation proves the│
│                                      │five Phase0BoundarySourceCoherence laws.                                                                │
│is_valid_indexed_attestation          │The bridge adds the structural check to the base signature check. honest_attestation_valid,             │
│                                      │valid_attestation_honest, on_attestation_committee, valid_attestation_default, and                      │
│                                      │process_slots_attestation_valid constrain accepted checks.                                              │
│AnchorCommitsToState                  │Fixed by the bridge: the slot-0 genesis block and the projected genesis state.                          │
│                                      │ConcreteBridge.ConcreteGenesis gives the genesis store. No hash theorem is proved.                      │
│get_ptc                               │Unconstrained: the theorem holds for every choice of this function. The handler reads the ordered PTC.  │
│is_valid_indexed_payload_attestation  │Unconstrained: the theorem holds for every choice of this function. No PTC signature contract exists.   │
│is_data_available                     │NextSlotSynchronyPremises.data_availability_relay and envelope_delivery transport true data reads. The  │
│                                      │handler checks the local Boolean result. No KZG soundness theorem is proved.                            │
│verify_execution_payload_envelope     │BeaconExternalsPremises.verify_envelope_deterministic and envelope_delivery constrain verified          │
│                                      │observations. No execution-engine or signature refinement theorem is proved.                            │
└──────────────────────────────────────┴────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

Under the bridge, eight of the `BeaconExternalsPremises` fields in this table
are theorems: `process_slots_slot`, `registry_static_in_horizon`,
`state_transition_slot`, `state_transition_pre_slot_lt`,
`state_transition_checkpoint_epoch`, `pjf_checkpoint_epoch`,
`anchor_state_checkpoint_epoch`, and `valid_attestation_default`
(`FastConfirmationProofs/FFG/Concrete/ExternalsLaws.lean`). They are not in
the public premise: `SafetyPremises.externals_coherence` has the residual
record `ConcreteExternalsPremises` (committee agreement, coverage, uniqueness
and activity, the three signature laws, slot-processing validity, and
envelope determinism), and the translation builds `BeaconExternalsPremises`.
The static validator set is also proved, so it is not a premise field.

`Execution.schedule` is supplied. `WellFormedExecution`, `HonestBehavior`, and
the delivery laws constrain it. The bridge computes the accepted FFG relation and
the checkpoint reads.
`Execution.store` is the handler fold.

`is_head_weak` reads the ordered `BeaconState.beacon_committee_reads` and
`BeaconState.committee_count_reads` tables. These tables are not constrained by
`BeaconExternalsPremises`; a client must relate them to its committee reads.
This is part of the fixed-committee idealization.

## Review dimensions

- **Python fidelity:** Compare each modeled FCR branch with the pinned Python source. Check each abstraction and changed Gloas branch.
- **Execution:** Check event order, successful handler returns, state at boundary seconds, payload validation, static stake, and external contracts.
- **Statements:** Expand the safety field of `ReviewClaims`. Check observer, time, and horizon quantifiers.
- **Premises:** Expand every nested record. Check that each premise is needed and jointly satisfiable. Check FFG and finalization ranges beyond the endpoint.
- **Non-vacuity:** Locate concrete runs for the audited theorem witnesses. Check each field that a run exercises only vacuously.
- **Paper:** Read the independent Section 3.1 and Section 4 theorems. Check where Algorithm 1 uses a stronger premise than paper Assumption 6.

## Premise strength and range

Paper Assumption 3.2 can allow a two-epoch FFG inclusion delay. The executable selector can close its gates before inclusion. The [history note](history/live-monotonicity-removed.md) explains the reset branches and the removed claim.

`ConcreteBridge.SafetyPremises` includes the admissible bridge, the concrete genesis store, the horizon tie to the fixed scope, scheduled execution, externals, honest behavior, delivery of body attestations, synchrony, static validators, a fault bound for each committee span, epoch arithmetic, the epoch-1 finalization scope, and checkpoint inclusion. `SafetyPremises.nextSlotSafetyPremises` computes the internal record `Execution.NextSlotSafetyPremises`: exact FFG state at each successful handler prefix, anchor alignment, checkpoint evidence, finalization delay, Phase0 source coherence, and a balance floor. No field directly states the stored-root safety conclusion. Global FFG and finalization premises can range beyond a conclusion endpoint.

`ByzantineWeightPremises.span_fraction` and `estimate_sound` are deterministic
events assumed on every checked span, including one slot. A global fault share
does not imply these events. Their probability under committee sampling is
outside this development.

Prediction support is derived. `SelectedPredictionVoteSupport` is internal proof vocabulary,
outside the safety premise. Its previous-result conclusion permits different targets
that all descend from the selected result.

The key theorem is
`Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold`.
The call induction retains the preceding lineage. The strict endpoint-slot
induction supplies earlier honest heads. The current crossing and previous-result
consumers use `Execution.preQueryVoteSelectedSIRBracketAt_of_earlierVotes` and
the two endpoint pinning lemmas. They do not assume future vote support.
After strict-result safety is proved, the fold derives support for later calls.

The historical payload retains the original caller, call second, target, source,
and `start(e+1)` deadline. Both its certificate and its quorum are functions of a
cutoff after the target epoch. An earlier endpoint uses the original gate and
votes before that endpoint. No strict justified-epoch external law was added.

The reachability audit keeps the Statements library focused on declarations
used by the safety review claim. The Internal library holds call and trace
vocabulary, vote-support predicates, and interpretation fidelity used by
proofs and witnesses.

The existing target-edge witness theorems remain facts about the runs. Their full-bundle constructors no longer prove support fields.
See [modeling choices](MODELING_CHOICES.md) for the Python note and the
counterexample to exact target agreement for a previous-epoch result.

## Delivery and evidence

`NextSlotSynchronyPremises` requires positive Δ and strict `A + Δ < S`. Its
`delivery_lookahead` field also covers the first boundary beyond the public
horizon and implies the in-horizon vote delivery law. A source observation
must occur by its slot deadline. A receiver observation occurs at or after the
next boundary. A receiver is later than the source. Honest votes use the vote
deadline. `synchrony_and_delivery_iff_nextSlot` relates these bundles.

Block and envelope exclusion is checked before the next-slot tick. It permits only a permanent finalized-guard conflict with a known parent. The FFG, economic, and finalization-delay premises establish that each honest head's known ancestor path is admissible. Carrier-certificate accountability covers other required roots. Ready blocks and envelopes precede the boundary vote handler. Data service and deterministic envelope validation justify payload acceptance. `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope event.

`on_attester_slashing` follows Python. It validates against `store.block_states[store.justified_checkpoint.root]`. Evidence relay is an implementation assumption that gives every honest node the indices by the next boundary. With the static registry and one fork, the missing-signer case cannot occur in scope: keyed states have the same validators and signing domain. Timely receipt and handler service remain premises. Five of six checked clients validate against a newer head state. The [modeling choices](MODELING_CHOICES.md) page records the pinned client commits. A late accepted item uses a fresh cutoff observation at the next scheduled FCR call. No validity-agreement field was added to the external contract.

## Source and checks

The source of record is fork `fradamt/consensus-specs`, tag `fcr-gloas-fix` (`13f391516`). The [source map](SPEC_MAP.md) records the exact difference from upstream. The [conformance harness](conformance.md) compares projected Python and Lean observations. A matching trace does not prove all external contracts or all reachable executions. The `weak-synchrony` branch contains work in progress on weaker timing premises and is outside this review.

`scripts/validate.sh --fast` checks the source pin, document names, import boundary, and hygiene. Full validation builds the libraries and checks imports, reachability, surface shape, and the 46 public witnesses. `scripts/Audit.lean` allows only `propext`, `Classical.choice`, and `Quot.sound`.

## Known limits

The conclusion covers stored boundary outputs in a finite horizon. Exact `estimate_sound` and coverage force equal slot-committee weights. The epoch-1 scope condition excludes runs in which an accepted block state finalizes epoch 1. A3.2 remains an untested implication. It does
not cover an arbitrary in-slot query. The confirmed root is in each honest
observer's block store from the next slot. The active validator set is fixed.
No witness has non-anchor finalization, positive Gloas discount, or a PTC
event. Every positive run uses zero proposer boost. The one-second runs use
`attestation_due_bps = 0`. The main safety runs have four or five validators
and one validator per slot committee, except in the Byzantine run, where validator 4
joins the committees of validator 3. The theorem
does not prove that the Python handlers or a client satisfy each external
contract. The independent Paper library has no refinement theorem to the
executable model.
