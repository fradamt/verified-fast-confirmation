# Modeling choices

Paper citations use [arXiv:2405.00549v4](https://arxiv.org/abs/2405.00549v4).

Each row states a choice in the executable model, why it is used, and the property it does not establish. The model definitions are the source of truth; this page is a guide to their boundaries.

```text
┌───────────────────────────────────────┬──────────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────────────┐
│ Choice                                │ Reason                                                           │ Cost                                                                              │
├───────────────────────────────────────┼──────────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────┤
│ Natural numbers for slots and time    │ Makes finite arithmetic and schedule folds explicit.             │ No uint64 wraparound inside the model; EpochEndsFitUint64 limits the              │
│                                       │                                                                  │ checked range.                                                                    │
│ Totalized finite maps                 │ Lean functions must return on missing keys.                      │ Proofs need domain laws for reachable keys; arbitrary missing-key reads           │
│                                       │                                                                  │ have defaults.                                                                    │
│ Injective block-root labels           │ WellFormedExecution.blocks_root_injective identifies blocks      │ It gives no hash_tree_root equation or cryptographic commitment.                  │
│                                       │ with equal roots.                                                │                                                                                   │
│ Atomic handler rejection              │ An invalid attestation returns none and leaves the run store     │ Python can retain a target checkpoint-state cache write before indexed            │
│                                       │ unchanged.                                                       │ validation fails. See the cache-write note below.                                 │
│ Explicit loop fuel                    │ Makes recursive Python walks total.                              │ Equivalence needs a bound on reachable parent walks.                              │
│ Projected BeaconState and Store       │ Keeps only fields used by the rule and checks.                   │ Unused source-state behavior is outside the model.                                │
│ Opaque BeaconFunctionInterface        │ Separates consensus logic from execution engine and              │ BeaconExternalsPremises must be justified by an implementation.                   │
│                                       │ cryptography.                                                    │                                                                                   │
│ Non-optimistic payload import         │ Every stored payload passed envelope validation, including       │ Optimistic fork-choice behavior is outside the theorem.                           │
│                                       │ VALID.                                                           │                                                                                   │
│ Accepted event prefix semantics       │ Tracks a handler result at every scheduled prefix.               │ Schedules and successful handler assumptions need a concrete network              │
│                                       │                                                                  │ argument.                                                                         │
│ Canonical FFG inclusion relation      │ Reads body votes of accepted blocks through the concrete         │ Counts only votes that set the timely-target flag; an aggregate stands for        │
│                                       │ transition (TargetIncludedAt).                                   │ single-validator votes of its signers.                                            │
│ Opaque block-validity oracle          │ Separates BLS, hash roots, proposer selection, and other         │ The theorem holds for every oracle; agreement with Python validity is class I.    │
│                                       │ unmodeled checks from the FFG transition.                        │                                                                                   │
│ Supplied FFG validation state         │ Prepares the keyed target block state from an honest store.      │ Stated in FFGInterpretationFidelity only; the prepared state may be unkeyed.      │
│ Static validator registry             │ Fixes the registry in the horizon.                               │ Blocks with slashings, exits, or parent requests are rejected; an epoch-step      │
│                                       │                                                                  │ registry change in Python is outside the scope.                                   │
│ Finite horizon                        │ Makes endpoints and next-slot receipt precise.                   │ Conclusions do not extend beyond the checked horizon.                             │
│ Global FFG and finalization laws      │ The translation proves them from the concrete transition.        │ They range over handler-successful prefixes beyond a conclusion endpoint.         │
│ Derived FCR prediction support        │ Exact targets for current results; descent for previous results. │ Both forms follow from the joint call and endpoint-slot induction.                │
│ Gloas payload-aware discount          │ Counts matching or PENDING parent votes in an empty slot.        │ Diverges from upstream rule; public fix at fcr-gloas-fix.                         │
│ Envelope and data relay               │ Carries verified payload state to honest receivers.              │ The finite next-slot witness has no envelope event.                               │
└───────────────────────────────────────┴──────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────────┘
```

On a failed indexed attestation, Python may retain the target checkpoint-state cache write. Lean returns none, and the scheduled fold keeps the prior store. The cache value comes from the target block state and deterministic `process_slots` when the target entry is absent. A later successful call computes the same value if the keyed block state is unchanged. This is an argument for later successful attestation validation, not a refinement proof for all later reads. A direct `checkpoint_states` read can observe the Python write before any successful call; the Lean model omits that effect.

The inclusion relation is the canonical relation of the bridge: the body votes
of accepted blocks, read through the concrete transition. It is not a free
input.
`review_claims` has one safety field. `DeadlineBlockRelay` supplies operational store retention close to membership; the proof removes permanent exclusion and proves executable ancestry.

The `ByzantineWeightPremises.span_fraction` bound applies to every in-horizon
committee span, including one slot. A global fault share does not establish
this bound. `span_fraction` and `estimate_sound` are deterministic events
assumed on every checked span, including one slot. Their probability under
committee sampling is outside this development. The fault bound matches
the committee majority bound in v4 Assumption 2.

The PTC assignment function, PTC signature check, ordered committee tables,
and committee counts are unconstrained. The theorem holds for every choice of
each of these functions or tables. Other external contracts are premises; see
the [trusted boundary](REVIEW_GUIDE.md#trusted-boundary).

`DeadlineBlockRelay` is an operational store-retention condition close to the membership result. Network delivery must bring cutoff blocks and parents before the next boundary. Clients must service ready blocks, retain accepted blocks, and apply only the stated permanent finalized-guard exemption. The proof rules out that exemption for the confirmed root and establishes head ancestry.

The execution records use a positive delay in milliseconds. Their strict bound
is `get_attestation_due_ms cfg + delay_ms < cfg.slot_duration_ms`. Let S be the
slot duration and A the attestation deadline offset. This is the paper's
`A + Δ < S`: immediate honest gossip delivers a message held by A strictly
before the next slot. `HonestBehavior.vote_deadline` bounds each honest vote
between its slot start and the Python due time, rounded down to whole seconds.
Phase0 calls for a vote after the expected valid block or at the due time,
whichever comes first. Gloas sets the offset with `attestation_due_bps`.
`HonestBehavior.no_forgery` also retains the causal send-time order.
The `delta` field supplies the positive timing parameter. The separate
delivery fields state receipt and handler service. No proof derives those
fields from `delta` alone.

`DeadlineBlockRelay` transports only roots held by an honest node at or before
the deadline of the source observation's slot. The receiver query is at or
after the next slot start and strictly after the source observation. The sole
exemption is `PermanentBlockExclusion`, evaluated at the second before the
next-slot tick. It requires a known parent and permanent failure of an exact
finalized-checkpoint guard in `on_block`. It cannot excuse a late block or a
missing parent. A block that arrives before the next boundary is either
accepted and retained, or its finalized-guard rejection persists through
that boundary's predecessor. Finality first installed by the next tick cannot
excuse an earlier absent block. The arrival-transfer lemmas check this time
step; the model has no network queue.

The accepted FFG, economic, and finalization-delay premises establish
admissibility of each honest head's known ancestor path. Accountability for
available and unrealized FFG certificates handles other required carriers. The proofs transport
these roots and paths, then use local store monotonicity at later times.
They do not require all roots of one honest store to reach every other store.
Scheduled FCR calls read at slot start. Stored heads and source-history records
retain their earlier deadline observations. These facts preserve the public
next-slot endpoints without a new public premise field.

`DeadlineBoundaryBlockPrefix` puts needed blocks before the next-slot
attestation handler. `DeadlineEnvelopeDelivery` uses the same cutoff and
pre-tick exemption. It states that every honest store has the verified payload
from the next slot start; one receipt at any earlier second is sufficient,
because Python keeps `store.payloads`. `DeadlineBoundaryEnvelopePrefix` puts
the verified payload before the next-slot attestation handler.
`DeadlineDataAvailabilityRelay` provides data at a matching receiver
observation at or after the next slot start. These contracts include honest
client service of ready messages, as required by Python's delay
consideration. Raw receipt alone does not prove handler acceptance or data
availability. The finite next-slot witness has
one-second slots, A = 0, and a 500 ms delay witness; it has no envelope event.
`FullTwelveWitness.full_bundle_witness` proves the full bundle at 12-second
slots, A = 3 s and Δ = 2 s, with two real delayed first receipts; it also has
no envelope event.

`DeadlineAttesterSlashingRelay` has the same source cutoff and later-slot
receiver gate, with no exclusion branch. Slashing delivery takes at most Δ,
so `A + Δ < S` puts it before the next slot. Acceptance needs the slashable-data
check and two indexed-attestation checks. They read the attestations, signer
pubkeys, and target-epoch domains. Pubkeys are immutable. The genesis validators
root is common, and the model has one fork, so the domains are common.

The relay is an operational assumption. Five of six checked clients validate evidence against the head state. The literal Python handler uses the justified state. With the static registry and one fork, the missing-signer case is outside this theorem scope.

The handler `on_attester_slashing` follows the Python and validates against
`store.block_states[store.justified_checkpoint.root]`. The relay field is a
premise, not a handler check: it states that every honest node holds the
indices by the next boundary. A missing signer at the justified state requires a registry change, which is outside the static-registry scope. The premise matches clients
that validate network evidence against a newer state. Lighthouse, Prysm, Teku,
Lodestar, and Nimbus use the head state; Lighthouse advances it to the
wall-clock slot. Grandine follows the specification and uses the justified
state. All six clients apply valid gossip evidence to fork choice before block
inclusion, and none prunes the equivocation set at finalization.

Client revisions for this comparison: Lighthouse e423a66763bb1bd780492d635123f208d80c3538; Prysm 5407381fc51c9604c7f95b8d87dbb8f4786a83fd; Teku 3d26533fb84a7d12da04e5ab59e1ab7399db5fc5; Lodestar c535e94f25e209f6b137be3d29a87562088035d3; Nimbus 404a0001561d1d83c5b5bf35dcbedbcb5fb86572; Grandine 66b3d385c3dc69d89e05b80bbb6baf7442a12966.

Evidence accepted late in a slot is included: the relay's source time is when
the confirmer holds the index at its scheduled slot-start FCR call. The two
margin consumers use that call's cutoff observation.

These execution premises implement the paper's positive-delay timing at slot
boundaries in the synchronous segment. They do not add a GST transition. The
paper's independent view model is not a refinement proof for Python handlers.

The source fork is `fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`). See [source map](SPEC_MAP.md), [review guide](REVIEW_GUIDE.md), and [paper library history](history/paper-side-removed.md).

## Strong conditions

These fourteen fields are stronger than a direct claim about all real clients.
Each item states why the proof uses the field and what a weaker model would
need.

1. `HonestBehavior.votes_head` requires every honest committee member to vote for its fork-choice head. It excludes abstention and other vote choices. The proof uses this vote support.
2. `HonestBehavior.not_slashable` requires all scheduled honest votes to be pairwise non-slashable. With `votes_head`, it constrains honest head votes across slots. The proof uses it to exclude honest equivocation.
3. `HonestBehavior.no_forgery` covers every scheduled attestation that names an honest validator, even before validation. It lets the proof identify honest vote data in received copies.
4. `BeaconExternalsPremises.registry_static_in_horizon` fixes the registry in keyed states of honest causal stores and in the slot-processed states that handlers read. Under the bridge it is a theorem (`ConcreteBridge.registry_static_in_horizon`). The concrete transition rejects blocks with slashings, voluntary exits, or parent execution requests. A Python run with an epoch-step registry change (effective-balance update, activation, ejection, or pending deposit) is outside the scope; see [the registry scope](#current-ffg-and-execution-scope). Withdrawals, rewards, and penalties change only balances, which the projection does not retain. The proof uses one anchor registry for weights and committees.
5. `StaticValidatorSet.activity_constant` fixes active status across the horizon. It lets committee and stake facts use one active set. Under the bridge it is a theorem (`ConcreteBridge.activity_constant`) from `FixedFFGScope.activity_fixed`, so it is not a public premise field.
6. `BeaconExternalsPremises.committees_agree` and `on_attestation_committee` model committees as one fixed ground-truth assignment `E.committee`. `committees_agree` makes every honest store query for every in-horizon slot return this assignment. In the real protocol, the committees of epoch e depend on the RANDAO mix of epoch e − 2 and on the branch of the reading state, so two honest nodes can read different committees. These RANDAO-seeded, fork-dependent committees are not modeled. A weaker model needs per-branch committees in the execution, with each weight bound stated for the committees of the reading branch.
7. `BeaconExternalsPremises.on_attestation_committee` confines successful delivered attestations to their slot committee. The Lean handler receives an indexed wire object. This premise stands for Python's committee-derived `get_indexed_attestation` path, with the fixed assignment of item 6 in place of the committee of the target checkpoint state. It does not constrain attester-slashing evidence; off-committee evidence can validate and only adds indices to the equivocating set.
8. `BeaconExternalsPremises.verify_envelope_deterministic` ignores observation context for a fixed state and signed envelope. It supports transport of a verified result to a later observation.
9. `ByzantineWeightPremises.estimate_sound` makes every in-horizon estimate an upper bound. Committee sampling is idealized: the premise takes the committee-weight estimate of the specification as exact, and the specification claims it only with high probability (COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR and the gist that the specification cites). The idealization has two parts, and both are intended: (i) equal slot-committee weights inside an epoch; (ii) a perfectly mixed reshuffle across an epoch boundary, so the committee weight of a cross-boundary span is at most the pro-rated estimate of the specification, which is the expected overlap. With the fixed committee schedule, `EstimateForcesBalance.slot_committee_weight_forced` proves part (i): the field and committee coverage give each slot committee in a full in-horizon epoch the weight total_active / SLOTS_PER_EPOCH. The statistical properties of committee sampling, and the tolerance of the FCR thresholds to sampling error, are out of scope by design.
10. `ByzantineWeightPremises.span_fraction` bounds non-honest weight in every checked slot span, including one slot. A global stake fraction alone cannot supply this field.
11. `NextSlotSynchronyPremises.attester_slashing_relay` gives each honest store the equivocation indices by the next boundary. Literal Python can reject evidence when its justified state lacks a signer.
12. `NextSlotSafetyPremises.anchor_state_checkpoints` admits the genesis anchor with a raw stub or a state with both checkpoints equal to the anchor. Older raw checkpoints in a checkpoint-sync state are outside its scope. Under `ConcreteBridge.SafetyPremises` the run starts from the concrete genesis (`ConcreteBridge.ConcreteGenesis`), and the translation proves this field.
13. `ScheduledFCRCallPremises.balance_floor` requires two increments of anchor active weight. With the static registry, this supplies the exact intermediate-state guard for `Phase0BoundarySourceCoherence.process_slots_checkpoint_epoch`. Under the concrete premise the translation proves it from the admissible setup (`FFGSetup.Admissible`).
14. `SafetyPremises.epoch_one_finalization_scope` (`ConcreteBridge.EpochOneFinalizationScope`, internally `AcceptedBlockFFGState.epoch_one_finalization_one_step`) restricts the scope: a finalization of epoch `GENESIS_EPOCH + 1` in a committed state of an accepted block, or in an eager copy, has a link to the next epoch. No such link can exist. A target-epoch-2 vote must match the current justified checkpoint in epoch 2 or the previous justified checkpoint in epoch 3, and both have epoch 0 because PJF returns early at the ends of epochs 0 and 1. So in effect the field says that no accepted block state finalizes epoch 1. Lean proves this (`ConcreteBridge.epochOneFinalizationScope_finalized_ne_one`), and the pyspec check finding.epoch_two_target_source_is_genesis tests the source epochs. Python finalizes epoch 1 when epoch-2 justification needs votes included in epoch 3, through the link 1 -> 3. The proof does not cover this case for two reasons. First, an honest vote of epoch 2 with a head in epoch 1 can have a source older than the finalized epoch. Second, Assumption 3.2 does not make a finalized epoch-1 checkpoint canonical during epoch 2. `test_realized_gap.py` has a run in which one store finalizes epoch 1 through the link 1 -> 3 while an honest store still has justified epoch 0 (regression.finalized_epoch_one_two_step_above_voter_justified). Finalizations of later epochs through two-epoch links are in scope: `realized_finalized_evidence` and `unrealized_finalized_evidence` state the `k = 2` Python law, and `Phase0BoundarySourceCoherence.process_slots_two_boundaries` gives the honest source of a stale head.

## Derived prediction support

`ScheduledFCRCallPremises` has no prediction-support field.
`SelectedPredictionVoteSupport` remains internal proof vocabulary. For a current-epoch
crossing it states exact target agreement. For a previous-epoch result it states
that each later honest target descends from the result in the execution parent
graph. It permits different target checkpoints.

The Python specs/phase0/fast-confirmation.md note on both prediction helpers
says: "This function assumes that all honest validators will be voting in
support of the current epoch target starting from the current moment in time."
The current-target condition is derived here, not assumed. As in paper Lemmas
44 and 45, canonicity gives the target agreement. Paper Lemma 42 needs only
descendant targets for a previous-epoch result; its exact-target reading is too
strong, as the execution below shows.

The joint call induction in `Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold`
proves safety and history together from the preceding call's lineage. Within
each strict-result proof, the endpoint-slot induction supplies canonicity at
all earlier honest votes. `Execution.currentResult_supportBefore_of_endpoint_induction`
and `Execution.previousResult_descendSupportBefore_of_canonical` give the
required support. The two endpoint pinning lemmas use included certificates
and committee assignment uniqueness to select a vote before the endpoint.
This also works when the target epoch has not ended. The proof does not use
the full safety theorem as an input, and adds no strict justified-epoch law.

After strict-result safety is proved, the call fold derives the original
call's vote support for the next lineage. The payload retains that call,
its target, its fixed source, and its original `start(e+1)` deadline.
`AcceptedHistoricalA32GatePayloadAt.certified` and `support_branch` require a
cutoff after the target epoch. Their producers use votes before that cutoff.
An earlier endpoint uses the original call's gate and truncated support to
pin its checkpoint, without producing the full historical quorum.

The six full-bundle witness constructors do not contain support fields.
Their support and non-vacuity theorems remain facts about the concrete runs.

Exact target agreement is too strong for a previous-epoch result. Let r be
the result in epoch e-1. A Byzantine proposer withholds a first-slot block
X1 of epoch e, which descends from r, then gives it only to the caller
after the vote deadline. The caller uses X1 as its current target at the
next slot's guarded call. Other honest validators propose and vote on a
branch from r before X1 arrives. Their epoch-e target is r, while the
caller's target is X1. The selected root r stays safe and the relay
deadlines permit this schedule. Thus safety and descendant support can hold
without exact target agreement. This is a protocol description, not a Lean
counterexample witness. The Byzantine run exercises the previous-result
proviso branch (`ByzantinePremiseWitness.previous_result_proviso_exercised`).

## Interpretation fidelity

The safety premise contains only the FFG inclusion facts that the proof uses.
`Execution.IncludedAttestationEvidence` gives the carrier message, a received
block copy of the vote, slot and target-epoch facts, and committee membership.
The accepted extension ties the message to the carrier root. The proof gets
honest-vote facts from the received copy and `HonestBehavior.no_forgery`.

`FFGInterpretationFidelity` in
`FastConfirmationInternal/FFG/InterpretationFidelity.lean` states the
intended interpretation: included votes are real, valid body members of
accepted blocks, and they validate on the target state that `on_attestation`
prepares. It also identifies the validity oracle with the external check and
orders realized and unrealized finality. The safety proof does not need these
facts, so they are not a hypothesis of `confirmed_root_safe_from_next_slot`.
Each full-bundle witness proves the record for the same interpretation that
satisfies its premises, so the witnesses still show that a faithful relation
satisfies the premises.

## Gloas and Phase0 heads

FULL payloads and available data do not make Gloas fork choice equal to
Phase0 fork choice. Gloas can suppress proposer boost for a weak previous-slot
parent after an early same-proposer equivocation. Gloas can also replace a
latest message with a later vote in the same epoch. The conformance harness
therefore compares Gloas observations with the pinned Gloas source.

## Anchor and boundary limits

`FFGStateReadAgreement` reads each raw state or store checkpoint as the
accepted selector through `CheckpointReadsAs`: the two are equal, or both have
epoch `GENESIS_EPOCH`. Away from epoch 0 the relation is equality. A real
genesis state has the stub `Checkpoint(GENESIS_EPOCH, ZERO_HASH)` as its
current justified and finalized checkpoints (fork-choice.md:217-244), and
honest votes carry that stub as their source until the first justification.
The stub reads as the genesis anchor. The same relation applies to link
sources (`IncludedSupermajorityLink.signer_attestation`), to the honest-source
identities, and to `ImportedBlockFinalizationLag`. Executable handlers and wire
attestations stay raw; the proof uses `normalizeAnchorCheckpoint` only at this
interpretation boundary.

`NextSlotSafetyPremises.anchor_state_checkpoints` states the anchor scope: the anchor epoch is `GENESIS_EPOCH`, or the anchor state's current justified and finalized checkpoints equal the anchor. The first case covers a real genesis state with a zero-root stub. The second case covers a normalized anchor state. A checkpoint-sync anchor whose state checkpoints are older than the anchor is excluded.
`GenesisStubPremiseWitness.genesis_stub_full_bundle_witness` satisfies the
full bundle with a genesis stub whose root is not the anchor root, and the
FCR still confirms its child.

Raw checkpoint equality in the handlers does not change a confirmed result at
a genesis anchor. is_head_unrealized_justified_ok compares the observed
justified checkpoint, which comes from the global unrealized field, with the
head's unrealized justification, which can be the stub. When they differ only
in the stub root, the observed checkpoint is the anchor at slot 0, so
is_confirmed_block_stale is false and the guarded branch has the same
outcome. `will_no_conflicting_checkpoint_be_justified` compares two global
fields, which never hold the stub. The filter compares the finalized root only
above `GENESIS_EPOCH`. Every other FCR and filter test compares epochs, and
the stub has the anchor's epoch.

`CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample` starts
with an epoch-3 anchor and raw justification at epoch 2. The unchanged FCR
confirms its slot-13 child at slot 14. At slot 20, raw source epoch 2 fails
the filter's `source.epoch + 2 >= current_epoch` test. The head returns to the
anchor. The fixture includes no attestation for two epochs. It does not assert the full safety bundle or its `EventualCheckpointInclusion` premise. The raw source can therefore lose a confirmed child, while the normalized source keeps it. This shows why the inclusion premise matters; it is not an FCR safety failure. With enough valid epoch-3
votes included on the canonical chain in epoch 4, PJF can instead advance
the raw source to epoch 3 before the filter's epoch-5 deadline. The raw source age and the filter's `+2` rule need an inclusion argument. That argument is not formalized.

`BeaconExternalsPremises.pjf_checkpoint_epoch` and
`state_transition_checkpoint_epoch` apply only to a state whose checkpoints
are not in a future epoch of the state. Python does not satisfy them on every
well-typed state: at slot 0 with justified epoch 5, the PJF early return keeps
epoch 5 (the labelled contract regression pjf_checkpoint_epoch_out_of_domain). With the antecedent,
both laws hold for every state. The proof carries the antecedent as a store
invariant: every keyed block state is sane. `anchor_state_checkpoint_epoch`
(class E-scope) gives the base case, and the transition law gives the step.
The `Phase0SourceCoherence` and `Phase0BoundarySourceCoherence` laws have no
such antecedent; the contract suite also checks them on unreachable states.

`Phase0BoundarySourceCoherence` has five laws. Slot processing across one
boundary gives the eager PJF checkpoint. Targets in the same epoch give the
same checkpoint. A block transition gives the checkpoint of slot processing
to the block slot. The fourth law has a balance antecedent: each state that
slot processing passes through has total active balance such that `3 * effective_balance_increment < 2 * get_total_active_balance`. Under this antecedent, slot processing keeps the checkpoint or
gives one no newer than the start epoch. The fifth law covers two or more
boundaries from a start epoch of at least `GENESIS_EPOCH + 2`: if the
registry and the total active balance do not change and the same balance
antecedent holds at every intermediate state, slot processing gives the eager
PJF checkpoint. The second PJF weighs the same start-epoch participants with
the same effective balances, and later PJF runs see no votes. Phase0 and
Altair PJF return early in epochs 0 and 1, so an epoch-1 state can keep the
old checkpoint under eager PJF and justify epoch 1 when slot processing
reaches epoch 3; the fifth law excludes these starts. The balance
antecedent is necessary: `get_total_balance` returns at least one increment,
so with a total active balance of at most one and a half increments an epoch with no
attestations passes the two-thirds test. `ScheduledFCRCallPremises.balance_floor`
asks for an anchor active weight of at least two increments. The registry is
static in the horizon, so this one constant fact gives the antecedent at each
use. Every real network satisfies it.

The proof reads the honest source of an old target as this boundary source.
After two or more boundaries, a known current-epoch block below the head
carries the same checkpoint as its `GJ`, and its formed evidence certifies
it. The gate producers ask for such a block. Every current-crossing call
supplies it. For a finalizing link to the next epoch, the finalization
argument excludes the late case: the vote's target epoch is one more than its
source epoch. For a link of two epochs, the head can be one epoch older than
the vote's source requires; `process_slots_two_boundaries` then reads the
source as the head's `GU` when the head epoch is at least `GENESIS_EPOCH + 2`,
and `epoch_one_finalization_scope` excludes the epoch-1 case.
`EarlyEpochBoundaryWitness.epoch_one_boundary_regression` records both boundary
outcomes and the included certificate for the newer source.
`EarlyEpochBoundaryWitness.epoch_one_fixture_satisfies_boundary_laws` shows
that the same reduced functions satisfy the five laws.

`normalizeAnchorCheckpoint` provides internal lemmas for anchor normalization. `CheckpointReadsAs` supplies the genesis-epoch read relation in the safety bundle. The genesis-stub witness proves that the full bundle can hold for raw genesis state checkpoints. The executable handlers and wire attestations keep their raw values.

`CheckpointSyncFilterWitness.anchor_only_view_satisfies_inclusion` checks an
additional obligation for checkpoint sync. In a normalized anchor-only view,
the epoch-F source and target are both the anchor. The strict-link support
antecedent then requires `F < F`. The current inclusion premise holds for this
finite view without an included vote. This is not a complete FFG interpretation
or a full-bundle counterexample; it identifies an antecedent that a repair must
address.

`scripts/anchor_semantics_probe.py` reproduces both behaviors with the pinned
Python functions. Run it with that checkout's existing Python environment
and pass the checkout path. It uses the minimal preset and skips BLS checks
through the test helper. The Gloas probe supplies old headers and timeliness
entries because the proposer-boost helper otherwise cannot find an old header
when it walks before a checkpoint-sync anchor. The Lean regression starts from
the literal one-block initial store. The positive Python control includes epoch-F votes in an epoch-F+1 carrier
and checks that the raw source is F at F+2. None of these tests is a new
full-bundle witness.

## Epoch-one inclusion

Phase0 and Altair `process_justification_and_finalization` return early when
the current epoch is `GENESIS_EPOCH + 1` or less. Thus a block of epoch 1 has
anchor unrealized justification, even when its chain includes a supermajority
of epoch-1 votes. Only a block of epoch 2 or later can justify epoch 1 through
unrealized justification.

`EventualCheckpointInclusion.included` therefore asks for an inclusion block
of epoch `GENESIS_EPOCH + 2` or later when the target epoch is above
`GENESIS_EPOCH`. `AcceptedBlockFFGState.unrealized_justified_max` has the same
epoch guard, and `AcceptedBlockFFGState.unrealized_justified_early` makes the
realized and unrealized selectors equal at those epochs.
`AcceptedBlockFFGState.realized_justified_max` asks for a seed
block of an earlier epoch and a block epoch above `GENESIS_EPOCH + 2`, because
realized justification at a block of epoch E shows only the boundaries before
E.

regression.fcr_confirmed_block_reorged_epoch_one in
`scripts/conformance/contracts/test_realized_gap.py` shows why the inclusion
guard is necessary. In the fork run, blocks at slots 1 to 15 include the
epoch-1 votes, and no block on that chain has epoch 2. A block at slot 16 on
the slot-8 block includes the same votes. The pinned Python FCR confirms the
slot-15 block at slots 16 to 23. In epoch 3 the slot-16 block has epoch-1
unrealized justification and the slot-15 block does not. The head moves to
the slot-16 block, and the slot-15 block is no longer on the canonical chain.
The old inclusion premise holds in this run, because the slot-15 chain
includes the epoch-1 votes in epoch 1. The new premise does not hold, because
no epoch-2 block on that chain includes them. The run is thus outside the
theorem. The test fails if the Python run stops showing the reorg.

Each non-vacuity witness has its carrier block in epoch 2 for this reason.
In epochs 0 and 1 the witness PJF keeps the anchor, as the Python early
return does.

## Current FFG and execution scope

The public premise is `ConcreteBridge.SafetyPremises`. A `ConcreteBridge`
fixes one concrete setup: the configuration, the fixed scope, the committee
schedule, the genesis state, and the block-validity oracle. It also fixes the
state and block commitments. Its interface runs the concrete FFG transition of
`FastConfirmationModel` for `process_slots`, `state_transition`, and PJF. The
other interface methods (signatures, PTC, payload envelopes, and data
availability) come from a base interface.

The FFG interpretation of the proof is not a premise.
`SafetyPremises.nextSlotSafetyPremises` computes it from the bridge. The
inclusion relation is `TargetIncludedAt`: the body votes of accepted blocks
whose `process_attestation` call set the timely-target flag. Python
`process_attestation` does not check the target root, so a body vote with a
wrong target root does not count. The checkpoint selectors read the committed
state of a block and one eager PJF copy of that state. The premise keeps paper
Assumption 3.2 (`checkpoint_inclusion`) over this view, and the scope condition
`epoch_one_finalization_scope`.

The internal formed-evidence relation `CarriedOrRealizable` also admits
`RealizableBySlotRun`: the justified checkpoint of a slot run from the
committed state of a block to a later in-scope slot. Such a checkpoint can be
one that no selector of the block carries, for example a run from slot 15 to
slot 24. The public Assumption 3.2 view uses only the carried checkpoints
(`ConcreteBridge.Carried`). The proof shows that each realizable checkpoint is
justified by the body votes on the chain of the block.

Python includes aggregates. The model reads an included aggregate as one
single-validator vote for each signer, with the data of the aggregate. The
honest vote of a validator is a single-validator vote, and the causal evidence
(`HonestEarlierTargetVoteOnCarrierChain`) asks for an included attestation that
names the validator and has the same data.

The block-validity oracle is opaque and class I. It can reject a block, but it
supplies no FFG state. It stands for BLS signatures, SSZ hash roots, proposer
selection, the execution-requests commitment, RANDAO, eth1 data, sync
aggregates, withdrawals, payload attestations, and BLS-to-execution changes;
none of these writes a retained field. The safety theorem holds for every
oracle, including one that accepts every block. A bridge represents a Python
run only if its oracle accepts the blocks that Python accepts and the run
satisfies the registry scope below. `ConcreteBridge.StateRootsCommit` (class I) is collision
resistance of the Python state hash root on the states of one run. With it, the bridge
accepts each in-scope scheduled block that Python accepts. The safety theorem
does not need it.

The concrete transition keeps every validator record fixed. It rejects a block with a proposer or attester slashing, a voluntary exit, or a parent execution request (`FFGWireBlock.InFixedScope`, error `scope`); a body deposit fails the Python guard. An epoch step can still change a record in Python: an effective-balance update, an activation, an ejection, or a pending deposit. The model has no balances and cannot detect these steps, so a Python run is in scope only if no epoch step in the horizon changes a validator record. The whole-bundle sample checks this condition on its run, and a negative control shows that the check detects an effective-balance change. Under the bridge, `registry_static_in_horizon` is a theorem (`ConcreteBridge.registry_static_in_horizon`): the concrete functions write no validator record. It is a fact of the model, so it does not by itself exclude a Python registry change; the epoch-step condition does. Withdrawals, rewards, penalties, and the slashing penalty change only balances, which the projection does not retain.

The concrete differential compares 59 cases with pinned Python. The whole-bundle
sample compares the retained fields after each of 48 accepted blocks of a
100-validator Python run with the Lean transition. The projection harness tests
the interpretation laws, `RealizableBySlotRun`, the aggregate split, and
`IncludedCheckpointEvidence.causal` on real pyspec runs. The finite full-bundle
witnesses show consistency. Their PJF returns early in epochs 0 and 1, like
Python.

The model projects `BeaconState` to fields used by FCR and totalizes state-valued
external functions on inputs where Python raises. The premises constrain those
total functions; they do not assert Python behavior on an invalid input. The
`process_slots_attestation_valid` law applies to successful in-horizon calls.
`is_head_weak` reads committee tables stored in `BeaconState`; a client must
relate these tables to real committee reads under the fixed-committee scope.
The registry and the single committee map stay fixed across the checked horizon.
The `IncludedAttestationEvidence.attesters_in_committee` field uses that map.

The anchor condition has a real genesis witness. Its normalized-state branch
is a condition, not a checkpoint-sync construction. Raw checkpoint-sync states
with older source checkpoints are outside the current result. A3.2 requires an
epoch-1 vote to be included in a block of epoch 2 or later. The Python FCR
regression in `scripts/conformance/contracts/test_realized_gap.py` loses a
confirmed block when epoch-1 evidence is seeded too early. The finality law uses
a two-epoch lag (`k = 2`), the source law covers two or more boundaries, and the
`epoch_one_finalization_scope` field gives the `F = 1` scope.
