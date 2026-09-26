# Modeling choices

Each row states a choice in the executable or paper model, why it is used, and the property it does not establish. The model definitions are the source of truth; this page is a guide to their boundaries.

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
│ Atomic handler rejection              │ An invalid attestation returns none and leaves the run store     │ Python can keep a checkpoint-state cache write before a failed assert.            │
│                                       │ unchanged.                                                       │ Accepted runs exclude that failed call's resulting store.                         │
│ Explicit loop fuel                    │ Makes recursive Python walks total.                              │ Equivalence needs a bound on reachable parent walks.                              │
│ Projected BeaconState and Store       │ Keeps only fields used by the rule and checks.                   │ Unused source-state behavior is outside the model.                                │
│ Opaque BeaconFunctionInterface        │ Separates consensus logic from execution engine and              │ BeaconExternalsPremises must be justified by an implementation.                   │
│                                       │ cryptography.                                                    │                                                                                   │
│ Non-optimistic payload import         │ Every stored payload passed envelope validation, including       │ Optimistic fork-choice behavior is outside the theorem.                           │
│                                       │ VALID.                                                           │                                                                                   │
│ Accepted event prefix semantics       │ Tracks a handler result at every scheduled prefix.               │ Schedules and successful handler assumptions need a concrete network              │
│                                       │                                                                  │ argument.                                                                         │
│ Supplied FFG carrier-vote relation    │ Checks accepted carrier origin and a received block vote copy.   │ A caller must supply the causal inclusion evidence for its execution.             │
│ Supplied FFG validation state         │ Prepares the keyed target block state from an honest store.      │ Stated in FFGInterpretationFidelity only; the prepared state may be unkeyed.      │
│ Static validator registry             │ Fixes balances and slashed flags in the horizon.                 │ Included slashing never marks a validator slashed in state.                       │
│ Finite horizon                        │ Makes endpoints and next-slot receipt precise.                   │ Conclusions do not extend beyond the checked horizon.                             │
│ Global FFG and finalization laws      │ Connects opaque beacon transitions to exact checkpoint state.    │ The premises range over handler-successful prefixes beyond a conclusion endpoint. │
│ Derived FCR prediction support        │ Exact targets for current results; descent for previous results. │ Both forms follow from the joint call and endpoint-slot induction.                │
│ Gloas payload-aware discount          │ Counts matching or PENDING parent votes in an empty slot.        │ Diverges from upstream rule; public fix at fcr-gloas-fix.                         │
│ Envelope and data relay               │ Carries verified payload state to honest receivers.              │ The finite next-slot witness has no envelope event.                               │
│ Live block production                 │ Prevents stale cache reversal and supplies descendant votes.     │ Requires an honest-proposer block every slot from execution start.                │
│ Timely live FFG justification         │ Opens the rule restart gates at epoch boundaries.                │ Stronger than paper Assumption 6. Joint witness only at the genesis checkpoint.   │
│ Paper exact rational balances         │ Keeps the paper threshold algebra direct.                        │ Does not by itself model executable integer rounding.                             │
│ Paper eligibility filter              │ Reuses the LMD head agreement result in HFC.                     │ The proof needs a separate never-filter premise and bridge.                       │
│ Paper AU from block-contained votes   │ Ties justification to concrete ancestry evidence.                │ OnChainAnchorInterface still supplies visibility and formation laws.              │
│ Algorithm 1 future confirmation input │ Discharges the later monotonicity gate.                          │ SafeConfirmedAlg1Inputs already confirms each honest-view-safe block.             │
└───────────────────────────────────────┴──────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────────┘```

The safety claim holds for every carrier-vote relation that meets the stated
fields. It does not alone certify the votes in real block bodies.
`review_claims` has one safety field. It gives observer-store membership and
executable ancestry. `live_confirmed_root_monotonicity` is a separate
conditional theorem. Its timely FFG premise supplies store outcomes for the
named FCR guards: previous_epoch_greatest_unrealized_checkpoint,
is_head_unrealized_justified_ok, and the previous-slot-head voting-source
recency guard.

The `ByzantineWeightPremises.span_fraction` bound applies to every in-horizon
committee span, including one slot. A global fault share does not establish
this bound. `span_fraction` and `estimate_sound` are deterministic events
assumed on every checked span, including one slot. Their probability under
committee sampling is outside this development. The fault bound matches
`CommitteeHonestMajority` in the repository's formal paper Assumption 2.

The PTC assignment function, PTC signature check, ordered committee tables,
and committee counts are unconstrained. The theorem holds for every choice of
each of these functions or tables. Other external contracts are premises; see
the [trusted boundary](REVIEW_GUIDE.md#trusted-boundary).

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
pre-tick exemption and puts the accepted envelope occurrence before that vote
handler. `DeadlineDataAvailabilityRelay` provides data at the matching receiver
observation. These contracts include honest client service of ready messages,
as required by Python's delay consideration. Raw receipt alone does not prove
handler acceptance or data availability. The finite next-slot witness has
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

The relay is an implementation assumption. Five of six checked clients
validate evidence against the head state. The literal Python handler uses
the justified state and can violate the relay when that state lacks a signer.

The handler `on_attester_slashing` follows the Python and validates against
`store.block_states[store.justified_checkpoint.root]`. The relay field is a
premise, not a handler check: it states that every honest node holds the
indices by the next boundary. Literal Python can reject evidence at a node
whose justified state does not contain a signer. The premise matches clients
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
The live block-production premise remains separate. Deriving delivery of an
honest proposal to same-slot voters would also require `P + Δ ≤ A`, where P
is its proposal offset; safety's strict bound alone does not supply that fact.

The source fork is `fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`). See [source map](SPEC_MAP.md), [paper map](PAPER_MAP.md), and [review guide](REVIEW_GUIDE.md).

## Strong conditions

These eleven fields are stronger than a direct claim about all real clients.
Each item states why the proof uses the field and what a weaker model would
need.

1. `HonestBehavior.votes_head` requires every honest committee member to vote for its fork-choice head. It excludes abstention and other vote choices. The proof uses this vote support.
2. `HonestBehavior.not_slashable` requires all scheduled honest votes to be pairwise non-slashable. With `votes_head`, it constrains honest head votes across slots. The proof uses it to exclude honest equivocation.
3. `HonestBehavior.no_forgery` covers every scheduled attestation that names an honest validator, even before validation. It lets the proof identify honest vote data in received copies.
4. `BeaconExternalsPremises.registry_static_in_horizon` fixes the registry in keyed states of honest causal stores and in the slot-processed states that handlers read. It excludes runs where included slashings, deposits, activations, exits, or effective-balance updates change those records in the horizon. The proof uses one anchor registry for weights and committees.
5. `StaticValidatorSet.activity_constant` fixes active status across the horizon. It lets committee and stake facts use one active set.
6. `BeaconExternalsPremises.committees_agree` covers every honest store query for every in-horizon slot. It connects the external committee read to the execution assignment.
7. `BeaconExternalsPremises.on_attestation_committee` confines successful delivered attestations to their slot committee. The Lean handler receives an indexed wire object. This execution premise represents Python's committee-derived `get_indexed_attestation` path. It does not constrain attester-slashing evidence; off-committee evidence can validate and only adds indices to the equivocating set.
8. `BeaconExternalsPremises.verify_envelope_deterministic` ignores observation context for a fixed state and signed envelope. It supports transport of a verified result to a later observation.
9. `ByzantineWeightPremises.estimate_sound` makes every in-horizon committee estimate an upper bound. It lets the proof use the executable estimate without a failure case.
10. `ByzantineWeightPremises.span_fraction` bounds non-honest weight in every checked slot span, including one slot. A global stake fraction alone cannot supply this field.
11. `NextSlotSynchronyPremises.attester_slashing_relay` gives each honest store the equivocation indices by the next boundary. Literal Python can reject evidence when its justified state lacks a signer.

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
The live fields and claim are unchanged; no live-only support premise is needed.

Exact target agreement is too strong for a previous-epoch result. Let r be
the result in epoch e-1. A Byzantine proposer withholds a first-slot block
X1 of epoch e, which descends from r, then gives it only to the caller
after the vote deadline. The caller uses X1 as its current target at the
next slot's guarded call. Other honest validators propose and vote on a
branch from r before X1 arrives. Their epoch-e target is r, while the
caller's target is X1. The selected root r stays safe and the relay
deadlines permit this schedule. Thus safety and descendant support can hold
without exact target agreement. This is a protocol description, not a Lean
counterexample witness. The finite Byzantine witness separately proves a
true previous-result guard and the new descendant conclusion.

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

## Paper vote payload limit

The paper model computes on-chain available and unrealized justification from
FFG votes carried in block ancestry. These votes keep their vote slot. They do
not count as LMD-GHOST votes. The model has no block-size cap or execution
participation flags. It ignores a validator for an epoch if that validator
equivocates on the chain. `OnChainAnchorInterface` supplies chain payload
formation and availability laws. `OnChainAnchorInterfacesForRule` limits that
bridge to selected blocks and previous-slot witness blocks.
