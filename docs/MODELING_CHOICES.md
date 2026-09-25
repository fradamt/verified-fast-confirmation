# Modeling choices

Each row states a choice in the executable or paper model, why it is used, and the property it does not establish. The model definitions are the source of truth; this page is a guide to their boundaries.

```text
┌───────────────────────────────────────┬─────────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────────────┐
│ Choice                                │ Reason                                                          │ Cost                                                                              │
├───────────────────────────────────────┼─────────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────┤
│ Natural numbers for slots and time    │ Makes finite arithmetic and schedule folds explicit.            │ No uint64 wraparound inside the model; EpochEndsFitUint64 limits the              │
│                                       │                                                                 │ checked range.                                                                    │
│ Totalized finite maps                 │ Lean functions must return on missing keys.                     │ Proofs need domain laws for reachable keys; arbitrary missing-key reads           │
│                                       │                                                                 │ have defaults.                                                                    │
│ Injective block-root labels           │ WellFormedExecution.blocks_root_injective identifies blocks     │ It gives no hash_tree_root equation or cryptographic commitment.                  │
│                                       │ with equal roots.                                               │                                                                                   │
│ Atomic handler rejection              │ An invalid attestation returns none and leaves the run store    │ Python can keep a checkpoint-state cache write before a failed assert.            │
│                                       │ unchanged.                                                      │ Accepted runs exclude that failed call's resulting store.                         │
│ Explicit loop fuel                    │ Makes recursive Python walks total.                             │ Equivalence needs a bound on reachable parent walks.                              │
│ Projected BeaconState and Store       │ Keeps only fields used by the rule and checks.                  │ Unused source-state behavior is outside the model.                                │
│ Opaque Externals                      │ Separates consensus logic from execution engine and             │ BeaconExternalsPremises must be justified by an implementation.                   │
│                                       │ cryptography.                                                   │                                                                                   │
│ Non-optimistic payload import         │ Every stored payload passed envelope validation, including      │ Optimistic fork-choice behavior is outside the theorem.                           │
│                                       │ VALID.                                                          │                                                                                   │
│ Accepted event prefix semantics       │ Tracks a handler result at every scheduled prefix.              │ Schedules and successful handler assumptions need a concrete network              │
│                                       │                                                                 │ argument.                                                                         │
│ Supplied FFG carrier-vote relation    │ Checks accepted carrier origin and a received block vote copy.  │ A caller must supply the causal inclusion evidence for its execution.             │
│ Supplied FFG validation state         │ Prepares the keyed target block state from an honest store.     │ Stated in FFGInterpretationFidelity only; the prepared state may be unkeyed.      │
│ Static validator registry             │ Matches the paper balance setting over the horizon.             │ The safety theorem does not cover validator churn.                                │
│ Finite horizon                        │ Makes endpoints and next-slot receipt precise.                  │ Conclusions do not extend beyond the checked horizon.                             │
│ Global FFG and finalization laws      │ Connects opaque beacon transitions to exact checkpoint state.   │ The premises range over handler-successful prefixes beyond a conclusion endpoint. │
│ Guarded FCR prediction support        │ Uses the spec proviso only when the selector guard is true.     │ Real voting agreement must supply that premise.                                   │
│ Gloas payload-aware discount          │ Counts matching or PENDING parent votes in an empty slot.       │ Diverges from upstream rule; public fix at fcr-gloas-fix.                         │
│ Envelope and data relay               │ Carries verified payload state to honest receivers.             │ The finite next-slot witness has no envelope event.                               │
│ Live block production                 │ Prevents stale cache reversal and supplies descendant votes.    │ Requires an honest-proposer block every slot from execution start.                │
│ Timely live FFG justification         │ Opens the rule restart gates at epoch boundaries.               │ Stronger than paper Assumption 6. Joint witness only at the genesis checkpoint.   │
│ Paper exact rational balances         │ Keeps the paper threshold algebra direct.                       │ Does not by itself model executable integer rounding.                             │
│ Paper eligibility filter              │ Reuses the LMD head agreement result in HFC.                    │ The proof needs a separate never-filter premise and bridge.                       │
│ Paper AU from block-contained votes   │ Ties justification to concrete ancestry evidence.               │ OnChainAnchorInterface still supplies visibility and formation laws.              │
│ Algorithm 1 future confirmation input │ Discharges the later monotonicity gate.                         │ SafeConfirmedAlg1Inputs is stronger than Assumption 6.                            │
└───────────────────────────────────────┴─────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────────┘
```

The safety claims hold for every carrier-vote relation that meets the stated
fields. They do not alone certify the votes in real block bodies. The
`ByzantineWeightPremises.span_fraction` bound applies to every in-horizon
committee span, including one slot. A global fault share does not establish
this bound. It matches `CommitteeHonestMajority` in the repository's formal
paper Assumption 2.

The execution records use a positive delay in milliseconds. Their strict bound
is `get_attestation_due_ms cfg + delay_ms < cfg.slot_duration_ms`. Let S be the
slot duration and A the attestation deadline offset. This is the paper's
`A + Δ < S`: immediate honest gossip delivers a message held by A strictly
before the next slot. `HonestBehavior.vote_deadline` bounds each honest vote
between its slot start and the Python due time, rounded down to whole seconds.
Phase0 calls for a vote after the expected valid block or at the due time,
whichever comes first. Gloas sets the offset with `attestation_due_bps`.
`HonestBehavior.no_forgery` also retains the causal send-time order.

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

Client provenance for this comparison (commits checked on 2026-09-25): Lighthouse e423a66763bb1bd780492d635123f208d80c3538; Prysm 5407381fc51c9604c7f95b8d87dbb8f4786a83fd; Teku 3d26533fb84a7d12da04e5ab59e1ab7399db5fc5; Lodestar c535e94f25e209f6b137be3d29a87562088035d; Nimbus 404a0001561d1d83c5b5bf35dcbedbcb5fb86572; Grandine 66b3d385c3dc69d89e05b80bbb6baf7442a12966.

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

## Interpretation fidelity

The safety premise contains only the FFG inclusion facts that the proof uses.
`Execution.IncludedAttestationEvidence` gives the carrier message, a received
block copy of the vote, slot and target-epoch facts, and committee membership.
The accepted extension ties the message to the carrier root. The proof gets
honest-vote facts from the received copy and `HonestBehavior.no_forgery`.

`FFGInterpretationFidelity` in
`FastConfirmationStatements/Premises/InterpretationFidelity.lean` states the
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
