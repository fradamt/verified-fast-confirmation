# Verified Fast Confirmation

[![CI](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml)

The Fast Confirmation Rule (FCR) selects a block root that a node can treat as confirmed from its fork-choice state, under explicit network, stake, and supplied FFG-interpretation premises.

- **Stored boundary output:** The confirmed root saved after a scheduled slot-boundary call.
- **Handler-successful prefix:** The state after a scheduled event whose handler returns successfully.
- **Carrier:** An accepted block that contains evidence for a checkpoint or vote.
- **AU:** An available or unrealized checkpoint with evidence on an accepted block's ancestry.

## Proved claims

`review_claims` proves the next-slot safety claim under the records in `FastConfirmationStatements/Premises/`:

- **Next-slot safety.** From the following slot through the finite verification horizon, every honest observer has the stored confirmed root in its block store. The executable ancestor walk also shows that the root stays on the observer's head.

The separate public theorem `live_confirmed_root_monotonicity` is conditional on the safety bundle and both fields of `LiveMonotonicityPremises`. `honest_block_each_slot` requires an honest block in every slot from execution start. Each block must be known by the next slot. Honest votes must support descendants of those blocks without reorg. `ffg_timely_justification` requires exact FFG store outcomes at the last-slot call and next epoch start. These outcomes close the named FCR guards: `previous_epoch_greatest_unrealized_checkpoint`, is_head_unrealized_justified_ok, and the previous-slot-head voting-source recency guard. The joint witness meets this field through the genesis anchor and has no included vote.

The result concerns stored boundary outputs. It does not cover an arbitrary query within a slot.

The proof takes an FFG interpretation as a premise: `AcceptedBlockFFGState`
with an inclusion relation and checkpoint selectors. It must agree with every
checkpoint read of successful handlers through `FFGStateAndCheckpointReadAgreement`
and satisfy eventual checkpoint inclusion (paper Assumption 3.2 style), link and
checkpoint agreement, checkpoint projection laws, and finalization lag. The
inclusion relation need not equal block-body membership. The theorem holds for
every relation with these laws. The intended relation uses body membership and
valid votes; `FFGInterpretationFidelity` states these facts, and every full-bundle
witness proves fidelity. This development does not derive the FFG layer from the
beacon state transition. To apply the theorem to a client or the Python rule,
one must show that its FFG behavior supplies this interpretation.

The read agreement reads each raw state checkpoint as the accepted selector:
equal, or both at `GENESIS_EPOCH`. The premise field `anchor_state_checkpoints`
states the scope: the anchor epoch is `GENESIS_EPOCH`, or the anchor state's
current justified and finalized checkpoints equal the anchor. A real genesis
state with the zero-root stub is covered;
`GenesisStubPremiseWitness.genesis_stub_full_bundle_witness` satisfies the full
bundle with such a state. A checkpoint-sync anchor whose state checkpoints are
older than the anchor remains excluded. The Phase0
boundary-source laws hold exactly for the pinned state functions, including
an epoch-1 state that skips into epoch 3. One law has a balance antecedent,
which the two-increment `balance_floor` supplies; see
[anchor and boundary limits](docs/MODELING_CHOICES.md#anchor-and-boundary-limits).
`CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample` checks
that, without eventual inclusion, an old raw checkpoint-sync source can fail
the filter's `+2` rule and lose a confirmed child. The normalized source keeps
the child. This is not a counterexample to the full safety bundle. See [anchor limits](docs/MODELING_CHOICES.md#anchor-and-boundary-limits).

## Assumptions at a glance

```text
┌────────────────────┬────────────────────────────────────────────────────────────────────────────────────────┐
│ Assumption         │ Plain meaning and premise record                                                       │
├────────────────────┼────────────────────────────────────────────────────────────────────────────────────────┤
│ Honest actions     │ Scheduled events and head votes. HonestBehavior.votes_head fixes each honest committee │
│                    │ vote.                                                                                  │
│ No forgery         │ HonestBehavior.no_forgery covers scheduled votes that name an honest validator.        │
│ No slashing        │ HonestBehavior.not_slashable makes honest votes pairwise non-slashable.                │
│ Root labels        │ WellFormedExecution.blocks_root_injective identifies blocks with equal root labels.    │
│ Timing             │ NextSlotSynchronyPremises requires receipt and handler service by the next boundary.   │
│ Stake and registry │ Keyed states in honest in-horizon stores and their slot-processed reads have the anchor registry. │
│ Stake floor        │ Positive total balance and ByzantineWeightPremises hold on each checked span.          │
│ Anchor             │ The initial anchor has the stated root, epoch, and boundary alignment. Its state is a  │
│                    │ genesis state or carries the anchor as its checkpoints (anchor_state_checkpoints).     │
│ FFG inclusion      │ AcceptedBlockFFGState.EventualCheckpointInclusion supplies Assumption 3.2 inclusion.   │
│ FFG state          │ ScheduledFFGInterpretation supplies accepted-block state, links, and checkpoint reads. │
│ Phase0 source      │ Phase0SourceCoherence and Phase0BoundarySourceCoherence constrain source reads.        │
│ Payload validity   │ BeaconExternalsPremises and the execution external contract govern imported payloads.  │
│ Live result only   │ LiveMonotonicityPremises supplies honest blocks and exact timely FFG store outcomes.   │
└────────────────────┴────────────────────────────────────────────────────────────────────────────────────────┘```

Prediction support is derived by joint induction over calls and endpoint slots.
Current-epoch crossings use exact targets. Previous-epoch results use descendant
targets. The proof needs only votes before each endpoint. Historical certificates
and quorums are produced on demand after the target epoch, with the original call,
target, source, and deadline. See `Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold`.
The [premise ledger](#premise-ledger) gives the remaining records and sources.
Evidence relay is a premise. The fault bound applies to each checked span.
The slashing relay is an implementation assumption. It matches clients that
validate evidence against the head state (five of six checked). The literal
Python justified-state handler can reject evidence and violate this relay.
The per-span fault bound and estimate soundness are deterministic events assumed
on every checked span, including one slot. A global fault share does not imply
them. This development does not calculate their probability under committee
sampling.
The live fields are stronger than paper Assumption 6.
The positive `delta` value is a timing parameter. The delivery laws in
`NextSlotSynchronyPremises` supply the network assumption. The proof does not
derive handler service or delivery from `delta` alone.
The attestation deadline offset A, the positive delay Δ, and the slot duration S
obey `A + Δ < S`. This bound puts a vote sent by the deadline before the next
slot. The delivery laws also require receipt and handler service.

## Trust and source

The executable model follows the `fradamt/consensus-specs` fork at tag `fcr-gloas-fix`
(`13f391516`). Gloas is the fork that separates beacon blocks from execution payloads. The
fork's empty-slot discount counts parent votes with a matching payload status or PENDING
status. Unmodified upstream can also count votes for the opposite resolved status. See the
[source map](docs/SPEC_MAP.md) and [counterexample](docs/history/gloas-negative-result.md).
Cryptography, beacon transitions, committee reads, and execution validation are opaque
external calls with stated contracts. The Lean kernel checks the proofs. The trust audit
allows only `propext`, `Classical.choice`, and `Quot.sound`. The [paper
library](#paper-library) models the [paper](https://arxiv.org/abs/2405.00549) separately.
There is no refinement theorem from the paper model to the executable model.
The [contract conformance checks](docs/conformance.md#contract-conformance) test generated states against the pinned Python functions and record known counterexamples.

## Verify

Install Python 3 and Elan. Use the pinned Lean toolchain from `lean-toolchain`. Check out the Python fork at tag `fcr-gloas-fix` locally. On a fresh checkout, `lake exe cache get` downloads Mathlib artifacts. Then run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
scripts/validate.sh --consensus-repo /path/to/fradamt-consensus-specs
```

A warm `lake build` took 24.19 seconds on a 12-core desktop. A fresh build can take longer.
`scripts/validate.sh --fast --consensus-repo /path/to/fradamt-consensus-specs` checks source
pinning, document names, boundaries, and hygiene. Full validation also builds the libraries
and audits 49 public theorems: 42 executable-side and seven paper-side. The Python
path must name the pinned local checkout.

## Premise ledger

The records in this table are in `FastConfirmationStatements/Premises/`. The last column gives the source of each condition.

```text
┌──────────────┬──────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────┬───────────────────────────────┐
│ Claim        │ Premise record                       │ Fields in plain words                                                            │ Source                        │
├──────────────┼──────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────┼───────────────────────────────┤
│ Safety field │ Execution.NextSlotSafetyPremises     │ Exact FFG state at every handler-successful prefix; a well formed scheduled run; │ Paper Assumption 3.2; Gloas   │
│              │                                      │ completed FCR calls; epoch arithmetic; anchor alignment; finalization            │ extension; model idealisation │
│              │                                      │ delay; more than one slot per epoch; checkpoint and link evidence.               │                               │
│ Safety field │ Execution.ScheduledExecutionPremises │ Whole seconds, well formed stores, coherent external calls, honest               │ Model idealisation            │
│              │                                      │ behavior with an attestation deadline, and a valid genesis store.                │ Phase0/Gloas; model premise   │
│ Safety field │ Execution.ScheduledFCRCallPremises   │ Six delivery laws; fixed active validators; committee and Byzantine              │ Paper Assumptions 1 and 2;    │
│              │                                      │ weight bounds; Phase0 source coherence; a two-increment balance floor;           │ Gloas extension; model        │
│              │                                      │ next-slot vote receipt.                                                          │ idealisation                  │
│ Safety field │ NextSlotSynchronyPremises            │ Positive delay parameter; delivery and handler-service laws for blocks,          │ Paper synchrony; Gloas        │
│              │                                      │ envelopes, data and evidence; pre-tick exclusion before boundary votes.          │ extension                     │
│ Safety field │ BeaconExternalsPremises              │ Slot and state transition coherence, committee and attestation                   │ Model idealisation            │
│              │                                      │ validity, and deterministic envelope verification.                               │                               │
│ Safety field │ ByzantineWeightPremises              │ Quantized balances, sound committee estimates, and a non-honest weight           │ Paper Assumption 2;           │
│              │                                      │ fraction bound for every span, including one slot. A global fault                │ executable estimate           │
│              │                                      │ share does not establish this span bound.                                        │                               │
│ Safety field │ ScheduledFFGInterpretation;          │ Exact handler-successful prefix FFG state, causal links, and projected           │ Paper Assumption 3.2; model   │
│              │ EpochCheckpointProjectionLaws        │ checkpoint roots.                                                                │ idealisation                  │
│ Live result  │ LiveMonotonicityPremises             │ An honest block in each slot from execution start, known by the next             │ Paper Theorem 1 monotonicity  │
│              │                                      │ slot and supported by honest votes; timely observed FFG justification            │ and Assumption 6,             │
│              │                                      │ at epoch boundaries.                                                             │ strengthened                  │
└──────────────┴──────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────┴───────────────────────────────┘```

`Execution.NextSlotSafetyPremises` supplies the safety premise to the review claim. `LiveConfirmedRootMonotonicity` adds `LiveMonotonicityPremises` to that same execution premise for the separate conditional result. The FFG and finalization laws can quantify over successful handler prefixes beyond the safety endpoint. The finite conclusion does not shorten those premise ranges.

## Witnesses

Each positive run proves its stated premise bundle. An exercised field has a
concrete source event, positive quantity, or true guard in that run. A proof of
the full bundle does not imply that every branch occurs.

- **Full safety at 1 s and 12 s:** `NextSlotPremiseWitness.finite_execution_satisfies_premises` and `FullTwelveWitness.full_bundle_witness` give stored root advances under the full safety bundle. The 12 s run has real delayed block and vote receipts.
- **Payload envelope:** `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope. Its delivery and data relay antecedents hold.
- **Byzantine weight and slashing:** `ByzantinePremiseWitness.full_bundle_witness` has positive non-honest weight and a slashing relay that the next call reads.
- **Guarded current-target edge:** `TargetEdgePremiseWitness.target_edge_support_exercised` reaches a selected epoch crossing. A later honest vote has the exact current target.
- **Live monotonicity:** `LiveMonotonicityWitness.joint_witness` satisfies the safety bundle and both live fields. The stored root advances at an epoch boundary.
- **Counterexamples:** `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` and `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` refute same-second head agreement at a mid-second prefix under the older synchrony record. Next-slot safety for an in-slot query is open.
- **Interpretation fidelity:** Full-bundle runs prove `FFGInterpretationFidelity` for their supplied included-vote relation. This record is outside the safety premise.

The table names fields with a concrete instance or true antecedent and labels
the gaps that no named full-bundle run exercises. A dash means that the row is
a counterexample and does not assert the safety bundle.

```text
┌─────────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Run                 │ Exercised premise fields or facts                                                                 │
├─────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────┤
│ 1 s full safety     │ HonestBehavior.votes_head; NextSlotSafetyPremises.checkpoint_inclusion; root advance.             │
│ 12 s full safety    │ NextSlotSynchronyPremises.attestation_delivery and deadline_block_relay; delayed receipts.        │
│ 12 s envelope       │ NextSlotSynchronyPremises.envelope_delivery and data_availability_relay; accepted payload.        │
│ Byzantine run       │ ByzantineWeightPremises.span_fraction with positive fault weight;                                 │
│                     │ NextSlotSynchronyPremises.attester_slashing_relay; previous-result guard.                         │
│ Current-target edge │ Selected current-target crossing guard and exact later target vote are derived facts.             │
│ Joint live run      │ LiveMonotonicityPremises.honest_block_each_slot and ffg_timely_justification; full safety bundle. │
│ Counterexamples     │ —                                                                                                 │
│ Fidelity records    │ FFGInterpretationFidelity body membership, validation state, and external validity check.         │
│ Non-anchor finality │ not exercised by a named full-bundle run.                                                         │
│ Positive discount   │ not exercised: the Gloas empty-slot discount is zero in the envelope run.                         │
│ PTC events          │ not exercised by a named full-bundle run.                                                         │
└─────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────┘```

No named run exercises non-anchor finalization or positive Gloas empty-slot
discount. The live run gets its FFG timing from the genesis anchor. The
envelope run computes a zero discount and does not select a FULL head. No run
has a PTC event. Every positive run sets `proposer_score_boost` to zero. The
proposer-score term and should_apply_proposer_boost are not exercised
positively. The one-second runs set `attestation_due_bps` to zero. The main
safety runs have four or five validators and one validator per slot committee.
The joint live run has two validators. Validator churn is outside
`StaticValidatorSet`. These are
coverage limits, not claims about unreachable protocol states.

## Scope limits

- `BeaconExternalsPremises.registry_static_in_horizon` fixes keyed states in honest in-horizon stores and their slot-processed reads to the anchor registry. Runs with included slashings, deposits, activations, exits, or effective-balance changes in the horizon are outside this condition.
- The model imports only validated payloads. An imported payload enters the store only after `verify_execution_payload_envelope` returns true. This external includes the execution engine's `VALID` decision. Execution validation itself is opaque.
- `BeaconExternalsPremises` supplies contracts for external state transitions and validation. `on_attestation_committee` constrains successful delivered attestations. Indexed attester-slashing evidence can have off-committee signers; its handler only updates the equivocating set. The Lean proof does not implement an execution engine.
- `AcceptedBlockAttestationInclusion.Included` is a supplied carrier-vote relation. Its safety evidence gives an accepted carrier block, a received block copy of the vote, slot and target-epoch facts, and committee membership.
- `FFGInterpretationFidelity` states the intended interpretation of the included votes: membership in the accepted carrier block's ordered FFG attestation body, validity on the target checkpoint state prepared from a keyed target block state in an honest in-horizon store, and the external validity check. The safety theorem does not assume it. Each full-bundle witness proves it for its interpretation.
- `ByzantineWeightPremises.span_fraction` must hold for every in-horizon slot span, including one slot. A global fault share does not establish this bound. The bound matches `CommitteeHonestMajority` in the repository's formal paper Assumption 2.
- `LiveMonotonicityPremises.honest_block_each_slot` requires a block with an honest proposer index in every slot from execution start. Its vote-support law and `ffg_timely_justification` require timely descendant votes and exact FFG state outputs at epoch boundaries. These conditions are stronger than paper Assumption 6. Proposer-index membership is not an authentication theorem.
- The result covers stored boundary outputs. The two extra-query counterexamples refute same-second head agreement at a mid-second prefix under the older synchrony record. Next-slot safety of an in-slot query is open.

## Paper library

`FastConfirmationPaper/Core/` defines the abstract objects. The seven audited public theorems are `head_agreement_after_confirmation`, `confirmed_block_safety`, `confirmed_block_monotonicity`, `gate_confirmed_block_safety`, `gate_confirmed_block_monotonicity`, `rule_confirmed_block_safety`, and `rule_confirmed_block_monotonicity`. This audit is separate from the finite non-vacuity witnesses. The paper library has no non-vacuity witness. Section 4 assumes `FFG_AccountableSafety`. Algorithm 1 safety also assumes a per-call `Alg1SelectorSafetyInterface`. Algorithm 1 monotonicity assumes `SafeConfirmedAlg1Inputs`: every honest-view-safe block is already confirmed by the local rule at its safe time. This is stronger than paper Assumption 6. No refinement theorem connects the paper and executable models.

## Where to read

Start with the [review guide](docs/REVIEW_GUIDE.md), [architecture](docs/ARCHITECTURE.md),
[modeling choices](docs/MODELING_CHOICES.md), [source map](docs/SPEC_MAP.md), and [paper
map](docs/PAPER_MAP.md). The [conformance guide](docs/conformance.md) covers trace
comparison. The claim and proof sources are `FastConfirmationStatements/Review.lean` and
`FastConfirmationProofs/ReviewTheorem.lean`. The [witness
index](FastConfirmationWitnesses/Index.lean) states each finite run's limit. The repository
uses the MIT [license](LICENSE).
