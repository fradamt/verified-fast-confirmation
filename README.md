# Verified Fast Confirmation

[![CI](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml)

The Fast Confirmation Rule (FCR) selects a block root that a node can treat as confirmed from its fork-choice state, under explicit network, stake, and supplied FFG-interpretation premises.

## Proved claims

`review_claims` proves two conditional claims under the records in `FastConfirmationStatements/Review.lean`:

- **Next-slot safety.** An honest node's stored confirmed root stays on every honest head from the following slot through the finite verification horizon.
- **Live monotonicity.** A later stored confirmed root descends from an earlier one when the safety bundle and both fields of `LiveMonotonicityPremises` hold. `honest_block_each_slot` requires an honest block in every slot from execution start, known by the next slot, with descendant honest votes. `ffg_timely_justification` requires exact timely FFG state at the last-slot call and next epoch start. The joint witness meets this field through the genesis anchor and has no included vote.

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

## Assumptions at a glance

```text
┌──────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Assumption           │ Plain meaning and premise record                                                            │
├──────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ Honest operation     │ Honest nodes process scheduled events. They vote by the due time. See                       │
│                      │ Execution.ScheduledExecutionPremises and HonestBehavior.                                    │
│ Timely delivery      │ Delivery laws require needed votes, blocks, payload data, and evidence before the next      │
│                      │ boundary. The positive delay is a timing parameter. See NextSlotSynchronyPremises.          │
│ Stake and committees │ Validators stay active. Committee estimates hold for every checked slot span. The fault     │
│                      │ bound holds for every checked slot span. See StaticValidatorSet and                         │
│                      │ ByzantineWeightPremises.                                                                    │
│ Beacon and FFG state │ External transitions match accepted evidence. Supplied checkpoint links match accepted      │
│                      │ evidence. See BeaconExternalsPremises and ScheduledFFGInterpretation.                       │
│ Payload validity     │ Imported payloads pass opaque execution validation. See BeaconExternalsPremises and the     │
│                      │ execution external contract.                                                                │
│ Live claim only      │ Each slot has an honest block. Honest votes support it. FFG justification is visible at the │
│                      │ required epoch boundary. See LiveMonotonicityPremises.                                      │
└──────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```

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
and audits 43 public theorem witnesses: 36 executable-side and seven paper-side. The Python
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
│              │                                      │ weight bounds; Phase0 source coherence; a nonzero balance floor;                 │ Gloas extension; model        │
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
│ Live field   │ LiveMonotonicityPremises             │ An honest block in each slot from execution start, known by the next             │ Paper Theorem 1 monotonicity  │
│              │                                      │ slot and supported by honest votes; timely observed FFG justification            │ and Assumption 6,             │
│              │                                      │ at epoch boundaries.                                                             │ strengthened                  │
└──────────────┴──────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────┴───────────────────────────────┘
```

`Execution.NextSlotSafetyPremises` supplies the common safety premise to the safety field. `LiveConfirmedRootMonotonicity` adds `LiveMonotonicityPremises` to that same execution premise. The FFG and finalization laws can quantify over successful handler prefixes beyond the safety endpoint. The finite conclusion does not shorten those premise ranges.

## Witnesses

Each positive run proves its stated premise bundle. An exercised field has a
concrete source event, positive quantity, or true guard in that run. A proof of
the full bundle does not imply that every branch occurs.

- **Full safety at 1 s and 12 s:** `NextSlotPremiseWitness.finite_execution_satisfies_premises` and `FullTwelveWitness.full_bundle_witness` give stored root advances under the full safety bundle. The 12 s run has real delayed block and vote receipts.
- **Payload envelope:** `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope. Its delivery and data relay antecedents hold.
- **Byzantine weight and slashing:** `ByzantinePremiseWitness.full_bundle_witness` has positive non-honest weight and a slashing relay that the next call reads.
- **Guarded current-target edge:** `TargetEdgePremiseWitness.target_edge_support_exercised` reaches a selected epoch crossing. A later honest vote has the exact current target.
- **Live monotonicity:** `LiveMonotonicityWitness.joint_witness` satisfies the safety bundle and both live fields. The stored root advances at an epoch boundary.
- **Counterexamples:** `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` and `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` show that an extra in-slot query needs a different safety claim.
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
└─────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────┘
```

No named run exercises non-anchor finalization or positive Gloas empty-slot
discount. The live run gets its FFG timing from the genesis anchor. The
envelope run computes a zero discount and does not select a FULL head. No run
has a PTC event. Validator churn is outside `StaticValidatorSet`. These are
coverage limits, not claims about unreachable protocol states.

## Scope limits

- Validator activity is fixed inside the checked horizon by `StaticValidatorSet`. The proof does not cover registry churn.
- The model imports only validated payloads. An imported payload enters the store only after `verify_execution_payload_envelope` returns true. This external includes the execution engine's `VALID` decision. Execution validation itself is opaque.
- `BeaconExternalsPremises` supplies contracts for external state transitions and validation. The Lean proof does not implement an execution engine.
- `AcceptedBlockAttestationInclusion.Included` is a supplied carrier-vote relation. Its safety evidence gives an accepted carrier block, a received block copy of the vote, slot and target-epoch facts, and committee membership.
- `FFGInterpretationFidelity` states the intended interpretation of the included votes: membership in the accepted carrier block's ordered FFG attestation body, validity on the target checkpoint state prepared from a keyed target block state in an honest in-horizon store, and the external validity check. The safety theorem does not assume it. Each full-bundle witness proves it for its interpretation.
- `ByzantineWeightPremises.span_fraction` must hold for every in-horizon slot span, including one slot. A global fault share does not establish this bound. The bound matches `CommitteeHonestMajority` in the repository's formal paper Assumption 2.
- `LiveMonotonicityPremises.honest_block_each_slot` requires a block with an honest proposer index in every slot from execution start. Its vote-support law and `ffg_timely_justification` require timely descendant votes and exact FFG state outputs at epoch boundaries. These conditions are stronger than paper Assumption 6. Proposer-index membership is not an authentication theorem.
- The result covers stored boundary outputs. `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` and `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` show why an arbitrary in-slot query needs a different statement.

## Paper library

`FastConfirmationPaper/Core/` defines the abstract objects. `FastConfirmationPaper/LMDGhost/` proves the Section 3.1 Theorem 1 safety and monotonicity claims through `confirmed_block_safety` and `confirmed_block_monotonicity`. `FastConfirmationPaper/HFC/` proves the Section 4 Algorithm 1 safety and monotonicity claims through `rule_confirmed_block_safety` and `rule_confirmed_block_monotonicity`. `head_agreement_after_confirmation` is the reusable Lemma 6 style result. `SafeConfirmedAlg1Inputs` requires later rule confirmation for each honest-view-safe block. That input is stronger than paper Assumption 6. No refinement theorem connects the paper and executable models.

## Where to read

Start with the [review guide](docs/REVIEW_GUIDE.md), [architecture](docs/ARCHITECTURE.md),
[modeling choices](docs/MODELING_CHOICES.md), [source map](docs/SPEC_MAP.md), and [paper
map](docs/PAPER_MAP.md). The [conformance guide](docs/conformance.md) covers trace
comparison. The claim and proof sources are `FastConfirmationStatements/Review.lean` and
`FastConfirmationProofs/ReviewTheorem.lean`. The [witness
index](FastConfirmationWitnesses/Index.lean) states each finite run's limit. The repository
uses the MIT [license](LICENSE).

The execution synchrony fields require a positive millisecond timing parameter Δ. The attestation
deadline offset A and slot duration S obey `A + Δ < S`. The delivery laws state the network and handler-service conditions. The FFG and carrier-evidence
premises make required ancestor blocks available to honest heads. Evidence relay is a
premise. The handler follows Python and looks up the justified state. Literal Python can
reject evidence when that state lacks a signer. The premise matches head-state clients. See
[modeling choices](docs/MODELING_CHOICES.md) for the pinned client commits.
`scripts/check_synchrony_corners.py` checks the relay boundary.
