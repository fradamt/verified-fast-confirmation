# Verified Fast Confirmation

The Fast Confirmation Rule (FCR) selects a block root that a node can treat as confirmed from its fork-choice state.

## Proved claims

`review_claims` proves two conditional claims under the records in `FastConfirmationStatements/Review.lean`:

- **Next-slot safety.** An honest node's stored confirmed root stays on every honest head from the following slot through the finite verification horizon.
- **Live monotonicity.** A later stored confirmed root descends from an earlier one when the safety bundle and both live fields hold. The live fields require honest block production, vote support, and timely Casper Friendly Finality Gadget (FFG) justification.

The result concerns stored boundary outputs. It does not cover an arbitrary query within a slot.

## Assumptions at a glance

```text
┌────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Assumption             │ Plain meaning and premise record                                                            │
├────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ Honest operation       │ Honest nodes process scheduled events. They vote by the due time. See                       │
│                        │ Execution.ScheduledPrefixPremises and HonestBehavior.                                       │
│ Timely delivery        │ Needed votes, blocks, payload data, and evidence reach honest nodes before the next         │
│                        │ boundary under positive delay. See NextSlotSynchronyPremises.                               │
│ Stake and committees   │ Validators stay active. Committee estimates hold for every checked slot span. The fault     │
│                        │ bound holds for every checked slot span. See StaticValidatorSet and                         │
│                        │ ByzantineWeightPremises.                                                                    │
│ Beacon and FFG state   │ External transitions match accepted evidence. Supplied checkpoint links match accepted      │
│                        │ evidence. See BeaconExternalsPremises and CausalPrefixFFGInterpretation.                    │
│ Payload validity       │ Imported payloads pass opaque execution validation. See BeaconExternalsPremises and the     │
│                        │ execution external contract.                                                                │
│ Live claim only        │ Each slot has an honest block. Honest votes support it. FFG justification is visible at the │
│                        │ required epoch boundary. See LiveMonotonicityPremises.                                      │
└────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```

The [premise ledger](#premise-ledger) gives the exact records and sources. Evidence relay is supplied as a premise. The fault bound applies to each checked span. The live fields are stronger than paper Assumption 6.

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
and audits 19 public theorem witnesses: 12 executable-side and seven paper-side. The Python
path must name the pinned local checkout.

## Premise ledger

The records in this table are in `FastConfirmationStatements/Premises/`. The last column gives the source of each condition.

```text
┌────────────────────┬────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────┬───────────────────────────────┐
│ Claim              │ Premise record                     │ Fields in plain words                                                            │ Source                        │
├────────────────────┼────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────┼───────────────────────────────┤
│ Safety field       │ Execution.NextSlotSafetyPremises   │ Exact FFG state at every handler-successful prefix; a well formed scheduled run; │ Paper Assumption 3.2; Gloas   │
│                    │                                    │ completed FCR calls; epoch arithmetic; anchor alignment; finalization            │ extension; model idealisation │
│                    │                                    │ delay; more than one slot per epoch; checkpoint and link evidence.               │                               │
│ Safety field       │ Execution.ScheduledPrefixPremises  │ Whole seconds, well formed stores, coherent external calls, honest               │ Model idealisation            │
│                    │                                    │ behavior with an attestation deadline, and a valid genesis store.                │ Phase0/Gloas; model premise   │
│ Safety field       │ Execution.CompletedFCRCallPremises │ Five delivery laws; fixed active validators; committee and Byzantine             │ Paper Assumptions 1 and 2;    │
│                    │                                    │ weight bounds; Phase0 source coherence; a nonzero balance floor;                 │ Gloas extension; model        │
│                    │                                    │ next-slot vote receipt; guarded prediction support.                              │ idealisation                  │
│ Safety field       │ NextSlotSynchronyPremises          │ Positive delay; deadline cutoff for block, envelope, data and evidence           │ Paper synchrony; Gloas        │
│                    │                                    │ relay; pre-tick exclusion; payload service before boundary votes.                │ extension                     │
│ Safety field       │ BeaconExternalsPremises            │ Slot and state transition coherence, committee and attestation                   │ Model idealisation            │
│                    │                                    │ validity, and deterministic envelope verification.                               │                               │
│ Safety field       │ ByzantineWeightPremises            │ Quantized balances, sound committee estimates, and a non-honest weight           │ Paper Assumption 2;           │
│                    │                                    │ fraction bound for every span, including one slot. A global fault                │ executable estimate           │
│                    │                                    │ share does not establish this span bound.                                        │                               │
│ Safety field       │ CausalPrefixFFGInterpretation;     │ Exact handler-successful prefix FFG state, causal links, and projected           │ Paper Assumption 3.2; model   │
│                    │ EpochCheckpointClosure             │ checkpoint roots.                                                                │ idealisation                  │
│ Live field         │ LiveMonotonicityPremises           │ An honest block in each slot from execution start, known by the next             │ Paper Theorem 1 monotonicity  │
│                    │                                    │ slot and supported by honest votes; timely observed FFG justification            │ and Assumption 6,             │
│                    │                                    │ at epoch boundaries.                                                             │ strengthened                  │
└────────────────────┴────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────┴───────────────────────────────┘
```

`Execution.NextSlotSafetyPremises` supplies the common safety premise to the safety field. `LiveConfirmedRootMonotonicity` adds `LiveMonotonicityPremises` to that same execution premise. The FFG and finalization laws can quantify over successful handler prefixes beyond the safety endpoint. The finite conclusion does not shorten those premise ranges.

## Scope limits

- Validator activity is fixed inside the checked horizon by `StaticValidatorSet`. The proof does not cover registry churn.
- The model imports only validated payloads. An imported payload enters the store only after `verify_execution_payload_envelope` returns true. This external includes the execution engine's `VALID` decision. Execution validation itself is opaque.
- `BeaconExternalsPremises` supplies contracts for external state transitions and validation. The Lean proof does not implement an execution engine.
- `CausalCarrierAttestationRelation.Included` is a supplied carrier-vote relation whose evidence checks membership in the accepted carrier block's ordered FFG attestation body.
- Included votes validate on the target checkpoint state prepared from a keyed target block state in an honest in-horizon store. The preparation advances the base state to the target epoch start only when needed. The prepared state need not itself be keyed.
- `ByzantineWeightPremises.span_fraction` must hold for every in-horizon slot span, including one slot. A global fault share does not establish this bound. The bound matches `CommitteeHonestMajority` in the repository's formal paper Assumption 2.
- `LiveMonotonicityPremises.honest_block_each_slot` requires a block with an honest proposer index in every slot from execution start. Its vote-support law and `ffg_timely_justification` require timely descendant votes and exact FFG state outputs at epoch boundaries. These conditions are stronger than paper Assumption 6. Proposer-index membership is not an authentication theorem.
- `LiveMonotonicityWitness.joint_witness` satisfies both live fields and the safety premise in one short run with a strict root advance. Its FFG timing field holds at epoch 0 through the genesis anchor; no vote-driven justification occurs. `FullTwelveWitness.full_bundle_witness` satisfies the full safety premise at 12-second slots with a 2-second delay and real delayed block and vote receipts. Neither next-slot witness has a payload envelope, so envelope relay conditions hold vacuously in both. The selector guard excludes selected current-target accepted edges, so it does not exercise their support premise. See `FastConfirmationWitnesses/Index.lean`.
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

The execution synchrony fields require a positive millisecond delay Δ. The attestation
deadline offset A and slot duration S obey `A + Δ < S`. The FFG and carrier-evidence
premises make required ancestor blocks available to honest heads. Evidence relay is a
premise. The handler follows Python and looks up the justified state. Literal Python can
reject evidence when that state lacks a signer. The premise matches head-state clients. See
[modeling choices](docs/MODELING_CHOICES.md) for the pinned client commits.
`scripts/check_synchrony_corners.py` checks the relay boundary.