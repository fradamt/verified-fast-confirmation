# Verified Fast Confirmation

[![CI](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml)

The Fast Confirmation Rule (FCR) selects a block root from fork-choice state. Under the stated premises, the Lean theorem proves that every honest observer stores that root and keeps it on its head from the next slot until the finite horizon. The fixed-committee premises force every slot committee to weigh exactly total_active / SLOTS_PER_EPOCH; ordinary 100-validator genesis and mainnet-like registries do not meet this condition. The theorem covers genesis-anchored runs in which epoch 1 is not finalized. In Python, honest votes finalize epoch 1 only through a 1 -> 3 link; this occurs when epoch-2 justification needs votes included in epoch 3. The horizon is an absolute epoch limit (`Execution.verification_horizon`). The proof uses a supplied FFG interpretation; the Python checks do not establish the full premise bundle.

- **Stored boundary output:** The confirmed root saved after a scheduled slot-boundary call.
- **Handler-successful prefix:** The state after a scheduled event whose handler returns successfully.
- **Carrier:** An accepted block that contains evidence for a checkpoint or vote.
- **AU:** An available or unrealized checkpoint with evidence on an accepted block's ancestry.
- **PJF:** `process_justification_and_finalization`. An eager PJF call reads a copy of a state before normal epoch processing. A slot-processed read runs `process_slots` first.
- **Keyed state:** The beacon state stored under a block root. An honest in-horizon prefix is the result of accepted scheduled events at an honest node before the absolute epoch limit.
- **Full bundle:** One witness of every field of `NextSlotSafetyPremises`. An exercised field has a true guard or a nonzero event in that run.
- **GST-0:** The delivery laws hold from the start of this execution.
- **Checked span:** An in-horizon slot interval used by the stake bound.
- **Joint witness:** A proof of several records for one run.
- **One-boundary law:** A law that crosses one epoch end.

Read the claim in `FastConfirmationStatements/Review.lean` and its premise bundle in `FastConfirmationStatements/Premises/NextSlotSafety.lean`.
Read `docs/REVIEW_GUIDE.md` for the audit path and `docs/MODELING_CHOICES.md` for the scope.
Run `scripts/validate.sh` with the pinned Python checkout, then inspect `FastConfirmationWitnesses/Index.lean` for finite examples.

## Proved claims

`review_claims` proves the next-slot safety claim under the records in `FastConfirmationStatements/Premises/`:

- **Next-slot safety.** From the following slot through the finite verification horizon, every honest observer has the stored confirmed root in its block store. The executable ancestor walk also shows that the root stays on the observer's head.

[Former live theorem history](docs/history/live-monotonicity-removed.md).

The result concerns stored boundary outputs. It does not cover an arbitrary query within a slot.

The proof takes an FFG interpretation as a premise: `AcceptedBlockFFGState`
with an inclusion relation and checkpoint selectors. It must agree with every
checkpoint read of successful handlers through `FFGStateAndCheckpointReadAgreement`
and satisfy eventual checkpoint inclusion (paper Assumption 3.2 style), link and
checkpoint agreement, checkpoint projection laws, and finalization lag. The
inclusion relation need not equal block-body membership. The theorem holds for
every relation with these laws. The intended relation selects included attestations whose target matches the
checkpoint. Python `process_attestation` does not check the target root.
`FFGInterpretationFidelity` states body membership and valid-vote facts, and
every full-bundle witness proves them for its supplied relation. The projection harness checks sampled interpretation fields on pinned pyspec runs. It marks `EventualCheckpointInclusion.included` (A3.2) as NOT_ESTABLISHED: its every-view antecedent and full implication are not tested. A concrete FFG state
and 34 Gloas functions exist in `FastConfirmationModel`; 59 differential cases
agreed with Python. The theorem does not yet use this concrete model. A client
still must supply the interpretation and show its laws.

A3.2 requires an epoch-1 attestation to appear in a block of epoch 2 or later.
The Python FCR regression in `scripts/conformance/contracts/test_realized_gap.py`
loses a confirmed block when epoch-1 evidence is included during the genesis
epochs. Finality evidence has a two-epoch lag (`k = 2`). The source law covers
two or more epoch boundaries, and `epoch_one_finalization_one_step` is the
`F = 1` scope field.

The [review guide](docs/REVIEW_GUIDE.md) explains anchor states, checkpoint reads, and the five boundary-source laws. It also lists the guards that the pinned Python probes check.

`GenesisStubPremiseWitness.genesis_stub_full_bundle_witness` satisfies the full safety bundle with a real genesis stub. It shows consistency of the bundle; it is not a Python-faithful execution. The contract suite, projection harness, and differential test check Python behavior. Witness PJF returns early in epochs 0 and 1, as Python does. See [anchor and boundary limits](docs/MODELING_CHOICES.md#anchor-and-boundary-limits).

## Assumptions at a glance

```text
┌──────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Assumption           │ Plain meaning and premise record                                                                 │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Honest actions       │ Scheduled events and head votes. `HonestBehavior.votes_head` fixes each honest committee vote.   │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ No forgery           │ `HonestBehavior.no_forgery` covers scheduled votes that name an honest validator.                │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ No slashing          │ `HonestBehavior.not_slashable` makes honest votes pairwise non-slashable.                        │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Root labels          │ `WellFormedExecution.blocks_root_injective` identifies blocks with equal root labels.            │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Timing               │ `NextSlotSynchronyPremises` requires receipt and handler service by the next boundary.           │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Registry             │ `registry_static_in_horizon` fixes the anchor registry in keyed states and slot-processed reads. │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Balance floor        │ `balance_floor` requires two increments of anchor active weight.                                 │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Anchor               │ `anchor_state_checkpoints` covers genesis with a stub or a state with both checkpoints equal to  │
│                      │ the anchor.                                                                                      │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ FFG inclusion        │ A3.2 needs epoch-1 evidence in a block of epoch 2 or later.                                      │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ FFG state            │ `ScheduledFFGInterpretation` supplies accepted-block state, links, and checkpoint reads.         │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Epoch-1 finality     │ `epoch_one_finalization_one_step` excludes genesis runs that finalize epoch 1 through 1 -> 3.  │
│                      │ Python takes that path when epoch-2 justification needs votes included in epoch 3.             │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Phase0 source        │ `Phase0SourceCoherence` and `Phase0BoundarySourceCoherence` constrain source reads.              │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Committee            │ `on_attestation_committee` covers successful delivered attestations. Slashing evidence can be    │
│                      │ off-committee.                                                                                   │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Committee model      │ Idealization. `committees_agree` and `on_attestation_committee` use one fixed ground-truth       │
│                      │ assignment `E.committee`. RANDAO-seeded, fork-dependent committees of the real protocol are not  │
│                      │ modeled.                                                                                         │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Equal slot weight    │ `estimate_sound` plus coverage forces each slot committee to weigh exactly `total_active / S`.   │
│                      │ Ordinary 100-validator genesis and mainnet-like balances do not satisfy this idealization.       │
├──────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Payload validity     │ `BeaconExternalsPremises` and the external contract govern imported payloads.                    │
└──────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────────┘
```

Prediction support is derived by joint induction over calls and endpoint slots.
Current-epoch crossings use exact targets. Previous-epoch results use descendant
targets. The proof needs only votes before each endpoint. Historical certificates
and quorums are produced on demand after the target epoch, with the original call,
target, source, and deadline. See `Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold`.
The [premise ledger](#premise-ledger) gives the remaining records and sources.
Evidence relay is a premise. The fault bound applies to each checked span.
The slashing relay is an operational premise. With the static registry and one fork, the claimed missing-signer rejection cannot occur in scope; the registry and domain are common. Handler service is still an assumption.
The per-span fault bound and estimate soundness are deterministic conditions on every checked span, including one slot. Their combination with coverage forces equal slot weights. Block-store membership depends closely on `DeadlineBlockRelay` store retention; the proof rules out its permanent-exclusion branch and establishes head ancestry. A global fault share does not imply
them. This development does not calculate their probability under committee
sampling.
The positive `delta` value is a timing parameter. The delivery laws in
`NextSlotSynchronyPremises` supply the network assumption. The proof does not
derive handler service or delivery from `delta` alone.
The attestation deadline offset A, the positive delay Δ, and the slot duration S
obey `A + Δ < S`. This bound puts a vote sent by the deadline before the next
slot. The delivery laws also require receipt and handler service. `DeadlineBlockRelay` requires a client to gossip each cutoff block, receive it at every honest node, accept it with known parents, and keep it by the next boundary unless the pre-boundary finalized guard rejects it permanently. The boundary prefix law requires block service before a boundary vote. Envelope, data, and slashing relay fields require receipt, handler service, and the stated validation behavior.

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
A pinned Python run with 100 validators, mixed balances, normal participation, and 48 imported blocks checks 71 finite premise fields. `ByzantineWeightPremises.estimate_sound` fails on 211 spans; A3.2 remains NOT_ESTABLISHED. The run has one view and no Byzantine validators, so it does not establish network delivery or a nonvacuous fault bound.

The [contract conformance checks](docs/conformance.md#contract-conformance) cover 160
claim-reachable premise fields, split into tested state laws (T), execution scope (E-scope), network and behavior (E-network/behavior), supplied FFG interpretation (E-interpretation), and idealizations (I). Run `python3
scripts/conformance/contracts/check_inventory.py --repo
/path/to/consensus-specs-pending-discount --output /tmp/contract-results.json` with the
pinned checkout's interpreter. Three labelled expected failures show why the balance
guard is necessary, why the two-boundary law starts in epoch 2, and why an older
raw checkpoint-sync state is outside `anchor_state_checkpoints`. These findings
do not stop validation.

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
and audits 44 public theorems: 37 executable-side and seven paper-side. The Python
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
└──────────────┴──────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────┴───────────────────────────────┘
```

`Execution.NextSlotSafetyPremises` supplies the safety premise to the review claim. The FFG and finalization laws can quantify over successful handler prefixes beyond the safety endpoint. The finite conclusion does not shorten those premise ranges.

## Witnesses

Each positive run proves its stated premise bundle. An exercised field has a
concrete source event, positive quantity, or true guard in that run. A proof of
the full bundle does not imply that every branch occurs.

- **Full safety at 1 s and 12 s:** `NextSlotPremiseWitness.finite_execution_satisfies_premises` and `FullTwelveWitness.full_bundle_witness` give stored root advances under the full safety bundle. The 12 s run has real delayed block and vote receipts.
- **Payload envelope:** `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope. Its delivery and data relay antecedents hold.
- **Byzantine weight and slashing:** `ByzantinePremiseWitness.full_bundle_witness` has positive non-honest weight and a slashing relay that the next call reads.
- **Guarded current-target edge:** `TargetEdgePremiseWitness.target_edge_support_exercised` reaches a selected epoch crossing. A later honest vote has the exact current target.
- **Counterexamples:** `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` and `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` refute same-second head agreement at a mid-second prefix under the counterexample synchrony record. Next-slot safety for an in-slot query is open.
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
│                     │ NextSlotSynchronyPremises.attester_slashing_relay.                                                │
│ Current-target edge │ Selected current-target crossing guard and exact later target vote are derived facts.             │
│ Counterexamples     │ —                                                                                                 │
│ Fidelity records    │ FFGInterpretationFidelity body membership, validation state, and external validity check.         │
│ Non-anchor finality │ not exercised by a named full-bundle run.                                                         │
│ Previous result     │ not exercised: the previous-result proviso branch is not exercised by a full-bundle witness.      │
│ Positive discount   │ not exercised: the Gloas empty-slot discount is zero in the envelope run.                         │
│ PTC events          │ not exercised by a named full-bundle run.                                                         │
│ Positive boost      │ not exercised: all full-bundle runs set proposer boost to zero.                                   │
└─────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────┘
```

No named run exercises non-anchor finalization or positive Gloas empty-slot
discount. The
envelope run computes a zero discount and does not select a FULL head. No run
has a PTC event. Every positive run sets `proposer_score_boost` to zero. The
proposer-score term and should_apply_proposer_boost are not exercised
positively. The one-second runs set `attestation_due_bps` to zero. The main
safety runs have four or five validators and one validator per slot committee.
Validator churn is outside
`StaticValidatorSet`. These are
coverage limits, not claims about unreachable protocol states.

## Scope limits

- `BeaconExternalsPremises.registry_static_in_horizon` fixes keyed states and slot-processed reads to the anchor registry. Included slashings, deposits, activations, exits, or effective-balance changes can break it. On mainnet this can limit a horizon to about one epoch. The pending-deposit probe shows an excluded registry change.
- The model imports only validated payloads. An imported payload enters the store only after `verify_execution_payload_envelope` returns true. This external includes the execution engine's `VALID` decision. Execution validation itself is opaque.
- `BeaconExternalsPremises` supplies contracts for external state transitions and validation. `on_attestation_committee` constrains successful delivered attestations. Indexed attester-slashing evidence can have off-committee signers; its handler only updates the equivocating set. The Lean proof does not implement an execution engine.
- `AcceptedBlockAttestationInclusion.Included` is a supplied carrier-vote relation. Its safety evidence gives an accepted carrier block, a received block copy of the vote, slot and target-epoch facts, and committee membership.
- `FFGInterpretationFidelity` states the intended interpretation of the included votes: membership in the accepted carrier block's ordered FFG attestation body, validity on the target checkpoint state prepared from a keyed target block state in an honest in-horizon store, and the external validity check. The safety theorem does not assume it. Each full-bundle witness proves it for its interpretation.
- `EstimateForcesBalance.slot_committee_weight_forced` proves that exact `estimate_sound` plus committee coverage forces equal per-slot weight in each full in-horizon epoch. Whether Python FCR thresholds tolerate committee-weight rounding remains open.
- `AcceptedBlockFFGState.epoch_one_finalization_one_step` excludes honest genesis runs with epoch-1 finality through 1 -> 3. Extending the proof to that path remains open.
- `ByzantineWeightPremises.span_fraction` must hold for every in-horizon slot span, including one slot. A global fault share does not establish this bound. The bound matches `CommitteeHonestMajority` in the repository's formal paper Assumption 2.
- The result covers stored boundary outputs. The two extra-query counterexamples refute same-second head agreement at a mid-second prefix under the counterexample synchrony record. Next-slot safety of an in-slot query is open.

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
