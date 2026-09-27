# Verified Fast Confirmation

Paper citations use [arXiv:2405.00549v4](https://arxiv.org/abs/2405.00549v4).

[![CI](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml)

The Fast Confirmation Rule (FCR) selects a block root from fork-choice state. Under the stated premises, the Lean theorem proves that every honest observer stores that root and keeps it on its head from the next slot until the finite horizon. The substantive part of the result is head ancestry. Store membership follows mostly from the block-relay and retention input `DeadlineBlockRelay` (`NextSlotSynchronyPremises.deadline_block_relay`). Committee sampling is idealized (`ByzantineWeightPremises.estimate_sound`, class I): slot committees have equal weight inside an epoch, and the reshuffle at an epoch boundary is perfectly mixed. The premise also keeps paper Assumption 3.2 (explicit), eventual checkpoint inclusion. The theorem covers genesis-anchored runs in which no accepted block state finalizes epoch 1. The premise field admits epoch-1 finality only through a 1 -> 2 finalization link, and included votes cannot form that link: a vote with target epoch 2 must have a source of epoch 0 (`ConcreteBridge.epochOneFinalizationScope_finalized_ne_one`). In Python, honest votes finalize epoch 1 only through a 1 -> 3 link; this occurs when epoch-2 justification needs votes included in epoch 3. The horizon is an absolute epoch limit (`Execution.verification_horizon`). The premise fixes a concrete bridge: a concrete Gloas FFG transition, state and block commitments, and an opaque block-validity oracle. The proof computes its FFG interpretation from that bridge. The Python checks do not establish the full premise bundle.

- **Stored boundary output:** The confirmed root saved after a scheduled slot-boundary call.
- **Handler-successful prefix:** The state after a scheduled event whose handler returns successfully.
- **Carrier:** An accepted block that contains evidence for a checkpoint or vote.
- **AU:** An available or unrealized checkpoint with evidence on an accepted block's ancestry.
- **PJF:** `process_justification_and_finalization`. An eager PJF call reads a copy of a state before normal epoch processing. A slot-processed read runs `process_slots` first.
- **Keyed state:** The beacon state stored under a block root. An honest in-horizon prefix is the result of accepted scheduled events at an honest node before the absolute epoch limit.
- **Full bundle:** One witness of every field of `ConcreteBridge.SafetyPremises`. An exercised field has a true guard or a nonzero event in that run.
- **GST-0:** The delivery laws hold from the start of this execution.
- **Checked span:** An in-horizon slot interval used by the stake bound.
- **Joint witness:** A proof of several records for one run.
- **One-boundary law:** A law that crosses one epoch end.

Read the claim in `FastConfirmationStatements/Review.lean` and its premise record in `FastConfirmationStatements/Premises/ConcreteSafety.lean`.
Read `docs/REVIEW_GUIDE.md` for the audit path and `docs/MODELING_CHOICES.md` for the scope.
Run `scripts/validate.sh` with the pinned Python checkout, then inspect `FastConfirmationWitnesses/Index.lean` for finite examples.

## Proved claims

`review_claims` proves the next-slot safety claim under the records in `FastConfirmationStatements/Premises/`:

- **Next-slot safety.** From the following slot through the finite verification horizon, every honest observer has the stored confirmed root in its block store. The executable ancestor walk also shows that the root stays on the observer's head.

The substantive part is head ancestry. Store membership follows mostly from one input: `DeadlineBlockRelay` (`NextSlotSynchronyPremises.deadline_block_relay`) requires every root that an honest node stores by the attestation deadline to be in every honest store from the next slot, unless a permanent finalized-conflict exclusion applies.

[Former live theorem history](docs/history/live-monotonicity-removed.md).

The result concerns stored boundary outputs. It does not cover an arbitrary query within a slot.

The premise `ConcreteBridge.SafetyPremises` fixes a concrete bridge. The
bridge runs the concrete Gloas FFG transition of `FastConfirmationModel` for
`process_slots`, `state_transition`, and PJF. An opaque block-validity oracle
(class I) stands for BLS, hash roots, proposer selection, and the operations
that the projection erases; the theorem holds for every oracle. The proof
computes the FFG interpretation from the bridge
(`SafetyPremises.nextSlotSafetyPremises`). It has two inclusion relations.
`TargetIncludedAt` feeds the FFG certificates: it counts the body votes of
accepted blocks that set the timely-target flag. `BodyIncludedAt` is the
slashing evidence D_b of the A3.2 view: it counts every body vote of an
accepted block, with or without that flag. Python
`process_attestation` does not check the target root, so a vote with a wrong
target root does not count. The premise keeps eventual checkpoint inclusion
(paper Assumption 3.2 (explicit)) over the view of the bridge. Its consequent: from the start of epoch e + 2, every honest view in the horizon stores the base block b and an accepted descendant of b, from an epoch below e + 2 (and above epoch 1 unless e = 0), that carries the checkpoint C(b, e) as an available or unrealized checkpoint. The projection harness checks the
interpretation laws on pinned pyspec runs. It marks `EventualCheckpointInclusion.included` (paper Assumption 3.2 (explicit)) as NOT_ESTABLISHED: its every-view antecedent and full implication are not tested. The concrete
transition agreed with Python in 59 differential cases and on the retained
fields of 48 accepted blocks of a 100-validator run.

Paper Assumption 3.2 (explicit) requires an epoch-1 attestation to appear in a block of epoch 2 or later.
The Python FCR regression in `scripts/conformance/contracts/test_realized_gap.py`
loses a confirmed block when epoch-1 evidence is included during the genesis
epochs. Finality evidence has a two-epoch lag (`k = 2`). The source law covers
two or more epoch boundaries, and `epoch_one_finalization_scope` is the
`F = 1` scope field.

The [review guide](docs/REVIEW_GUIDE.md) explains anchor states, checkpoint reads, and the five boundary-source laws. It also lists the guards that the pinned Python probes check.

`GenesisStubPremiseWitness.genesis_stub_full_bundle_witness` satisfies the full safety bundle with a real genesis stub: its stub root is not the anchor root, as in Python. It shows consistency of the bundle; it is not a Python-faithful execution. Four full-bundle families (next-slot, twelve-second, envelope, and GenesisStub) have four validators of 100 Gwei and the same committee schedule in each epoch. They meet part (ii) of the committee-sampling idealization only through the rounding of `adjust_committee_weight_estimate_to_ensure_safety`: it rounds up to 1000-Gwei units and multiplies by 1.005, so every estimate is at least 1005 Gwei, more than their total stake of 400 Gwei. The target-edge and Byzantine families have 4000 Gwei of stake and prove the field by finite evaluation at that scale. A witness at realistic scale with a mixed committee schedule is deferred. It uses one-second slots, four validators and four slots per epoch, zero attestation due time and proposer boost, an oracle that accepts every block, a base signature check that accepts exactly the ground votes, and the genesis payload fields below. The other five full-bundle families set `zeroRoot := anchorRoot`, which Python cannot do because ZERO_HASH is not the genesis root; with it, the genesis stub reads as the anchor checkpoint in honest votes. `ConcreteJustificationWitness.concrete_certificate_extraction` and `ConcreteFinalityWitness.k2_certificate_extraction` come from concrete FFG fixtures outside the bundle; they show non-anchor justification and finality with two-epoch and adjacent links. The contract suite, projection harness, and differential test check Python behavior. Witness PJF returns early in epochs 0 and 1, as Python does. See [anchor and boundary limits](docs/MODELING_CHOICES.md#anchor-and-boundary-limits).

## Assumptions at a glance

The premise `ConcreteBridge.SafetyPremises` has 14 fields. The class is the
inventory class: E-scope limits the execution, E-network/behavior states
delivery or behavior, E-interpretation states external contracts, and I marks
an idealization.

```text
┌──────────────────────────────┬─────────────────────┬──────────────────────────────────────────────────────────────────────────────┐
│ SafetyPremises field         │ Class               │ Plain meaning                                                                │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ admissible                   │ E-scope             │ The fixed setup starts at genesis, has two increments of active weight, lets │
│                              │                     │ the root ring cover two epochs, fits uint64 root reads, and has a uint64     │
│                              │                     │ genesis time.                                                                │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ genesis                      │ E-scope + I         │ The run starts from the genesis store of the setup; the state commitment     │
│                              │                     │ opens the genesis state root. The genesis state differs from Python only in  │
│                              │                     │ payload availability and the latest block hash (see below).                  │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ horizon_scope                │ E-scope             │ The verification horizon is the epoch after the last epoch of the fixed      │
│                              │                     │ scope.                                                                       │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ whole_seconds                │ E-scope             │ The slot duration is a whole number of seconds.                              │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ wellFormed                   │ E-interpretation    │ Block root labels are injective (class I root labels), and the anchor parent │
│                              │                     │ is unscheduled.                                                              │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ externals_coherence          │ E-interpretation    │ ConcreteExternalsPremises: committee, signature, and envelope contracts that │
│                              │                     │ the bridge does not prove. Committees are one fixed ground-truth assignment  │
│                              │                     │ (class I); RANDAO-seeded, fork-dependent committees are not modeled.         │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ honest_behavior              │ E-network/behavior  │ Honest committee members vote for their head by the deadline, sign no        │
│                              │                     │ slashable pair, and are not forged.                                          │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ body_attestations_delivered  │ E-network/behavior  │ Each attestation in an accepted block body reaches some node as a block      │
│                              │                     │ attestation.                                                                 │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ synchrony                    │ E-network/behavior  │ GST-0 delivery and handler service by the next boundary for votes, blocks,   │
│                              │                     │ envelopes, data, and slashing evidence. DeadlineBlockRelay puts every root   │
│                              │                     │ stored by the deadline into every honest store from the next slot; it gives  │
│                              │                     │ most of the store-membership part of the claim.                              │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ byzantine_bound              │ E-network/behavior  │ Quantized balances, sound committee estimates, and a fault bound on every    │
│                              │                     │ slot span. estimate_sound (class I) takes the high-probability committee     │
│                              │                     │ weight estimate of the specification as exact: (i) equal slot-committee      │
│                              │                     │ weights inside an epoch; (ii) a perfectly mixed reshuffle across an epoch    │
│                              │                     │ boundary. Sampling statistics are out of scope.                              │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ epoch_ends_fit               │ E-scope             │ The horizon fits the uint64 slot range.                                      │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ slots_per_epoch_gt_one       │ E-scope             │ An epoch has more than one slot.                                             │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ epoch_one_finalization_scope │ E-scope             │ No accepted block state finalizes epoch 1. The field admits epoch-1 finality │
│                              │                     │ only through a 1 -> 2 link, and included votes cannot form it. Python can    │
│                              │                     │ finalize epoch 1 only when epoch-2 justification needs votes included in     │
│                              │                     │ epoch 3.                                                                     │
├──────────────────────────────┼─────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ checkpoint_inclusion         │ E-network/behavior  │ Paper Assumption 3.2 (explicit) over the view of the bridge. If b is         │
│                              │                     │ canonical and has two-thirds link support in every honest view throughout    │
│                              │                     │ epoch e + 1, then from epoch e + 2 every honest view stores b and a          │
│                              │                     │ descendant of b that carries C(b, e) as an available or unrealized           │
│                              │                     │ checkpoint.                                                                  │
└──────────────────────────────┴─────────────────────┴──────────────────────────────────────────────────────────────────────────────┘
```

Proved from the bridge, not assumed: the FFG interpretation
(`ScheduledFFGInterpretation`, with its inclusion relation and checkpoint
reads), the anchor conditions (`anchor_state_checkpoints`, `anchor_eq`,
`anchor_boundary`), the Phase0 source laws (`Phase0SourceCoherence`,
`Phase0BoundarySourceCoherence`), the balance floor, the finalization lag, the
checkpoint projection, the link agreement, eight of the 17 contracts of the
internal record `BeaconExternalsPremises` (slot and checkpoint-epoch laws,
anchor checkpoint epochs, default-state rejection, and the static registry),
and the static validator set (`StaticValidatorSet`: the genesis epoch is in
the horizon, and active status is fixed). `SafetyPremises.nextSlotSafetyPremises`
computes them; `FastConfirmationProofs/FFG/Concrete/ExternalsLaws.lean` holds
the external and static-set proofs. The block-validity oracle of the bridge is opaque (class I): the
theorem holds for every oracle, and no oracle can accept a block outside the
fixed scope.

Applicability: the transition rejects blocks with slashings, voluntary exits,
or parent execution requests, and a Python run is in scope only if no epoch
step in the horizon changes a validator record. See [scope limits](#scope-limits).

The genesis state of the setup sets every payload-availability bit to false and
the latest block hash to the zero root. Python genesis sets every bit to true
and the hash to the genesis payload hash. These fields affect only the
timely-head flag and the parent-payload branch of a genesis child. The
timely-target flag, the FFG selectors, and the fork-choice read state do not
read them.

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
The bridge runs the concrete Gloas FFG transition for slot processing, block
transitions, and PJF. Cryptography, the other block-validity checks, payload
envelopes, data availability, and execution validation are opaque, with stated
contracts. Committees are one fixed assignment (class I). The Lean kernel checks the proofs. The trust audit
allows only `propext`, `Classical.choice`, and `Quot.sound`. The former paper library is recorded in its [history note](docs/history/paper-side-removed.md).
A pinned Python run with 100 validators, mixed balances, normal participation, and 48 imported blocks checks 76 finite fields: 10 public premise fields, 64 laws of the derived internal records, and two checks of the concrete transition (the retained fields of each block, and a negative control for an epoch-step registry change). `ByzantineWeightPremises.estimate_sound` fails on 211 of 1176 spans: 96 of 216 within-epoch spans (first at slots 0 to 1: 846e9 Gwei against an estimate of 837.5e9 Gwei) and 115 of 960 cross-boundary spans. A second genesis with 128 validators of 32 ETH checks only `estimate_sound`, in two more fields: 0 of 216 within-epoch spans fail, so a real pyspec registry meets part (i), and 120 of 960 cross-boundary spans fail (for example slots 1 to 14: 4096e9 Gwei against 4052.16e9 Gwei), because the real reshuffle is one sample. These failures are the expected result of the committee-sampling idealization. Paper Assumption 3.2 (explicit) remains NOT_ESTABLISHED. The run has one view and no Byzantine validators, so it does not establish network delivery or a nonvacuous fault bound.

The [contract conformance checks](docs/conformance.md#contract-conformance) cover
62 claim-reachable fields. Seventeen are definitions, not assumptions: the seven fields of the A3.2 view, which the bridge fixes (its modeling choices are the fixed committee schedule, AU from the four carried selectors, and the genesis-epoch read as the anchor), and the ten parts of the A3.2 antecedent. Seven are records whose own fields are listed. The other 38 fields are the assumed leaves: tested state laws (T) 4, execution scope (E-scope) 7, network and behavior (E-network/behavior) 16, and idealizations (I) 15; four leaves have two labels, and no leaf is E-interpretation. Paper Assumption 3.2 (explicit) (`EventualCheckpointInclusion.included`) is E-network/behavior: the bridge fixes its view, so it states only that proposers include the supporting votes and that the network delivers a carrier block. Run `python3
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
and audits 39 public executable theorems. The Python
path must name the pinned local checkout.

## Premise ledger

The records in this table are in `FastConfirmationStatements/Premises/`, except the derived internal record. The last column gives the source of each condition.

```text
┌──────────────┬──────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────┬───────────────────────────────┐
│ Claim        │ Premise record                       │ Fields in plain words                                                            │ Source                        │
├──────────────┼──────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────┼───────────────────────────────┤
│ Premise      │ ConcreteBridge.SafetyPremises        │ An admissible bridge; the concrete genesis store; a horizon tied to the          │ Paper Assumption 3.2          │
│              │                                      │ fixed scope; whole seconds; a well formed scheduled run; delivered body          │ (explicit); Gloas extension;  │
│              │                                      │ attestations; the epoch-1 finalization scope; checkpoint inclusion.              │ model idealization            │
│ Safety field │ ConcreteExternalsPremises            │ Committee agreement, coverage and activity, the signature laws, slot-processing  │ Model idealization            │
│              │                                      │ validity, and deterministic envelope verification. The bridge proves the other   │                               │
│              │                                      │ contracts and the static validator set.                                          │                               │
│ Safety field │ HonestBehavior                       │ Honest head votes by the assigned committee, a vote deadline, no forgery,        │ Paper; model premise          │
│              │                                      │ no slashable honest vote pair, and unslashed honest validators.                  │                               │
│ Safety field │ NextSlotSynchronyPremises            │ Positive delay parameter; delivery and handler-service laws for blocks,          │ Paper synchrony; Gloas        │
│              │                                      │ envelopes, data and evidence; pre-tick exclusion before boundary votes.          │ extension                     │
│ Safety field │ ByzantineWeightPremises              │ Quantized balances, sound committee estimates, and a non-honest weight           │ Paper Assumption 2;           │
│              │                                      │ fraction bound for every span, including one slot. A global fault                │ executable estimate           │
│              │                                      │ share does not establish this span bound.                                        │                               │
│ Safety field │ EventualCheckpointInclusion          │ Paper Assumption 3.2 (explicit) over the view of the bridge: carried             │ Paper Assumption 3.2          │
│              │                                      │ checkpoints and body votes of accepted blocks.                                   │ (explicit)                    │
│ Derived      │ Execution.NextSlotSafetyPremises     │ Internal record. The translation proves its FFG interpretation, Phase0           │ Lean proof                    │
│              │                                      │ source laws, balance floor, and anchor facts from the bridge premise.            │                               │
└──────────────┴──────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────┴───────────────────────────────┘
```

`ConcreteBridge.SafetyPremises` is the premise of the review claim. The proof uses the internal record `Execution.NextSlotSafetyPremises` that `SafetyPremises.nextSlotSafetyPremises` computes; its FFG and finalization laws are proved, not assumed.

## Witnesses

Each positive run proves its stated premise bundle. An exercised field has a
concrete source event, positive quantity, or true guard in that run. A proof of
the full bundle does not imply that every branch occurs.

- **Full safety at 1 s and 12 s:** `NextSlotPremiseWitness.finite_execution_satisfies_premises` and `FullTwelveWitness.full_bundle_witness` give stored root advances under the full safety bundle. The 12 s run has real delayed block and vote receipts.
- **Payload envelope:** `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope. Each node receives it once, before the next boundary, and keeps the payload. Its delivery, boundary-prefix, and data relay antecedents hold.
- **Byzantine weight and slashing:** `ByzantinePremiseWitness.full_bundle_witness` has positive non-honest weight and a slashing relay that the next call reads.
- **Previous-result proviso:** `ByzantinePremiseWitness.previous_result_proviso_exercised` selects an epoch-2 block at a non-start slot of epoch 3. `ByzantinePremiseWitness.previous_result_descendant_support_exercised` shows its descendant target support.
- **Guarded current-target edge:** `TargetEdgePremiseWitness.target_edge_support_exercised` reaches a selected epoch crossing. A later honest vote has the exact current target.
- **Counterexamples:** `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` and `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` refute same-second head agreement at a mid-second prefix under the counterexample synchrony record. Next-slot safety for an in-slot query is open.
- **Interpretation fidelity:** Full-bundle runs prove `FFGInterpretationFidelity` for the canonical included-vote relation of their bridge. This record is outside the safety premise.

The table names fields with a concrete instance or true antecedent and labels
the gaps that no named full-bundle run exercises. A dash means that the row is
a counterexample and does not assert the safety bundle.

```text
┌─────────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Run                 │ Exercised premise fields or facts                                                                 │
├─────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────┤
│ 1 s full safety     │ HonestBehavior.votes_head; SafetyPremises.checkpoint_inclusion; root advance.                     │
│ 12 s full safety    │ NextSlotSynchronyPremises.attestation_delivery and deadline_block_relay; delayed receipts.        │
│ 12 s envelope       │ NextSlotSynchronyPremises.envelope_delivery, boundary_envelope_prefix, and                        │
│                     │ data_availability_relay; one early receipt per node; accepted payload.                            │
│ Byzantine run       │ ByzantineWeightPremises.span_fraction with positive fault weight;                                 │
│                     │ NextSlotSynchronyPremises.attester_slashing_relay.                                                │
│ Current-target edge │ Selected current-target crossing guard and exact later target vote are derived facts.             │
│ Counterexamples     │ —                                                                                                 │
│ Fidelity records    │ FFGInterpretationFidelity body membership, validation state, and external validity check.         │
│ Non-anchor finality │ not exercised by a named full-bundle run.                                                         │
│ Previous result     │ Byzantine run: selected previous-epoch result at a non-start slot;                                │
│                     │ its descendant target support.                                                                    │
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
safety runs have four or five validators. Each slot committee has one
validator, except in the Byzantine run, where validator 4 joins the
committees of validator 3.
Validator churn is outside the fixed scope. These are
coverage limits, not claims about unreachable protocol states.

## Scope limits

- Registry scope. The concrete transition keeps every validator record fixed. It rejects a block with a proposer or attester slashing, a voluntary exit, or a parent execution request (`FFGWireBlock.InFixedScope`, error `scope`); a body deposit fails the Python guard. An epoch step can still change a record in Python: an effective-balance update, an activation, an ejection, or a pending deposit. The model has no balances and cannot detect these steps, so a Python run is in scope only if no epoch step in the horizon changes a validator record. The whole-bundle sample checks this condition on its run, and a negative control shows that the check detects an effective-balance change. Under the bridge, `registry_static_in_horizon` is a theorem (`ConcreteBridge.registry_static_in_horizon`): the concrete functions write no validator record. It is a fact of the model, so it does not by itself exclude a Python registry change; the epoch-step condition does. On mainnet this can limit a horizon to about one epoch. The pending-deposit probe shows an excluded registry change.
- The model imports only validated payloads. An imported payload enters the store only after `verify_execution_payload_envelope` returns true. This external includes the execution engine's `VALID` decision. Execution validation itself is opaque.
- `BeaconExternalsPremises` supplies contracts for external state transitions and validation. `on_attestation_committee` constrains successful delivered attestations. Indexed attester-slashing evidence can have off-committee signers; its handler only updates the equivocating set. The Lean proof does not implement an execution engine.
- The concrete block-validity oracle is opaque (class I). Agreement with Python needs an oracle that accepts the blocks that Python accepts. `ConcreteBridge.StateRootsCommit` (class I, collision resistance on the states of one run) makes the bridge accept each such in-scope block; the safety theorem does not need it.
- `AcceptedBlockAttestationInclusion.Included` is the canonical carrier-vote relation of the bridge. An included aggregate stands for one single-validator vote of each signer with the same data. Its safety evidence gives an accepted carrier block, a received block copy of the vote, slot and target-epoch facts, and committee membership.
- `FFGInterpretationFidelity` states the intended interpretation of the included votes: membership in the accepted carrier block's ordered FFG attestation body, validity on the target checkpoint state prepared from a keyed target block state in an honest in-horizon store, and the external validity check. The safety theorem does not assume it. Each full-bundle witness proves it for its interpretation.
- Committee sampling is idealized. `estimate_sound` takes the committee-weight estimate of the specification as exact; the specification claims it only with high probability (COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR and the gist that the specification cites). The idealization has two parts, and both are intended: (i) equal slot-committee weights inside an epoch; (ii) a perfectly mixed reshuffle across an epoch boundary, so the committee weight of a cross-boundary span is at most the pro-rated estimate of the specification, which is the expected overlap. `EstimateForcesBalance.slot_committee_weight_forced` proves part (i) from the field and committee coverage in each full in-horizon epoch. The statistical properties of committee sampling, and the tolerance of the FCR thresholds to sampling error, are out of scope by design.
- `SafetyPremises.epoch_one_finalization_scope` excludes genesis runs that finalize epoch 1. No target-included link from epoch 1 to epoch 2 can exist, so in effect the field says that no accepted block state finalizes epoch 1. Lean proves this (`no_finalizationLink_epoch_one_to_two` and `ConcreteBridge.epochOneFinalizationScope_finalized_ne_one` in `FastConfirmationProofs/FFG/Concrete/EpochOneLinks.lean`), and the pyspec check finding.epoch_two_target_source_is_genesis in `test_realized_gap.py` agrees. Python finalizes epoch 1 when epoch-2 justification needs votes included in epoch 3. Extending the proof to that path remains open.
- `ByzantineWeightPremises.span_fraction` must hold for every in-horizon slot span, including one slot. A global fault share does not establish this bound. The bound models the committee majority condition of v4 Assumption 2.
- The result covers stored boundary outputs. The two extra-query counterexamples refute same-second head agreement at a mid-second prefix under the counterexample synchrony record. Next-slot safety of an in-slot query is open.

## Where to read

Start with the [review guide](docs/REVIEW_GUIDE.md), [architecture](docs/ARCHITECTURE.md),
[modeling choices](docs/MODELING_CHOICES.md), and [source map](docs/SPEC_MAP.md). The [conformance guide](docs/conformance.md) covers trace
comparison. The claim and proof sources are `FastConfirmationStatements/Review.lean` and
`FastConfirmationProofs/ReviewTheorem.lean`. The [witness
index](FastConfirmationWitnesses/Index.lean) states each finite run's limit.

## Citation

To cite this repository, use the "Cite this repository" button on GitHub. It
reads [CITATION.cff](CITATION.cff).

The repository uses the MIT [license](LICENSE).
