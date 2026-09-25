# Verified Fast Confirmation

This Lean 4 repository verifies two properties of the executable Fast Confirmation Rule (FCR) under explicit execution, network, economic, and Casper FFG premises. The primary model follows the Python specification in the fork `fradamt/consensus-specs`, tag `fcr-gloas-fix` (`13f391516`). That tag includes the public Gloas empty-slot discount fix. The paper library is independent of the executable model. The proofs are kernel checked; the stated premises and the model boundary need separate review.

## Review theorem

`review_claims` in `FastConfirmationProofs/ReviewTheorem.lean` proves both fields of `ReviewClaims` in `FastConfirmationStatements/Review.lean`:

- `confirmed_root_safe_from_next_slot`: an honest node's stored confirmed root is on every honest head from the following slot, within the verification horizon.
- `live_confirmed_root_monotonicity`: an honest node's later stored confirmed root descends from its earlier one when honest blocks and timely FFG justification meet the live premises.

## Premise ledger

The records in this table are in `FastConfirmationStatements/Premises/`. The paper is [arXiv:2405.00549](https://arxiv.org/abs/2405.00549). The source of each condition is shown in the last column.

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

`Execution.NextSlotSafetyPremises` supplies the common safety premise to the safety field. `LiveConfirmedRootMonotonicity` adds `LiveMonotonicityPremises` to that same execution premise. The FFG and finalization laws quantify over handler-successful prefixes beyond the safety endpoint where their declarations require it; the finite conclusion does not reduce their premise range.

## Scope limits

- Validator activity is fixed inside the checked horizon by `StaticValidatorSet`. The proof does not cover registry churn.
- The model is non-optimistic. An imported payload enters the store only after `verify_execution_payload_envelope` returns true. This external includes the execution engine's `VALID` decision. Execution validation itself is opaque.
- `BeaconExternalsPremises` supplies contracts for external state transitions and validation. The Lean proof does not implement an execution engine.
- `CausalCarrierAttestationRelation.Included` is a supplied carrier-vote relation whose evidence checks membership in the accepted carrier block's ordered FFG attestation body.
- Included votes validate on the target checkpoint state prepared from a keyed target block state in an honest in-horizon store. The preparation advances the base state to the target epoch start only when needed. The prepared state need not itself be keyed.
- `ByzantineWeightPremises.span_fraction` must hold for every in-horizon slot span, including one slot. A global fault share does not establish this bound. The bound matches `CommitteeHonestMajority` in the repository's formal paper Assumption 2.
- `LiveMonotonicityPremises.honest_block_each_slot` requires a block with an honest proposer index in every slot from execution start. Its vote-support law and `ffg_timely_justification` require timely descendant votes and exact FFG state outputs at epoch boundaries. These conditions are stronger than paper Assumption 6. Proposer-index membership is not an authentication theorem.
- `LiveMonotonicityWitness.joint_witness` satisfies both live fields and the safety premise in one short run with a strict root advance. Its FFG timing field holds at epoch 0 through the genesis anchor; no vote-driven justification occurs. The next-slot finite witness has no payload envelope, so its envelope relay conditions hold vacuously. Its selector guard excludes selected current-target accepted edges, so it does not exercise their support premise. See `FastConfirmationWitnesses/Index.lean`.
- The result covers stored boundary outputs. `StrictPrefixExtraQuery.extra_query_changes_head_counterexample` and `PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample` show why an arbitrary in-slot query needs a different statement.

## Paper library

`FastConfirmationPaper/Core/` defines the abstract objects. `FastConfirmationPaper/LMDGhost/` proves the Section 3.1 Theorem 1 safety and monotonicity claims through `confirmed_block_safety` and `confirmed_block_monotonicity`. `FastConfirmationPaper/HFC/` proves the Section 4 Algorithm 1 safety and monotonicity claims through `rule_confirmed_block_safety` and `rule_confirmed_block_monotonicity`. `head_agreement_after_confirmation` is the reusable Lemma 6 style result. `SafeConfirmedAlg1Inputs` requires later rule confirmation for each honest-view-safe block. That input is stronger than paper Assumption 6. There is no refinement theorem between the paper and executable models.

## How to verify

Use the pinned Lean toolchain and a local checkout of the Python fork. The full check builds the six libraries, checks their imports and review surface, and audits the public witnesses for non-standard axioms:

```sh
scripts/validate.sh --consensus-repo /path/to/fradamt-consensus-specs
```

`--fast` runs source, document-name, boundary, and hygiene checks. The full check covers 14 public witnesses in `scripts/Audit.lean`.

## Where to read

Read [architecture](docs/ARCHITECTURE.md), [source map](docs/SPEC_MAP.md), [paper map](docs/PAPER_MAP.md), [modeling choices](docs/MODELING_CHOICES.md), [review guide](docs/REVIEW_GUIDE.md), and [audit brief](docs/AI_AUDIT.md). The [conformance guide](docs/conformance.md) covers trace comparison. Source declarations are in `FastConfirmationStatements/Review.lean`, `FastConfirmationProofs/ReviewTheorem.lean`, and `FastConfirmationWitnesses/Index.lean`.

The execution synchrony fields use a positive millisecond delay and strict
`A + Δ < S`. G4 and exact AU accountability justify transport of the required
roots. The public next-slot endpoints are unchanged. Evidence relay
is a premise. Literal Python validates evidence against the justified state and
can reject a signer that this state lacks. Five of six checked clients (all but
Grandine) validate against the head state, which matches the premise. See [modeling choices](docs/MODELING_CHOICES.md) and the
[review guide](docs/REVIEW_GUIDE.md). `scripts/check_synchrony_corners.py` runs
with validation and rejects the old relay shapes.
