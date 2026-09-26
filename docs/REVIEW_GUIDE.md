# Review guide

`ReviewClaims` has two fields. `review_claims` proves both. The trust audit checks 42 public theorem witnesses: 35 executable-side and seven paper-side.

## Short glossary

- **FCR:** Fast Confirmation Rule. It selects a confirmed root from fork-choice state.
- **FFG:** Casper Friendly Finality Gadget. It supplies checkpoint justification and finalization state.
- **LMD-GHOST:** Latest Message Driven Greedy Heaviest Observed SubTree. It selects a fork-choice head from latest votes.
- **Gloas:** The consensus fork that separates beacon blocks from execution payloads.
- **AU:** Available and unrealized justification from FFG votes in a block's ancestry in the paper model.
- **PTC:** Payload Timeliness Committee. It supplies payload timeliness votes in Gloas.
- **GST:** Global stabilization time. The paper's synchrony assumptions apply after this point.
- **A, Δ, S:** A is the attestation deadline offset. Δ is the positive message delay. S is the slot duration. The execution premise requires `A + Δ < S`.

## Review status

```text
┌─────────────────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Finding                     │ Status and evidence                                                                                           │
├─────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Stored next-slot safety     │ Proved under Execution.NextSlotSafetyPremises for honest stored boundary outputs within a finite horizon.     │
│ Live monotonicity           │ Proved under the safety bundle and both fields of LiveMonotonicityPremises.                                   │
│ Selected result             │ A spec-correspondence lemma covers the find_latest_confirmed_descendant note. It is not a review claim.       │
│ Optional in-slot query      │ No general safety claim. StrictPrefixExtraQuery and PinnedEconomicsExtraQuery give counterexamples.           │
│ Joint live witness          │ LiveMonotonicityWitness.joint_witness satisfies the safety bundle and both live fields in one short run. Its  │
│                             │ confirmed root advances. Its FFG timing uses the genesis anchor at epoch 0.                                   │
│ Payload envelope            │ Exercised by FullTwelveEnvelopeWitness.envelope_relay_exercised and data_relay_exercised under the full       │
│                             │ safety bundle, with an accepted envelope that one node receives two seconds late.                             │
│ Guarded target edge         │ Exercised by TargetEdgePremiseWitness.target_edge_support_exercised under the full safety bundle.             │
│ Byzantine weight            │ Exercised by ByzantinePremiseWitness.byzantine_weight_exercised: non-honest weight 200 of 4000 under the      │
│                             │ full safety bundle.                                                                                           │
│ Slashing relay              │ Exercised by ByzantinePremiseWitness.slashing_relay_exercised; the call at second six reads the evidence.     │
│ Previous-result proviso     │ Exercised by ByzantinePremiseWitness.previous_result_proviso_exercised at the call from second eight to       │
│                             │ nine.                                                                                                         │
│ Included carrier votes      │ The safety premise needs an accepted carrier and a received block copy of each included vote. Body            │
│                             │ membership and validity are in FFGInterpretationFidelity, outside the premise.                                │
│ Interpretation fidelity     │ Each full-bundle witness proves FFGInterpretationFidelity for its interpretation. Validation uses a prepared  │
│                             │ target checkpoint state from a reachable keyed target block state.                                            │
│ Committee span bound        │ The fault fraction applies to every in-horizon span, including one slot. A global fault share does not        │
│                             │ establish it.                                                                                                 │
│ Opaque validation           │ BeaconExternalsPremises and verified envelope events supply the engine verdict and deterministic behavior.    │
│ Static registry             │ StaticValidatorSet covers the finite horizon. Validator churn is outside the claim.                           │
│ Paper Algorithm 1           │ SafeConfirmedAlg1Inputs requires future rule confirmation for each honest-view-safe block. This is stronger   │
│                             │ than paper Assumption 6.                                                                                      │
│ Gloas discount              │ The pinned fork counts matching-status or PENDING parent votes. Upstream can count opposite resolved-status   │
│                             │ votes.                                                                                                        │
└─────────────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Audit path

1. Read `FastConfirmationModel/` and `FastConfirmationStatements/`. Check each definition, premise field, and quantifier. Confirm that the claims concern stored boundary outputs.
2. Compare `FastConfirmationModel/Spec/` with the pinned Python fork. Check changed branches, totalized maps, loop fuel, integer arithmetic, and the Gloas discount. Review schedules, accepted handler returns, static stake, and payload import in `FastConfirmationModel/Execution/`.
3. Check external contracts and supplied FFG evidence. The handler uses the Python justified-state lookup. The evidence relay field is a separate premise that matches head-state clients.
4. Read proof terms in `FastConfirmationProofs/`. Then read `FastConfirmationWitnesses/Index.lean`. Check each finite run and each vacuous field. Check the 42 names in `scripts/Audit.lean`.
5. Read `FastConfirmationPaper/` independently. Compare the paper claims and assumptions with [the paper map](PAPER_MAP.md). The paper library has no refinement theorem to the executable model.

## Review dimensions

- **Python fidelity:** Compare each modeled FCR branch with the pinned Python source. Check each abstraction and changed Gloas branch.
- **Execution:** Check event order, successful handler returns, state at boundary seconds, payload validation, static stake, and external contracts.
- **Statements:** Expand the two fields of `ReviewClaims`. Check observer, time, and horizon quantifiers.
- **Premises:** Expand every nested record. Check that each premise is needed and jointly satisfiable. Check FFG and finalization ranges beyond the endpoint.
- **Non-vacuity:** Locate concrete runs for the audited theorem witnesses. Check the joint live witness and each field that a run exercises only vacuously.
- **Paper:** Read the independent Section 3.1 and Section 4 theorems. Check where Algorithm 1 uses a stronger premise than paper Assumption 6.

## Premise strength and range

`LiveMonotonicityPremises` has two fields. `honest_block_each_slot` requires an honest-proposer block in each slot from execution start. All honest stores know it by the next slot. Honest votes support descendants. `ffg_timely_justification` requires exact unrealized justification at the last-slot call. It also requires an aligned head state at the next epoch start and a recent previous-head voting source. These conditions require production and state outputs. Proposer-index membership does not prove authentication.

Paper Assumption 3.2 can allow a two-epoch FFG inclusion delay. The executable selector can close its gates before inclusion. `get_latest_confirmed_eq_finalized_of_stale` and `Execution.confirmed_succ_eq_finalized_of_stale_call` show the stale fallback. The live claim uses timely closure. The joint finite witness meets both live fields, but its FFG timing holds through the genesis anchor. No vote-driven justification occurs in that run. Paper Theorem 1 has no block-in-every-slot premise.

`Execution.NextSlotSafetyPremises` includes exact FFG state at each successful handler prefix. It also includes scheduled execution, completed FCR calls, epoch arithmetic, anchor alignment, checkpoint evidence, and finalization delay. `Execution.CompletedFCRCallPremises` adds static validators, a fault bound for each committee span, Phase0 source coherence, a balance floor, next-slot vote receipt, and guarded prediction support. No field directly states the stored-root safety conclusion. Global FFG and finalization premises can range beyond a conclusion endpoint.

## Delivery and evidence

`NextSlotSynchronyPremises` requires positive Δ and strict `A + Δ < S`. A source observation must occur by its slot deadline. A receiver observation occurs at or after the next boundary. A receiver is later than the source. Honest votes use the vote deadline. `synchrony_and_delivery_iff_nextSlot` relates the current bundles.

Block and envelope exclusion is checked before the next-slot tick. It permits only a permanent finalized-guard conflict with a known parent. The FFG, economic, and finalization-delay premises establish that each honest head's known ancestor path is admissible. Carrier-certificate accountability covers other required roots. Ready blocks and envelopes precede the boundary vote handler. Data service and deterministic envelope validation justify payload acceptance. `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope event.

`on_attester_slashing` follows Python. It validates against `store.block_states[store.justified_checkpoint.root]`. Evidence relay is a premise that gives every honest node the indices by the next boundary. Literal Python can reject evidence if this state lacks a signer. The premise matches clients that validate against a newer head state. The [modeling choices](MODELING_CHOICES.md) page records the pinned client commits. A late accepted item uses a fresh cutoff observation at the next scheduled FCR call. No validity-agreement field was added to the external contract.

## Source and checks

The source of record is fork `fradamt/consensus-specs`, tag `fcr-gloas-fix` (`13f391516`). The [source map](SPEC_MAP.md) records the exact difference from upstream. The [conformance harness](conformance.md) compares projected Python and Lean observations. A matching trace does not prove all external contracts or all reachable executions. The weak-synchrony branch is separate from this main review.

`scripts/validate.sh --fast` checks the source pin, document names, import boundary, and hygiene. Full validation builds the libraries and checks imports, reachability, surface shape, and the 42 public witnesses. `scripts/Audit.lean` allows only `propext`, `Classical.choice`, and `Quot.sound`.
