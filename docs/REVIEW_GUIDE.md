# Review guide

`ReviewClaims` has one safety field. `review_claims` proves it. The public live theorem is a separate conditional result. The trust audit checks 43 public theorem witnesses: 36 executable-side and seven paper-side.

The safety proof takes a supplied FFG interpretation as a premise. Its
accepted-block FFG state includes an inclusion relation and checkpoint
selectors. `FFGStateAndCheckpointReadAgreement` requires agreement with every
checkpoint read of successful handlers. The interpretation also requires
eventual checkpoint inclusion (paper Assumption 3.2 style), link and checkpoint
agreement, checkpoint projection laws, and finalization lag. The inclusion
relation need not equal block-body membership. The theorem holds for every
relation that satisfies these laws. `FFGInterpretationFidelity` states the
intended body-membership and valid-vote interpretation, and every full-bundle
witness proves it. This development does not derive the FFG layer from the
beacon state transition. A client or the Python rule needs a proof that its
FFG behavior supplies the interpretation before the theorem applies to it.

## Short glossary

- **FCR:** Fast Confirmation Rule. It selects a confirmed root from fork-choice state.
- **Beacon function interface:** `BeaconFunctionInterface` supplies the opaque beacon, committee, signature, and payload functions.
- **FFG:** Casper Friendly Finality Gadget. It supplies checkpoint justification and finalization state.
- **LMD-GHOST:** Latest Message Driven Greedy Heaviest Observed SubTree. It selects a fork-choice head from latest votes.
- **Gloas:** The consensus fork that separates beacon blocks from execution payloads.
- **Available checkpoint:** `AcceptedBlockFFGState.AvailableCheckpoint` holds when an accepted block on the tip's chain has checkpoint evidence. `CheckpointInclusionView.AvailableCheckpoint` is the paper view.
- **PTC:** Payload Timeliness Committee. It supplies payload timeliness votes in Gloas.
- **GST:** Global stabilization time. The paper's synchrony assumptions apply after this point.
- **Scheduled prefix:** `Execution.ScheduledPrefixStore` is a store from the exact event fold. `Execution.RootKnownInScheduledPrefix` also covers the initial store.
- **Selected vote support:** `SelectedPredictionVoteSupport` is an internal derived fact. Current-edge votes use the exact target. Previous-result votes may use different targets below the selected root.
- **FFG interpretation:** `ScheduledFFGInterpretation` holds the accepted block state and its checkpoint read agreement. `FFGInterpretationFidelity` checks real included votes and the external validity function.
- **A, Δ, S:** A is the attestation deadline offset. Δ is the positive message delay. S is the slot duration. The execution premise requires `A + Δ < S`.

## Review status

```text
┌─────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Finding                 │ Status and evidence                                                                                          │
├─────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Stored next-slot safety │ The root is in each honest observer's block store and on its head from the next slot, within the horizon.    │
│ Live monotonicity       │ Conditional theorem under the safety bundle and both fields of LiveMonotonicityPremises.                     │
│ Selected result         │ A spec-correspondence lemma covers the find_latest_confirmed_descendant note. It is not a review claim.      │
│ Optional in-slot query  │ No general safety claim. StrictPrefixExtraQuery and PinnedEconomicsExtraQuery give counterexamples.          │
│ Joint live witness      │ LiveMonotonicityWitness.joint_witness satisfies the safety bundle and both live fields in one short run. Its │
│                         │ confirmed root advances. Its FFG timing uses the genesis anchor at epoch 0.                                  │
│ Payload envelope        │ Exercised by FullTwelveEnvelopeWitness.envelope_relay_exercised and data_relay_exercised under the full      │
│                         │ safety bundle, with an accepted envelope that one node receives two seconds late.                            │
│ Guarded target edge     │ Exercised by TargetEdgePremiseWitness.target_edge_support_exercised under the full safety bundle.            │
│ Byzantine weight        │ Exercised by ByzantinePremiseWitness.byzantine_weight_exercised: non-honest weight 200 of 4000 under the     │
│                         │ full safety bundle.                                                                                          │
│ Slashing relay          │ Exercised by ByzantinePremiseWitness.slashing_relay_exercised; the call at second six reads the evidence.    │
│ Previous-result guard   │ Exercised by ByzantinePremiseWitness.previous_result_proviso_exercised at the call from second eight to      │
│                         │ nine.                                                                                                        │
│ Included carrier votes  │ The safety premise needs an accepted carrier and a received block copy of each included vote. Body           │
│                         │ membership and validity are in FFGInterpretationFidelity, outside the premise.                               │
│ Interpretation fidelity │ Each full-bundle witness proves FFGInterpretationFidelity for its interpretation. Validation uses a prepared │
│                         │ target checkpoint state from a reachable keyed target block state.                                           │
│ Committee span bound    │ The fault fraction applies to every in-horizon span, including one slot. A global fault share does not       │
│                         │ establish it.                                                                                                │
│ Opaque validation       │ BeaconExternalsPremises and verified envelope events supply the engine verdict and deterministic behavior.   │
│ Static registry         │ StaticValidatorSet covers the finite horizon. Validator churn is outside the claim.                          │
│ Paper Algorithm 1       │ SafeConfirmedAlg1Inputs requires future rule confirmation for each honest-view-safe block. This is stronger  │
│                         │ than paper Assumption 6.                                                                                     │
│ Gloas discount          │ The pinned fork counts matching-status or PENDING parent votes. Upstream can count opposite resolved-status  │
│                         │ votes.                                                                                                       │
└─────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Audit path

1. **Model:** Read `FastConfirmationModel/`. Compare `Spec/` with the pinned Python fork. Check the Gloas discount, finite maps, loop fuel, and arithmetic. Check schedules and accepted handler results in `Execution/`.
2. **Statements premises:** Read both fields of `ReviewClaims`. Expand each record in `FastConfirmationStatements/Premises/`. Check the observer, time, horizon, and successful-prefix ranges.
3. **Externals:** Check the table below against `BeaconFunctionInterface` and `BeaconExternalsPremises`. Check the supplied FFG inclusion and certificate evidence. The slashing relay is a separate premise over the literal Python handler.
4. **Claims:** Read the proof terms in `FastConfirmationProofs/`. Check `confirmed_root_safe_from_next_slot`, `live_confirmed_root_monotonicity`, and `review_claims`. Read the independent Paper library with [the paper map](PAPER_MAP.md).
5. **Witnesses:** Read `FastConfirmationWitnesses/Index.lean`. Check each run's true guards and vacuous branches. Check the 43 registered theorems in `scripts/Audit.lean`.

## Trusted boundary

`BeaconFunctionInterface` has 11 supplied functions or relations. The table
distinguishes constrained externals, whose contracts are premises, from
unconstrained externals. The theorem holds for every choice of an unconstrained
function. A source or client interpretation must justify the constrained
contracts and the intended behavior of any unconstrained function it uses.

```text
┌────────────────────────────────────────┬────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ External field                         │ Constraining premise and limit                                                                         │
├────────────────────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────────────────┤
│ get_beacon_committee                   │ Constrained: BeaconExternalsPremises.committees_agree, committee_assignment_unique,                    │
│                                        │ committee_coverage, and committee_members_active constrain the union read. Ordered committee tables    │
│                                        │ are unconstrained: the theorem holds for every choice of these tables.                                 │
│ get_committee_count_per_slot           │ Unconstrained: the theorem holds for every choice of this function. No count contract is a premise.    │
│ process_slots                          │ BeaconExternalsPremises.process_slots_slot, process_slots_registry, and                                │
│                                        │ process_slots_attestation_valid constrain used outputs. Both Phase0 source-coherence records           │
│                                        │ constrain justification. FFGInterpretationFidelity constrains target-state origin outside safety.      │
│ state_transition                       │ BeaconExternalsPremises.state_transition_slot, registry, pre_slot_lt, and checkpoint_epoch             │
│                                        │ constrain imports. Both Phase0 source records, FFG state transitions, and                              │
│                                        │ ImportedBlockFinalizationLag constrain used state outputs.                                             │
│ process_justification_and_finalization │ BeaconExternalsPremises.pjf_checkpoint_epoch and FFG state genesis/transition laws constrain           │
│                                        │ checkpoint outputs. Both Phase0 boundary-source equations constrain justification.                     │
│ is_valid_indexed_attestation           │ honest_attestation_valid, valid_attestation_honest, valid_attestation_committee,                       │
│                                        │ valid_attestation_default, and process_slots_attestation_valid constrain accepted checks.              │
│ AnchorCommitsToState                   │ ScheduledExecutionPremises.genesis supplies the initial anchor relation. No hash theorem is proved.    │
│ get_ptc                                │ Unconstrained: the theorem holds for every choice of this function. The handler reads the ordered PTC. │
│ is_valid_indexed_payload_attestation   │ Unconstrained: the theorem holds for every choice of this function. No PTC signature contract exists.  │
│ is_data_available                      │ NextSlotSynchronyPremises.data_availability_relay and envelope_delivery transport true data reads.     │
│                                        │ The handler checks the local Boolean result. No KZG soundness theorem is proved.                       │
│ verify_execution_payload_envelope      │ BeaconExternalsPremises.verify_envelope_deterministic and envelope_delivery constrain verified         │
│                                        │ observations. No execution-engine or signature refinement theorem is proved.                           │
└────────────────────────────────────────┴────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

`Execution.schedule` is supplied. `WellFormedExecution`, `HonestBehavior`, and
the delivery laws constrain it. The accepted FFG relation and checkpoint
reads are also supplied under their evidence and read-agreement premises.
`Execution.store` is the handler fold.

The ordered `BeaconState.beacon_committee_reads` and
`BeaconState.committee_count_reads` tables are unconstrained. The theorem holds
for every choice of these tables. A client interpretation must relate them to
its committee queries.

## Review dimensions

- **Python fidelity:** Compare each modeled FCR branch with the pinned Python source. Check each abstraction and changed Gloas branch.
- **Execution:** Check event order, successful handler returns, state at boundary seconds, payload validation, static stake, and external contracts.
- **Statements:** Expand the safety field of `ReviewClaims`. Check observer, time, and horizon quantifiers. Read `live_confirmed_root_monotonicity` as a separate conditional result.
- **Premises:** Expand every nested record. Check that each premise is needed and jointly satisfiable. Check FFG and finalization ranges beyond the endpoint.
- **Non-vacuity:** Locate concrete runs for the audited theorem witnesses. Check the joint live witness and each field that a run exercises only vacuously.
- **Paper:** Read the independent Section 3.1 and Section 4 theorems. Check where Algorithm 1 uses a stronger premise than paper Assumption 6.

## Premise strength and range

`LiveMonotonicityPremises` has two fields. `honest_block_each_slot` requires an honest-proposer block in each slot from execution start. All honest stores know it by the next slot. Honest votes support descendants without reorg of those blocks. `ffg_timely_justification` requires exact unrealized justification at the last-slot call. It also requires an aligned head state at the next epoch start and a recent previous-head voting source. These store outcomes close the FCR guards. They are conditions of the separate live theorem, not network or behavior assumptions. Proposer-index membership does not prove authentication.

Paper Assumption 3.2 can allow a two-epoch FFG inclusion delay. The executable selector can close its gates before inclusion. `get_latest_confirmed_eq_finalized_of_stale` and `Execution.confirmed_succ_eq_finalized_of_stale_call` show the stale fallback. The live claim uses timely closure. The joint finite witness meets both live fields, but its FFG timing holds through the genesis anchor. No vote-driven justification occurs in that run. Paper Theorem 1 has no block-in-every-slot premise.

`Execution.NextSlotSafetyPremises` includes exact FFG state at each successful handler prefix. It also includes scheduled execution, completed FCR calls, epoch arithmetic, anchor alignment, checkpoint evidence, and finalization delay. `Execution.ScheduledFCRCallPremises` adds static validators, a fault bound for each committee span, Phase0 source coherence, a balance floor and next-slot vote receipt. No field directly states the stored-root safety conclusion. Global FFG and finalization premises can range beyond a conclusion endpoint.

`ByzantineWeightPremises.span_fraction` and `estimate_sound` are deterministic
events assumed on every checked span, including one slot. A global fault share
does not imply these events. Their probability under committee sampling is
outside this development.

Prediction support is derived. `SelectedPredictionVoteSupport` is internal proof vocabulary,
outside the safety premise. Its previous-result conclusion permits different targets
that all descend from the selected result. The live premise and conditional theorem are unchanged.

The key theorem is
`Execution.confirmed_safety_and_lineage_of_acceptedActualFCRFold`.
The call induction retains the preceding lineage. The strict endpoint-slot
induction supplies earlier honest heads. The current crossing and previous-result
consumers use `Execution.preQueryVoteSelectedSIRBracketAt_of_earlierVotes` and
the two endpoint pinning lemmas. They do not assume future vote support.
After strict-result safety is proved, the fold derives support for later calls.

The historical payload retains the original caller, call second, target, source,
and `start(e+1)` deadline. Both its certificate and its quorum are functions of a
cutoff after the target epoch. An earlier endpoint uses the original gate and
votes before that endpoint. No strict justified-epoch external law was added.

The reachability audit keeps the Statements library focused on declarations
used by the safety review claim and the conditional live statement. The Internal library holds call and trace
vocabulary, vote-support predicates, and interpretation fidelity used by
proofs and witnesses.

The existing target-edge and previous-result witness theorems remain facts about
the runs. Their full-bundle constructors no longer prove support fields.
See [modeling choices](MODELING_CHOICES.md) for the Python note and the
counterexample to exact target agreement for a previous-epoch result.

## Delivery and evidence

`NextSlotSynchronyPremises` requires positive Δ and strict `A + Δ < S`. Its
`delivery_lookahead` field also covers the first boundary beyond the public
horizon and implies the in-horizon vote delivery law. A source observation
must occur by its slot deadline. A receiver observation occurs at or after the
next boundary. A receiver is later than the source. Honest votes use the vote
deadline. `synchrony_and_delivery_iff_nextSlot` relates these bundles.

Block and envelope exclusion is checked before the next-slot tick. It permits only a permanent finalized-guard conflict with a known parent. The FFG, economic, and finalization-delay premises establish that each honest head's known ancestor path is admissible. Carrier-certificate accountability covers other required roots. Ready blocks and envelopes precede the boundary vote handler. Data service and deterministic envelope validation justify payload acceptance. `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope event.

`on_attester_slashing` follows Python. It validates against `store.block_states[store.justified_checkpoint.root]`. Evidence relay is an implementation assumption that gives every honest node the indices by the next boundary. Literal Python can reject evidence if this state lacks a signer and can violate the relay. The premise matches five of six checked clients that validate against a newer head state. The [modeling choices](MODELING_CHOICES.md) page records the pinned client commits. A late accepted item uses a fresh cutoff observation at the next scheduled FCR call. No validity-agreement field was added to the external contract.

## Source and checks

The source of record is fork `fradamt/consensus-specs`, tag `fcr-gloas-fix` (`13f391516`). The [source map](SPEC_MAP.md) records the exact difference from upstream. The [conformance harness](conformance.md) compares projected Python and Lean observations. A matching trace does not prove all external contracts or all reachable executions. The weak-synchrony branch is separate from this main review.

`scripts/validate.sh --fast` checks the source pin, document names, import boundary, and hygiene. Full validation builds the libraries and checks imports, reachability, surface shape, and the 43 public witnesses. `scripts/Audit.lean` allows only `propext`, `Classical.choice`, and `Quot.sound`.

## Known limits

The conclusion covers stored boundary outputs in a finite horizon. It does
not cover an arbitrary in-slot query. The confirmed root is in each honest
observer's block store from the next slot. The active validator set is fixed.
No witness has non-anchor finalization, positive Gloas discount, or a PTC
event. The live witness uses the genesis anchor for FFG timing. The theorem
does not prove that the Python handlers or a client satisfy each external
contract. The independent Paper library has no refinement theorem to the
executable model.
