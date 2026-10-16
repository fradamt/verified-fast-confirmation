# Witnesses

The witnesses are finite runs in `FastConfirmationWitnesses/`. A positive run proves
that the premise of the safety theorem is satisfiable and exercises some of its
fields. A counterexample shows a limit of the result. The
[witness index](../FastConfirmationWitnesses/Index.lean) states the limit of each run.

Each positive run proves its stated premise bundle. An exercised field has a
concrete source event, positive quantity, or true guard in that run. A proof of
the full bundle does not imply that every branch occurs.

- **Full safety at 1 s and 12 s:** `NextSlotPremiseWitness.finite_execution_satisfies_premises` and `FullTwelveWitness.full_bundle_witness` give stored root advances under the full safety bundle. The 12 s run has real delayed block and vote receipts.
- **Payload envelope:** `FullTwelveEnvelopeWitness.full_bundle_witness` has an accepted envelope. Each node receives it once, before the next boundary, and keeps the payload. The antecedent of its boundary prefix holds.
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
│ 12 s envelope       │ NextSlotSynchronyPremises.boundary_envelope_prefix; one early receipt per node; accepted payload. │
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
│ Competing forks     │ not exercised: each full-bundle run imports one chain; no run has a sibling block.                │
└─────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────┘
```

No named run exercises non-anchor finalization or positive Gloas empty-slot
discount. Each full-bundle run has one chain of blocks, so head ancestry is not
shown against a competing branch under the full bundle; only the
counterexamples have forks. The
envelope run computes a zero discount and does not select a FULL head. No run
has a PTC event. Every positive run sets `proposer_score_boost` to zero. The
proposer-score term and should_apply_proposer_boost are not exercised
positively. The one-second runs set `attestation_due_bps` to zero. The main
safety runs have four or five validators. Each slot committee has one
validator, except in the Byzantine run, where validator 4 joins the
committees of validator 3.
Validator churn is outside the fixed scope. These are
coverage limits, not claims about unreachable protocol states.

## Full-bundle families

`GenesisStubPremiseWitness.genesis_stub_full_bundle_witness` satisfies the full safety bundle with a real genesis stub: its stub root is not the anchor root, as in Python. It shows consistency of the bundle; it is not a Python-faithful execution. Four full-bundle families (next-slot, twelve-second, envelope, and GenesisStub) have four validators of 100 Gwei and the same committee schedule in each epoch. They meet part (ii) of the committee-sampling idealization only through the rounding of `adjust_committee_weight_estimate_to_ensure_safety`: it rounds up to 1000-Gwei units and multiplies by 1.005, so every cross-boundary estimate is at least 1005 Gwei, more than their total stake of 400 Gwei. The target-edge and Byzantine families have 4000 Gwei of stake and prove the field by finite evaluation at that scale. A witness at realistic scale with a mixed committee schedule is deferred. The GenesisStub run uses one-second slots, four validators and four slots per epoch, zero attestation due time and proposer boost, an oracle that accepts every block, a base signature check that accepts exactly the ground votes, and the genesis payload fields of the setup (see [premise fields](ASSUMPTIONS.md#premise-fields)). The other five full-bundle families set `zeroRoot := anchorRoot`, which Python cannot do because ZERO_HASH is not the genesis root; with it, the genesis stub reads as the anchor checkpoint in honest votes. `ConcreteJustificationWitness.concrete_certificate_extraction` and `ConcreteFinalityWitness.k2_certificate_extraction` come from concrete FFG fixtures outside the bundle; they show non-anchor justification and finality with two-epoch and adjacent links. The contract suite, projection harness, and differential test check Python behavior. Witness PJF returns early in epochs 0 and 1, as Python does. See [anchor and boundary limits](MODELING_CHOICES.md#anchor-and-boundary-limits).
