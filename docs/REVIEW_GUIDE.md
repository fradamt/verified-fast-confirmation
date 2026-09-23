# Review guide

## Known scope limits

- The model is non-optimistic by design. No optimistic status will be added.
  A payload enters `store.payloads` only through
  `on_execution_payload_envelope`, after
  `verify_execution_payload_envelope = true`. That external represents the
  complete Python validation, including the execution engine's `VALID`
  verdict. Every imported payload is fully validated. The `is_one_confirmed`
  `MUST` concerning non-`VALID` blocks holds by construction in this model.
- The execution layer remains uninterpreted. Data-availability relay and
  envelope-verification determinism are explicit premises. This is the
  intended abstraction boundary for the external checks.
- The paper-model Algorithm-1 monotonicity witness assumes future confirmation
  of honest-view-safe blocks.
- Live monotonicity needs an FFG timing premise. See
  [Missing FFG timing premise](#missing-ffg-timing-premise).

## Proposed live monotonicity premises (open)

`Spec_Monotonicity_live` is a proposed statement in
`FastConfirmation/Spec/TheoremStatements.lean`. Its accepted-bundle
specialization is `AcceptedSpec_Monotonicity_live`. No proof or audit witness
is claimed yet. The new `MonotonicityLiveAssumptions` has four premises:

- `honest_block_each_slot`: every slot from the execution start through the
  interval has a block with an honest proposer index, and every honest store
  knows it at the next slot start. Honest votes in that slot and later slots
  see the block and support its descendants. The prefix is needed because an
  interval can begin with an already stale cached root. Same-slot support is
  needed for a full epoch's committee to support its first block.
- `honest_votes_extend_initial_head`: honest votes in the interval support a
  descendant of the observer's initial head in the voter's store.
- `paper_byzantine_boost_bound`: four times the actual non-honest active stake plus
  proposer boost is less than the total active stake.
- `configured_threshold_margin`: twice the actual non-honest active stake, twice the
  configured adversarial allowance, and proposer boost total less than the
  active stake. The executable FCR uses the configured cap in its threshold.

The accepted trajectory already supplies honest committee participation and
active-validator committee coverage in each in-horizon epoch. These facts are
not repeated in the new liveness record. The live monotonicity statement
remains open until staleness and epoch-start reconfirmation are derived from
these execution premises.

`MonotonicityTrace.lean` proves that the observed restart and descendant
selector cannot lower the candidate's block slot on the known-walk domain.
The finalized-revert phase remains the open branch; this local fact does not
establish the live statement.

### Missing FFG timing premise

The four fields do not bound the delay before a justification appears in
`store.unrealized_justifications`. The accepted paper Assumption 3.2
(`PaperA32Inclusion`) lets the checkpoint of epoch `e` appear there only by
the start of epoch `e + 2`, through the last block of epoch `e + 1`. The
executable selector needs the previous epoch's justification during the
current epoch. `MonotonicityLiveGates.lean` proves the two executable facts:

- `find_latest_confirmed_descendant_eq_of_lagging_unrealized`: in a
  non-start slot, if the unrealized justification of the head and of the
  previous-slot head is older than the previous epoch, the selector returns
  its input.
- `get_latest_confirmed_eq_finalized_of_stale` and
  `Execution.confirmed_succ_eq_finalized_of_stale_call`: a cached root that
  is two epochs old reverts to the finalized root when the observed
  checkpoint block is not from the previous epoch and the finalized block is
  two epochs old.

Scenario, all stake honest, one honest block in each slot: at the start of
epoch 1 the previous-epoch loop confirms epoch-0 blocks, and in epoch 1 the
tentative loop can confirm epoch-1 blocks (the head gate is `0 + 1 >= 1`).
If the epoch-1 checkpoint appears in `unrealized_justifications` only through
the last block of epoch 2, and that block arrives after the last-slot call,
then both selector gates stay closed in every non-start slot of epoch 2. The
start-slot call cannot confirm the epoch's own first block, because no vote
supports it yet. At the start of epoch 3 the cached epoch-1 root is stale,
the observed checkpoint is from epoch 0, and the call returns the anchor. The
four fields hold in this run. This argument is not a kernel-checked accepted
execution: the finite witness does not yet have a block in each slot.

A live proof therefore needs an additional FFG timing field. The minimal
candidate is: at the last-slot call of each epoch `e` in the interval, each
honest store's `unrealized_justified_checkpoint` is the epoch-`e` checkpoint
of the honest chain; at the next epoch start the head's unrealized
justification is equal to it; and the voting source of the previous-slot head
is at most two epochs old. The observed restart then moves a stale cached
root forward to the epoch-`e` boundary block. Epoch-start reconfirmation of a
same-epoch cached root can use the configured bound
`CONFIRMATION_BYZANTINE_THRESHOLD <= 25` (`Config`) with the accepted
`span_fraction` and `estimate_sound`: each added committee adds honest support
of at least `3/4` of its weight, and the threshold grows by at most half of
`3/2` of that weight. These parts are not yet proved.

The accepted finite witness proves the need for prefix production:
`descendant_votes_without_continuous_production_revert` has all honest stake,
descendant votes in slots 2–7, and the paper's strict economic bound. The
cached child still reverts to the anchor at second 8 because slots 2–6 have
no new block. A kernel check also showed that the first interval-only draft
of the three-field bundle held for seconds 7–8 while strict monotonicity
failed. The production field now starts at the execution's initial slot.

The paper inequality alone is too weak for the executable threshold when
actual Byzantine stake is below the configured cap. With total stake 10000,
actual Byzantine stake 2300, proposer score 500, and a configured 25% cap,
`4*2300+500 < 10000` holds. Honest support is 7700, while the executable
threshold is 7750. The extra margin excludes this case. This arithmetic
check does not construct a complete accepted execution.

Same-slot voting is another explicit timing premise. In a two-slot epoch
with 10000 all-honest stake, if the first slot's 5000-stake committee votes
before the first block arrives, later votes supply only 5000 support. The
configured 25% FCR threshold is 7500 even with zero actual Byzantine stake
and zero proposer boost. Production by the next slot alone cannot establish
one-confirmation for that block. This is an arithmetic check, not a complete
accepted execution.

Gloas status: **proved** for the payload-aware discount in
[the spec deviation](gloas-spec-deviation.md). Full validation passes,
including the trust audit of the 13 public witnesses. The payload envelope
relay closes G2-003. `StatusMarginConstruction.lean` closes G2-004: it
constructs the pending-parent payload status margin for every selected edge.
The public witness declaration texts are unchanged. The G3 negative result
applies to the upstream discount rule; it is kept in the [history](#history).

## Trust and architecture

The repository publishes two independent developments. `FastConfirmation.Spec`
models the executable Ethereum consensus specification and contains the primary
accepted theorem. `FastConfirmation.Paper` formalizes the companion paper. There
is no refinement theorem between them, and cross-imports are prohibited.

All Lean modules must be reachable through their own public facade and then
through `FastConfirmation.lean`. This keeps internal experiments, historical
audits, and countermodels out of the publication unless they are deliberately
made part of a reviewed import cone.

Imports are checked using the parser from the repository's pinned Lean
toolchain (`lean --deps-json`), not a duplicate header grammar.

The accepted Spec result is next-slot stored-output safety. The literal
mandatory boundary-call result is also proved. Optional calls at arbitrary
in-slot action prefixes are not covered; the two exported strict-prefix
counterexamples are required regression results, not ancillary examples.

The primary assumption surface is the GST-0 specialization. Public safety
endpoints and static-set laws use a finite verification horizon.
`HorizonVoteDeliveryLookahead` can also require the mandated receipt at the
first second of the following slot, just outside the endpoint cutoff. Legacy
or exact-current statement vocabularies are diagnostic surfaces, not
substitutes for the accepted theorem.

## Consensus source

The authoritative public source is `ethereum/consensus-specs` commit
`6b9bd532cca16555e2f3282d757622ebff29743e`. The manifest in
`spec_source/manifest.json` records the exact twelve source and configuration
objects consumed by the model.
The Gloas empty-slot discount is a documented local change to that source.
See [the exact diff and proof status](gloas-spec-deviation.md).

The manifest proves byte identity and provenance only. A pin change must also
be reviewed against:

- `docs/spec-model-design.md`
- `docs/spec-annotation.md`
- `FastConfirmation/Spec/Model/`
- the accepted assumption surface and theorem statement

Regenerating hashes never establishes semantic faithfulness by itself.

## Deterministic gates

`scripts/validate.sh --fast` checks:

- the pinned consensus-source Git objects and content hashes;
- fail-closed exact strings for proof placeholders, native decision shortcuts,
  implementation overrides, and `#exit` are absent from project Lean sources
  (including comments and strings);
- whitespace errors in the pending Git diff and project text.

`scripts/validate.sh` additionally runs:

- facade reachability and Spec/Paper independence using Lean's own parser;
- `scripts/check_build.sh`, elaborating the complete import graph and rejecting
  Lean's proof-placeholder diagnostic even for non-persistent commands;
- `scripts/Audit.lean`, which inspects declarations originating in project
  modules and checks an exact public theorem witness set.

The Lean build and environment audit are authoritative for elaborated
declarations. Lake promotes Lean's named `hasSorry` diagnostic and the build
wrapper independently rejects its diagnostic text, including for
non-persistent commands such as `example`. The audit rejects `sorryAx`, unsafe,
source-authored partial, axiom, constant, opaque, extern, and `implemented_by`
project declarations.
Equation-compiler partial implementation details are recognized generically
through Lean's declaration-range metadata and must have safe public parents.
The audit permits only `propext`, `Classical.choice`, and `Quot.sound` in
project declaration dependencies.

GitHub CI runs the same deterministic gates with a checksum-pinned Elan
bootstrap. It uses no model API and receives read-only repository permissions.
The bundled `leanchecker` is intentionally not a blocking gate: on this
295-module environment it fans out replay work across matching modules, is not
an external verifier, and showed an unsuitable runtime/memory profile for
routine hosted CI.

## Gloas envelope premises (23 September 2026)

`PaperSafetySynchrony` has two operational premises. Their definitions are
verbatim:

```lean
def EnvelopeDelivery (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    is_payload_verified (E.store cfg ext v n) r = true →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      ∃ (d k : ℕ) (signed : SignedExecutionPayloadEnvelope Root)
        (sourceObservation receiverObservation : EnvelopeObservation Root)
        (before after : List (Event Root)),
        0 < d ∧ d ≤ m ∧
        E.slot_at cfg n + 1 ≤ E.slot_at cfg (d + 1) ∧ k ≤ n ∧
        Event.execution_payload_envelope signed sourceObservation ∈ E.schedule v k ∧
        signed.message.beacon_block_root = r ∧
        r ∈ (E.store cfg ext v n).block_roots ∧
        ext.is_data_available r sourceObservation = true ∧
        ext.verify_execution_payload_envelope
          ((E.store cfg ext v n).block_states r) signed sourceObservation = true ∧
        E.schedule w d = before ++
          Event.execution_payload_envelope signed receiverObservation :: after ∧
        r ∈ (before.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w (d - 1)) (E.time_at d))).block_roots

def DataAvailabilityRelay (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ k n (signed : SignedExecutionPayloadEnvelope Root)
      (sourceObservation : EnvelopeObservation Root),
    k ≤ n → E.WithinHorizon cfg n →
    Event.execution_payload_envelope signed sourceObservation ∈ E.schedule v k →
    ext.is_data_available signed.message.beacon_block_root sourceObservation = true →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      ∀ receiverSigned receiverObservation,
        receiverSigned.message.beacon_block_root = signed.message.beacon_block_root →
        Event.execution_payload_envelope receiverSigned receiverObservation ∈ E.schedule w m →
        ext.is_data_available signed.message.beacon_block_root receiverObservation = true

  envelope_delivery : EnvelopeDelivery cfg ext E
  data_availability_relay : DataAvailabilityRelay cfg ext E
```

`ExternalsCoherence` has this law, verbatim:

```lean
  verify_envelope_deterministic : ∀ state signed o o',
    ext.verify_execution_payload_envelope state signed o =
      ext.verify_execution_payload_envelope state signed o'
```

The bound matches `block_relay`. Delivery occurs at a position where the
receiver knows the block. The model does not retry a rejected envelope, so
the premise requires delivery after the block or redelivery after an earlier
rejection. `BlockStateAgreement.lean` derives equal block states at common
roots from the root commitment and deterministic `state_transition` function.
The relay lemma then derives verified-payload presence. Payload persistence
carries it through the next tick and each event prefix, so an honest index-1
vote finds a verified payload before validation. The 13 public witness
statement texts are unchanged; record-dependent witness types have the new
premises.

Payload availability alone does not compare FULL and EMPTY branch weights.
The local experiment in `scripts/GloasPayloadBranchObstacle.lean` is not an
accepted execution. The [negative result](history/gloas-negative-result.md)
for the upstream discount uses honest singleton votes and the derived relay.
The payload-aware discount charges only matching parent-payload votes; the
opposite ancestor votes then stay in the confirmation slack and pay for the
status margin.

## History

These records describe earlier states of the Gloas port. They are not
current proof obligations.

- [G3 negative result for the upstream discount](history/gloas-negative-result.md)
- [Historical G2 proof obligations](history/gloas-proof-obligations-history.md)
