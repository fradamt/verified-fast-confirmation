# Gloas model design

The G3 lane ports this design onto main `4b9ef30`. The executable model and
payload-delivery lemmas build. Payload branch selection fails on the
[exact-source honest execution](gloas-negative-result.md), so this lane stops. The [historical G2 obligations](gloas-proof-obligations-history.md)
record the prior gaps. The [review guide](REVIEW_GUIDE.md) states the one new
synchrony field. This design note does not establish Gloas safety.

This note specifies the Gloas model. Gloas replaces the phase0 fork-choice
model. The revised lane contract removes the pre-Gloas equivalence
requirement. The FULL and always-available case does not have phase0
behavior. Keep that difference explicit. No legacy fork policy is added.

The source is `consensus-specs` commit
`477321355d48d527e7e1e4d572f6a40a0b41072a`. All line numbers below refer to
that commit. Keep the source annotation rules in
[spec-annotation.md](spec-annotation.md). Keep the arithmetic, map, state,
and projection rules in [spec-model-design.md](spec-model-design.md), except
where this note gives a change.

## Nodes and messages

Add an inductive `PayloadStatus` with three values: EMPTY, FULL, and PENDING.
Their source values are 0, 1, and 2. Define `ForkChoiceNode Root` as a record
with `root : Root` and `payload_status : PayloadStatus`. Equality compares
both fields. A root does not determine a node. Source:
`specs/gloas/fork-choice.md:78`, `:103`, and `:153`.

Change `LatestMessage` from `(epoch, root)` to
`(slot, root, payload_present)`. Compute its epoch with
`compute_epoch_at_slot cfg message.slot`. Update a latest message only when
the new slot is greater. Do not retain the phase0 epoch comparison in the
Gloas handler. Source: `specs/gloas/fork-choice.md:181`, `:651`, and `:940`.

Extend the block projection with `proposer_index` and the bid fields
`parent_block_hash` and `block_hash`. Keep execution hashes distinct from
beacon roots in field names, even if both use the same opaque hash type.
Keep indexed payload attestations from the block body. Their indices are
the result of the source aggregation-bit projection. Source:
`specs/gloas/beacon-chain.md:708`, `:729`, `:738`, `:749`, and `:829`.

Add projected execution payload envelopes and signed envelopes. They carry
their beacon root and parent beacon root. Envelope validity must also have
access to the source envelope identity or its full validation inputs. An
external function must not infer validity from these two roots alone.

## Store and external functions

Keep the existing store fields. Change `block_timeliness` to an optional
pair of booleans: the attestation deadline result and the PTC deadline
result. Add these fields from `specs/gloas/fork-choice.md:191`:

- `payloads : Root → Option (ExecutionPayloadEnvelope Root)`.
- `payload_timeliness_vote : Root → Option (List (Option Bool))`.
- `payload_data_availability_vote : Root → Option (List (Option Bool))`.

The two outer options express the map domains. Each known root has two
vote lists of length `PTC_SIZE`. Each list position is a PTC position, not a
validator index. A validator can have more than one position. A received
PTC message writes all its positions. A later accepted message can replace
the earlier values. The source has no separate permanent PTC message log.
Do not add one to the store. Source: `specs/gloas/fork-choice.md:1115`.

Payload verification is concrete: `is_payload_verified store root` tests
membership in `payloads`. Payload timeliness and payload data availability
are also concrete. Count both positive and negative votes with the source
strict majority test. If a payload is absent, return `not timely` or
`not available` before the vote count. Do not replace these helpers with a
single availability flag. Source: `specs/gloas/fork-choice.md:313`, `:325`,
and `:346`.

Put these operations behind `Externals`:

- `get_ptc`, including its ordered result and repeated validator indices.
- Indexed payload-attestation signature and index validation.
- Sidecar retrieval, commitment checks, and KZG verification for
  `is_data_available`.
- Execution envelope validation, including signature, state commitment,
  bid commitment, timestamp, withdrawals, execution requests, and execution
  engine validation.

The last two operations depend on local observations and validation
context. Supply their result with the envelope event, or supply an explicit
observation argument to the external function. A fixed function of the root
alone cannot represent data that arrives later. An absent observation must
not mean successful verification. The payload map changes only after a
successful envelope handler. Source: `specs/gloas/fork-choice.md:293`,
`:658`, and `:1089`.

The coherence contract is as follows. Each accepted projected input must
have a source input. External outputs must equal the projection of the
source operation on that input and its recorded observation. Inputs that
are equal in the model must give equal outputs in the same context. Retain
opaque identities when the read projection alone does not determine an
output. Source validation failure maps to rejection. Successful envelope
validation binds the envelope to the stored block and bid. Successful data
validation certifies the required sidecars for that envelope and context.
The PTC result must have `PTC_SIZE` entries from the validator registry and
must preserve source order and duplicates. Block-body index extraction must
agree with that PTC. Existing slot, registry, checkpoint, and committee
coherence requirements remain in force.

These are requirements on concrete external instances. They are not new
axioms, and they must not include the desired safety conclusion. Prove
payload-map and vote-map domain invariants from initialization and handlers.
If the safety proof needs a payload delivery assumption, state and review
that assumption separately. Do not hide it in an external validity result.

Add configuration fields for `PTC_SIZE`, Gloas deadlines, and
`REORG_HEAD_WEIGHT_THRESHOLD`. Derive each PTC threshold as `PTC_SIZE / 2`.
Mainnet uses PTC size 512, attestation deadline 2500 basis points, payload
deadline 5000, payload-attestation deadline 7500, and weak-head threshold
20 percent. Minimal uses PTC size 16. Pin the Gloas preset used by each
checked configuration as well as the three requested Gloas source files.

## Ancestry and fork choice

`get_node_for_root root` returns the PENDING node. This is an unconditional
Gloas helper; it does not read the store. Source:
`specs/gloas/fast-confirmation.md:26`.

The ancestor walk preserves the input status when it does not move. When
it moves to a parent, compare the child's bid parent hash with the parent's
bid block hash. Set the parent status to FULL if they are equal, and to
EMPTY otherwise. The root walk is unchanged. In `is_ancestor`, first compare
roots. Then accept equal statuses, or a PENDING ancestor. A PENDING ancestor
thus covers both resolved statuses. Source:
`specs/gloas/fork-choice.md:367`, `:387`, and `:405`.

`get_checkpoint_block` starts at a PENDING node and returns only the root.
`get_supported_node` returns PENDING for a vote at the block's own slot.
For a later vote, it returns FULL or EMPTY from `payload_present`. Source:
`specs/gloas/fork-choice.md:420` and `:435`.

A PENDING node has an EMPTY child with the same root. It also has a FULL
child if the payload is verified. A resolved node has PENDING block
children only when their parent payload status agrees. A head search can
visit two nodes at each root. Replace the old head fuel bound with
`2 * blocks.length + 2`, with a proof on the known tree domain. The ancestor
fuel bound remains `block.slot + 1`. Source:
`specs/gloas/fork-choice.md:597` and `:622`.

Transcribe the complete head key `(weight, root, payload status tiebreaker)`.
Transcribe previous-slot zero weights, `should_extend_payload`, and
`should_apply_proposer_boost`. The last helper calls `is_head_weak`, so its
committee calculation is now in scope. Keep the public `get_head cfg store` signature. Add a concrete read view to
`BeaconState`: finite `beacon_committee_reads` and `committee_count_reads`
lists, with lookup helpers `beacon_committees` and
`committee_count_per_slot`. The projection records the exact source lists
and counts for all reached queries. `is_head_weak` sums
these lists, including duplicates. For every projected state, including
anchor and external transition outputs, this read view must equal the
source results and the corresponding `Externals` results. Do not assume
that a slot transition preserves a committee view. Also retain an optional
opaque `source_identity` in `BeaconState`. A source projection sets it to the
source state commitment. External functions can then distinguish source
states whose other projected fields agree. Synthetic model states can use
`none`; this does not claim that they are concrete source projections. The
trace exporter must record and rebuild the identity and all reached queries.
These requirements are part of the
projection coherence contract, not new axioms. Source:
`specs/gloas/fork-choice.md:460`, `:496`, `:530`, `:566`, and `:785`.

## Handlers, executions, and the FCR overlay

Initialization creates an empty payload map, two anchor PTC vote lists of
length `PTC_SIZE` filled with `None`, and both true block-timeliness values.
`on_block` checks a FULL parent's verified payload before the state transition. After
insertion it creates the new vote lists, applies the block's PTC messages,
records both deadlines, updates boost, and updates checkpoints in source
order. Source: `specs/gloas/fork-choice.md:218` and `:1020`.

The handler returns an optional store. Rejection retains the caller's store.
Python can mutate a store before a later assertion fails. The faithful domain
therefore requires successful block state validation to establish the PTC
notification guards. Source block validation binds each PTC vote to the
parent root and previous slot and checks its indexed signature
(`specs/gloas/beacon-chain.md:2428`). The external state-transition projection
must retain that validity. Outside this coherent domain, rollback is a
rejection totalization, not a claim about Python's intermediate mutations.

PTC index extraction uses the child post-state. PTC notification uses the
stored parent state. For a child in the next slot, both states must return
the same ordered PTC for the parent slot. The cached PTC window preserves
this value, including at an epoch boundary. If the child skips slots, the
PTC data slot differs from the stored parent slot. The notification then
returns without a vote update. Preserve these source relations in the
external instance. This source-instance contract does not add a field to
the formal safety assumptions. Source: `specs/gloas/beacon-chain.md:1392`,
`:1411`, `:1698`, and `:2428`; `specs/gloas/fork-choice.md:267` and `:1115`.

Add execution-envelope and PTC-message events to `Event` and `apply_event`.
The envelope handler checks known block, local data, and envelope validity
before inserting the payload. The PTC handler checks the assigned block
slot and all committee positions. Only wire PTC messages require the
current-slot and signature checks. Block messages skip those two checks.
Source: `specs/gloas/fork-choice.md:1089` and `:1115`.

Update attestation validation for index 0 or 1. At the block's own slot the
index must be 0. Index 1 requires a verified payload. Update honest vote
construction to use the Gloas payload meaning of the index. The committee
index remains an input to committee lookup; it is no longer the attestation
data index. Source: `specs/gloas/fork-choice.md:889`.

The FCR algorithm retains its root and checkpoint fields. Change its node
helper to PENDING. Add the safe execution hash helper: it returns the
confirmed block bid's parent hash. Source:
`specs/gloas/fast-confirmation.md:38`.

## Proof interface

The node field alone forces no text change in the public definitions in
`Spec/TheoremStatements.lean`. `Spec_Safety`, `Spec_Safety_next_slot`,
`Spec_Monotonicity`, and `Spec_Monotonicity_no_revert` already use the node
helpers. The predicates `JustifiedIn` and `HonestVotesSupportTarget`, the
`JustificationInterface` record, and `SpecAssumptions` also need no text
change from the added node field alone. Audit the new external dependency
separately before any signature edit. Record every actual statement edit
with its old and new text in the lane report. No such edit is made by this
design commit.

Private ancestry results which equate an ancestor with a root-only
constructor need new statements. Use a status parameter or a root equality.
Root equality no longer proves node equality. Child-slot strictness is
false at a PENDING-to-resolved edge. Root descent proofs must represent
payload resolution followed by a block edge. `get_weight_ge` also needs
review: a previous-slot resolved node has zero weight by definition.

Keep all 13 names in `scripts/Audit.lean`. The seven paper witnesses do not
depend on the Spec node type. Review the six Spec witnesses after the
model change. The two counterexamples and joint non-vacuity construction
must remain valid concrete constructions. Do not preserve their names by
weakening their conclusions. Use only the standard Lean axioms.

## Differences from phase0 with FULL and available payloads

The earlier proposed instance sets all payloads to verified and all data to
available. Give every parent link matching execution hashes, so it resolves
to FULL. Give every PTC position a true timeliness and availability vote.
Compare head roots, since phase0 has no status component. Even this strong
interpretation of the requested instance does not give phase0 fork choice.

Consider anchor 1 at slot 0, siblings 2 and 3 at slot 1 from the same
proposer, and block 4 at slot 2 with parent 2. Let the current slot be 2,
the boost root be 4, and both siblings be early. Let 100 active validators
each have balance 32 billion Gwei. Use 32 slots per epoch and proposer
boost 40 percent. Let one validator's latest message support root 3.

Phase0 gives branch 2 a boost of 40 billion Gwei and branch 3 a vote weight
of 32 billion Gwei. It selects head 4. Gloas classifies parent 2 as weak
and finds the early same-proposer block 3. It suppresses boost, gives
branch 2 weight zero, and selects head 3. All payload and data conditions
above still hold. The difference is in the beacon root, not just the
payload status. See `specs/phase0/fork-choice.md:362` and
`specs/gloas/fork-choice.md:530`.

There is a second independent change: a later-slot vote in the same epoch
replaces a latest message in Gloas but not in phase0. Payload availability
does not restore the old epoch comparison.

Thus unrestricted `get_head` equality with phase0 is false. The FCR stores also retain `get_head(store).root` in
`current_slot_head`, so their full outputs cannot agree on this example.
A frozen `Phase0Reference` would preserve these differences; it would not
remove them. Do not assert the equality or add an axiom for it.

Pre-Gloas executions do not instantiate this model with the same behavior.
An explicit legacy fork policy would need different boost, message-update,
and vote-index rules. Such a policy is outside this lane. Historical
phase0, Altair, Bellatrix, Capella, and Deneb traces describe the old model.
Retire them from the default harness run. The conformance target is
`gloas-minimal`.

Other FULL/available differences are:

- A previous-slot resolved node has zero weight. A PENDING node at that
  root keeps its attestation score and eligible boost.
- A head result has a resolved payload status. A PENDING node first chooses
  EMPTY or FULL, then follows block children with that parent status.
- `get_node_for_root` returns PENDING. It denotes either resolved status
  for the ancestry test used by the FCR.
- The safe execution hash is the confirmed block bid's parent hash.

## Trace migration

Schema v2 records node status, proposer index, bid hashes, both block
deadlines, payload membership, both optional PTC vote lists, and exact
latest-message slots with payload presence. Keep local availability
observations separate from PTC votes. Record external calls reached by the
new weak-head helper. Preserve the six FCR result fields.

Reject v1 with a message that it describes a phase0 store. It lacks
proposer identities, PTC deadlines, and exact vote slots. These cannot be
recovered from root, epoch, and one timeliness boolean.

Use path-limited commits for types, helpers, handlers, proofs, and harness
changes. Add pinned Gloas paths, Git blob identities, byte lengths, and
SHA-256 values to the manifest and source checker. Keep the phase0 sources
for the helpers inherited by Gloas. Run one Lean command at a time across
the shared machine. Run the source and trust audits, the Gloas conformance
suite, and full validation before completion.
