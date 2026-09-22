# FCR conformance trace schema, version 2

One JSON Lines record describes one Gloas `on_fast_confirmation` call.
The exporter snapshots the source store, records `get_head`, runs FCR, and
records the result. The Lean runner rebuilds the projections and compares
both the head node and the six FCR fields. The schema value is the integer
`2`. Version 1 describes a phase0 store. Both readers reject it with this
message: `schema v1 describes a phase0 store; schema v2 is required`.

## Encoding

- Roots and opaque identities use `0x` followed by 64 lowercase hex digits.
  Lean maps them to `Nat` in big-endian order.
- Nonnegative integers use JSON numbers up to `2^53`. Larger values use
  decimal strings. Readers accept both forms.
- Booleans use JSON booleans. An unset PTC vote uses JSON `null`.
- A checkpoint is `{"epoch": n, "root": "0x.."}`.
- A node is `{"root": "0x..", "payload_status": n}`. Status 0 means EMPTY,
  1 means FULL, and 2 means PENDING. A status is not inferred from its root.
- Lists retain source order. Root maps use lists of entries in source dict
  insertion order. Validator messages use increasing validator index order.

## Record fields

```text
┌─────────────┬──────────────────────────────────────────────────────────┐
│ schema      │ 2                                                        │
│ fork        │ "gloas"                                                  │
│ preset      │ "minimal" or "mainnet"                                   │
│ test_id     │ pytest node id                                           │
│ call_index  │ zero-based call index within the test                    │
│ head_before │ node from get_head before FCR                            │
│ config      │ slots_per_epoch, slot_duration_ms, proposer_score_boost, │
│             │ confirmation_byzantine_threshold,                        │
│             │ committee_weight_estimation_adjustment_factor,           │
│             │ effective_balance_increment, attestation_due_bps,        │
│             │ min_seed_lookahead, ptc_size, payload_due_bps,           │
│             │ payload_attestation_due_bps, reorg_head_weight_threshold │
│ store       │ the projection below, before FCR                         │
│ fcr_before  │ six FCR fields below, before FCR                         │
│ fcr_after   │ six FCR fields below, after FCR                          │
│ externals   │ recorded source calls below                              │
└─────────────┴──────────────────────────────────────────────────────────┘
```

`attestation_due_bps` records `ATTESTATION_DUE_BPS_GLOAS`. Each PTC threshold
is `ptc_size / 2`, with integer division. The exporter rejects a call if FCR
changes any projected fork-choice store field.

The optional root field `safe_execution_block_hash_after` records the source
`get_safe_execution_block_hash` result after FCR. New exports include this
field. The runner compares the model helper when the field is present.
Earlier v2 records remain valid and skip this comparison. In Gloas the
safe execution hash is the confirmed block's `parent_block_hash`.

## State projection

A state contains these fields:

```text
┌──────────────────────────────┬──────────────────────────────────────────────────────┐
│ id                           │ hash_tree_root of the full source state              │
│ slot, genesis_time           │ nonnegative integers                                 │
│ validators                   │ [{effective_balance, slashed,                        │
│                              │ activation_epoch, exit_epoch}, ...]                  │
│ current_justified_checkpoint │ checkpoint                                           │
│ finalized_checkpoint         │ checkpoint                                           │
│ beacon_committee_reads       │ [{slot, index, result: [validator_index, ...]}, ...] │
│ committee_count_reads        │ [{epoch, result: count}, ...]                        │
└──────────────────────────────┴──────────────────────────────────────────────────────┘
```

The state `id` is a semantic opaque identity for the full source state.
The runner sets `BeaconState.source_identity` to `some id`. Lean equality
uses this identity and all other projected fields, including both finite
read lists. The exporter collects all reached
committee and count queries, including those reached by Gloas `get_head`. It also fills the potential
`is_head_weak` query domain for the proposer-boost parent's state. This
covers head scoring paths that a later call can take on the same snapshot.
After the source call, it attaches the resulting lists to every copy of each
state projection. Committee reads are sorted by `(slot, index)`; count reads
are sorted by epoch. Duplicate queries with the same result produce one
read-list entry. Committee results retain order and repeated indices.

Read lists are complete for the queries reached in the record. The runner
reports a missing external if its execution requests a committee or count
that is absent from the state's read list. It must not silently use the
model's total default for an unrecorded query.

## Store projection

The store has these fields:

```text
┌─────────────────────────────────┬──────────────────────────────────────────────┐
│ time, genesis_time              │ nonnegative integers                         │
│ justified_checkpoint            │ checkpoint                                   │
│ finalized_checkpoint            │ checkpoint                                   │
│ unrealized_justified_checkpoint │ checkpoint                                   │
│ unrealized_finalized_checkpoint │ checkpoint                                   │
│ proposer_boost_root             │ root                                         │
│ equivocating_indices            │ sorted validator indices                     │
│ blocks                          │ block entries, below                         │
│ block_states                    │ [{root, state}, ...]                         │
│ block_timeliness                │ [{root, timely: [attestation, ptc]}, ...]    │
│ checkpoint_states               │ [{checkpoint, state}, ...]                   │
│ latest_messages                 │ [{index, slot, root, payload_present}, ...]  │
│ unrealized_justifications       │ [{root, checkpoint}, ...]                    │
│ payloads                        │ [{root, beacon_block_root,                   │
│                                 │ parent_beacon_block_root, identity}, ...]    │
│ payload_timeliness_vote         │ [{root, votes: [null or boolean, ...]}, ...] │
│ payload_data_availability_vote  │ [{root, votes: [null or boolean, ...]}, ...] │
└─────────────────────────────────┴──────────────────────────────────────────────┘
```

Each block entry has `root`, `slot`, `parent_root`, `proposer_index`,
`parent_block_hash`, `block_hash`, and `payload_attestations`. The two block
hash fields come from `body.signed_execution_payload_bid.message`.
Each payload attestation contains `attesting_indices`, `data`, and
`signature`. The exporter calls the source `get_indexed_payload_attestation`
with the stored post-state to obtain the indices. Data contains `slot`,
`beacon_block_root`, `payload_present`, and `blob_data_available`.
The signature field is the hash-tree-root of the source signature.

A payload map entry represents a delivered and verified envelope. Its map
key equals `beacon_block_root`. Its opaque `identity` is the hash-tree-root
of that envelope. An absent entry means the payload is not verified. Each
PTC vote list has exactly `ptc_size` positions. Local verified-payload
membership and PTC payload/data votes are separate observations. This trace
checks FCR on a snapshot; it does not replay the envelope handler's sidecar
or execution-engine validation.

## FCR projection

These six fields remain roots or checkpoints:

```text
confirmed_root
previous_epoch_observed_justified_checkpoint
current_epoch_observed_justified_checkpoint
previous_epoch_greatest_unrealized_checkpoint
previous_slot_head
current_slot_head
```

## Externals

The exporter wraps these source functions while it obtains `head_before`
and runs FCR:

```text
┌────────────────────────────────────────┬───────────────────────────────────────────────┐
│ get_beacon_committee                   │ [{state, slot, index, result: [n, ...]}, ...] │
│ get_committee_count_per_slot           │ [{state, epoch, result: n}, ...]              │
│ process_slots                          │ [{state, slot, result: state}, ...]           │
│ process_justification_and_finalization │ [{state, result: state}, ...]                 │
└────────────────────────────────────────┴───────────────────────────────────────────────┘
```

Argument states describe the state before a call. Result states describe
it after a mutating call. After it attaches finite read views, the exporter
checks that equal projected input keys have equal projected results.
This check includes source state IDs on both sides. Distinct full source
states can give different external answers even when their other projected
fields are equal. Equal identities bind equal source states. Every external
state result carries the identity of its exact full source result.
A conflict aborts export with `projection ambiguity` and the test ID.
A missing Lean lookup is `MISSING_EXTERNAL`, never a silent default.
Handler-only external functions are not reached by FCR and are not part
of this snapshot trace.

## Result

The runner prints one result per record. It compares `head_before`,
including the payload status, then the six FCR fields, then the optional
safe execution hash. A failure names
the first different field and gives the Lean and source values. It prints:

```text
SUMMARY records=<n> ok=<n> mismatch=<n> missing_external=<n>
```

A successful run requires at least one record and no mismatch or missing
external. The exporter script preserves pytest and runner failure codes.
