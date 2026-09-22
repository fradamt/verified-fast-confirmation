# FCR conformance trace schema, version 1

One trace file is JSON Lines: one JSON object per executed `on_fast_confirmation`
call in the Python reference tests. The Python exporter writes it; the Lean
runner reads it, rebuilds the store, runs the Lean `on_fast_confirmation`, and
compares. Both sides implement this document exactly. Do not change it without
updating both sides and bumping `schema`.

## Encoding rules
- `Root` values: `0x` + 64 lowercase hex characters (32 bytes). Lean maps a root
  to `Nat` by big-endian value; lexicographic byte order equals numeric order.
- Integers (`Slot`, `Epoch`, `Gwei`, indices, `time`, `genesis_time`): JSON
  numbers. Values above 2^53 are written as decimal strings; Lean accepts both.
- `Checkpoint`: `{"epoch": n, "root": "0x.."}`.
- Booleans as JSON booleans.
- A `state` is the projection Lean's `BeaconState` reads:
  `{"id": "0x..hash_tree_root of the full state..", "genesis_time": n, "slot": n,
    "validators": [{"effective_balance": n, "slashed": b, "activation_epoch": n,
    "exit_epoch": n}, ...], "current_justified_checkpoint": cp,
    "finalized_checkpoint": cp}`.
  `id` is informational for humans. Lean matches states structurally on the
  other five fields, in order, exactly.

## Record fields
```text
schema                 1
test_id                pytest node id
fork                   e.g. "altair"
preset                 "minimal" | "mainnet"
call_index             0-based index of this call inside the test
config                 slots_per_epoch, slot_duration_ms, proposer_score_boost,
                       confirmation_byzantine_threshold,
                       committee_weight_estimation_adjustment_factor,
                       effective_balance_increment, attestation_due_bps,
                       min_seed_lookahead
store                  time, genesis_time, justified_checkpoint,
                       finalized_checkpoint, unrealized_justified_checkpoint,
                       unrealized_finalized_checkpoint, proposer_boost_root,
                       equivocating_indices [n...] (sorted),
                       blocks [{root, slot, parent_root}] in dict insertion order,
                       block_states [{root, state}],
                       block_timeliness [{root, timely}],
                       checkpoint_states [{checkpoint, state}],
                       latest_messages [{index, epoch, root}] (sorted by index),
                       unrealized_justifications [{root, checkpoint}]
fcr_before             confirmed_root,
                       previous_epoch_observed_justified_checkpoint,
                       current_epoch_observed_justified_checkpoint,
                       previous_epoch_greatest_unrealized_checkpoint,
                       previous_slot_head, current_slot_head
fcr_after              same six fields, after the Python call
externals              recorded answers, see below
```

The Python `store` is snapshotted immediately before the call. The FCR call does
not mutate the fork-choice store; if it does in some fork, the exporter must
abort with an error naming the field.

## Externals
During the Python call the exporter wraps exactly these spec functions and
records every invocation:
```text
get_beacon_committee                    [{state, slot, index, result: [n...]}]
get_committee_count_per_slot            [{state, epoch, result: n}]
process_slots                           [{state, slot, result: state}]
process_justification_and_finalization  [{state, result: state}]
```
`state` is the projection of the argument state **before** the call;
`result` for the two mutating functions is the projection **after** the call.
Because Lean's state is a projection, two different full states can share one
projection. The exporter must check inside each record that equal
`(projection, other args)` keys never map to different results; if they do it
must abort with `projection ambiguity` and the test id. Lean looks answers up by
structural equality on `(projection, args)`. A lookup miss is reported as a
`MISSING_EXTERNAL <function> <args>` mismatch, never defaulted silently.
`state_transition` and `is_valid_indexed_attestation` are not called by
`on_fast_confirmation`; they are not recorded and Lean instantiates them with
constant functions that are never reached (`fun _ _ => none`, `fun _ _ => false`).

## Comparison
For each record the Lean runner constructs `FastConfirmationStore` from `store`
and `fcr_before`, runs `on_fast_confirmation cfg ext`, and compares the six
`fcr_after` fields. Output: one line per record,
`OK <test_id> <call_index>` or `MISMATCH <test_id> <call_index> <field> lean=<v> python=<v>`
or `MISSING_EXTERNAL ...`, then a summary line
`SUMMARY records=<n> ok=<n> mismatch=<n> missing_external=<n>`.
Exit status 0 only when mismatch and missing_external are both 0.
