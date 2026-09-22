# FCR conformance trace schema, versions 1 and 2


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
schema                 1 (legacy) or 2 (weak greatest-unrealized reset)

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
                       current_epoch_greatest_unrealized_checkpoint (v2 only),
                       previous_slot_head, current_slot_head
fcr_after              same fields, after the Python call

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

## v2 (weak greatest-unrealized reset)

Version 2 adds `current_epoch_greatest_unrealized_checkpoint` to `fcr_before`
and `fcr_after`. The weak rule copies the previous-epoch greatest-unrealized
snapshot into this field at epoch start. The field stays fixed through the
epoch, including the last slot when the previous-epoch snapshot is overwritten.
The getter uses this checkpoint for its reset after the certified restart, immediately before descendant search. The
certified observed checkpoint remains the anchor for positive confirmations.

The exporter emits version 2 when the Python FCR store has the new field.
It emits version 1 for older and strong stores. Both versions use the same
`Config`, `Store`, and four executable externals. For version 1, the Lean
parser sets the missing field to `store.finalized_checkpoint`. Each record is
independent, so this default does not reconstruct an earlier epoch-start value.

The weak Python helper has one extra derived check,
`safe_execution_block_hash`, for post-Bellatrix forks. It is not an
`FastConfirmationStore` field, is absent from the requested Altair run, and
cannot be rebuilt by this phase-0 Lean model because the projected block does
not contain execution-payload data. It is therefore not added to this trace
schema. A future post-Bellatrix port must add that block-payload projection
and bump the schema together with the runner.

All v1 records remain readable by the weak runner. The runner selects
`Weak.on_fast_confirmation`; records do not need a handler discriminator
because this branch has one weak-specific parity runner.

## Comparison
For each record the Lean runner constructs `FastConfirmationStore` from `store`
and `fcr_before`, runs `Weak.on_fast_confirmation cfg ext`, and compares the six
legacy `fcr_after` fields, plus the new checkpoint for version 2. Version 1 does
not compare an output field that was absent from its source record.
Output: one line per record,

`OK <test_id> <call_index>` or `MISMATCH <test_id> <call_index> <field> lean=<v> python=<v>`
or `MISSING_EXTERNAL ...`, then a summary line
`SUMMARY records=<n> ok=<n> mismatch=<n> missing_external=<n>`.
Exit status 0 only when mismatch and missing_external are both 0.
## Same-input containment check

Run `lake env lean --run scripts/conformance/lean/Conformance.lean --containment
<trace.jsonl>` to compare the frozen `Strong` rule and the `Weak` rule. Both
handlers receive the same reconstructed `store`, `fcr_before`, and external
answers. Each record is independent; neither output becomes the next input.
Repeated `--test <substring>` filters select test IDs by OR. The selected mode
streams the file. The existing single-path conformance command is unchanged.

Each line reports `EQUAL`, `WEAK_BELOW`, `WEAK_ABOVE`, or `INCOMPARABLE`, with
confirmed roots as `root@slot`, both current-epoch banked checkpoints as
`(epoch,root)`, and their equality. `WEAK_BELOW` means that the weak root is a
strict ancestor of the strong root. `WEAK_ABOVE` and `INCOMPARABLE` violate
handler containment. Getter fields compare `get_latest_confirmed` on the same
unchanged `fcr_before`; they do not include either handler's variable update.

`CONTAINMENT` totals handler results. `GETTER_CONTAINMENT` totals getter results.
`CONTAINMENT_COVERAGE` counts records with missing external answers and parse
errors. Each miss identifies the rule and handler/getter. A trace records only
the calls made by its source rule, so the other rule can request absent
answers. Such classifications use the existing fallback values and are
diagnostic; they do not establish containment for a complete external oracle.
The mode processes all records and exits nonzero for missing answers or parse
errors. A containment violation alone does not cause a nonzero exit.

Containment reconstruction removes repeated identical JSON external answers
before parsing their states. It keeps first occurrences in order and keeps
answers with different results. This preserves all first-match lookup outputs.
Containment lookups also check scalar query fields before full state equality.
