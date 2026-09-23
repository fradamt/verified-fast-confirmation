# Gloas payload-aware empty-slot discount

The upstream source pin is `6b9bd532cca16555e2f3282d757622ebff29743e`.
The local Python changes are `e40df4fe5` and `13f391516` on the
`fcr-gloas-pending-discount` branch. The pin audit checks the twelve unchanged
upstream blobs and the exact local Gloas overlay hash
`e62ba45c9024b6621493b9b2ac7a21913bd6426a61b3e02827e164ac4968742b`. Between the
old pin `477321355` and the new pin, upstream changes only the return type
annotation of `compute_weak_subjectivity_period` from `Uint64` to `Epoch` in
phase0, electra, and Gloas weak subjectivity files. None of the twelve pinned
blobs changes.

The empty-slot range and adversarial weight are unchanged. The discount counts
parent votes whose supported node has the payload status selected by the
child's parent bid, plus PENDING parent votes. A PENDING vote supports neither
the FULL nor the EMPTY child of its root. A parent vote for the other resolved
status supports the competing payload branch and must remain in the safety
threshold.

## Exact Python diff against upstream

````diff
diff --git a/specs/gloas/fast-confirmation.md b/specs/gloas/fast-confirmation.md
index cf1259fd9..2db7b981f 100644
--- a/specs/gloas/fast-confirmation.md
+++ b/specs/gloas/fast-confirmation.md
@@ -8,0 +9,2 @@
+    - [New `get_parent_payload_support_between_slots`](#new-get_parent_payload_support_between_slots)
+    - [Modified `compute_empty_slot_support_discount`](#modified-compute_empty_slot_support_discount)
@@ -30,0 +33,73 @@ def get_node_for_root(block_root: Root) -> ForkChoiceNode:
+#### New `get_parent_payload_support_between_slots`
+
+Count parent votes when they support the payload branch required by the child
+or have PENDING status. A PENDING parent vote supports neither resolved payload
+branch. A vote for the other resolved status supports the competing branch.
+
+```python
+def get_parent_payload_support_between_slots(
+    store: Store,
+    balance_source: BeaconState,
+    block_root: Root,
+    payload_status: PayloadStatus,
+    start_slot: Slot,
+    end_slot: Slot,
+) -> Gwei:
+    participants: Set[ValidatorIndex] = set()
+    for slot in range(start_slot, end_slot + 1):
+        participants.update(get_slot_committee(store, Slot(slot)))
+
+    unslashed_and_active_indices = [
+        i
+        for i in participants
+        if (
+            not balance_source.validators[i].slashed
+            and is_active_validator(balance_source.validators[i], get_current_epoch(balance_source))
+        )
+    ]
+
+    return Gwei(
+        sum(
+            balance_source.validators[i].effective_balance
+            for i in unslashed_and_active_indices
+            if (
+                i in store.latest_messages
+                and store.latest_messages[i].root == block_root
+                and i not in store.equivocating_indices
+                and get_supported_node(store, store.latest_messages[i]).payload_status
+                in (payload_status, PAYLOAD_STATUS_PENDING)
+            )
+        )
+    )
+```
+
+#### Modified `compute_empty_slot_support_discount`
+
+*Note*: The empty-slot range and adversarial weight are unchanged from Phase 0.
+
+```python
+def compute_empty_slot_support_discount(
+    store: Store, balance_source: BeaconState, block_root: Root
+) -> Gwei:
+    block = store.blocks[block_root]
+    parent_block = store.blocks[block.parent_root]
+    if parent_block.slot + 1 == block.slot:
+        return Gwei(0)
+
+    parent_support_in_empty_slots = get_parent_payload_support_between_slots(
+        store,
+        balance_source,
+        block.parent_root,
+        get_parent_payload_status(store, block),
+        parent_block.slot + 1,
+        block.slot - 1,
+    )
+    adversarial_weight = compute_adversarial_weight(
+        store, balance_source, parent_block.slot + 1, block.slot - 1
+    )
+    if parent_support_in_empty_slots > adversarial_weight:
+        return parent_support_in_empty_slots - adversarial_weight
+    else:
+        return Gwei(0)
+```
+
````

## Evidence and proof status

The g4 test `c93e16fba` uses real signed minimal-preset objects. With the
upstream rule, it confirms `c` at slot 6 and another honest store follows `P`
EMPTY. With this rule, support is 16 units and threshold is 19.6 units at
slot 6. The source does not confirm `c`. The receiver still follows `P` EMPTY.
The g3 projected-source replay gives discount 150 units, threshold 545 units,
and support 400 units at slot 11; it also does not confirm `c`.

The original upstream epoch-boundary test with validator 35 in the parent slot
55 and the empty slot 56 keeps its confirmation expectation. Its last parent
vote has PENDING status and can be discounted. The Gloas minimal reftest passes
on this branch.

The Lean model change is in `FastConfirmation/Spec/Model/LMDHelpers.lean`.
`Discount.lean` proves the matching-or-PENDING parent discount bound.
`Endpoint.lean` proves the source Oanc strip from actual confirmation and
the source V/pre partition. `OancTransport.lean` proves honest old-vote
transport, the complete-window opposite score bound, and transport of a
fixed Oanc debt when the aggregate growth facts hold. `LedgerV2.lean`
defines the status enemy. It includes old Byzantine votes on the ancestor
line and fits inside the existing complete-window Byzantine budget.

## Proof of the pending-parent status margin (G2-004)

Full validation passes. The accepted public theorem
`acceptedSpec_safety_next_slot` depends on the constructions below; the
trust audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

```text
┌──────────────────────────────────────┬─────────────────────────────────────────────┐
│ Step                                 │ Location                                    │
├──────────────────────────────────────┼─────────────────────────────────────────────┤
│ Margin consumed by a descent step    │ Endpoint.lean `PendingStatusMargin`         │
│ Certificate field `status_margin`    │ ArbitraryQueryMargin.lean,                  │
│                                      │ FutureCrossingMargin.lean                   │
│ Four call sites filled               │ SelectedCoveredMarginConstruction.lean      │
│                                      │ `selectedCoveredMarginSupplyAt_of_filter-   │
│                                      │ Supply_minimal`                             │
│ FULL parent availability             │ FullParentAvailability.lean                 │
│                                      │ `Execution.full_parent_payload_verified`    │
│ Status is a pending-parent child     │ StatusMarginConstruction.lean               │
│                                      │ `required_parent_status_mem_pending_minimal`│
│ Honest opposite classification       │ `endpoint_opposite_honest_classification`   │
│ Old opposite voter is not discounted │ `endpoint_opposite_not_parentPayloadStuck`  │
│ Strip with opposite debt (lo window) │ `endpoint_status_strip_lo`                  │
│ Direct-window and same-epoch arms    │ `statusMargin_loWindow_minimal`             │
│ Re-anchored certificate with debt    │ `intraEpochFuture_endpoint_inequality_opp`, │
│                                      │ `crossingEdgeFuture_endpoint_inequality_opp`│
│ Future-crossing and crossing arms    │ `statusMargin_crossing_minimal`             │
└──────────────────────────────────────┴─────────────────────────────────────────────┘
```

The argument has three parts.

1. An honest endpoint supporter of the opposite resolved status of the parent
   is sibling-stuck (`Xclass`), or it is an ancestor-class voter whose message
   is from the query window. The query holds the same message, so the voter is
   neither a matching nor a PENDING parent-payload supporter at the query.
   A PENDING message cannot support either resolved parent status.
2. The discount is at most the weight of the matching-or-PENDING parent-payload
   supporters (`Discount.lean` `support_discount_le_matching_parent_stuck`).
   The remaining ancestor-class weight stays in the confirmation strip. It
   pays for the opposite ancestor voters.
3. Byzantine opposite supporters lie in the parent-to-endpoint window. The
   crossing arms split them as in the crossing sibling bound, and they
   subtract relayed query equivocators on a crossing edge.

The earlier confirmed counterexample applies to the upstream rule; see
[the historical negative result](history/gloas-negative-result.md).
