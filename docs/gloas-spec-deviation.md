# Gloas payload-aware empty-slot discount

The upstream source pin is `6b9bd532cca16555e2f3282d757622ebff29743e`.
The local Python change is `e40df4fe5`. The pin audit checks the twelve
unchanged upstream blobs and the exact local Gloas overlay hash. Between the
old pin `477321355` and the new pin, upstream changes only the return type
annotation of `compute_weak_subjectivity_period` from `Uint64` to `Epoch` in
phase0, electra, and Gloas weak subjectivity files. None of the twelve pinned
blobs changes.

The empty-slot range and adversarial weight are unchanged. The discount counts
only parent votes whose supported node has the payload status selected by the
child's parent bid. A parent vote for the other status supports the competing
payload branch and must remain in the safety threshold.

## Exact Python diff against upstream

````diff
diff --git a/specs/gloas/fast-confirmation.md b/specs/gloas/fast-confirmation.md
index cf1259fd9..ae638befa 100644
--- a/specs/gloas/fast-confirmation.md
+++ b/specs/gloas/fast-confirmation.md
@@ -8,0 +9,2 @@
+    - [New `get_parent_payload_support_between_slots`](#new-get_parent_payload_support_between_slots)
+    - [Modified `compute_empty_slot_support_discount`](#modified-compute_empty_slot_support_discount)
@@ -30,0 +33,71 @@ def get_node_for_root(block_root: Root) -> ForkChoiceNode:
+#### New `get_parent_payload_support_between_slots`
+
+Count parent votes only when they support the payload branch required by the
+child. A parent vote for the other payload status supports the competing branch.
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
+                and get_supported_node(store, store.latest_messages[i]).payload_status == payload_status
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

The Lean implementation is in `FastConfirmation/Spec/Model/LMDHelpers.lean`.
Its discount bound is in `FastConfirmation/Spec/Proof/Discount.lean`.
`FastConfirmation/Spec/Proof/Endpoint.lean:137` is still open. Its current
`ledger_descendStep` statement is false: at the g3 receiver in slot 12,
`hchild`, `hbside`, `hledger`, and `hsib` hold, but the pending parent selects
EMPTY while `c` needs FULL. This run does not confirm `c`; it refutes the
local lemma, not the repaired safety rule. See `docs/gloas-negative-result.md`
for the old rule's confirmed counterexample and the g5 lane report for the
new local proof obstruction.
