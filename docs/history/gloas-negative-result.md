# G3 negative result: payload branch selection

> **History.** This record applies to the upstream discount rule before the
> payload-aware change in [the spec deviation](../gloas-spec-deviation.md).
> The current Gloas proof constructs the pending-parent status margin in
> `FastConfirmation/Spec/Proof/StatusMarginConstruction.lean`. The G2b port
> archive was removed after commit `28faf6d`.

G2-004 is false on the exact-source execution below. Payload-envelope relay
closes G2-003, but it does not make the root ledger control payload branches.
The G3 lane stops without adding a branch-weight premise. The port does not
establish Gloas safety, and full validation fails at `Endpoint.ledger_descendStep`.

## Reproduce

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/conformance/python/gloas_accepted_payload_branch_obstacle.py --consensus-repo /home/fradamt/lean/consensus-specs
```

The command executes unchanged fork-choice, handler, and FCR function bodies
from Git objects at `477321355d48d527e7e1e4d572f6a40a0b41072a`. It exits 0 when
all negative-result assertions pass. It uses the same abstract external
boundary as the Lean model. It is not a generated full-state pyspec trace or
a kernel construction of every accepted-theorem assumption record.

`scripts/GloasPayloadBranchObstacle.lean` remains a separate local,
non-accepted counterexample. It is not the evidence for this STOP.

## Execution

There are 3,200 active validators with balance `U = 1,000,000,000` Gwei.
Each of the 32 slots has a disjoint committee of 100 validators. Slot 0 has
no Byzantine validators; each later committee has 25. The script checks
the Byzantine fraction and committee estimate for every in-horizon interval.
The verification horizon is epoch 1. There are two honest store histories;
each honest validator uses one of these histories for its whole execution.

All nodes start from the same committed anchor, root 1 at slot 0. At second
12, fifty slot-1 honest validators vote for its EMPTY head. The source receives
the anchor envelope at second 13. Twenty-five honest validators then vote for
the source FULL head. The receiver gets the envelope at second 23, the last
second of slot 1. Thus the new relay field holds. Both views accept all
honest singleton votes at second 24.

In each of slots 1 through 6, the Byzantine committee members send FULL votes
to the source and EMPTY votes to the receiver. Honest committees supply
25 FULL and 50 EMPTY votes. The source sees a tie and selects FULL. The
receiver selects EMPTY. No node receives both Byzantine versions, and no
slashing event is scheduled. The honest votes in later slots still follow
the heads those stores compute, although both nodes now have the envelope.

At second 85, both views accept child 2 at slot 7 and its envelope. The child
uses the FULL payload of parent 1. In slots 7 onward, all 75 honest committee
members use the source history and vote for child 2. Byzantine members vote
for child 2 at the source and for parent 1 EMPTY at the receiver. Every honest
vote is delivered as its exact singleton event to both views at the next
slot boundary. The script checks all 2,425 honest votes and all 4,850 honest
singleton deliveries, including the last receipt at second 384.

Both FCR stores start with `get_fast_confirmation_store`. The script calls
`on_fast_confirmation` once at each in-horizon slot boundary after delivery.
It does not seed a confirmed child or inject a non-head honest vote.

```text
┌──────┬──────────────────┬───────────────┬───────────┬────────────┬───────────┬────────────┐
│ Slot │ Source confirmed │ Child support │ Threshold │ Discount   │ FULL at w │ EMPTY at w │
├──────┼──────────────────┼───────────────┼───────────┼────────────┼───────────┼────────────┤
│ 10   │ 1                │ 300U          │ 320U      │ 450U       │ 375U      │ 525U       │
│ 11   │ 2                │ 400U          │ 395U      │ 450U       │ 450U      │ 550U       │
│ 12   │ 2                │ 500U          │ 470U      │ 450U       │ 525U      │ 575U       │
└──────┴──────────────────┴───────────────┴───────────┴────────────┴───────────┴────────────┘
```

At slot 12, the receiver head is root 1 EMPTY. It is not a descendant of
confirmed child 2. Both payloads are verified at both views, and every
index-1 attestation passes its payload check.

The old ledger also holds at this endpoint. For slots 1 through 11,
`S = 375U`, `X = 0`, `B = 275U`, and `P = 40U`, so `X + B + P + 1 ≤ S`.
The margin is `60U` before the strict one-Gwei increment. However, honest
ancestor votes contribute `150U` to FULL and `300U` to EMPTY. The receiver's
`275U` of Byzantine ancestor votes adds to EMPTY. The resulting payload
weights are `525U < 575U`.

The empty-slot discount counts support for the ancestor root without its
payload status. Here it discounts `450U` while only `150U` of honest ancestor
support is compatible with the child's FULL branch. This is the missing
payload-status accounting in G2-004.

## Accepted-premise boundary

Honest votes use their actual Gloas heads and the validator index rule. A
fixed signed-data table is defined before execution. The validity external
rejects the empty default state, confines indices to their committees, and
accepts honest data only from that fixed table. Each actual honest vote is
checked against the table. Slot processing preserves the registry. The
transition external accepts only the specified child from the committed
anchor state; other inputs reject. Epoch processing clamps future checkpoint
epochs on malformed inputs. These completions meet the m2 external laws
without changing the observed execution. The source initializer checks the
anchor state commitment.

Block and envelope histories are identical after their relay deadlines.
Payload persistence extends those checks to all later seconds. Honest
attestations are delivered at the mandated boundary, and all handler calls
succeed. Honest validators sign once in the epoch and never sign conflicting
FFG data. There are no PTC events. The accepted `HonestBehavior` record places
no PTC duty or PTC relay condition on this execution.

The remaining FFG interfaces admit constant anchor selectors in this first
epoch. The inclusion relation can be empty and the anchor can be the only
formed checkpoint. Exact-link validity is then vacuous. Paper A3.2 requires
an in-horizon endpoint at least two epochs later, so it is vacuous at this
horizon. Every in-horizon honest target is `(0, anchor)`, which supplies the
helper's honest-target proviso. Finalization delay holds through its anchor
case. Checkpoint projection sends either root at epoch 0 to the anchor and
the child at a positive epoch to itself. This is a source-level premise
audit, not a Lean kernel witness for the complete accepted bundle.

## Missing premise, not added

The exact local condition needed by `descendStep_of_dom` is that the pending
parent's lexicographic argmax selects the payload branch used by the child:

```lean
(get_node_children store (get_filtered_block_tree cfg store)
    (ForkChoiceNode.mk h .pending)).argmax
    (fun child => toLex (get_weight cfg store child,
      toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
  some (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c)))
```

For an older parent with both payload branches available, a sufficient
weight form is: the required branch's attestation score exceeds the opposite
branch's attestation score plus the maximum proposer score. The score must
include ancestor-root votes and all descendants, even those outside the
filtered beacon sibling list. This is the smallest local branch-choice
condition absent from the existing ledger interface. It has not been added
to any assumption record. A repair to the FCR rule could instead make the
ancestor-support discount depend on payload status; that is outside this lane.
