# Modeling choices

Each row states a choice in the executable or paper model, why it is used, and the property it does not establish. The model definitions are the source of truth; this page is a guide to their boundaries.

```text
┌────────────────────────────────────────┬────────────────────────────────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ Choice                                 │ Reason                                                         │ Cost                                                                     │
├────────────────────────────────────────┼────────────────────────────────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────┤
│ Natural numbers for slots and time     │ Makes finite arithmetic and schedule folds explicit.           │ No uint64 wraparound inside the model; EpochEndsFitUint64 limits the     │
│                                        │                                                                │ checked range.                                                           │
│ Totalized finite maps                  │ Lean functions must return on missing keys.                    │ Proofs need domain laws for reachable keys; arbitrary missing-key reads  │
│                                        │                                                                │ have defaults.                                                           │
│ Explicit loop fuel                     │ Makes recursive Python walks total.                            │ Equivalence needs a bound on reachable parent walks.                     │
│ Projected BeaconState and Store        │ Keeps only fields used by the rule and checks.                 │ Unused source-state behavior is outside the model.                       │
│ Opaque Externals                       │ Separates consensus logic from execution engine and            │ BeaconExternalsPremises must be justified by an implementation.          │
│                                        │ cryptography.                                                  │                                                                          │
│ Non-optimistic payload import          │ Every stored payload passed envelope validation, including     │ Optimistic fork-choice behavior is outside the theorem.                  │
│                                        │ VALID.                                                         │                                                                          │
│ Accepted event prefix semantics        │ Tracks a handler result at every scheduled prefix.             │ Schedules and successful handler assumptions need a concrete network     │
│                                        │                                                                │ argument.                                                                │
│ Static validator registry              │ Matches the paper balance setting over the horizon.            │ The safety theorem does not cover validator churn.                       │
│ Finite horizon                         │ Makes endpoints and next-slot receipt precise.                 │ Conclusions do not extend beyond the checked horizon.                    │
│ Global FFG and finalization laws       │ Connects opaque beacon transitions to exact checkpoint state.  │ The premises range over accepted prefixes beyond a conclusion endpoint.  │
│ Guarded FCR prediction support         │ Uses the spec proviso only when the selector guard is true.    │ Real voting agreement must supply that premise.                          │
│ Gloas payload-aware discount           │ Counts matching or PENDING parent votes in an empty slot.      │ Diverges from upstream rule; public fix at fcr-gloas-fix.                │
│ Envelope and data relay                │ Carries verified payload state to honest receivers.            │ The finite next-slot witness has no envelope event.                      │
│ Live block production                  │ Prevents stale cache reversal and supplies descendant votes.   │ Requires an honest-proposer block every slot from execution start.       │
│ Timely live FFG justification          │ Opens the rule restart gates at epoch boundaries.              │ Stronger than paper Assumption 6 and lacks a joint finite witness.       │
│ Paper exact rational balances          │ Keeps the paper threshold algebra direct.                      │ Does not by itself model executable integer rounding.                    │
│ Paper eligibility filter               │ Reuses the LMD head agreement result in HFC.                   │ The proof needs a separate never-filter premise and bridge.              │
│ Paper AU from block-contained votes    │ Ties justification to actual ancestry evidence.                │ OnChainAnchorInterface still supplies visibility and formation laws.     │
│ Algorithm 1 future confirmation input  │ Discharges the later monotonicity gate.                        │ SafeConfirmedAlg1Inputs is stronger than Assumption 6.                   │
└────────────────────────────────────────┴────────────────────────────────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

The source fork is `fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`). The independent weak rule is on branch `fcr-weak-synchrony` and tag `fcr-weak-synchrony-v1`; its live monotonicity proposition remains open. See [source map](SPEC_MAP.md), [paper map](PAPER_MAP.md), and [review guide](REVIEW_GUIDE.md).
