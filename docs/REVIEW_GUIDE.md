# Review guide

This page records known limits and their current status. The exact public propositions are in `FastConfirmationStatements/Review.lean`. `review_claims` in `FastConfirmationProofs/ReviewTheorem.lean` proves both fields. `scripts/Audit.lean` checks 14 public witnesses: seven executable-side results and seven paper results.

```text
┌────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Finding                        │ Status and evidence                                                                                                  │
├────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
│ Stored next-slot safety        │ Proved by confirmed_root_safe_from_next_slot under Execution.NextSlotSafetyPremises. It covers honest stored         │
│                                │ boundary outputs within a finite horizon.                                                                            │
│ Scheduled selected result      │ The premise theorem is a spec-correspondence lemma for the `find_latest_confirmed_descendant` note. It is not a    │
│                                │ review claim.                                                                                                      │
│ Live monotonicity              │ Proved by live_confirmed_root_monotonicity under two fields of LiveMonotonicityPremises and the safety execution     │
│                                │ bundle.                                                                                                              │
│ Optional in-slot queries       │ No general safety claim. StrictPrefixExtraQuery.extra_query_changes_head_counterexample and                          │
│                                │ PinnedEconomicsExtraQuery.extra_query_changes_head_counterexample refute exact-current variants.                     │
│ Live joint satisfiability      │ Open, user decision (S9-3). No finite run witnesses both live fields with Execution.NextSlotSafetyPremises.          │
│ Payload envelope exercise      │ Open, user decision (S9-6). The finite next-slot run has no envelope, so its envelope and data relay conditions      │
│                                │ hold vacuously.                                                                                                      │
│ Guarded target-edge exercise   │ Open, user decision (S9-5). The next-slot witness selector guard excludes selected current-target accepted edges.    │
│ Included-vote carrier relation │ Fixed (S9-1; W5) in 7dde0ef. Accepted inclusion requires membership in the carrier block's ordered FFG body.         │
│ Included-vote validation state │ Fixed (S9-2; W6) in 7dde0ef. The state follows target checkpoint preparation from a reachable keyed target block     │
│                                │ state in an honest in-horizon store. The prepared state need not itself be keyed.                                    │
│ Committee-union economics      │ Confirmed, open (W4). The fraction bound applies to every in-horizon span, including one slot. A global fault share  │
│                                │ does not establish it. This matches CommitteeHonestMajority in the repository's formal paper Assumption 2.           │
│ Weak full-bundle witness       │ Open, user decision (W3). No accepted run witnesses all weak headline premises with a non-anchor stored output.      │
│ Weak branch witnesses          │ Open, user decision (W11). The store fixture omits rollover and empty-slot PENDING discount; bank tests are vacuous. │
│ Opaque execution validation    │ Explicit abstraction. BeaconExternalsPremises and verified envelope events supply the engine verdict and             │
│                                │ deterministic behavior.                                                                                              │
│ Static registry                │ Explicit model idealisation. StaticValidatorSet covers the finite horizon; validator churn is outside the claim.     │
│ Paper Algorithm 1 monotonicity │ Proved conditionally. SafeConfirmedAlg1Inputs assumes future rule confirmation for each honest-view-safe block,      │
│                                │ stronger than paper Assumption 6.                                                                                    │
│ Weak live monotonicity         │ Open on the fcr-weak-synchrony branch. The weak threshold does not subtract equivocation, so a historical supporter  │
│                                │ can disappear without a matching reduction at an epoch boundary. Duty freshness can also remove votes. No            │
│                                │ full-premise execution counterexample is known.                                                                      │
│ Gloas discount                 │ The public fcr-gloas-fix tag uses parent votes with matching payload status or PENDING status. The upstream          │
│                                │ discount can count opposite resolved status and is unsafe in the recorded source example.                            │
└────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Live premise strength

`LiveMonotonicityPremises` has exactly two fields. `honest_block_each_slot` requires a block with an honest proposer index in every slot from the execution start through the interval. All honest stores know it by the next slot, and honest votes in that slot and later slots support descendants. `ffg_timely_justification` requires an epoch checkpoint block and exact unrealized justification at the last-slot call, with aligned head state at the next epoch start and a recent previous-head voting source. These are production and state-output requirements, not merely message delivery. Proposer-index membership does not prove authentication.

Paper Assumption 3.2 can allow a two-epoch FFG inclusion delay. The executable selector may close its gates before that inclusion appears. `get_latest_confirmed_eq_finalized_of_stale` and `Execution.confirmed_succ_eq_finalized_of_stale_call` show the stale fallback. `live_confirmed_root_monotonicity` is proved with timely closure; the finite witness does not establish that the live fields can hold jointly. The paper's Theorem 1 has no block-in-every-slot premise. The executable live claim is therefore stronger.

## Safety premise range

`Execution.NextSlotSafetyPremises` contains exact handler-successful prefix FFG semantics, a scheduled trajectory, completed-call premises, epoch arithmetic, anchor and checkpoint alignment, finalization delay, Assumption 3.2 support, and exact-link validity. The nested `Execution.CompletedFCRCallPremises` adds a fixed validator set, an economic span bound, Phase0 source coherence, a balance floor, a vote-delivery lookahead, and guarded FCR prediction support. None of its fields directly states the stored-root safety conclusion.

The instantaneous-synchrony finding is fixed for the execution safety path.
`NextSlotSynchronyPremises` records positive Δ with strict `A + Δ < S`.
The block, envelope, data, and evidence relays all require a source observation
at or before its slot deadline and a distinct receiver time at or after the
next boundary. Honest vote delivery uses the vote deadline. The unused
latest-message field and the old block-relay field have been removed;
`synchrony_and_delivery_iff_nextSlot` relates the two current bundles.
The public next-slot claims and their premise-field sets are unchanged.

Block and envelope exclusion is tested before the next-slot tick and only
permits a permanent finalized-guard conflict with a known parent. G4 derives
honest head-path admissibility. AU accountability handles other required
carriers. Ready blocks and envelopes precede the boundary vote handler;
data service and deterministic envelope validation justify payload acceptance.
The finite witness still does not exercise envelope delivery.

Evidence has no exclusion branch. The field models evidence retention and
application with known signer pubkeys, using a pubkey cache. Literal Python
uses the receiver's justified block state; an older state can lack a signer
whose deposit is newer and drop the slashing. The model instead uses immutable
pubkeys and a common domain in its single fork, with signer keys supplied by
the source justification that reaches the receiver. This deviation is explicit
in the field docstring and [modeling choices](MODELING_CHOICES.md). Late evidence
has a fresh cutoff observation when the scheduled FCR call reads it at slot
start. No validity-agreement field was added to the public external contract.

The global FFG and finalization premises still quantify over successful handler
prefixes beyond a safety endpoint when their declarations do. A finite endpoint
restricts the conclusion, not those premise quantifiers.
`scripts/check_synchrony_corners.py` checks the cutoff shapes and rejects old
relay fields, missing cutoffs, same-second receiver states, and tick-time
exemptions. Full validation also checks all 14 public witnesses.

## Python source and conformance

The source of record is fork `fradamt/consensus-specs`, tag `fcr-gloas-fix` (`13f391516`). Branch `fcr-gloas-discount-fix` starts at upstream master `63a81afa6` and adds only the public discount fix. Branch `fcr-weak-synchrony` and tag `fcr-weak-synchrony-v1` contain the independent weak rule. The source map is [SPEC_MAP.md](SPEC_MAP.md). The local [conformance harness](conformance.md) compares projected Python and Lean FCR observations. A matching trace does not prove the opaque external contracts or all reachable executions.

## Weak branch status

The `fcr-weak-synchrony` branch and tag `fcr-weak-synchrony-v1` have 55 trust-audit entries: 14 earlier executable and paper witnesses plus 41 weak-side results. The two full weak safety headlines take the common top-level inputs B, hji, hanchor, hboundary, hDelay, hpaper, P, V, hW, hCbase, and hfit. The endpoint also takes hw, hnm, hnext, and hHm. The exact anchor and known-walk facts are derived inside the proof; they are not headline binders. The weak live monotonicity proposition remains open. Its equivocation-budget and duty-freshness obligations remain unresolved at epoch boundaries.

## Mechanical checks

`scripts/validate.sh --fast` checks source pinning, names, the Statements import boundary, and hygiene. Full `scripts/validate.sh` also builds the libraries, checks imports, checks reachability and surface shape, and runs `scripts/Audit.lean`. The trust audit permits only `propext`, `Classical.choice`, and `Quot.sound`. Read `FastConfirmationWitnesses/Index.lean` for each non-vacuity witness and counterexample.
