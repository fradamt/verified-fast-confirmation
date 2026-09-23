# Spec-model design — `FastConfirmationModel/`

Gloas status: G2-003 and G2-004 are proved with the payload-aware discount.
Full validation passed at commit `6d478e7`. The accepted Gloas theorem is
proved under the stated assumption bundle. See [the exact rule change and
proof status](gloas-spec-deviation.md).

This repository models both the FCR **paper** (arXiv:2405.00549) and the FCR
**consensus spec**. This document describes the consensus-spec layer:

- **Source of truth**:
  [`consensus-specs/specs/phase0/fast-confirmation.md`](https://github.com/ethereum/consensus-specs/blob/6b9bd532cca16555e2f3282d757622ebff29743e/specs/phase0/fast-confirmation.md)
  at public commit `6b9bd532cca16555e2f3282d757622ebff29743e`.
- **Environment**: Gloas fork choice and its FCR overlay, with inherited
  phase0 arithmetic and FCR helpers, at the same commit except for the
  [payload-aware discount](gloas-spec-deviation.md). The complete delta
  and external projection contract are in
  [gloas-model-design.md](gloas-model-design.md).
- **Scope**: Gloas is the sole fork-choice model. The numbered decisions below
  describe the inherited projection conventions. The Gloas design supersedes
  their root-only node, epoch-only latest-message, single-deadline, and
  head-fuel details. Historical phase0 traces do not instantiate Gloas.

`FastConfirmationPaper/` contains a separate formalization of the paper. The
consensus-spec layer is `FastConfirmationModel/` and imports only Mathlib—not
the paper-model modules—so the accepted spec proof stands alone. No formal
refinement theorem connecting the two models is currently claimed.

## Faithfulness contract

Every function defined **inside** `fast-confirmation.md` is transcribed 1:1,
in document order, with the **exact python name** (snake_case, e.g.
`is_one_confirmed`, `get_latest_confirmed`) and the exact control-flow shape.
The same holds for the fork-choice helpers the FCR document calls (they come
from `fork-choice.md`, still executable spec) and the handful of trivial
beacon-chain helpers (`compute_epoch_at_slot`, `is_active_validator`, …).
Snake_case is a deliberate faithfulness device: a reviewer can diff each Lean
def against the python block line-by-line. `docs/spec-annotation.md` carries
the per-function mapping table and lists every deviation.

Abstraction enters **only** where the spec itself bottoms out in machinery that
is out of scope for the rule (committee shuffling, state transition):

| Abstract external (bundled in `Externals`) | Spec origin |
|---|---|
| `get_beacon_committee : BeaconState → Slot → ℕ → List ValidatorIndex` | beacon-chain shuffling |
| `get_committee_count_per_slot : BeaconState → Epoch → ℕ` | beacon-chain |
| `process_slots : BeaconState → Slot → BeaconState` | state transition (used by `get_pulled_up_head_state`) |
| `state_transition : BeaconState → SignedBeaconBlock → Option BeaconState` | phase0 state transition (`on_block`; `none` = invalid) |
| `process_justification_and_finalization : BeaconState → BeaconState` | epoch processing (`compute_pulled_up_tip`) |
| `is_valid_indexed_attestation : BeaconState → IndexedAttestation → Bool` | beacon-chain index/signature validity |

This is coarser than the spec's own declared override seam ("State helpers …
Implementations MAY override"): the State-helper functions themselves
(`get_slot_committee`, `get_pulled_up_head_state`, the balance sources) **are
transcribed**, on top of these primitives (the last three added by
decision 13).

## Modelling decisions

1. **Numbers.** `Slot`/`Epoch`/`Gwei`/`ValidatorIndex` are `ℕ` abbreviations.
   Python `uint64` arithmetic is modelled as unbounded `ℕ`: `//` = `Nat.div`
   (`/`), python `-` = truncated `Nat` subtraction. Every subtraction in the
   spec is audited in `spec-annotation.md`; each is either explicitly guarded
   by the spec (`compute_safety_threshold` underflow guard,
   `compute_adversarial_weight`/`compute_empty_slot_support_discount`
   comparisons, `min`-capped `compute_honest_ffg_support_for_current_target`)
   or non-negative in the spec's own domain (`Slot(current_slot - 1)` with
   `current_slot ≥ 1`, `total_active_balance - ffg_weight_till_now` within an
   epoch). Where python `uint64` would *raise* on underflow, `ℕ` truncates to
   `0`; no FCR code path reaches such a state from a well-formed store, and the
   annotation table flags each site.

2. **`Root` is a type parameter** `{Root : Type*} [LinearOrder Root] [Inhabited Root]`
   (hash digests are opaque 32-byte strings; `LinearOrder` models the
   lexicographic tie-break in `get_head`, `Inhabited.default` models `Root()`
   in the `proposer_boost_root` check). Structures (`Checkpoint`,
   `ForkChoiceNode`, `LatestMessage`, …) are parameterized by `Root`.
   `ForkChoiceNode` is kept as a distinct structure (not collapsed into `Root`)
   exactly because the spec introduced it for upgradability (Gloas modifies it).

3. **Python dicts → total functions + explicit domains.** Python map lookups
   (`store.blocks[root]`) raise `KeyError` outside the domain; the spec only
   ever looks up keys it assumes present. We totalize: `blocks : Root →
   BeaconBlock` returns junk (`Inhabited.default`) outside the domain, and the
   domain `block_roots : List Root` is carried separately because
   `filter_block_tree` **iterates** over the dict's keys — a `List` (not a
   `Finset`) because python dicts iterate in insertion order (and it keeps the
   model computable); key distinctness is the
   `WellFormedStore.block_roots_nodup` invariant (Execution.lean).
   Same treatment for `block_states`, `checkpoint_states`,
   `unrealized_justifications` (no iteration ⇒ no domain field needed);
   `latest_messages : ValidatorIndex → Option (LatestMessage Root)` keeps
   `Option` because the spec tests membership (`i in store.latest_messages`);
   `block_timeliness : Root → Option Bool` also keeps `Option` (never read by
   the FCR, and its fork-choice consumers do membership-style access — no
   junk default is warranted). `equivocating_indices : Finset`. Junk values are unreachable in the
   well-formed domain; the `WellFormedStore` predicate (Execution.lean)
   records these domain invariants.

4. **Unbounded recursion → fuel.** Python's `get_ancestor` (recursion),
   `get_ancestor_roots`/`get_head` (while-loops), and `filter_block_tree`
   (recursion over children) terminate only on well-formed stores (parent slots
   strictly decrease; the block relation is a tree). We use the paper project's
   established fuel pattern: an `_aux (fuel : ℕ)` worker plus a wrapper that
   supplies a fuel that provably suffices under well-formedness
   (the *start block's* slot `+ 1` for parent-walks — an upper bound on the
   number of strictly-slot-decreasing steps regardless of the target slot —
   and, for tree walks, the walked root list's length `+ 1` —
   `block_roots.length + 1` in `get_filtered_block_tree`, the *filtered*
   list's `length + 1` in `get_head`). On
   fuel exhaustion the worker returns a python-divergence value (the node
   reached so far for `get_ancestor`/`get_head`, `(false, [])` for
   `filter_block_tree`, `none` for `get_ancestor_roots`); this is outside the
   well-formed domain, exactly where python would loop forever or `KeyError`.

5. **`get_ancestor_roots`'s failure path** ("Return empty list if
   `terminal_root` is not in the chain") is modelled with an `Option (List
   Root)` worker: `none` = terminal never reached (python's fall-through
   `return []`), `some l` = python's in-loop `return ancestor_roots`. The
   wrapper `getD []` collapses both to the spec's observable behavior. The list
   is oldest→newest (python `insert(0, ·)`), terminal-exclusive,
   block-inclusive — order is load-bearing for the confirmation loops.

6. **Mutation → state-passing.** `update_fast_confirmation_variables` and
   `on_fast_confirmation` mutate `fcr_store` in python; they become
   `FastConfirmationStore → FastConfirmationStore`. Field-update *order*
   matters (`previous_slot_head := current_slot_head` before `current_slot_head
   := get_head`) and is preserved by the functional record update, which reads
   all old fields. `find_latest_confirmed_descendant`'s two sequential
   `for … break` loops over `canonical_roots` become structural-recursion
   helpers over the `List Root` carrying the loop-mutable accumulator
   (`confirmed_root` / `tentative_confirmed_root`); a `break` = returning the
   accumulator, loop fall-through = recursing on the tail.

7. **`max(children, key=λc: (weight, root))`** in `get_head` is
   `List.argmax` over the children list with the lexicographic key
   `(get_weight store c, c.root)` (mathlib `Prod.Lex` linear order). Children
   have pairwise-distinct roots, so the key is injective and the maximum is
   unique — the model is deterministic and order-independent, like python
   (whose tie-break by `child.root` is total for the same reason).

8. **`filter_block_tree`'s output dict** accumulates the roots it marks
   viable; values are always `store.blocks[root]`, so the model returns the
   *root list* (`List Root`, in dict-insertion order: each child call's
   additions first, then the parent when viable) instead of a map.
   `get_node_children` then filters that list by parent (values would be
   redundant lookups); python's `any(children)` is list non-emptiness
   (non-empty `bytes` are truthy).

9. **Constants → a `Config` record** (`slots_per_epoch` with `0 <` proof,
   `slot_duration_ms` with `0 <` proof — excluding the degenerate config where
   Lean's `x / 0 = 0` would silently diverge from python's
   `ZeroDivisionError` in `get_slots_since_genesis`, `proposer_score_boost`,
   `confirmation_byzantine_threshold` with a `≤ 25` proof — the spec table's
   normative "Max. Value" column, which also keeps the
   `100 - CONFIRMATION_BYZANTINE_THRESHOLD` subtraction non-truncating,
   `committee_weight_estimation_adjustment_factor`,
   `effective_balance_increment`), plus `mainnet_config` recording the spec
   values (32 / 12000 / 40 / 25 / 5 / 10⁹). `GENESIS_SLOT = GENESIS_EPOCH = 0`
   are hardcoded as in the spec. The literals `1000`/`999` in
   `adjust_committee_weight_estimate_to_ensure_safety` are the spec's own
   per-mille encoding and stay literal.

10. **`BeaconState` is the projection the FCR reads**: `slot`,
    `validators : List Validator` (`effective_balance`, `slashed`,
    `activation_epoch`, `exit_epoch` — the fields `is_active_validator` and the
    balance sums touch), `current_justified_checkpoint` (read by
    `get_voting_source`). `state.validators[i]` totalizes with `List.getD`.
    `enumerate` in `get_active_validator_indices` becomes a filter over
    `List.range validators.length` (order-preserving).

## Gloas payload-envelope synchrony

The accepted synchrony assumption has separate `envelope_delivery` and
`data_availability_relay` fields. A verified envelope reaches each honest
receiver at an event position where its block is known, by the same deadline
as `block_relay`. An earlier rejected envelope needs redelivery after the
block. Data availability propagates to the receiver's envelope observation
by that deadline. `BeaconExternalsPremises.verify_envelope_deterministic` states
that verification depends on the state and envelope, not the observation.
The sender and receiver states are within the verification horizon. The
successor clock read identifies the deadline only.

An honest index-1 attestation has a FULL head, whose envelope is locally
verified. `Execution.payload_envelope_relay_of_parts` derives the old relay
outcome, using block-state agreement proved from deterministic state
transitions. Handler preservation carries it through any events before the
attestation.
This closes the payload part of validation without adding a branch-weight
assumption. The exact premises are in [the review guide](REVIEW_GUIDE.md). The
legacy `Synchrony` record is unchanged; conversion to `NextSlotSynchronyPremises`
now takes explicit envelope-delivery and data-relay evidence.

## Live monotonicity and the paper

The paper's `ConfirmedBlockMonotonicity` (`FastConfirmationPaper/LMDGhost/`)
states that the LMD-GHOST safety predicate persists: a block confirmed at
`t` is confirmed at each later `t'`. It uses Assumption 4,
`beta < (1 - pb) / 4`, and `CommitteeCoversEpoch`. The proved spec statement
`ConfirmedRootMonotonicity` is about the cached executable root. The
correspondence is:

| Paper | Spec model |
|---|---|
| Assumption 4 | `paper_byzantine_boost_bound`, with actual non-honest stake |
| `CommitteeCoversEpoch` | accepted `BeaconExternalsPremises.committee_coverage` |
| synchronous honest votes | `honest_block_each_slot`, `honest_votes_extend_initial_head`, accepted synchrony |
| threshold with `beta` | `configured_threshold_margin`, because the executable threshold uses the configured cap |
| Assumption 6, conditional eventual FFG closure | `ffg_timely_justification`, with checkpoint timing at the last-slot call and next epoch start |
| none | FFG gates, staleness revert, observed restart, epoch-start reconfirmation |

The last row has no counterpart in the paper's LMD-only theorem. The paper's
Assumption 3.2 lets a justification appear two epochs late; the executable
selector needs it one epoch earlier. `Proof/MonotonicityLiveGates.lean`
records the resulting gate and revert facts. The fifth live field supplies the
earlier checkpoint observation; `Proof/MonotonicityLiveBridge.lean`,
`MonotonicityLiveConfirmation.lean`, and `MonotonicityLiveRestart.lean` prove
the historical certificates and restart rules.
`MonotonicityLiveAssemble.lean` applies those certificates to each block
between the checkpoint and a cache ahead of it, proves chain safety, and
combines start and non-start calls by induction over seconds. Its public
`live_confirmed_root_monotonicity` theorem uses live fields 1 and 5. Live fields
2–4 remain in the record and statement but are unused in this proof.

## Module system

Each library file starts with `module`. Use `public import` for library
imports to keep declarations visible through the existing import paths.
Files with declarations put `@[expose] public section` after the import
header and close it with `end`. This keeps definition bodies available for
reduction and theorem statements available to importers. Import-only files
do not need a public section.

The module system keeps theorem proof bodies private. Keep explicit
`private theorem` and `private lemma` helpers private. A definition used in
a public statement or exposed definition must be public, as must the
definitions that it depends on. Keep other local helpers private when the
module rules permit this. Close each namespace and section before closing
the public section; use the scope name on each named `end`.

A proof-body edit can rebuild only its own module when its public interface
stays the same. Changes to public statements or exposed definitions can
rebuild dependent modules. Build caches must retain `.olean.private` and
`.olean.server` files with the other Lake build files.

`scripts/Audit.lean` stays outside the library and does not start with
`module`. Its ordinary imports load private proof bodies, so its body checks
and axiom checks still apply. If the audit becomes a module, it needs
`import all` to inspect those bodies. Run `scripts/validate.sh` to check
imports, build the library, and run the audit.

## Module map (build order)

| Module | Content |
|---|---|
| `Spec/Model/Config.lean` | `Config`, `mainnet_config` |
| `Spec/Model/Types.lean` | `Checkpoint`, `ForkChoiceNode`, `LatestMessage`, `BeaconBlock`, `Validator`, `BeaconState`, `Externals`; beacon-chain helpers |
| `Spec/Model/ForkChoice.lean` | `Store`; fork-choice helpers through `get_head` |
| `Spec/Model/FCRStore.lean` | `FastConfirmationStore`, `get_fast_confirmation_store`, misc + state helpers |
| `Spec/Model/LMDHelpers.lean` | LMD-GHOST helpers (`get_block_support_between_slots` … `is_confirmed_chain_safe`) |
| `Spec/Model/FFGHelpers.lean` | FFG helpers (`get_current_target_score` … `will_current_target_be_justified`) |
| `Spec/Model/Confirmation.lean` | `update_fast_confirmation_variables`, `find_latest_confirmed_descendant`, `get_latest_confirmed`, `on_fast_confirmation` |
| `Spec/Model/Handlers.lean` | fork-choice handlers: `update_checkpoints` … `get_forkchoice_store`, the `on_tick`/`on_attestation`/`on_block` chains |
| `Spec/Model/Validator.lean` | honest attesting (`honest_attestation_data`, `honest_attestation`) |
| `Spec/Model/Execution.lean` | `Event`, `Execution`, store/FCR trajectories, `WellFormedStore` |
| `Spec/Model/Assumptions.lean` | ground-truth quantities; `HonestBehavior`, `Synchrony`, `BeaconExternalsPremises`, `StaticValidatorSet`, `ByzantineWeightPremises` |
| `Spec/Internal/Legacy/Vocabulary.lean` | `JustifiedIn`, `JustificationInterface`, `SpecAssumptions`, `Spec_Safety`, `Spec_Monotonicity` |
| `Spec/Proof/StoreInvariants.lean`, `Spec/Proof/Trajectory.lean` | proof layer 0: store-extension order `StoreLE` + handler preservation; clock coherence |
| `Spec/Model.lean`, `Spec.lean` | facades |

Everything lives in namespace `FastConfirmation.Spec`.

## Dynamics layer (model completion)

A single `Store` snapshot cannot state safety; the model is completed with the
spec's own dynamics: the fork-choice **handlers** driving store evolution,
**honest validator behavior** (validator spec), and a **synchronous network**
— the same three ingredients the paper model carries (in simplified form).

11. **Handlers are transcribed** from `fork-choice.md`: `update_checkpoints`,
    `update_unrealized_checkpoints`, `compute_pulled_up_tip`,
    `on_tick_per_slot`/`on_tick`, the `on_attestation` helper chain
    (`validate_target_epoch_against_current_time`, `validate_on_attestation`,
    `store_target_checkpoint_state`, `update_latest_messages`), the `on_block`
    helper chain (`record_block_timeliness`,
    `compute_shuffling_lookahead_start_slot`, `compute_shuffling_dependent_slot`,
    `get_shuffling_dependent_root`, `update_proposer_boost_root`), the four
    handlers, and
    `get_forkchoice_store`. Python mutation → `Store → … → Store`; python
    `assert`-rejection in handlers → `Option Store` (`none` = the message is
    not applied now — python's "delay consideration"/drop). Validation
    helpers whose python body is only asserts return `Bool`.

11a. **Additional dynamics modeling choices:** the
    `on_tick` catch-up while-loop is a fuel site like decision 4's (fuel
    `tick_slot + 1`; the loop advances one slot per iteration on
    whole-second-boundary configs). The executable `get_forkchoice_store`
    omits python's
    `assert anchor_block.state_root == hash_tree_root(anchor_state)`.
    The accepted `ScheduledPrefixPremises.genesis` requires
    `Externals.AnchorCommitsToState anchorBlock.message anchorState`.
    This abstract contract must come from the external interpretation of the
    full block and state; the model does not prove a concrete hashing result.
    Slot agreement and parent/root inequality remain separate premises.
    The legacy `SpecAssumptions` bundle still has only those two premises.
    The relation defaults to `False`, so an external implementation must
    supply a relation and anchor evidence to satisfy the accepted trajectory.
    The function takes the *signed* wire container because the root travels
    on it;
    `Event.attestation` with
    `is_from_block = true` may appear in adversarial schedules unaccompanied
    by a block — a **conservative over-approximation** (the adversary gets
    strictly more latitude than the spec's block-embedded path; honest
    messages are still pinned by `HonestBehavior.no_forgery`); events
    scheduled at second 0 are ignored (`store v 0 = genesis_store`) —
    harmless for honest traffic, one second of trimmed adversarial power;
    `on_tick` called with `time < genesis_time` would move the clock
    backwards where python's uint64 raises — unreachable from trajectories
    (`time_at` is increasing).

12. **Wire containers.** `AttestationData` is transcribed in full. The wire
    `Attestation` is modelled as its **indexed** projection
    (`IndexedAttestation`: `attesting_indices` + `data`): aggregation-bits →
    indices extraction (`get_indexed_attestation`) and BLS signatures are
    absorbed into the abstract validity check
    `Externals.is_valid_indexed_attestation` (none of the transcribed logic
    reads bits or signatures). `SignedBeaconBlock` carries its projected
    `message` plus its `root` — `hash_tree_root` absorbed into the wire
    object (roots are unique commitments; distinctness is a well-formedness
    invariant). `AttesterSlashing` and `is_slashable_attestation_data` are
    transcribed in full.

13. **Abstract `Externals` fields**: `state_transition : BeaconState → SignedBeaconBlock
    → Option BeaconState` (`none` = invalid block; `validate_result=True`
    absorbed), `process_justification_and_finalization` (for
    `compute_pulled_up_tip`), `is_valid_indexed_attestation`. `BeaconState`
    includes the `genesis_time` and `finalized_checkpoint` fields the handlers
    read. `Config` includes `attestation_due_bps` (mainnet 3333) and
    `min_seed_lookahead` (1); `BASIS_POINTS = 10000` and `UINT64_MAX` are
    constants.

    `BeaconExternalsPremises` restricts `honest_attestation_valid`,
    `valid_attestation_honest`, and `valid_attestation_committee` to
    `Execution.ReachableValidationState`. A state is in this domain only if
    it occurs at a known block or checkpoint key in an honest node's
    in-horizon causal store. A fresh checkpoint state can be prepared before
    a successful handler stores it. Its check uses the reachable base state
    and the separate `process_slots_attestation_valid` contract on that base. In Phase0,
    slot processing preserves public keys, fork data, and the genesis
    validators root; the attestation supplies its target epoch.
    `valid_attestation_default` maps rejection and an invalid validator-index
    lookup on the empty default state to `false`; Python need not return a
    Boolean on that lookup failure.
    The handler proofs establish that an unkeyed block-state read returns
    that default. These are explicit contracts for the abstract functions,
    not a refinement proof. Supporting validity-based trajectory invariants
    now require an honest node and an in-horizon second.

14. **Dict-update fidelity.** `blocks[root] = block` preserves python dict
    semantics: `Function.update` on the totalized map plus key-list append
    *only if absent* (python assignment to an existing key keeps its
    position). `checkpoint_states` gains a domain field
    `checkpoint_state_keys : Finset (Checkpoint Root)` because
    `store_target_checkpoint_state` tests membership (`target not in
    store.checkpoint_states`); `block_states` shares its key set with
    `blocks` by construction (a `WellFormedStore` invariant), so python's
    `block.parent_root in store.block_states` is tested against
    `block_roots`. `update_proposer_boost_root` reads
    `store.block_timeliness[root]` as `(… root).getD false` — always set by
    `on_block` immediately before, so the default is unreachable.

15. **Honest validator behavior** (`validator.md` "Attesting"):
    `honest_attestation_data store slot index` builds the `AttestationData`
    the validator spec prescribes — LMD vote = `get_head` at voting time,
    source = the (pulled-up) head state's `current_justified_checkpoint`,
    target = `Checkpoint(epoch_at(slot), get_checkpoint_block(store, head,
    epoch_at(slot)))`. The target root uses the store's ancestor walk rather
    than the state's block-root history: `validate_on_attestation` *asserts*
    exactly this equality, so the two coincide on every attestation the fork
    choice accepts (documented substitution). Honest wire attestations are
    singletons (`attesting_indices = [v]`), one per assigned slot, cast at a
    voting time within the assigned slot.

16. **Executions.** Time is `ℕ` seconds since genesis; nodes are identified
    with validators (as in the paper). An `Event` is a wire message (block /
    attestation with its `is_from_block` flag / slashing); a schedule assigns
    each node the list of events it processes at each second. The store
    trajectory is *defined* by folding: at second `t+1`, `on_tick` to
    absolute time, then apply the scheduled events left-to-right, a rejected
    event (`none`) leaving the store unchanged. The FCR trajectory applies
    `on_fast_confirmation` at the first second of each slot, after that
    second's events — inside the handler's mandated window (once per slot, in
    the first part of the slot, after past-slot attestations were applied
    under synchrony).

17. **Network/timing assumptions** are `Prop`-valued records over executions,
    the spec's own synchrony sentence made precise, mirroring the paper's
    `Synchrony` bundle where the spec is silent: honest attestations created
    in slot `s` are processed successfully by every honest node by the first
    second of slot `s+1` (the fork choice's own `current_slot ≥ slot + 1`
    gate makes "end of slot `s`" operationally the `s+1` boundary); blocks an
    honest attestation references propagate on the same schedule (needed for
    its validity asserts to pass elsewhere — implicit in the spec, explicit
    in the paper); store/message relay between honest nodes. Several paper
    *axioms* become **provable invariants** here (view monotonicity,
    ancestor-closure of `blocks`, no-future-messages), exactly the payoff of
    modelling evolution. Economic assumptions (Byzantine weight ≤
    `CONFIRMATION_BYZANTINE_THRESHOLD`% against the balance sources the rule
    reads; committee-weight-estimation soundness — the spec's own
    "high-probability" 5‰ adjustment assumption; balance/committee
    consistency within `MAX_SEED_LOOKAHEAD`) are separate records: they are
    exactly the spec's stated assumptions, consumed, not derived.

The accepted theorem surface is
`NextSlotSafetyPremises` together with
`confirmed_root_safe_from_next_slot`. Its intended conclusion is that a root
stored by an honest node's FCR is an ancestor of every in-horizon honest head from the following
slot onward. The literal descendant-selector result is also safe at an actual
scheduled boundary call. Reset safety is a proved result. Its finalized-reset
case uses the separate `RealizedFinalizationDelay` premise, and its
active-observed case uses the accepted execution and FFG premises. The proof
is entirely spec-side; the paper model supplies mathematical guidance but is
not imported.

The next-slot boundary matters. Optional queries at arbitrary in-slot action
prefixes can run after one honest endpoint has processed an event and before
another endpoint has processed it. The finite counterexamples in `Spec/Proof/`
show that universal cross-node safety at every such prefix is false.
