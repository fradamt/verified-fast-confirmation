# Spec-model design — `FastConfirmation/Spec/`

This repository models both the FCR **paper** (arXiv:2405.00549) and the FCR
**consensus spec**. This document describes the consensus-spec layer:

- **Source of truth**:
  [`consensus-specs/specs/phase0/fast-confirmation.md`](https://github.com/ethereum/consensus-specs/blob/477321355d48d527e7e1e4d572f6a40a0b41072a/specs/phase0/fast-confirmation.md)
  at public commit `477321355d48d527e7e1e4d572f6a40a0b41072a`.
- **Environment**: `specs/phase0/fork-choice.md` (Store, `get_head`,
  `get_attestation_score`, `get_voting_source`, …) and `specs/phase0/beacon-chain.md`
  (epoch arithmetic, `is_active_validator`, `get_total_active_balance`) at the same
  commit.
- **Out of scope (documented, deliberate)**: the Bellatrix/Gloas deltas
  (`get_safe_execution_block_hash`, Gloas `get_node_for_root` payload status) —
  pure execution-payload plumbing, no rule logic; the optimistic-sync `MUST
  return False if not VALID` note on `is_one_confirmed` (meaningless in phase0,
  which has no execution payloads — becomes relevant only if the Bellatrix delta
  is added later).

`FastConfirmation/Paper/` contains a separate formalization of the paper. The
consensus-spec layer is `FastConfirmation/Spec/` and imports only Mathlib—not
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
| `Spec/Model/Assumptions.lean` | ground-truth quantities; `HonestBehavior`, `Synchrony`, `ExternalsCoherence`, `StaticValidatorSet`, `ByzantineBound` |
| `Spec/TheoremStatements.lean` | `JustifiedIn`, `JustificationInterface`, `SpecAssumptions`, `Spec_Safety`, `Spec_Monotonicity` |
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
    whole-second-boundary configs); `get_forkchoice_store` drops python's
    `assert anchor_block.state_root == hash_tree_root(anchor_state)`; the
    accepted anchor relation does not represent this state-root commitment
    and requires only slot agreement and parent/root inequality. The function
    takes the *signed* wire container because the root travels on it);
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
`AcceptedActualFCRNextSlotSafetyAssumptions` together with
`acceptedSpec_safety_next_slot`. It proves that a root stored by an honest
node's FCR is an ancestor of every in-horizon honest head from the following
slot onward. The literal descendant-selector result is also safe at an actual
scheduled boundary call. Reset safety is a proved result. Its finalized-reset
case uses the separate `AcceptedRealizedFinalizationDelay` premise, and its
active-observed case uses the accepted execution and FFG premises. The proof
is entirely spec-side; the paper model supplies mathematical guidance but is
not imported.

The next-slot boundary matters. Optional queries at arbitrary in-slot action
prefixes can run after one honest endpoint has processed an event and before
another endpoint has processed it. The finite counterexamples in `Spec/Proof/`
show that universal cross-node safety at every such prefix is false.
