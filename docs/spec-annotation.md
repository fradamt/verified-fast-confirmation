# Spec ↔ Lean annotation — `FastConfirmation/Spec/`

Per-function mapping between public `consensus-specs` commit
[`4773213`](https://github.com/ethereum/consensus-specs/tree/477321355d48d527e7e1e4d572f6a40a0b41072a) and the Lean
model. Lean names equal python names (the faithfulness device — diff each def's
docstring, which quotes the python, against its body). "Deviations" lists
only per-function items; the global conventions (ℕ arithmetic, totalized
dicts, fuel, state-passing, `List` for ordered iteration) are in
`docs/spec-model-design.md` and are not repeated per row.

The dynamics sections at the end (Handlers/Validator/Execution/Assumptions/
TheoremStatements) include model-only objects with no python counterpart;
there the Spec column cites the prose being rendered.

## Beacon-chain helpers (`Spec/Model/Types.lean`)

| Spec (`beacon-chain.md`) | Lean | Deviations / notes |
|---|---|---|
| Constants / Configuration tables | `Config`, `mainnet_config` (Config.lean) | proof fields: `0 < slots_per_epoch`, `0 < slot_duration_ms`, `confirmation_byzantine_threshold ≤ 25` (the table's "Max. Value") — see design §9 |
| `Checkpoint`, `Validator`, `BeaconState`, `BeaconBlock` | same names | Projected to the fields the FCR reads (design §10); parameterized by `Root` |
| `compute_epoch_at_slot` | same | — |
| `compute_start_slot_at_epoch` | same | — |
| `is_active_validator` | same | returns `Bool` (`decide`) |
| `get_active_validator_indices` | same | `enumerate` = filter over `List.range` (order-preserving) |
| `get_current_epoch` | same | — |
| `get_total_balance` | same | takes `Finset` (python `Set`); sum order-independent |
| `get_total_active_balance` | same | — |
| `SignedBeaconBlock` | same (Types.lean) | projected: `message` + its `root` — `hash_tree_root` absorbed into the wire object (design §12); signature absorbed into `Externals.state_transition` |
| `AttestationData` | same | transcribed in full |
| `IndexedAttestation` / `Attestation` | same / `abbrev` to it | wire `Attestation` = its indexed projection; aggregation-bits → indices (`get_indexed_attestation`) and BLS absorbed into `Externals.is_valid_indexed_attestation` (design §12) |
| `AttesterSlashing` | same | transcribed in full |
| `is_slashable_attestation_data` | same | transcribed in full; returns `Bool` (`decide`) |
| `BeaconState` (extended) | same | gains `genesis_time`, `finalized_checkpoint` — read by `get_forkchoice_store` / `on_block` / `compute_pulled_up_tip` (design §13) |
| `Externals` (extended) | same | gains `state_transition` (`Option`: `none` = python raise, `validate_result=True` absorbed), `process_justification_and_finalization`, `is_valid_indexed_attestation` (design §13) |
| `ATTESTATION_DUE_BPS`, `MIN_SEED_LOOKAHEAD` | `Config.attestation_due_bps`, `Config.min_seed_lookahead` | mainnet 3333 / 1 |
| `BASIS_POINTS`, `UINT64_MAX` | same (Config.lean) | constants 10000 / 2^64 − 1 |

## Fork-choice environment (`Spec/Model/ForkChoice.lean`)

| Spec (`fork-choice.md`) | Lean | Deviations / notes |
|---|---|---|
| `ForkChoiceNode`, `LatestMessage` | same (Types.lean) | — |
| `Store` | same | dicts totalized (design §3); `block_roots : List Root` = dict key order; `checkpoint_state_keys : Finset` = `checkpoint_states` domain (membership test in `store_target_checkpoint_state` — design §14); `block_timeliness` (`Option`) written by `record_block_timeliness`, read by `update_proposer_boost_root`, unread by the FCR itself |
| `get_slots_since_genesis` | same | `time - genesis_time` truncates if `time < genesis_time` (store invariant: never) |
| `get_current_slot` | same | — |
| `get_current_store_epoch` | same | — |
| `compute_slots_since_epoch_start` | same | subtraction always non-negative |
| `get_ancestor` | `get_ancestor_aux` + wrapper | fuel `block.slot + 1` (design §4); fuel-out returns current node (python diverges) |
| `is_ancestor` | same | — |
| `calculate_committee_fraction` | — | called only by the (out-of-scope) proposer-reorg helpers; out of scope |
| `get_checkpoint_block` | same | — |
| `get_supported_node` | same | unused `store` arg kept for signature fidelity |
| `get_attestation_score` | same | list-comprehension = `List.filter`/`map`/`sum`; a vote counts for `node` when `node` is an ancestor of the supported node — `is_ancestor (supported) node`, argument order verified |
| `compute_proposer_score` | same | — |
| `get_proposer_score` | same | — |
| `get_weight` | same | `Root()` = `Inhabited.default`; conditional boost as `if`-expression; boost applies when the queried `node` is an ancestor of `proposer_boost_node` — `is_ancestor proposer_boost_node node`, argument order verified |
| `get_voting_source` | same | — |
| `filter_block_tree` | `filter_block_tree_aux` | returns `(viable, added roots)`; output dict → insertion-ordered `List` (design §8); `any(children)` = non-emptiness; fuel `block_roots.length + 1`; python's unconditional `block = store.blocks[block_root]` binding is dropped (value never needed in the root-list encoding) — a python-divergence point when the base root is absent from the dict (python `KeyError`s, Lean proceeds on junk; outside the well-formed domain) |
| `get_filtered_block_tree` | same | returns the root list |
| `get_node_children` | same | takes the root list; block values looked up in `store` (design §8) |
| `get_head` | `get_head_aux` + wrapper | `max(children, key=(weight, root))` = `List.argmax` with `toLex` key, unique max (design §7); fuel `blocks.length + 1` |
| `update_checkpoints`, `update_unrealized_checkpoints`, pull-up/on-tick/on-attestation/on-block helper chains, the four handlers, `get_forkchoice_store` | Handlers.lean | transcribed — see "Fork-choice handlers" section below |
| `seconds_to_milliseconds` | same | overflow guard transcribed literally (`UINT64_MAX` constant) although `ℕ` cannot overflow |
| `get_slot_component_duration_ms` | same | — |
| `get_attestation_due_ms` | same | — |
| proposer-reorg helpers (`is_head_late` … `get_proposer_head`), `get_proposer_reorg_cutoff_ms`, `get_aggregate_due_ms` | — | not called by the FCR or the transcribed handlers; out of scope |
| `get_latest_message_epoch` | same | — |

## FCR store + misc/state helpers (`Spec/Model/FCRStore.lean`)

| Spec (`fast-confirmation.md`) | Lean | Deviations / notes |
|---|---|---|
| `FastConfirmationStore` | same | — |
| `get_fast_confirmation_store` | same | the SHOULD prose (initialize together with the fork-choice store, same trusted checkpoint) is represented by `Execution.fcr v 0 = get_fast_confirmation_store (E.store v 0)` (Execution.lean) |
| `get_node_for_root` | same | phase0 form (Gloas adds `payload_status` — out of scope) |
| `get_block_slot` | same | — |
| `get_block_epoch` | same | — |
| `get_checkpoint_for_block` | same | — |
| `get_current_target` | same | — |
| `is_start_slot_at_epoch` | same | — |
| `get_ancestor_roots` | `get_ancestor_roots_aux` + wrapper | `Option` worker: `none` = terminal unreached → `[]` (design §5); oldest→newest, terminal-exclusive, block-inclusive; fuel `block.slot + 1` |
| `get_slot_committee` | same | over abstract `Externals` shuffling; python `Set` = `Finset.biUnion` over `Finset.range`; "MUST support epochs from `current_epoch - 2`" is a semantic obligation on `Externals` instances |
| `get_pulled_up_head_state` | same | `process_slots` abstract (total — it absorbs python's `assert state.slot < slot`, which cannot fire at this guarded call site); python `copy()` moot under state-passing |
| `get_previous_balance_source` | same | — |
| `get_current_balance_source` | same | — |

## LMD-GHOST helpers (`Spec/Model/LMDHelpers.lean`)

| Spec | Lean | Deviations / notes |
|---|---|---|
| `get_block_support_between_slots` | same | `range(a, b+1)` = `Finset.Icc a b` (empty when `a > b`); membership match via `Option.any` |
| `is_full_validator_set_covered` | same | `slots_per_epoch - 1` non-truncating by `Config.slots_per_epoch_pos` |
| `adjust_committee_weight_estimate_to_ensure_safety` | same | `999`/`1000` literals kept (spec's per-mille encoding) |
| `estimate_committee_weight_between_slots` | same | all four branches literal; every `-` non-negative in-branch |
| `get_equivocation_score` | same | intersection = `Finset ∩`; (spec has no slashed-filter here — preserved) |
| `compute_adversarial_weight` | same | guarded subtraction literal |
| `get_adversarial_weight` | same | `Slot(current_slot - 1)`: at `current_slot = 0`, ℕ truncates to `0` where python `uint64` would raise — benign because at slot 0 no call path evaluates it against nonempty content (all chain segments are empty or short-circuited), not because slot 0 is pre-genesis |
| `compute_empty_slot_support_discount` | same | `block.slot - 1` well-defined in the taken branch on well-formed stores |
| `get_support_discount` | same | — |
| `compute_safety_threshold` | same | the spec's own underflow guard transcribes exactly to ℕ |
| `is_one_confirmed` | same | strict `>`; optimistic-sync MUST is post-Bellatrix, out of scope (design doc) |
| `is_confirmed_chain_safe` | same | early `return False` = `if/else`; `current_epoch - 1` reached only with `current_epoch ≥ 2` |

## FFG helpers (`Spec/Model/FFGHelpers.lean`)

| Spec | Lean | Deviations / notes |
|---|---|---|
| `get_current_target_score` | same | — |
| `compute_honest_ffg_support_for_current_target` | same | `total - ffg_weight_till_now` non-negative (within-epoch estimate ≤ total); two `current_slot - 1` sites use saturating ℕ subtraction; `100 - confirmation_byzantine_threshold` non-truncating by `Config.confirmation_byzantine_threshold_le` |
| `will_no_conflicting_checkpoint_be_justified` | same | — |
| `will_current_target_be_justified` | same | — |

## Top level (`Spec/Model/Confirmation.lean`)

| Spec | Lean | Deviations / notes |
|---|---|---|
| `update_fast_confirmation_variables` | same | mutation → chained record updates, order preserved (design §6) |
| `find_latest_confirmed_descendant` | same + `…_prev_epoch_loop`, `…_tentative_loop` | `for … break` loops → structural recursions carrying the accumulator (design §6); loop-2's nested `if not will…: break` = the conjunction `epoch-advance ∧ ¬will…`; `canonical_roots` recomputed after loop 1, as in python |
| `get_latest_confirmed` | same | the four restart booleans kept as named `let`s mirroring python locals; python's local-variable reassignment = `let`-shadowing — the staleness check and the final advance guard read the *post-revert/post-restart* binding, and `find_latest_confirmed_descendant` receives the original `fcr_store` alongside the updated local, exactly as python (verified) |
| `on_fast_confirmation` | same | `Execution.fcr` models the handler timing rules (once per slot, before attestation due, after applying past-slot attestations): the call occurs at the first second of each slot (before the attestation-due cutoff), after that second's events — under `Synchrony.attestation_delivery` these are exactly the past-slot attestations |

## Fork-choice handlers (`Spec/Model/Handlers.lean`)

| Spec (`fork-choice.md`) | Lean | Deviations / notes |
|---|---|---|
| `update_checkpoints` | same | total `Store → Store`; python's two sequential `if`s = `let`-shadowing |
| `update_unrealized_checkpoints` | same | as `update_checkpoints` |
| `compute_pulled_up_tip` | same | `process_justification_and_finalization` abstract (`Externals`); python `copy()` moot under state-passing; `unrealized_justifications` write = `Function.update` (no domain field — the dict is never iterated) |
| `on_tick_per_slot` | same | `Root()` = `Inhabited.default`; both `if`s literal |
| `on_tick` | `on_tick_aux` + wrapper | catch-up while-loop → fuel `tick_slot + 1` (advances a slot per iteration only when slot boundaries land on whole seconds — `1000 ∣ slot_duration_ms`, a `SpecAssumptions` conjunct; fuel-out = python's nontermination, design §11a); `time - store.genesis_time` truncates where python `uint64` raises — unreachable from trajectories (`time_at` increasing) |
| `validate_target_epoch_against_current_time` | same | assert-only body → `Bool`; `current_epoch - 1` is the spec's explicit saturating subtraction |
| `validate_on_attestation` | same | assert-only body → `Bool` (`false` = "delay consideration"/drop); `if not is_from_block:` = short-circuit `is_from_block \|\|`; `in store.blocks` tested against `block_roots`; assert order preserved by the `&&` chain |
| `store_target_checkpoint_state` | same | `target not in store.checkpoint_states` = `checkpoint_state_keys` membership (design §14); `process_slots` abstract, the spec's own slot guard transcribed; `copy` moot |
| `update_latest_messages` | same | for-loop → `List.foldl` over the non-equivocating filter; `i not in … or epoch >` = `Option` match |
| `record_block_timeliness` | same | `store.time - store.genesis_time` truncates (store invariant `WellFormedStore.time_ge_genesis`); writes `some is_timely` |
| `compute_shuffling_lookahead_start_slot` | same | `epoch - MIN_SEED_LOOKAHEAD` is the spec's explicit saturating subtraction |
| `compute_shuffling_dependent_slot` | same | `lookahead_start_slot - 1` is the spec's explicit saturating subtraction |
| `get_shuffling_dependent_root` | same | `hash_tree_root`/`Root()` are represented by the projected root and totalized node model (design §12) |
| `update_proposer_boost_root` | same | `store.block_timeliness[root]` = `.getD false` — default unreachable (`on_block` sets it immediately before); dependent roots are computed at the current store epoch |
| `on_block` | same | handler asserts → `Option (Store Root)` (`none` = not applied); known roots return the unchanged store before validation; `parent_root in store.block_states` tested against `block_roots` (shared key set — design §14); `state_transition` abstract, `none` = python raise; `hash_tree_root(block)` = `signed_block.root` (design §12); fresh dict insert = `Function.update` + append (design §14); `head` computed before the insert — python mutation order preserved |
| `on_attestation` | same | asserts → `Option`; **documented divergence**: on the signature-failure path the reference python's in-place checkpoint-state cache write survives the raise — the model discards it, the normative "invalid calls to handlers must not modify store" reading (see docstring); `get_indexed_attestation` absorbed (wire attestation already indexed — design §12); `is_from_block := false` default kept |
| `on_attester_slashing` | same | asserts → `Option`; python set intersection = `toFinset ∩`; the add-loop = `Finset ∪` |
| `get_forkchoice_store` | same | takes `SignedBeaconBlock` (the root travels on the wire object); python's `assert anchor_block.state_root == hash_tree_root(anchor_state)` dropped — an execution well-formedness premise on the anchor (design §11a); singleton dicts = `Function.update` over junk-totalized defaults |

## Honest validator (`Spec/Model/Validator.lean`)

| Spec (`validator.md`) | Lean | Deviations / notes |
|---|---|---|
| "Attestation data" | `honest_attestation_data` | head = `get_head` at voting time; head-state pull-up guarded (python `process_slots` asserts `state.slot < slot`); **documented substitution**: target root via the store ancestor walk `get_checkpoint_block` in place of the state's `get_block_root` history — `validate_on_attestation` asserts exactly this equality, so they coincide on every accepted attestation (design §15) |
| "Construct attestation" | `honest_attestation` | singleton `attesting_indices = [validator_index]` (aggregation-bits projection); BLS absorbed (design §12) |

## Executions (`Spec/Model/Execution.lean`) — model-only; no python counterparts

| Renders | Lean | Notes |
|---|---|---|
| wire messages | `Event` | block / attestation (with `is_from_block`) / attester slashing |
| handler dispatch | `apply_event` | `none` = the handler rejected the message |
| protocol execution | `Execution` | genesis store, per-node/per-second schedule, honest set, ground-truth committee, per-(validator, slot) vote record (design §16) |
| clock | `time_at`, `slot_at`, `slot_start` | `slot_at` = the `get_current_slot` arithmetic on `time_at`; `slot_start` truncates to 0 for slots before the genesis store's time, exact under `1000 ∣ slot_duration_ms` (a `SpecAssumptions` conjunct) |
| store trajectory | `Execution.store` | second 0 = genesis store (events scheduled at second 0 ignored — trimmed adversarial power, design §11a); at `n+1`: `on_tick`, then the second's events left-to-right, rejected events `.getD` no-ops |
| FCR trajectory | `Execution.fcr` | the read-only `store` field tracks `E.store` every second; `on_fast_confirmation` at the first second of each slot (slot-advance test), after that second's events — the handler's mandated window (design §16) |
| confirmed root | `Execution.confirmed` | `(E.fcr v n).confirmed_root` |
| store well-formedness | `WellFormedStore` | structural invariants (nodup keys, clock ≥ genesis, parent slots strictly decrease, justified/finalized known, finalized ≼ justified), with handler-preservation lemmas in the proof layer |

## Assumption records (`Spec/Model/Assumptions.lean`)

| Spec origin | Lean | Notes |
|---|---|---|
| — (ground truth) | `anchor_state`, `registry`, `weight_of`, `weight`, `total_active`, `span_committee` | derived quantities over an `Execution` (anchor state = the genesis store's justified-checkpoint state) |
| validator.md "Attesting" + slashing discipline | `HonestBehavior` | `votes_head` (the recorded vote is `honest_attestation` from the node's own store at a second of the assigned slot), `votes_assigned`, `no_forgery` (BLS unforgeability + equivocation slashing) |
| FCR intro synchrony sentence | `PaperSafetySynchrony` | The primary theorem uses `attestation_delivery` (slot-`s` honest attestations processed at the first second of slot `s+1`), `block_relay` (known blocks propagate by the following slot), and `attester_slashing_relay` (known equivocation evidence propagates by the following slot). The fields hold throughout the checked execution, so this is the GST-0 specialization of the paper's post-GST timing model. |
| behavior of the abstracted beacon-chain functions | `ExternalsCoherence` | slot/registry behavior of `process_slots`/`state_transition`/`process_justification_and_finalization`; `committees_agree` (the spec's committee-consistency window, idealized to the whole execution); `honest_attestation_valid`; `committee_assignment_unique` (one assigned slot per epoch) |
| balance-source design note (static set) | `StaticValidatorSet` | the trusted anchor lies inside the verification horizon and validator activity is constant below that horizon (paper Assumption 1); genesis registry constancy is derived from the already-required `get_forkchoice_store` initialization |
| `CONFIRMATION_BYZANTINE_THRESHOLD` + the 5‰ estimation note | `ByzantineBound` | balance quantization, `estimate_sound` (the estimate upper-bounds actual span-committee weight), and `span_fraction` (the non-honest span weight is at most the configured percentage, cross-multiplied) |

## Accepted theorem surface

| Spec claim | Lean | Notes |
|---|---|---|
| "will remain canonical in the view of all honest validators starting from the current moment in time" (`find_latest_confirmed_descendant` note) | `AcceptedActualFCRNextSlotSafetyAssumptions.findLatestConfirmedDescendant_safeFrom_of_actualCall` | exact mandatory boundary-call helper result under the primary reset-free accepted bundle and the literal selector guard. Carried input safety comes from the preceding following-slot invariant; causal finalization lag forces a selector-eligible finalized reset to the anchor; observed input safety is derived dynamically. Covers helper calls which return their input unchanged |
| `get_latest_confirmed` may be called at any point in a slot + the helper's all-honest current-moment note | `strict_prefix_extra_query_counterexample`, `pinned_economics_strict_prefix_extra_query_counterexample` | universal action-prefix safety is false: at one global query position the actor has processed the synchronized vote and returns the candidate while another honest endpoint has processed only the preceding sibling block. The first theorem proves the full non-FFG environment and also shows actor-side ground replay coexists with failed endpoint ancestry; the second uses pinned economic values `40`/`25` and threshold `95`, but is not a complete `mainnet_config` instantiation |
| Primary accepted stored-cache safety | `AcceptedActualFCRNextSlotSafetyAssumptions`, `AcceptedSpec_Safety_next_slot`, `acceptedSpec_safety_next_slot` | every stored honest output is on every in-horizon honest head from the following slot. Finalized and active-observed resets are derived from accepted execution/FFG dynamics; the bundle has no reset-specific law. This is a separate accepted premise surface, not a bridge from `SpecAssumptions`, and it makes no optional in-slot action-prefix claim |
| Finalized fallback timing used by the primary theorem | `finalizedReset_safeFrom_of_nextSlotSynchrony` | safety from the following slot, derived from accepted certificates and ordinary synchrony without a same-moment adoption law |

## Out of scope (sanctioned)

- `bellatrix/fast-confirmation.md` (`get_safe_execution_block_hash`) and
  `gloas/fast-confirmation.md` (modified `get_node_for_root`,
  `get_safe_execution_block_hash`): execution-payload plumbing.
- The optimistic-sync `MUST return False if not VALID` note on
  `is_one_confirmed`: post-Bellatrix (phase0 has no payloads).
- The proposer-reorg helper family (`is_head_late` … `get_proposer_head`,
  `get_proposer_reorg_cutoff_ms`, `get_aggregate_due_ms`) and
  `calculate_committee_fraction` (their only would-be transcribed consumer):
  not called by the FCR or the transcribed handlers.
- validator.md block-proposal and aggregation duties: the FCR's safety
  guarantee does not rely on honest proposals (proposer boost is handled
  adversarially), and aggregation is invisible to the indexed-attestation
  projection (design §12).
