> Historical document. Replaced by [docs/SPEC_MAP.md](../SPEC_MAP.md).

# Spec ↔ Lean annotation — `FastConfirmationModel/`

Per-function mapping between public `consensus-specs` commit
[`6b9bd53`](https://github.com/ethereum/consensus-specs/tree/6b9bd532cca16555e2f3282d757622ebff29743e) and the Lean
model. Lean names equal python names (the faithfulness device — diff each def's
docstring, which quotes the python, against its body). "Deviations" lists
only per-function items; the global conventions (ℕ arithmetic, totalized
dicts, fuel, state-passing, `List` for ordered iteration) are in
`docs/spec-model-design.md` and are not repeated per row.

The dynamics sections at the end (Handlers/Validator/Execution/Assumptions/
TheoremStatements) include model-only objects with no python counterpart;
there the Spec column cites the prose being rendered.

## Gloas source layer

The active fork is Gloas. The rows below for inherited phase0 helpers remain
applicable except where this section gives a replacement. Each changed Lean
definition cites its pinned Gloas source line. See
[gloas-model-design.md](gloas-model-design.md) for the full projection contract.

- `PayloadStatus`, `ForkChoiceNode`, and `LatestMessage` use the Gloas types.
  Nodes carry root and status. Latest messages carry slot, root, and payload
  presence. The epoch helper derives the epoch from the slot.
- `BeaconBlock` adds proposer and bid fields and indexed body PTC messages.
  `BeaconState` adds finite committee-query read views for `is_head_weak`
  and retains an opaque source-state identity for external calls.
  `Externals` adds ordered PTC lookup, PTC validation, local data checks, and
  envelope verification with explicit observation context.
- `Store` has both block deadlines, verified payloads, and both optional PTC
  vote maps. `is_payload_verified` tests map membership. Timeliness and data
  availability use strict majorities and the source absent-payload rule.
- `get_parent_payload_status`, `get_ancestor`, `is_ancestor`, and
  `get_supported_node` resolve statuses from bid hashes or vote data.
  `get_node_for_root` and checkpoint walks start at PENDING.
- `get_node_children` first resolves PENDING into EMPTY or verified FULL.
  Resolved nodes admit matching block children. `get_head` uses fuel
  `2 * blocks.length + 2` and the key `(weight, root, status tiebreaker)`.
- `get_weight` includes the previous-slot zero rule and Gloas boost guard.
  `calculate_committee_fraction` and `is_head_weak` are in scope because the
  boost guard calls them. Committee list multiplicity is preserved.
- `on_block` requires a verified FULL parent, initializes PTC maps, and
  processes body PTC messages before timeliness and checkpoint updates.
  `on_execution_payload_envelope` and `on_payload_attestation_message` have
  corresponding execution events. Rejected calls discard partial writes.
- `validate_on_attestation` checks the Gloas index conditions. Honest data
  uses index 0 or 1 for payload presence, independent of committee index.
- `get_safe_execution_block_hash` returns the confirmed bid's parent hash.
  Mainnet attestation deadline is 2500 basis points. Payload and PTC
  deadlines are 5000 and 7500; mainnet PTC size is 512, minimal size is 16.

## Beacon-chain helpers (`Spec/Model/Types.lean`)

```text
┌─────────────────────────────────────┬─────────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec (beacon-chain.md)              │ Lean                        │ Deviations / notes                                                                          │
├─────────────────────────────────────┼─────────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ Constants / Configuration tables    │ Config, mainnet_config      │ proof fields: 0 < slots_per_epoch, 0 < slot_duration_ms, confirmation_byzantine_threshold ≤ │
│                                     │ (Config.lean)               │ 25 (the table's "Max. Value") — see design §9                                               │
│ Checkpoint, Validator, BeaconState, │ same names                  │ Projected to the fields the FCR reads (design §10); parameterized by Root                   │
│ BeaconBlock                         │                             │                                                                                             │
│ compute_epoch_at_slot               │ same                        │ —                                                                                           │
│ compute_start_slot_at_epoch         │ same                        │ —                                                                                           │
│ is_active_validator                 │ same                        │ returns Bool (decide)                                                                       │
│ get_active_validator_indices        │ same                        │ enumerate = filter over List.range (order-preserving)                                       │
│ get_current_epoch                   │ same                        │ —                                                                                           │
│ get_total_balance                   │ same                        │ takes Finset (python Set); sum order-independent                                            │
│ get_total_active_balance            │ same                        │ —                                                                                           │
│ SignedBeaconBlock                   │ same (Types.lean)           │ projected: message + its root — hash_tree_root absorbed into the wire object (design §12);  │
│                                     │                             │ signature absorbed into Externals.state_transition                                          │
│ AttestationData                     │ same                        │ transcribed in full                                                                         │
│ IndexedAttestation / Attestation    │ same / abbrev to it         │ wire Attestation = its indexed projection; aggregation-bits → indices                       │
│                                     │                             │ (get_indexed_attestation) and BLS absorbed into Externals.is_valid_indexed_attestation      │
│                                     │                             │ (design §12)                                                                                │
│ AttesterSlashing                    │ same                        │ transcribed in full                                                                         │
│ is_slashable_attestation_data       │ same                        │ transcribed in full; returns Bool (decide)                                                  │
│ BeaconState (extended)              │ same                        │ gains genesis_time, finalized_checkpoint — read by get_forkchoice_store / on_block /        │
│                                     │                             │ compute_pulled_up_tip (design §13)                                                          │
│ Externals (extended)                │ same                        │ gains state_transition (Option: none = python raise, validate_result=True absorbed),        │
│                                     │                             │ process_justification_and_finalization, is_valid_indexed_attestation (design §13)           │
│ ATTESTATION_DUE_BPS_GLOAS,          │ Config.attestation_due_bps, │ Gloas mainnet 2500 / 1                                                                      │
│ MIN_SEED_LOOKAHEAD                  │ Config.min_seed_lookahead   │                                                                                             │
│ BASIS_POINTS, UINT64_MAX            │ same (Config.lean)          │ constants 10000 / 2^64 − 1                                                                  │
└─────────────────────────────────────┴─────────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Fork-choice environment (`Spec/Model/ForkChoice.lean`)

```text
┌─────────────────────────────────────────┬────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec (fork-choice.md)                   │ Lean                       │ Deviations / notes                                                                           │
├─────────────────────────────────────────┼────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ ForkChoiceNode, LatestMessage           │ same (Types.lean)          │ —                                                                                            │
│ Store                                   │ same                       │ dicts totalized (design §3); block_roots : List Root = dict key order; checkpoint_state_keys │
│                                         │                            │ : Finset = checkpoint_states domain (membership test in store_target_checkpoint_state —      │
│                                         │                            │ design §14); block_timeliness (Option) written by record_block_timeliness, read by           │
│                                         │                            │ update_proposer_boost_root, unread by the FCR itself                                         │
│ get_slots_since_genesis                 │ same                       │ time - genesis_time truncates if time < genesis_time (store invariant: never)                │
│ get_current_slot                        │ same                       │ —                                                                                            │
│ get_current_store_epoch                 │ same                       │ —                                                                                            │
│ compute_slots_since_epoch_start         │ same                       │ subtraction always non-negative                                                              │
│ get_ancestor                            │ get_ancestor_aux + wrapper │ fuel block.slot + 1 (design §4); fuel-out returns current node (python diverges)             │
│ is_ancestor                             │ same                       │ —                                                                                            │
│ calculate_committee_fraction            │ same                       │ transcribed for Gloas is_head_weak                                                           │
│ get_checkpoint_block                    │ same                       │ —                                                                                            │
│ get_supported_node                      │ same                       │ compares message slot with block slot; then uses payload presence                            │
│ get_attestation_score                   │ same                       │ list-comprehension = List.filter/map/sum; a vote counts for node when node is an ancestor of │
│                                         │                            │ the supported node — is_ancestor (supported) node, argument order verified                   │
│ compute_proposer_score                  │ same                       │ —                                                                                            │
│ get_proposer_score                      │ same                       │ —                                                                                            │
│ get_weight                              │ same                       │ Root() = Inhabited.default; conditional boost as if-expression; boost applies when the       │
│                                         │                            │ queried node is an ancestor of proposer_boost_node — is_ancestor proposer_boost_node node,   │
│                                         │                            │ argument order verified                                                                      │
│ get_voting_source                       │ same                       │ —                                                                                            │
│ filter_block_tree                       │ filter_block_tree_aux      │ returns (viable, added roots); output dict → insertion-ordered List (design §8);             │
│                                         │                            │ any(children) = non-emptiness; fuel block_roots.length + 1; python's unconditional block =   │
│                                         │                            │ store.blocks[block_root] binding is dropped (value never needed in the root-list encoding) — │
│                                         │                            │ a python-divergence point when the base root is absent from the dict (python KeyErrors, Lean │
│                                         │                            │ proceeds on junk; outside the well-formed domain)                                            │
│ get_filtered_block_tree                 │ same                       │ returns the root list                                                                        │
│ get_node_children                       │ same                       │ takes the root list; block values looked up in store (design §8)                             │
│ get_head                                │ get_head_aux + wrapper     │ List.argmax uses the Gloas weight/root/status key and keeps the first maximum; fuel 2 *      │
│                                         │                            │ blocks.length + 2                                                                            │
│ update_checkpoints,                     │ Handlers.lean              │ transcribed — see "Fork-choice handlers" section below                                       │
│ update_unrealized_checkpoints,          │                            │                                                                                              │
│ pull-up/on-tick/on-attestation/on-block │                            │                                                                                              │
│ helper chains, the four handlers,       │                            │                                                                                              │
│ get_forkchoice_store                    │                            │                                                                                              │
│ seconds_to_milliseconds                 │ same                       │ overflow guard transcribed literally (UINT64_MAX constant) although ℕ cannot overflow        │
│ get_slot_component_duration_ms          │ same                       │ —                                                                                            │
│ get_attestation_due_ms                  │ same                       │ —                                                                                            │
│ remaining proposer-reorg helpers        │ —                          │ not called by the FCR or the transcribed handlers; out of scope                              │
│ (is_parent_strong, get_proposer_head),  │                            │                                                                                              │
│ reorg cutoff and                        │                            │                                                                                              │
│ aggregate/sync/contribution deadlines   │                            │                                                                                              │
│ get_latest_message_epoch                │ same                       │ derives epoch from the message slot and cfg                                                  │
└─────────────────────────────────────────┴────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## FCR store + misc/state helpers (`Spec/Model/FCRStore.lean`)

```text
┌─────────────────────────────┬──────────────────────────────────┬────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec (fast-confirmation.md) │ Lean                             │ Deviations / notes                                                                         │
├─────────────────────────────┼──────────────────────────────────┼────────────────────────────────────────────────────────────────────────────────────────────┤
│ FastConfirmationStore       │ same                             │ —                                                                                          │
│ get_fast_confirmation_store │ same                             │ the SHOULD prose (initialize together with the fork-choice store, same trusted checkpoint) │
│                             │                                  │ is represented by Execution.fcr v 0 = get_fast_confirmation_store (E.store v 0)            │
│                             │                                  │ (Execution.lean)                                                                           │
│ get_node_for_root           │ same                             │ Gloas PENDING node                                                                         │
│ get_block_slot              │ same                             │ —                                                                                          │
│ get_block_epoch             │ same                             │ —                                                                                          │
│ get_checkpoint_for_block    │ same                             │ —                                                                                          │
│ get_current_target          │ same                             │ —                                                                                          │
│ is_start_slot_at_epoch      │ same                             │ —                                                                                          │
│ get_ancestor_roots          │ get_ancestor_roots_aux + wrapper │ Option worker: none = terminal unreached → [] (design §5); oldest→newest,                  │
│                             │                                  │ terminal-exclusive, block-inclusive; fuel block.slot + 1                                   │
│ get_slot_committee          │ same                             │ over abstract Externals shuffling; python Set = Finset.biUnion over Finset.range; "MUST    │
│                             │                                  │ support epochs from current_epoch - 2" is a semantic obligation on Externals instances     │
│ get_pulled_up_head_state    │ same                             │ process_slots abstract (total — it absorbs python's assert state.slot < slot, which cannot │
│                             │                                  │ fire at this guarded call site); python copy() moot under state-passing                    │
│ get_previous_balance_source │ same                             │ —                                                                                          │
│ get_current_balance_source  │ same                             │ —                                                                                          │
└─────────────────────────────┴──────────────────────────────────┴────────────────────────────────────────────────────────────────────────────────────────────┘
```

## LMD-GHOST helpers (`Spec/Model/LMDHelpers.lean`)

```text
┌───────────────────────────────────────────────────┬──────┬──────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec                                              │ Lean │ Deviations / notes                                                                       │
├───────────────────────────────────────────────────┼──────┼──────────────────────────────────────────────────────────────────────────────────────────┤
│ get_block_support_between_slots                   │ same │ range(a, b+1) = Finset.Icc a b (empty when a > b); membership match via Option.any       │
│ is_full_validator_set_covered                     │ same │ slots_per_epoch - 1 non-truncating by Config.slots_per_epoch_pos                         │
│ adjust_committee_weight_estimate_to_ensure_safety │ same │ 999/1000 literals kept (spec's per-mille encoding)                                       │
│ estimate_committee_weight_between_slots           │ same │ all four branches literal; every - non-negative in-branch                                │
│ get_equivocation_score                            │ same │ intersection = Finset ∩; (spec has no slashed-filter here — preserved)                   │
│ compute_adversarial_weight                        │ same │ guarded subtraction literal                                                              │
│ get_adversarial_weight                            │ same │ Slot(current_slot - 1): at current_slot = 0, ℕ truncates to 0 where python uint64 would  │
│                                                   │      │ raise — benign because at slot 0 no call path evaluates it against nonempty content (all │
│                                                   │      │ chain segments are empty or short-circuited), not because slot 0 is pre-genesis          │
│ compute_empty_slot_support_discount               │ local│ payload-aware parent support; see gloas-spec-deviation.md                                │
│ get_support_discount                              │ same │ —                                                                                        │
│ compute_safety_threshold                          │ same │ the spec's own underflow guard transcribes exactly to ℕ                                  │
│ is_one_confirmed                                  │ same │ strict >; the source optimistic-sync precondition remains an external input-domain       │
│                                                   │      │ obligation; Gloas payload verification is concrete                                       │
│ is_confirmed_chain_safe                           │ same │ early return False = if/else; current_epoch - 1 reached only with current_epoch ≥ 2      │
└───────────────────────────────────────────────────┴──────┴──────────────────────────────────────────────────────────────────────────────────────────┘
```

## FFG helpers (`Spec/Model/FFGHelpers.lean`)

```text
┌───────────────────────────────────────────────┬──────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec                                          │ Lean │ Deviations / notes                                                                           │
├───────────────────────────────────────────────┼──────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ get_current_target_score                      │ same │ —                                                                                            │
│ compute_honest_ffg_support_for_current_target │ same │ total - ffg_weight_till_now non-negative (within-epoch estimate ≤ total); two current_slot - │
│                                               │      │ 1 sites use saturating ℕ subtraction; 100 - confirmation_byzantine_threshold non-truncating  │
│                                               │      │ by Config.confirmation_byzantine_threshold_le                                                │
│ will_no_conflicting_checkpoint_be_justified   │ same │ —                                                                                            │
│ will_current_target_be_justified              │ same │ —                                                                                            │
└───────────────────────────────────────────────┴──────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Top level (`Spec/Model/Confirmation.lean`)

```text
┌────────────────────────────────────┬───────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec                               │ Lean                      │ Deviations / notes                                                                          │
├────────────────────────────────────┼───────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ update_fast_confirmation_variables │ same                      │ mutation → chained record updates, order preserved (design §6)                              │
│ find_latest_confirmed_descendant   │ same + …_prev_epoch_loop, │ for … break loops → structural recursions carrying the accumulator (design §6); loop-2's    │
│                                    │ …_tentative_loop          │ nested if not will…: break = the conjunction epoch-advance ∧ ¬will…; canonical_roots        │
│                                    │                           │ recomputed after loop 1, as in python                                                       │
│ get_latest_confirmed               │ same                      │ the four restart booleans kept as named lets mirroring python locals; python's              │
│                                    │                           │ local-variable reassignment = let-shadowing — the staleness check and the final advance     │
│                                    │                           │ guard read the *post-revert/post-restart* binding, and find_latest_confirmed_descendant     │
│                                    │                           │ receives the original fcr_store alongside the updated local, exactly as python (verified)   │
│ on_fast_confirmation               │ same                      │ Execution.fcr models the handler timing rules (once per slot, before attestation due, after │
│                                    │                           │ applying past-slot attestations): the call occurs at the first second of each slot (before  │
│                                    │                           │ the attestation-due cutoff), after that second's events — under                             │
│                                    │                           │ Synchrony.attestation_delivery these are exactly the past-slot attestations                 │
└────────────────────────────────────┴───────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Fork-choice handlers (`Spec/Model/Handlers.lean`)

```text
┌────────────────────────────────────────────┬───────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec (fork-choice.md)                      │ Lean                  │ Deviations / notes                                                                           │
├────────────────────────────────────────────┼───────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ update_checkpoints                         │ same                  │ total Store → Store; python's two sequential ifs = let-shadowing                             │
│ update_unrealized_checkpoints              │ same                  │ as update_checkpoints                                                                        │
│ compute_pulled_up_tip                      │ same                  │ process_justification_and_finalization abstract (Externals); python copy() moot under        │
│                                            │                       │ state-passing; unrealized_justifications write = Function.update (no domain field — the dict │
│                                            │                       │ is never iterated)                                                                           │
│ on_tick_per_slot                           │ same                  │ Root() = Inhabited.default; both ifs literal                                                 │
│ on_tick                                    │ on_tick_aux + wrapper │ catch-up while-loop → fuel tick_slot + 1 (advances a slot per iteration only when slot       │
│                                            │                       │ boundaries land on whole seconds — 1000 ∣ slot_duration_ms, a SpecAssumptions conjunct;      │
│                                            │                       │ fuel-out = python's nontermination, design §11a); time - store.genesis_time truncates where  │
│                                            │                       │ python uint64 raises — unreachable from trajectories (time_at increasing)                    │
│ validate_target_epoch_against_current_time │ same                  │ assert-only body → Bool; current_epoch - 1 is the spec's explicit saturating subtraction     │
│ validate_on_attestation                    │ same                  │ assert-only body → Bool (false = "delay consideration"/drop); if not is_from_block: =        │
│                                            │                       │ short-circuit is_from_block ||; in store.blocks tested against block_roots; assert order     │
│                                            │                       │ preserved by the && chain                                                                    │
│ store_target_checkpoint_state              │ same                  │ target not in store.checkpoint_states = checkpoint_state_keys membership (design §14);       │
│                                            │                       │ process_slots abstract, the spec's own slot guard transcribed; copy moot                     │
│ update_latest_messages                     │ same                  │ for-loop → List.foldl over the non-equivocating filter; i not in … or slot > = Option match  │
│ record_block_timeliness                    │ same                  │ store.time - store.genesis_time truncates (store invariant WellFormedStore.time_ge_genesis); │
│                                            │                       │ writes both attestation and PTC deadline results                                             │
│ compute_shuffling_lookahead_start_slot     │ same                  │ epoch - MIN_SEED_LOOKAHEAD is the spec's explicit saturating subtraction                     │
│ compute_shuffling_dependent_slot           │ same                  │ lookahead_start_slot - 1 is the spec's explicit saturating subtraction                       │
│ get_shuffling_dependent_root               │ same                  │ hash_tree_root/Root() are represented by the projected root and totalized node model (design │
│                                            │                       │ §12)                                                                                         │
│ update_proposer_boost_root                 │ same                  │ attestation bit of store.block_timeliness[root], totalized by .getD (false, false) — default │
│                                            │                       │ unreachable (on_block sets it immediately before); dependent roots are computed at the       │
│                                            │                       │ current store epoch                                                                          │
│ on_block                                   │ same                  │ handler asserts → Option (Store Root) (none = not applied); known roots return the unchanged │
│                                            │                       │ store before validation; parent_root in store.block_states tested against block_roots        │
│                                            │                       │ (shared key set — design §14); state_transition abstract, none = python raise;               │
│                                            │                       │ hash_tree_root(block) = signed_block.root (design §12); fresh dict insert = Function.update  │
│                                            │                       │ + append (design §14); head computed before the insert — python mutation order preserved     │
│ on_attestation                             │ same                  │ asserts → Option; **documented divergence**: on the signature-failure path the reference     │
│                                            │                       │ python's in-place checkpoint-state cache write survives the raise — the model discards it,   │
│                                            │                       │ the normative "invalid calls to handlers must not modify store" reading (see docstring);     │
│                                            │                       │ get_indexed_attestation absorbed (wire attestation already indexed — design §12);            │
│                                            │                       │ is_from_block := false default kept                                                          │
│ on_attester_slashing                       │ same                  │ asserts → Option; python set intersection = toFinset ∩; the add-loop = Finset ∪              │
│ get_forkchoice_store                       │ same                  │ takes SignedBeaconBlock (the root travels on the wire object); python's assert               │
│                                            │                       │ anchor_block.state_root == hash_tree_root(anchor_state) omitted by the executable;           │
│                                            │                       │ accepted trajectory.genesis requires the external AnchorCommitsToState contract,             │
│                                            │                       │ parent/root inequality (design §11a); singleton dicts = Function.update over junk-totalized  │
│                                            │                       │ defaults                                                                                     │
└────────────────────────────────────────────┴───────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Honest validator (`Spec/Model/Validator.lean`)

```text
┌─────────────────────────┬─────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec (validator.md)     │ Lean                    │ Deviations / notes                                                                          │
├─────────────────────────┼─────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ "Attestation data"      │ honest_attestation_data │ head = get_head at voting time; head-state pull-up guarded (python process_slots asserts    │
│                         │                         │ state.slot < slot); **documented substitution**: target root via the store ancestor walk    │
│                         │                         │ get_checkpoint_block in place of the state's get_block_root history —                       │
│                         │                         │ validate_on_attestation asserts exactly this equality, so they coincide on every accepted   │
│                         │                         │ attestation (design §15)                                                                    │
│ "Construct attestation" │ honest_attestation      │ singleton attesting_indices = [validator_index] (aggregation-bits projection); BLS absorbed │
│                         │                         │ (design §12)                                                                                │
└─────────────────────────┴─────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Executions (`Spec/Model/Execution.lean`) — model-only; no python counterparts

```text
┌───────────────────────┬──────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Renders               │ Lean                         │ Notes                                                                                        │
├───────────────────────┼──────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ wire messages         │ Event                        │ block / attestation / attester slashing / envelope with observation / PTC message            │
│ handler dispatch      │ apply_event                  │ none = the handler rejected the message                                                      │
│ protocol execution    │ Execution                    │ genesis store, per-node/per-second schedule, honest set, ground-truth committee,             │
│                       │                              │ per-(validator, slot) vote record (design §16)                                               │
│ clock                 │ time_at, slot_at, slot_start │ slot_at = the get_current_slot arithmetic on time_at; slot_start truncates to 0 for slots    │
│                       │                              │ before the genesis store's time, exact under 1000 ∣ slot_duration_ms (a SpecAssumptions      │
│                       │                              │ conjunct)                                                                                    │
│ store trajectory      │ Execution.store              │ second 0 = genesis store (events scheduled at second 0 ignored — trimmed adversarial power,  │
│                       │                              │ design §11a); at n+1: on_tick, then the second's events left-to-right, rejected events .getD │
│                       │                              │ no-ops                                                                                       │
│ FCR trajectory        │ Execution.fcr                │ the read-only store field tracks E.store every second; on_fast_confirmation at the first     │
│                       │                              │ second of each slot (slot-advance test), after that second's events — the handler's mandated │
│                       │                              │ window (design §16)                                                                          │
│ confirmed root        │ Execution.confirmed          │ (E.fcr v n).confirmed_root                                                                   │
│ store well-formedness │ WellFormedStore              │ structural invariants (nodup keys, clock ≥ genesis, parent slots strictly decrease,          │
│                       │                              │ justified/finalized known, finalized ≼ justified), with handler-preservation lemmas in the   │
│                       │                              │ proof layer                                                                                  │
└───────────────────────┴──────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Assumption records (`Spec/Model/Assumptions.lean`)

```text
┌─────────────────────────────────────────┬────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec origin                             │ Lean                               │ Notes                                                                                        │
├─────────────────────────────────────────┼────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ — (ground truth)                        │ anchor_state, registry, weight_of, │ derived quantities over an Execution (anchor state = the genesis store's                     │
│                                         │ weight, total_active,              │ justified-checkpoint state)                                                                  │
│                                         │ span_committee                     │                                                                                              │
│ validator.md "Attesting" + slashing     │ HonestBehavior                     │ votes_head (the recorded vote is honest_attestation from the node's own store at a second of │
│ discipline                              │                                    │ the assigned slot), votes_assigned, no_forgery (BLS unforgeability + equivocation slashing)  │
│ FCR intro synchrony sentence            │ NextSlotSynchronyPremises               │ The primary theorem uses attestation_delivery (slot-s honest attestations scheduled at the   │
│                                         │                                    │ first second of slot s+1; Gloas acceptance also needs the payload for index 1), block_relay  │
│                                         │                                    │ (known blocks propagate by the following slot), and attester_slashing_relay (known           │
│                                         │                                    │ equivocation evidence propagates by the following slot). The fields hold throughout the      │
│                                         │                                    │ checked execution, so this is the GST-0 specialization of the paper's post-GST timing model. │
│ behavior of the abstracted beacon-chain │ BeaconExternalsPremises                 │ slot/registry behavior of                                                                    │
│ functions                               │                                    │ process_slots/state_transition/process_justification_and_finalization; committees_agree (the │
│                                         │                                    │ spec's committee-consistency window, idealized to the whole execution);                      │
│                                         │                                    │ honest_attestation_valid; committee_assignment_unique (one assigned slot per epoch)          │
│ balance-source design note (static set) │ StaticValidatorSet                 │ the trusted anchor lies inside the verification horizon and validator activity is constant   │
│                                         │                                    │ below that horizon (paper Assumption 1); genesis registry constancy is derived from the      │
│                                         │                                    │ already-required get_forkchoice_store initialization                                         │
│ CONFIRMATION_BYZANTINE_THRESHOLD + the  │ ByzantineWeightPremises                     │ balance quantization, estimate_sound (the estimate upper-bounds actual span-committee        │
│ 5‰ estimation note                      │                                    │ weight), and span_fraction (the non-honest span weight is at most the configured percentage, │
│                                         │                                    │ cross-multiplied)                                                                            │
└─────────────────────────────────────────┴────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Accepted theorem surface

```text
┌─────────────────────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Spec claim                              │ Lean                                                                                            │ Notes                                                                                        │
├─────────────────────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ "will remain canonical in the view of   │ NextSlotSafetyPremises.selected_result_safe_from_next_slot_of_scheduled_call │ Spec-correspondence lemma for the exact mandatory boundary-call helper result under the      │
│ all honest validators starting from the │                                                                                                 │ primary reset-free accepted bundle and literal selector guard. It maps the                  │
│ current moment in time"                 │                                                                                                 │ `find_latest_confirmed_descendant` note; it is not a review claim. Carried input safety       │
│ (find_latest_confirmed_descendant note) │                                                                                                 │ comes from the preceding following-slot invariant; causal finalization lag forces a          │
│                                         │                                                                                                 │ selector-eligible finalized reset to the anchor; observed input safety is derived dynamically.│
│ get_latest_confirmed may be called at   │ extra_query_changes_head_counterexample,                                                       │ universal action-prefix safety is false: at one global query position the actor has          │
│ any point in a slot + the helper's      │ extra_query_changes_head_counterexample                                       │ processed the synchronized vote and returns the candidate while another honest endpoint has  │
│ all-honest current-moment note          │                                                                                                 │ processed only the preceding sibling block. The first theorem proves the full non-FFG        │
│                                         │                                                                                                 │ environment and also shows actor-side ground replay coexists with failed endpoint ancestry;  │
│                                         │                                                                                                 │ the second uses pinned economic values 40/25 and threshold 95, but is not a complete         │
│                                         │                                                                                                 │ mainnet_config instantiation                                                                 │
│ Primary accepted stored-cache safety    │ NextSlotSafetyPremises,                                                     │ every stored honest output is on every in-horizon honest head from the following slot.       │
│                                         │ ConfirmedRootSafeFromNextSlot,                                                                  │ Finalized and active-observed resets are derived from accepted execution/FFG dynamics; the   │
│                                         │ confirmed_root_safe_from_next_slot                                                                   │ bundle has no reset-specific law. This is a separate accepted premise surface, not a bridge  │
│                                         │                                                                                                 │ from SpecAssumptions, and it makes no optional in-slot action-prefix claim                   │
│ Finalized fallback timing used by the   │ finalizedReset_safeFrom_of_nextSlotSynchrony                                                    │ safety from the following slot, derived from accepted certificates and ordinary synchrony    │
│ primary theorem                         │                                                                                                 │ without a same-moment adoption law                                                           │
└─────────────────────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Out of scope (sanctioned)

- Proposer-reorg helpers that are not called by the FCR or its handlers.
  `is_head_weak` and `calculate_committee_fraction` are in scope in Gloas.
- validator.md block-proposal and aggregation duties: the FCR's safety
  guarantee does not rely on honest proposals (proposer boost is handled
  adversarially), and aggregation is invisible to the indexed-attestation
  projection (design §12).
