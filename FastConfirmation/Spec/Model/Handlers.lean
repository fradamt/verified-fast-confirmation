import Mathlib.Logic.Function.Basic
import FastConfirmation.Spec.Model.ForkChoice

/-!
# Spec / Model / Handlers

The `specs/phase0/fork-choice.md` store-mutating helpers and handlers that
drive store evolution: `update_checkpoints`, `update_unrealized_checkpoints`,
`compute_pulled_up_tip`, the `on_tick`/`on_attestation`/`on_block` helper
chains, the four handlers, and `get_forkchoice_store`.

Python mutation → `Store → … → Store`; python `assert`-rejection inside
handlers → `Option (Store Root)` (`none` = the message is not applied — the
spec's "delay consideration" / drop); helpers whose python body is only
asserts return `Bool`. Dict writes preserve python dict semantics
(`Function.update` + key-list append only if absent). See
`docs/spec-model-design.md`, decisions 11–14.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `update_checkpoints`: Update checkpoints in store if necessary.
```python
if justified_checkpoint.epoch > store.justified_checkpoint.epoch:
    store.justified_checkpoint = justified_checkpoint
if finalized_checkpoint.epoch > store.finalized_checkpoint.epoch:
    store.finalized_checkpoint = finalized_checkpoint
``` -/
def update_checkpoints (store : Store Root)
    (justified_checkpoint finalized_checkpoint : Checkpoint Root) : Store Root :=
  -- Update justified checkpoint
  let store :=
    if justified_checkpoint.epoch > store.justified_checkpoint.epoch then
      { store with justified_checkpoint := justified_checkpoint }
    else store
  -- Update finalized checkpoint
  if finalized_checkpoint.epoch > store.finalized_checkpoint.epoch then
    { store with finalized_checkpoint := finalized_checkpoint }
  else store

/-- `update_unrealized_checkpoints`: Update unrealized checkpoints in store if
necessary.
```python
if unrealized_justified_checkpoint.epoch > store.unrealized_justified_checkpoint.epoch:
    store.unrealized_justified_checkpoint = unrealized_justified_checkpoint
if unrealized_finalized_checkpoint.epoch > store.unrealized_finalized_checkpoint.epoch:
    store.unrealized_finalized_checkpoint = unrealized_finalized_checkpoint
``` -/
def update_unrealized_checkpoints (store : Store Root)
    (unrealized_justified_checkpoint unrealized_finalized_checkpoint : Checkpoint Root) :
    Store Root :=
  -- Update unrealized justified checkpoint
  let store :=
    if unrealized_justified_checkpoint.epoch >
        store.unrealized_justified_checkpoint.epoch then
      { store with unrealized_justified_checkpoint := unrealized_justified_checkpoint }
    else store
  -- Update unrealized finalized checkpoint
  if unrealized_finalized_checkpoint.epoch >
      store.unrealized_finalized_checkpoint.epoch then
    { store with unrealized_finalized_checkpoint := unrealized_finalized_checkpoint }
  else store

/-- `compute_pulled_up_tip`:
```python
state = store.block_states[block_root].copy()
# Pull up the post-state of the block to the next epoch boundary
process_justification_and_finalization(state)
store.unrealized_justifications[block_root] = state.current_justified_checkpoint
update_unrealized_checkpoints(store, state.current_justified_checkpoint, state.finalized_checkpoint)
# If the block is from a prior epoch, apply the realized values
block_epoch = compute_epoch_at_slot(store.blocks[block_root].slot)
current_epoch = get_current_store_epoch(store)
if block_epoch < current_epoch:
    update_checkpoints(store, state.current_justified_checkpoint, state.finalized_checkpoint)
``` -/
def compute_pulled_up_tip (store : Store Root) (block_root : Root) : Store Root :=
  let state :=
    ext.process_justification_and_finalization (store.block_states block_root)
  let store :=
    { store with
      unrealized_justifications :=
        Function.update store.unrealized_justifications block_root
          state.current_justified_checkpoint }
  let store :=
    update_unrealized_checkpoints store state.current_justified_checkpoint
      state.finalized_checkpoint
  let block_epoch := compute_epoch_at_slot cfg (store.blocks block_root).slot
  let current_epoch := get_current_store_epoch cfg store
  if block_epoch < current_epoch then
    update_checkpoints store state.current_justified_checkpoint state.finalized_checkpoint
  else store

/-- `on_tick_per_slot`:
```python
previous_slot = get_current_slot(store)
store.time = time
current_slot = get_current_slot(store)
if current_slot > previous_slot:
    store.proposer_boost_root = Root()
if current_slot > previous_slot and compute_slots_since_epoch_start(current_slot) == 0:
    update_checkpoints(store, store.unrealized_justified_checkpoint,
                       store.unrealized_finalized_checkpoint)
``` -/
def on_tick_per_slot (store : Store Root) (time : ℕ) : Store Root :=
  let previous_slot := get_current_slot cfg store
  -- Update store time
  let store := { store with time := time }
  let current_slot := get_current_slot cfg store
  -- If this is a new slot, reset store.proposer_boost_root
  let store :=
    if current_slot > previous_slot then
      { store with proposer_boost_root := (default : Root) }
    else store
  -- If a new epoch, pull-up justification and finalization from previous epoch
  if current_slot > previous_slot ∧
      compute_slots_since_epoch_start cfg current_slot = 0 then
    update_checkpoints store store.unrealized_justified_checkpoint
      store.unrealized_finalized_checkpoint
  else store

/-- Fuel-bounded worker for `on_tick`'s catch-up loop (each iteration is meant
to advance the current slot by one; fuel `tick_slot + 1` suffices whenever the
loop advances, which holds for configs where `SLOT_DURATION_MS` per-slot
boundaries are representable in whole seconds — e.g. mainnet 12000ms).
```python
while get_current_slot(store) < tick_slot:
    previous_time = store.genesis_time + (get_current_slot(store) + 1) * SLOT_DURATION_MS // 1000
    on_tick_per_slot(store, previous_time)
``` -/
def on_tick_aux (tick_slot : ℕ) : ℕ → Store Root → Store Root
  | 0, store => store
  | fuel + 1, store =>
    if get_current_slot cfg store < tick_slot then
      let previous_time :=
        store.genesis_time + (get_current_slot cfg store + 1) * cfg.slot_duration_ms / 1000
      on_tick_aux tick_slot fuel (on_tick_per_slot cfg store previous_time)
    else store

/-- `on_tick`: catch up slot by slot so every previous slot is processed with
`on_tick_per_slot`, then process the actual `time`.
```python
tick_slot = (time - store.genesis_time) * 1000 // SLOT_DURATION_MS
while get_current_slot(store) < tick_slot: ...
on_tick_per_slot(store, time)
``` -/
def on_tick (store : Store Root) (time : ℕ) : Store Root :=
  let tick_slot := (time - store.genesis_time) * 1000 / cfg.slot_duration_ms
  let store := on_tick_aux cfg tick_slot (tick_slot + 1) store
  on_tick_per_slot cfg store time

/-- `validate_target_epoch_against_current_time` (python body is asserts;
`true` = valid):
```python
target = attestation.data.target
current_epoch = get_current_store_epoch(store)
previous_epoch = saturating_sub(current_epoch, 1)
assert target.epoch in [current_epoch, previous_epoch]
``` -/
def validate_target_epoch_against_current_time (store : Store Root)
    (attestation : Attestation Root) : Bool :=
  let target := attestation.data.target
  -- Attestations must be from the current or previous epoch
  let current_epoch := get_current_store_epoch cfg store
  let previous_epoch := current_epoch - 1
  decide (target.epoch = current_epoch ∨ target.epoch = previous_epoch)

/-- `validate_on_attestation` (python body is asserts; `true` = valid — a
failing assert means "delay consideration" / reject for now):
```python
target = attestation.data.target
if not is_from_block:
    validate_target_epoch_against_current_time(store, attestation)
assert target.epoch == compute_epoch_at_slot(attestation.data.slot)
assert target.root in store.blocks
assert attestation.data.beacon_block_root in store.blocks
assert store.blocks[attestation.data.beacon_block_root].slot <= attestation.data.slot
assert target.root == get_checkpoint_block(store, attestation.data.beacon_block_root, target.epoch)
assert get_current_slot(store) >= attestation.data.slot + 1
``` -/
def validate_on_attestation (store : Store Root) (attestation : Attestation Root)
    (is_from_block : Bool) : Bool :=
  let target := attestation.data.target
  -- If not from a block, check the target epoch scope
  (is_from_block || validate_target_epoch_against_current_time cfg store attestation) &&
  -- The epoch number and slot number must match
  decide (target.epoch = compute_epoch_at_slot cfg attestation.data.slot) &&
  -- Attestation target must be for a known block
  decide (target.root ∈ store.block_roots) &&
  -- Attestations must be for a known block
  decide (attestation.data.beacon_block_root ∈ store.block_roots) &&
  -- Attestations must not be for blocks in the future
  decide ((store.blocks attestation.data.beacon_block_root).slot ≤ attestation.data.slot) &&
  -- LMD vote must be consistent with FFG vote target
  decide (target.root =
    get_checkpoint_block cfg store attestation.data.beacon_block_root target.epoch) &&
  -- Attestations can only affect the fork choice of subsequent slots
  decide (get_current_slot cfg store ≥ attestation.data.slot + 1)

/-- `store_target_checkpoint_state`:
```python
if target not in store.checkpoint_states:
    base_state = store.block_states[target.root].copy()
    if base_state.slot < compute_start_slot_at_epoch(target.epoch):
        process_slots(base_state, compute_start_slot_at_epoch(target.epoch))
    store.checkpoint_states[target] = base_state
``` -/
def store_target_checkpoint_state (store : Store Root) (target : Checkpoint Root) :
    Store Root :=
  -- Store target checkpoint state if not yet seen
  if target ∉ store.checkpoint_state_keys then
    let base_state := store.block_states target.root
    let base_state :=
      if base_state.slot < compute_start_slot_at_epoch cfg target.epoch then
        ext.process_slots base_state (compute_start_slot_at_epoch cfg target.epoch)
      else base_state
    { store with
      checkpoint_state_keys := insert target store.checkpoint_state_keys
      checkpoint_states := Function.update store.checkpoint_states target base_state }
  else store

/-- `update_latest_messages`:
```python
target = attestation.data.target
beacon_block_root = attestation.data.beacon_block_root
non_equivocating_attesting_indices = [
    i for i in attesting_indices if i not in store.equivocating_indices
]
for i in non_equivocating_attesting_indices:
    if i not in store.latest_messages or target.epoch > store.latest_messages[i].epoch:
        store.latest_messages[i] = LatestMessage(epoch=target.epoch, root=beacon_block_root)
``` -/
def update_latest_messages (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    Store Root :=
  let target := attestation.data.target
  let beacon_block_root := attestation.data.beacon_block_root
  let non_equivocating_attesting_indices :=
    attesting_indices.filter (fun i => decide (i ∉ store.equivocating_indices))
  non_equivocating_attesting_indices.foldl
    (fun store i =>
      let should_update :=
        match store.latest_messages i with
        | none => true
        | some latest_message => decide (target.epoch > latest_message.epoch)
      if should_update then
        { store with
          latest_messages :=
            Function.update store.latest_messages i
              (some (LatestMessage.mk target.epoch beacon_block_root)) }
      else store)
    store

/-- `record_block_timeliness`:
```python
block = store.blocks[root]
seconds_since_genesis = store.time - store.genesis_time
time_into_slot_ms = seconds_to_milliseconds(seconds_since_genesis) % SLOT_DURATION_MS
attestation_threshold_ms = get_attestation_due_ms()
is_before_attesting_interval = time_into_slot_ms < attestation_threshold_ms
is_timely = get_current_slot(store) == block.slot and is_before_attesting_interval
store.block_timeliness[root] = is_timely
``` -/
def record_block_timeliness (store : Store Root) (root : Root) : Store Root :=
  let block := store.blocks root
  let seconds_since_genesis := store.time - store.genesis_time
  let time_into_slot_ms :=
    seconds_to_milliseconds seconds_since_genesis % cfg.slot_duration_ms
  let attestation_threshold_ms := get_attestation_due_ms cfg
  let is_before_attesting_interval :=
    decide (time_into_slot_ms < attestation_threshold_ms)
  let is_timely :=
    decide (get_current_slot cfg store = block.slot) && is_before_attesting_interval
  { store with
    block_timeliness := Function.update store.block_timeliness root (some is_timely) }

/-- `compute_shuffling_lookahead_start_slot`:
```python
def compute_shuffling_lookahead_start_slot(epoch: Epoch) -> Slot:
    lookahead_epoch = saturating_sub(epoch, MIN_SEED_LOOKAHEAD)
    return compute_start_slot_at_epoch(lookahead_epoch)
``` -/
def compute_shuffling_lookahead_start_slot (epoch : Epoch) : Slot :=
  let lookahead_epoch := epoch - cfg.min_seed_lookahead
  compute_start_slot_at_epoch cfg lookahead_epoch

/-- `compute_shuffling_dependent_slot`:
```python
def compute_shuffling_dependent_slot(epoch: Epoch) -> Slot:
    lookahead_start_slot = compute_shuffling_lookahead_start_slot(epoch)
    return saturating_sub(lookahead_start_slot, 1)
``` -/
def compute_shuffling_dependent_slot (epoch : Epoch) : Slot :=
  let lookahead_start_slot := compute_shuffling_lookahead_start_slot cfg epoch
  lookahead_start_slot - 1

/-- `get_shuffling_dependent_root`:
```python
def get_shuffling_dependent_root(store: Store, root: Root, epoch: Epoch) -> Root:
    node = ForkChoiceNode(root=root)
    dependent_slot = compute_shuffling_dependent_slot(epoch)
    return get_ancestor(store, node, dependent_slot).root
``` -/
def get_shuffling_dependent_root (store : Store Root) (root : Root) (epoch : Epoch) : Root :=
  let node := ForkChoiceNode.mk root
  let dependent_slot := compute_shuffling_dependent_slot cfg epoch
  (get_ancestor store node dependent_slot).root

/-- `update_proposer_boost_root` (python reads `store.block_timeliness[root]`,
always set by `on_block` immediately before — the `getD false` default is
unreachable there):
```python
is_first_block = store.proposer_boost_root == Root()
is_timely = store.block_timeliness[root]
epoch = get_current_store_epoch(store)
head_dependent_root = get_shuffling_dependent_root(store, head, epoch)
block_dependent_root = get_shuffling_dependent_root(store, root, epoch)
is_same_dependent_root = head_dependent_root == block_dependent_root

# Add proposer score boost if the block is timely, not conflicting with an
# existing block, with the same dependent root as the canonical chain head.
if is_timely and is_first_block and is_same_dependent_root:
    store.proposer_boost_root = root
``` -/
def update_proposer_boost_root (store : Store Root) (head root : Root) : Store Root :=
  let is_first_block := decide (store.proposer_boost_root = (default : Root))
  let is_timely := (store.block_timeliness root).getD false
  let epoch := get_current_store_epoch cfg store
  let head_dependent_root := get_shuffling_dependent_root cfg store head epoch
  let block_dependent_root := get_shuffling_dependent_root cfg store root epoch
  let is_same_dependent_root :=
    decide (head_dependent_root = block_dependent_root)
  -- Add proposer score boost if the block is timely, not conflicting with an
  -- existing block, with the same dependent root as the canonical chain head
  if is_timely && is_first_block && is_same_dependent_root then
    { store with proposer_boost_root := root }
  else store

/-- `on_block` handler. `none` = one of the python asserts failed or
`state_transition` raised (the block is not applied). A known block returns
the unchanged store. Python's `assert block.parent_root in store.block_states`
is tested against `block_roots` (`blocks` and `block_states` share their key
set by construction — design decision 14).
```python
block = signed_block.message
block_root = hash_tree_root(block)

# Return early if the block is already known
if block_root in store.blocks:
    return

# Parent block must be known
assert block.parent_root in store.block_states
# Make a copy of the state to avoid mutability issues
pre_state = store.block_states[block.parent_root].copy()
assert get_current_slot(store) >= block.slot
finalized_slot = compute_start_slot_at_epoch(store.finalized_checkpoint.epoch)
assert block.slot > finalized_slot
finalized_checkpoint_block = get_checkpoint_block(store, block.parent_root,
                                                  store.finalized_checkpoint.epoch)
assert store.finalized_checkpoint.root == finalized_checkpoint_block
state = pre_state.copy()
state_transition(state, signed_block, validate_result=True)
head = get_head(store)
store.blocks[block_root] = block
store.block_states[block_root] = state
record_block_timeliness(store, block_root)
update_proposer_boost_root(store, head.root, block_root)
update_checkpoints(store, state.current_justified_checkpoint, state.finalized_checkpoint)
compute_pulled_up_tip(store, block_root)
``` -/
def on_block (store : Store Root) (signed_block : SignedBeaconBlock Root) :
    Option (Store Root) :=
  let block := signed_block.message
  let block_root := signed_block.root
  -- Return early if the block is already known
  if block_root ∈ store.block_roots then some store
  else
    -- Parent block must be known
    if block.parent_root ∉ store.block_roots then none
    else
      let pre_state := store.block_states block.parent_root
      -- Blocks cannot be in the future
      if ¬ get_current_slot cfg store ≥ block.slot then none
      else
        -- Check that block is later than the finalized epoch slot
        let finalized_slot := compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch
        if ¬ block.slot > finalized_slot then none
        else
          -- Check block is a descendant of the finalized block
          let finalized_checkpoint_block :=
            get_checkpoint_block cfg store block.parent_root store.finalized_checkpoint.epoch
          if store.finalized_checkpoint.root ≠ finalized_checkpoint_block then none
          else
            -- Check that the block is valid and compute the post-state
            match ext.state_transition pre_state signed_block with
            | none => none
            | some state =>
              -- Compute head before applying the block
              let head := get_head cfg store
              -- Add new block and its state to the store
              let store :=
                { store with
                  block_roots := store.block_roots ++ [block_root]
                  blocks := Function.update store.blocks block_root block
                  block_states := Function.update store.block_states block_root state }
              let store := record_block_timeliness cfg store block_root
              let store := update_proposer_boost_root cfg store head.root block_root
              -- Update checkpoints in store if necessary
              let store :=
                update_checkpoints store state.current_justified_checkpoint
                  state.finalized_checkpoint
              -- Eagerly compute unrealized justification and finality
              some (compute_pulled_up_tip cfg ext store block_root)

/-- `on_attestation` handler. `none` = validation failed (python assert — the
attestation is not applied now). Note: on the python validity-failure path
*after* `store_target_checkpoint_state`, the reference implementation's
in-place checkpoint-state cache write survives the raise; this model discards
it. The discard is the **normative** behavior — fork-choice.md: "Invalid
calls to handlers must not modify store" — and the surviving write in the
reference python is an implementation artifact (observable only through
later direct `checkpoint_states` reads such as `get_weight`, on stores whose
justified checkpoint was never target-cached by a *valid* attestation).
```python
validate_on_attestation(store, attestation, is_from_block)
store_target_checkpoint_state(store, attestation.data.target)
target_state = store.checkpoint_states[attestation.data.target]
indexed_attestation = get_indexed_attestation(target_state, attestation)
assert is_valid_indexed_attestation(target_state, indexed_attestation)
update_latest_messages(store, indexed_attestation.attesting_indices, attestation)
``` -/
def on_attestation (store : Store Root) (attestation : Attestation Root)
    (is_from_block : Bool := false) : Option (Store Root) :=
  if ¬ validate_on_attestation cfg store attestation is_from_block then none
  else
    let store := store_target_checkpoint_state cfg ext store attestation.data.target
    -- Get state at the `target` to fully validate attestation
    let target_state := store.checkpoint_states attestation.data.target
    -- (the wire attestation is already its indexed projection — design §12)
    let indexed_attestation := attestation
    if ¬ ext.is_valid_indexed_attestation target_state indexed_attestation then none
    else
      -- Update latest messages for attesting indices
      some (update_latest_messages store indexed_attestation.attesting_indices attestation)

/-- `on_attester_slashing` handler (`none` = a python assert failed).
```python
attestation_1 = attester_slashing.attestation_1
attestation_2 = attester_slashing.attestation_2
assert is_slashable_attestation_data(attestation_1.data, attestation_2.data)
state = store.block_states[store.justified_checkpoint.root]
assert is_valid_indexed_attestation(state, attestation_1)
assert is_valid_indexed_attestation(state, attestation_2)
indices = set(attestation_1.attesting_indices).intersection(attestation_2.attesting_indices)
for index in indices:
    store.equivocating_indices.add(index)
``` -/
def on_attester_slashing (store : Store Root)
    (attester_slashing : AttesterSlashing Root) : Option (Store Root) :=
  let attestation_1 := attester_slashing.attestation_1
  let attestation_2 := attester_slashing.attestation_2
  if ¬ is_slashable_attestation_data attestation_1.data attestation_2.data then none
  else
    let state := store.block_states store.justified_checkpoint.root
    if ¬ ext.is_valid_indexed_attestation state attestation_1 then none
    else if ¬ ext.is_valid_indexed_attestation state attestation_2 then none
    else
      let indices :=
        attestation_1.attesting_indices.toFinset ∩ attestation_2.attesting_indices.toFinset
      some { store with equivocating_indices := store.equivocating_indices ∪ indices }

/-- `get_forkchoice_store`: the trusted-anchor initialization. The python
`assert anchor_block.state_root == hash_tree_root(anchor_state)` is
**dropped** (untranscribable in the projection — the modeled block carries no
`state_root`); anchor block/state consistency is an execution
well-formedness premise (design §11a). Dict fields outside their singleton
domains are junk-totalized.
```python
anchor_root = hash_tree_root(anchor_block)
anchor_epoch = get_current_epoch(anchor_state)
justified_checkpoint = Checkpoint(epoch=anchor_epoch, root=anchor_root)
finalized_checkpoint = Checkpoint(epoch=anchor_epoch, root=anchor_root)
proposer_boost_root = Root()
return Store(
    time=Uint64(anchor_state.genesis_time + SLOT_DURATION_MS * anchor_state.slot // 1000),
    genesis_time=anchor_state.genesis_time, ...,
    blocks={anchor_root: anchor_block.copy()},
    block_states={anchor_root: anchor_state.copy()},
    block_timeliness={},
    checkpoint_states={justified_checkpoint: anchor_state.copy()},
    latest_messages={},
    unrealized_justifications={anchor_root: justified_checkpoint})
``` -/
def get_forkchoice_store (anchor_state : BeaconState Root)
    (anchor_block : SignedBeaconBlock Root) : Store Root :=
  let anchor_root := anchor_block.root
  let anchor_epoch := get_current_epoch cfg anchor_state
  let justified_checkpoint := Checkpoint.mk anchor_epoch anchor_root
  let finalized_checkpoint := Checkpoint.mk anchor_epoch anchor_root
  let proposer_boost_root : Root := default
  { time := anchor_state.genesis_time + cfg.slot_duration_ms * anchor_state.slot / 1000
    genesis_time := anchor_state.genesis_time
    justified_checkpoint := justified_checkpoint
    finalized_checkpoint := finalized_checkpoint
    unrealized_justified_checkpoint := justified_checkpoint
    unrealized_finalized_checkpoint := finalized_checkpoint
    proposer_boost_root := proposer_boost_root
    equivocating_indices := ∅
    block_roots := [anchor_root]
    blocks := Function.update (fun _ => default) anchor_root anchor_block.message
    block_states := Function.update (fun _ => default) anchor_root anchor_state
    block_timeliness := fun _ => none
    checkpoint_state_keys := {justified_checkpoint}
    checkpoint_states := Function.update (fun _ => default) justified_checkpoint anchor_state
    latest_messages := fun _ => none
    unrealized_justifications :=
      Function.update (fun _ => default) anchor_root justified_checkpoint }

end FastConfirmation.Spec
