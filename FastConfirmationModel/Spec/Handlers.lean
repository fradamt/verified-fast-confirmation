module
public import Mathlib.Logic.Function.Basic
public import FastConfirmationModel.Spec.ForkChoice

@[expose] public section

/-!
# Spec / Model / Handlers

The Gloas store-mutating helpers and handlers, plus unchanged helpers from
`specs/phase0/fork-choice.md`, drive store evolution: `update_checkpoints`,
`update_unrealized_checkpoints`,
`compute_pulled_up_tip`, the `on_tick`/`on_attestation`/`on_block` helper
chains, the six handlers, and `get_forkchoice_store`.

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

/-- Source: `specs/phase0/fork-choice.md:494`.
`update_checkpoints`: Update checkpoints in store if necessary.
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

/-- Source: `specs/phase0/fork-choice.md:512`.
`update_unrealized_checkpoints`: Update unrealized checkpoints in store if
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

/-- Source: `specs/phase0/fork-choice.md:755`.
`compute_pulled_up_tip`:
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

/-- Source: `specs/phase0/fork-choice.md:777`.
`on_tick_per_slot`:
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

/-- Source: `specs/phase0/fork-choice.md:932`.
Fuel-bounded worker for `on_tick`'s catch-up loop (each iteration is meant
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

/-- Source: `specs/phase0/fork-choice.md:932`.
`on_tick`: catch up slot by slot so every previous slot is processed with
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

/-- Source: `specs/phase0/fork-choice.md:801`.
`validate_target_epoch_against_current_time` (python body is asserts;
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

/-- Source: `specs/gloas/fork-choice.md:889`.
`validate_on_attestation` (python body is asserts; `true` = valid — a
failing assert means "delay consideration" / reject for now):
```python
target = attestation.data.target
if not is_from_block:
    validate_target_epoch_against_current_time(store, attestation)
assert target.epoch == compute_epoch_at_slot(attestation.data.slot)
assert target.root in store.blocks
assert attestation.data.beacon_block_root in store.blocks
block_slot = store.blocks[attestation.data.beacon_block_root].slot
assert block_slot <= attestation.data.slot
assert attestation.data.index in [0, 1]
if block_slot == attestation.data.slot:
    assert attestation.data.index == 0
if attestation.data.index == 1:
    assert is_payload_verified(store, attestation.data.beacon_block_root)
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
  -- The index encodes payload presence, not the committee index.
  decide (attestation.data.index = 0 ∨ attestation.data.index = 1) &&
  (decide ((store.blocks attestation.data.beacon_block_root).slot ≠ attestation.data.slot) ||
    decide (attestation.data.index = 0)) &&
  (decide (attestation.data.index ≠ 1) ||
    is_payload_verified store attestation.data.beacon_block_root) &&
  -- LMD vote must be consistent with FFG vote target
  decide (target.root =
    get_checkpoint_block cfg store attestation.data.beacon_block_root target.epoch) &&
  -- Attestations can only affect the fork choice of subsequent slots
  decide (get_current_slot cfg store ≥ attestation.data.slot + 1)

/-- Source: `specs/phase0/fork-choice.md:845`.
`store_target_checkpoint_state`:
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

/-- Source: `specs/gloas/fork-choice.md:940`.
`update_latest_messages` compares exact slots and records payload presence.
```python
slot = attestation.data.slot
beacon_block_root = attestation.data.beacon_block_root
payload_present = attestation.data.index == 1
non_equivocating_attesting_indices = [
    i for i in attesting_indices if i not in store.equivocating_indices
]
for i in non_equivocating_attesting_indices:
    if i not in store.latest_messages or slot > store.latest_messages[i].slot:
        store.latest_messages[i] = LatestMessage(
            slot=slot, root=beacon_block_root, payload_present=payload_present)
``` -/
def update_latest_messages (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    Store Root :=
  let slot := attestation.data.slot
  let beacon_block_root := attestation.data.beacon_block_root
  let payload_present := decide (attestation.data.index = 1)
  let non_equivocating_attesting_indices :=
    attesting_indices.filter (fun i => decide (i ∉ store.equivocating_indices))
  non_equivocating_attesting_indices.foldl
    (fun store i =>
      let should_update :=
        match store.latest_messages i with
        | none => true
        | some latest_message => decide (slot > latest_message.slot)
      if should_update then
        { store with
          latest_messages :=
            Function.update store.latest_messages i
              (some (LatestMessage.mk slot beacon_block_root payload_present)) }
      else store)
    store

/-- Source: `specs/gloas/fork-choice.md:964`.
`record_block_timeliness` records the attestation and PTC deadlines.
```python
block = store.blocks[root]
seconds_since_genesis = store.time - store.genesis_time
time_into_slot_ms = seconds_to_milliseconds(seconds_since_genesis) % SLOT_DURATION_MS
attestation_threshold_ms = get_attestation_due_ms()
is_current_slot = get_current_slot(store) == block.slot
ptc_threshold_ms = get_payload_attestation_due_ms()
store.block_timeliness[root] = [
    is_current_slot and time_into_slot_ms < threshold
    for threshold in [attestation_threshold_ms, ptc_threshold_ms]
]
``` -/
def record_block_timeliness (store : Store Root) (root : Root) : Store Root :=
  let block := store.blocks root
  let seconds_since_genesis := store.time - store.genesis_time
  let time_into_slot_ms :=
    seconds_to_milliseconds seconds_since_genesis % cfg.slot_duration_ms
  let attestation_threshold_ms := get_attestation_due_ms cfg
  let is_current_slot := decide (get_current_slot cfg store = block.slot)
  let ptc_threshold_ms := get_payload_attestation_due_ms cfg
  { store with
    block_timeliness := Function.update store.block_timeliness root
      (some (is_current_slot && decide (time_into_slot_ms < attestation_threshold_ms),
        is_current_slot && decide (time_into_slot_ms < ptc_threshold_ms))) }

/-- Source: `specs/phase0/fork-choice.md:888`.
`compute_shuffling_lookahead_start_slot`:
```python
def compute_shuffling_lookahead_start_slot(epoch: Epoch) -> Slot:
    lookahead_epoch = saturating_sub(epoch, MIN_SEED_LOOKAHEAD)
    return compute_start_slot_at_epoch(lookahead_epoch)
``` -/
def compute_shuffling_lookahead_start_slot (epoch : Epoch) : Slot :=
  let lookahead_epoch := epoch - cfg.min_seed_lookahead
  compute_start_slot_at_epoch cfg lookahead_epoch

/-- Source: `specs/phase0/fork-choice.md:896`.
`compute_shuffling_dependent_slot`:
```python
def compute_shuffling_dependent_slot(epoch: Epoch) -> Slot:
    lookahead_start_slot = compute_shuffling_lookahead_start_slot(epoch)
    return saturating_sub(lookahead_start_slot, 1)
``` -/
def compute_shuffling_dependent_slot (epoch : Epoch) : Slot :=
  let lookahead_start_slot := compute_shuffling_lookahead_start_slot cfg epoch
  lookahead_start_slot - 1

/-- Source: `specs/gloas/fork-choice.md:982`.
`get_shuffling_dependent_root`:
```python
def get_shuffling_dependent_root(store: Store, root: Root, epoch: Epoch) -> Root:
    node = ForkChoiceNode(root=root, payload_status=PAYLOAD_STATUS_PENDING)
    dependent_slot = compute_shuffling_dependent_slot(epoch)
    return get_ancestor(store, node, dependent_slot).root
``` -/
def get_shuffling_dependent_root (store : Store Root) (root : Root) (epoch : Epoch) : Root :=
  let node := ForkChoiceNode.mk root .pending
  let dependent_slot := compute_shuffling_dependent_slot cfg epoch
  (get_ancestor store node dependent_slot).root

/-- Source: `specs/gloas/fork-choice.md:995`.
`update_proposer_boost_root` (python reads `store.block_timeliness[root]`,
always set by `on_block` immediately before — the `getD (false, false)` default is
unreachable there):
```python
is_first_block = store.proposer_boost_root == Root()
is_timely = store.block_timeliness[root][ATTESTATION_TIMELINESS_INDEX]
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
  let is_timely := ((store.block_timeliness root).getD (false, false)).1
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

/-- Source: `specs/gloas/fork-choice.md:1115`.
`on_payload_attestation_message` writes every PTC position for its validator.
A different assigned slot returns the unchanged store. Only wire messages need
current-slot and signature checks. Missing vote entries or out-of-range PTC
positions reject, as Python dictionary/list access would raise; initialization,
block insertion, and the PTC coherence contract exclude these cases.
```python
data = ptc_message.data
assert data.beacon_block_root in store.block_states
state = store.block_states[data.beacon_block_root]
if data.slot != state.slot:
    return
ptc_indices = []
ptc = get_ptc(state, data.slot)
for ptc_index, validator_index in enumerate(ptc):
    if validator_index == ptc_message.validator_index:
        ptc_indices.append(ptc_index)
assert len(ptc_indices) > 0
if not is_from_block:
    assert data.slot == get_current_slot(store)
    assert is_valid_indexed_payload_attestation(
        state, IndexedPayloadAttestation(
            attesting_indices=PayloadTimelinessCommitteeIndices(
                data=[ptc_message.validator_index]),
            data=data, signature=ptc_message.signature))
payload_timeliness_vote = store.payload_timeliness_vote[data.beacon_block_root]
payload_data_availability_vote = store.payload_data_availability_vote[data.beacon_block_root]
for ptc_index in ptc_indices:
    payload_timeliness_vote[ptc_index] = data.payload_present
    payload_data_availability_vote[ptc_index] = data.blob_data_available
``` -/
def on_payload_attestation_message (store : Store Root)
    (ptc_message : PayloadAttestationMessage Root) (is_from_block : Bool := false) :
    Option (Store Root) :=
  let data := ptc_message.data
  if data.beacon_block_root ∉ store.block_roots then none
  else
    let state := store.block_states data.beacon_block_root
    if data.slot ≠ state.slot then some store
    else
      let ptc := ext.get_ptc state data.slot
      let ptc_indices := (List.range ptc.length).filter
        (fun i => decide (ptc[i]? = some ptc_message.validator_index))
      if ptc_indices.isEmpty then none
      else if !is_from_block &&
          (decide (data.slot ≠ get_current_slot cfg store) ||
            !ext.is_valid_indexed_payload_attestation state
              { attesting_indices := [ptc_message.validator_index]
                data := data
                signature := ptc_message.signature }) then none
      else
        match store.payload_timeliness_vote data.beacon_block_root,
            store.payload_data_availability_vote data.beacon_block_root with
        | some timeliness, some availability =>
          if ¬ ptc_indices.all
              (fun i => decide (i < timeliness.length ∧ i < availability.length)) then none
          else
            let timeliness := ptc_indices.foldl
              (fun votes i => votes.set i (some data.payload_present)) timeliness
            let availability := ptc_indices.foldl
              (fun votes i => votes.set i (some data.blob_data_available)) availability
            some { store with
              payload_timeliness_vote := Function.update store.payload_timeliness_vote
                data.beacon_block_root (some timeliness)
              payload_data_availability_vote :=
                Function.update store.payload_data_availability_vote
                  data.beacon_block_root (some availability) }
        | _, _ => none

/-- Source: `specs/gloas/fork-choice.md:267`.
`notify_ptc_messages` consumes the indexed projection of block-body attestations.
The projection preserves source PTC index extraction. A failed inner handler
rejects the outer block; no earlier partial store write is retained.
```python
if state.slot == 0:
    return
for payload_attestation in payload_attestations:
    indexed_payload_attestation = get_indexed_payload_attestation(state, payload_attestation)
    for idx in indexed_payload_attestation.attesting_indices:
        on_payload_attestation_message(
            store, PayloadAttestationMessage(
                validator_index=idx, data=payload_attestation.data,
                signature=BLSSignature()), is_from_block=True)
``` -/
def notify_ptc_messages (store : Store Root) (state : BeaconState Root)
    (payload_attestations : List (IndexedPayloadAttestation Root)) : Option (Store Root) :=
  if state.slot = 0 then some store
  else
    payload_attestations.foldl
      (fun (result : Option (Store Root)) attestation => result.bind fun store =>
        attestation.attesting_indices.foldl
          (fun (result : Option (Store Root)) idx => result.bind fun store =>
            on_payload_attestation_message cfg ext store
              { validator_index := idx
                data := attestation.data
                signature := default } true)
          (some store))
      (some store)

/-- Source: `specs/gloas/fork-choice.md:1020`.
`on_block` requires a verified payload for a FULL parent, initializes both PTC
vote lists, then applies the block's PTC messages before timeliness and boost.
`none` means a source assertion or external transition failed. Known blocks
return the unchanged store. `blocks` and `block_states` have the same domain.
```python
block = signed_block.message
block_root = hash_tree_root(block)
if block_root in store.blocks:
    return
assert block.parent_root in store.block_states
if is_parent_node_full(store, block):
    assert is_payload_verified(store, block.parent_root)
current_slot = get_current_slot(store)
assert current_slot >= block.slot
finalized_slot = compute_start_slot_at_epoch(store.finalized_checkpoint.epoch)
assert block.slot > finalized_slot
finalized_checkpoint_block = get_checkpoint_block(
    store, block.parent_root, store.finalized_checkpoint.epoch)
assert store.finalized_checkpoint.root == finalized_checkpoint_block
state = store.block_states[block.parent_root].copy()
state_transition(state, signed_block, validate_result=True)
head = get_head(store)
store.blocks[block_root] = block
store.block_states[block_root] = state
store.payload_timeliness_vote[block_root] = [None] * PTC_SIZE
store.payload_data_availability_vote[block_root] = [None] * PTC_SIZE
notify_ptc_messages(store, state, block.body.payload_attestations)
record_block_timeliness(store, block_root)
update_proposer_boost_root(store, head.root, block_root)
update_checkpoints(store, state.current_justified_checkpoint, state.finalized_checkpoint)
compute_pulled_up_tip(store, block_root)
``` -/
def on_block (store : Store Root) (signed_block : SignedBeaconBlock Root) :
    Option (Store Root) :=
  let block := signed_block.message
  let block_root := signed_block.root
  if block_root ∈ store.block_roots then some store
  else if block.parent_root ∉ store.block_roots then none
  else if is_parent_node_full store block && !is_payload_verified store block.parent_root then none
  else
    let pre_state := store.block_states block.parent_root
    if ¬ get_current_slot cfg store ≥ block.slot then none
    else
      let finalized_slot := compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch
      if ¬ block.slot > finalized_slot then none
      else
        let finalized_checkpoint_block :=
          get_checkpoint_block cfg store block.parent_root store.finalized_checkpoint.epoch
        if store.finalized_checkpoint.root ≠ finalized_checkpoint_block then none
        else
          match ext.state_transition pre_state signed_block with
          | none => none
          | some state =>
            let head := get_head cfg store
            let store :=
              { store with
                block_roots := store.block_roots ++ [block_root]
                blocks := Function.update store.blocks block_root block
                block_states := Function.update store.block_states block_root state
                payload_timeliness_vote := Function.update store.payload_timeliness_vote
                  block_root (some (List.replicate cfg.ptc_size none))
                payload_data_availability_vote :=
                  Function.update store.payload_data_availability_vote
                    block_root (some (List.replicate cfg.ptc_size none)) }
            match notify_ptc_messages cfg ext store state block.payload_attestations with
            | none => none
            | some store =>
              let store := record_block_timeliness cfg store block_root
              let store := update_proposer_boost_root cfg store head.root block_root
              let store :=
                update_checkpoints store state.current_justified_checkpoint
                  state.finalized_checkpoint
              some (compute_pulled_up_tip cfg ext store block_root)

/-- Source: `specs/gloas/fork-choice.md:1089`.
`on_execution_payload_envelope` records a payload only after block, local data,
and envelope validation. The observation is the explicit local context for the
source's context-dependent availability and execution-engine calls.
```python
envelope = signed_envelope.message
assert envelope.beacon_block_root in store.block_states
assert is_data_available(envelope.beacon_block_root)
state = store.block_states[envelope.beacon_block_root]
verify_execution_payload_envelope(state, signed_envelope, EXECUTION_ENGINE)
store.payloads[envelope.beacon_block_root] = envelope
``` -/
def on_execution_payload_envelope (store : Store Root)
    (signed_envelope : SignedExecutionPayloadEnvelope Root)
    (observation : EnvelopeObservation Root) : Option (Store Root) :=
  let envelope := signed_envelope.message
  if envelope.beacon_block_root ∉ store.block_roots then none
  else if !ext.is_data_available envelope.beacon_block_root observation then none
  else
    let state := store.block_states envelope.beacon_block_root
    if !ext.verify_execution_payload_envelope state signed_envelope observation then none
    else some { store with
      payloads := Function.update store.payloads envelope.beacon_block_root (some envelope) }

/-- Source: `specs/phase0/fork-choice.md:1000`.
`on_attestation` handler. `none` = validation failed (python assert — the
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

/-- Source: `specs/phase0/fork-choice.md:1027`.
`on_attester_slashing` handler (`none` = a python assert failed).
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

/-- Source: `specs/gloas/fork-choice.md:218`.
`get_forkchoice_store`: the trusted-anchor initialization. The python
`assert anchor_block.state_root == hash_tree_root(anchor_state)` is omitted
from this executable function: the projected block carries no `state_root`.
`ScheduledPrefixTrajectoryAssumptions.genesis` requires the abstract
`Externals.AnchorCommitsToState` contract from the external interpretation,
along with separate slot agreement and parent/root inequality premises
(design §11a). This is not a concrete hashing proof. Dict fields outside their
singleton domains are junk-totalized.
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
    block_timeliness={anchor_root: [True, True]},
    checkpoint_states={justified_checkpoint: anchor_state.copy()},
    latest_messages={},
    unrealized_justifications={anchor_root: justified_checkpoint},
    payloads={},
    payload_timeliness_vote={anchor_root: [None] * PTC_SIZE},
    payload_data_availability_vote={anchor_root: [None] * PTC_SIZE})
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
    block_timeliness := Function.update (fun _ => none) anchor_root (some (true, true))
    checkpoint_state_keys := {justified_checkpoint}
    checkpoint_states := Function.update (fun _ => default) justified_checkpoint anchor_state
    latest_messages := fun _ => none
    unrealized_justifications :=
      Function.update (fun _ => default) anchor_root justified_checkpoint
    payloads := fun _ => none
    payload_timeliness_vote :=
      Function.update (fun _ => none) anchor_root (some (List.replicate cfg.ptc_size none))
    payload_data_availability_vote :=
      Function.update (fun _ => none) anchor_root (some (List.replicate cfg.ptc_size none)) }

end FastConfirmation.Spec

end
