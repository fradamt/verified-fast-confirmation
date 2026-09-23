module
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Prod.Lex
public import FastConfirmationModel.Spec.BeaconChain.Helpers

@[expose] public section

/-!
# Spec / Model / ForkChoice

The Gloas fork-choice `Store` and helpers used by Fast Confirmation. Modified
helpers follow `specs/gloas/fork-choice.md`; unchanged helpers retain the
inherited phase0 definition.

Python dicts become total functions plus, where iterated, an explicit domain
list or set. Python's unbounded recursion/loops (`get_ancestor`,
`filter_block_tree`, `get_head`) become fuel-bounded workers whose wrappers
supply fuel sufficient on well-formed stores — see `docs/spec-model-design.md`,
decisions 3, 4, 7, 8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-- Gloas `Store` (`specs/gloas/fork-choice.md:191`).
Dict fields are totalized functions;
`blocks` additionally carries its key set `block_roots` because
`filter_block_tree` iterates over the dict; `latest_messages` keeps `Option`
because the spec tests membership (`i in store.latest_messages`). -/
structure Store (Root : Type*) where
  time : ℕ
  genesis_time : ℕ
  justified_checkpoint : Checkpoint Root
  finalized_checkpoint : Checkpoint Root
  unrealized_justified_checkpoint : Checkpoint Root
  unrealized_finalized_checkpoint : Checkpoint Root
  proposer_boost_root : Root
  equivocating_indices : Finset ValidatorIndex
  /-- Key list of the python `blocks: Dict[Root, BeaconBlock]` (python dicts
      iterate keys in insertion order, so the domain is a `List`; keys are
      pairwise distinct — a future `WellFormedStore` invariant). -/
  block_roots : List Root
  /-- Totalized lookup of the python `blocks` dict (junk outside `block_roots`). -/
  blocks : Root → BeaconBlock Root
  block_states : Root → BeaconState Root
  /-- Attestation and PTC deadlines, in source index order
  (`specs/gloas/fork-choice.md:203`; indices at :105). -/
  block_timeliness : Root → Option (Bool × Bool)
  /-- Key set of the python `checkpoint_states` dict
      (`store_target_checkpoint_state` tests membership). -/
  checkpoint_state_keys : Finset (Checkpoint Root)
  checkpoint_states : Checkpoint Root → BeaconState Root
  latest_messages : ValidatorIndex → Option (LatestMessage Root)
  unrealized_justifications : Root → Checkpoint Root
  /-- Locally delivered and verified envelopes
  (`specs/gloas/fork-choice.md:208`). -/
  payloads : Root → Option (ExecutionPayloadEnvelope Root) := fun _ => none
  /-- PTC timeliness votes; `none` in a list means no vote
  (`specs/gloas/fork-choice.md:210`). -/
  payload_timeliness_vote : Root → Option (List (Option Bool)) := fun _ => none
  /-- PTC data availability votes (`specs/gloas/fork-choice.md:212`). -/
  payload_data_availability_vote : Root → Option (List (Option Bool)) := fun _ => none

/-- `get_slots_since_genesis`:
```python
return (store.time - store.genesis_time) * 1000 // SLOT_DURATION_MS
```
(`store.time` is in seconds.) -/
def get_slots_since_genesis (store : Store Root) : ℕ :=
  (store.time - store.genesis_time) * 1000 / cfg.slot_duration_ms

/-- `get_current_slot`:
```python
return GENESIS_SLOT + get_slots_since_genesis(store)
``` -/
def get_current_slot (store : Store Root) : Slot :=
  GENESIS_SLOT + get_slots_since_genesis cfg store

/-- `get_current_store_epoch`:
```python
return compute_epoch_at_slot(get_current_slot(store))
``` -/
def get_current_store_epoch (store : Store Root) : Epoch :=
  compute_epoch_at_slot cfg (get_current_slot cfg store)

/-- `compute_slots_since_epoch_start`:
```python
return slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot))
``` -/
def compute_slots_since_epoch_start (slot : Slot) : ℕ :=
  slot - compute_start_slot_at_epoch cfg (compute_epoch_at_slot cfg slot)

/-- `is_payload_verified` (`specs/gloas/fork-choice.md:313`).
Only the local verified-envelope map determines this predicate. -/
def is_payload_verified (store : Store Root) (root : Root) : Bool :=
  (store.payloads root).isSome

/-- `payload_timeliness` (`specs/gloas/fork-choice.md:325`).
The source requires a keyed vote list. A missing key is outside the helper's
domain and is totalized as an empty list. The strict majority threshold is
`PTC_SIZE // 2` (`specs/gloas/fork-choice.md:100`). -/
def payload_timeliness (store : Store Root) (root : Root) (timely : Bool) : Bool :=
  if !is_payload_verified store root then !timely
  else
    let votes := ((store.payload_timeliness_vote root).getD []).filterMap id
    decide ((votes.filter (fun vote => vote == timely)).length > cfg.ptc_size / 2)

/-- `payload_data_availability` (`specs/gloas/fork-choice.md:346`).
As with timeliness, the source requires the vote list to be keyed. Local
verification is required before affirmative PTC votes can make data available.
The strict majority threshold is `PTC_SIZE // 2`
(`specs/gloas/fork-choice.md:101`). -/
def payload_data_availability (store : Store Root) (root : Root)
    (available : Bool) : Bool :=
  if !is_payload_verified store root then !available
  else
    let votes := ((store.payload_data_availability_vote root).getD []).filterMap id
    decide ((votes.filter (fun vote => vote == available)).length > cfg.ptc_size / 2)

/-- `get_parent_payload_status` (`specs/gloas/fork-choice.md:367`).
The child bid chooses FULL exactly when its parent hash equals the parent bid's
block hash. -/
def get_parent_payload_status (store : Store Root) (block : BeaconBlock Root) :
    PayloadStatus :=
  if block.parent_block_hash = (store.blocks block.parent_root).block_hash then .full
  else .empty

/-- `is_parent_node_full` (`specs/gloas/fork-choice.md:377`). -/
def is_parent_node_full (store : Store Root) (block : BeaconBlock Root) : Bool :=
  decide (get_parent_payload_status store block = .full)

/-- Fuel worker for `get_ancestor` (`specs/gloas/fork-choice.md:387`).
Each parent step resolves the parent's payload status from the child bid.
Exhausted fuel returns the current node, outside the well-formed domain. -/
def get_ancestor_aux (store : Store Root) (slot : Slot) :
    ℕ → ForkChoiceNode Root → ForkChoiceNode Root
  | 0, node => node
  | fuel + 1, node =>
    let block := store.blocks node.root
    if block.slot > slot then
      get_ancestor_aux store slot fuel
        (ForkChoiceNode.mk block.parent_root (get_parent_payload_status store block))
    else node

/-- `get_ancestor` (`specs/gloas/fork-choice.md:387`):
wrapper supplying fuel `block.slot + 1`, sufficient on a
well-formed store (each step strictly decreases the walked block's slot). -/
def get_ancestor (store : Store Root) (node : ForkChoiceNode Root) (slot : Slot) :
    ForkChoiceNode Root :=
  get_ancestor_aux store slot ((store.blocks node.root).slot + 1) node

/-- `is_ancestor` (`specs/gloas/fork-choice.md:405`). A pending ancestor
accepts either resolved status at the same root. -/
def is_ancestor (store : Store Root) (node ancestor : ForkChoiceNode Root) : Bool :=
  let node_ancestor := get_ancestor store node (store.blocks ancestor.root).slot
  decide (node_ancestor.root = ancestor.root) &&
    decide (node_ancestor.payload_status = ancestor.payload_status ∨
      ancestor.payload_status = .pending)

/-- `get_checkpoint_block` (`specs/gloas/fork-choice.md:420`).
Start from the pending node and project the ancestor's beacon root. -/
def get_checkpoint_block (store : Store Root) (root : Root) (epoch : Epoch) : Root :=
  let epoch_first_slot := compute_start_slot_at_epoch cfg epoch
  let node := ForkChoiceNode.mk root .pending
  (get_ancestor store node epoch_first_slot).root

/-- `get_supported_node` (`specs/gloas/fork-choice.md:435`). A vote from
the block slot supports PENDING. A later-slot vote resolves FULL or EMPTY. -/
def get_supported_node (store : Store Root) (message : LatestMessage Root) :
    ForkChoiceNode Root :=
  let payload_status :=
    if (store.blocks message.root).slot < message.slot then
      if message.payload_present then PayloadStatus.full else PayloadStatus.empty
    else PayloadStatus.pending
  ForkChoiceNode.mk message.root payload_status

/-- `get_attestation_score`:
```python
unslashed_and_active_indices = [
    i for i in get_active_validator_indices(state, get_current_epoch(state))
    if not state.validators[i].slashed
]
return Gwei(sum(
    state.validators[i].effective_balance for i in unslashed_and_active_indices
    if (i in store.latest_messages
        and i not in store.equivocating_indices
        and is_ancestor(store, get_supported_node(store, store.latest_messages[i]), node))
))
``` -/
def get_attestation_score (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) : Gwei :=
  let unslashed_and_active_indices :=
    (get_active_validator_indices state (get_current_epoch cfg state)).filter
      (fun i => !(state.validators.getD i default).slashed)
  ((unslashed_and_active_indices.filter fun i =>
      match store.latest_messages i with
      | none => false
      | some latest_message =>
          decide (i ∉ store.equivocating_indices) &&
            is_ancestor store (get_supported_node store latest_message) node)
    |>.map fun i => (state.validators.getD i default).effective_balance).sum

/-- `compute_proposer_score`:
```python
committee_weight = get_total_active_balance(state) // Uint64(SLOTS_PER_EPOCH)
return (committee_weight * PROPOSER_SCORE_BOOST) // 100
``` -/
def compute_proposer_score (state : BeaconState Root) : Gwei :=
  let committee_weight := get_total_active_balance cfg state / cfg.slots_per_epoch
  committee_weight * cfg.proposer_score_boost / 100

/-- `get_proposer_score`:
```python
justified_checkpoint_state = store.checkpoint_states[store.justified_checkpoint]
return compute_proposer_score(justified_checkpoint_state)
``` -/
def get_proposer_score (store : Store Root) : Gwei :=
  let justified_checkpoint_state := store.checkpoint_states store.justified_checkpoint
  compute_proposer_score cfg justified_checkpoint_state

/-- `is_previous_slot_payload_decision` (`specs/gloas/fork-choice.md:460`). -/
def is_previous_slot_payload_decision (store : Store Root)
    (node : ForkChoiceNode Root) : Bool :=
  decide ((store.blocks node.root).slot + 1 = get_current_slot cfg store ∧
    (node.payload_status = .empty ∨ node.payload_status = .full))


/-- `should_extend_payload` (`specs/gloas/fork-choice.md:496`). The source
requires `root` to be from the previous slot. Without affirmative PTC votes,
a proposer-boost block which selects EMPTY can prevent extension. -/
def should_extend_payload (store : Store Root) (root : Root) : Bool :=
  if !is_payload_verified store root then false
  else
    let proposer_root := store.proposer_boost_root
    let payload_is_timely := payload_timeliness cfg store root true
    let payload_data_is_available := payload_data_availability cfg store root true
    (payload_is_timely && payload_data_is_available) ||
      decide (proposer_root = default) ||
      decide ((store.blocks proposer_root).parent_root ≠ root) ||
      is_parent_node_full store (store.blocks proposer_root)

/-- `get_payload_status_tiebreaker` (`specs/gloas/fork-choice.md:514`).
Previous-slot EMPTY has priority 1. FULL has priority 2 or 0, according to
`should_extend_payload`. Other nodes use the source status number. -/
def get_payload_status_tiebreaker (store : Store Root)
    (node : ForkChoiceNode Root) : ℕ :=
  if is_previous_slot_payload_decision cfg store node then
    if node.payload_status = .empty then 1
    else if should_extend_payload cfg store node.root then 2
    else 0
  else node.payload_status.toNat

/-- Inherited `calculate_committee_fraction`
(`specs/phase0/fork-choice.md:291`), used by the Gloas weak-head test at
`specs/gloas/fork-choice.md:788`. -/
def calculate_committee_fraction (state : BeaconState Root)
    (committee_percent : ℕ) : Gwei :=
  let committee_weight := get_total_active_balance cfg state / cfg.slots_per_epoch
  committee_weight * committee_percent / 100

/-- `is_head_late` (`specs/gloas/fork-choice.md:778`). The first deadline
is the attestation deadline. A missing key is outside the source read domain. -/
def is_head_late (store : Store Root) (head_root : Root) : Bool :=
  !((store.block_timeliness head_root).getD (false, false)).1

/-- `is_head_weak` (`specs/gloas/fork-choice.md:785`). Committee query
results are concrete state read projections. The coherence contract binds
them to beacon-chain committee queries. List order and multiplicity are kept. -/
def is_head_weak (store : Store Root) (head_root : Root) : Bool :=
  let justified_state := store.checkpoint_states store.justified_checkpoint
  let reorg_threshold :=
    calculate_committee_fraction cfg justified_state cfg.reorg_head_weight_threshold
  let head_state := store.block_states head_root
  let head_block := store.blocks head_root
  let epoch := compute_epoch_at_slot cfg head_block.slot
  let head_node := ForkChoiceNode.mk head_root .pending
  let head_weight := get_attestation_score cfg store head_node justified_state
  let equivocation_weight :=
    ((List.range (head_state.committee_count_per_slot epoch)).map fun index =>
      (((head_state.beacon_committees head_block.slot index).filter
        (fun i => decide (i ∈ store.equivocating_indices))).map
        (fun i => (justified_state.validators.getD i default).effective_balance)).sum).sum
  decide (head_weight + equivocation_weight < reorg_threshold)

/-- `should_apply_proposer_boost` (`specs/gloas/fork-choice.md:530`).
For a weak parent in the previous slot, an early proposer equivocation
disables boost. Early means timely at the PTC deadline. -/
def should_apply_proposer_boost (store : Store Root) : Bool :=
  if store.proposer_boost_root = default then false
  else
    let block := store.blocks store.proposer_boost_root
    let parent_root := block.parent_root
    let parent := store.blocks parent_root
    let slot := block.slot
    if parent.slot + 1 < slot then true
    else if !is_head_weak cfg store parent_root then true
    else
      let equivocations := store.block_roots.filter fun root =>
        ((store.block_timeliness root).getD (false, false)).2 &&
          decide ((store.blocks root).proposer_index = parent.proposer_index ∧
            (store.blocks root).slot + 1 = slot ∧ root ≠ parent_root)
      decide (equivocations.length = 0)

/-- `get_weight` (`specs/gloas/fork-choice.md:566`). Previous-slot
payload decisions have zero weight. Other nodes receive attestation weight
and, when enabled, proposer boost on the boost block's ancestor chain. -/
def get_weight (store : Store Root) (node : ForkChoiceNode Root) : Gwei :=
  if is_previous_slot_payload_decision cfg store node then 0
  else
    let state := store.checkpoint_states store.justified_checkpoint
    let attestation_score := get_attestation_score cfg store node state
    if !should_apply_proposer_boost cfg store then attestation_score
    else
      let proposer_boost_node := ForkChoiceNode.mk store.proposer_boost_root .pending
      let proposer_score : Gwei :=
        if is_ancestor store proposer_boost_node node then get_proposer_score cfg store else 0
      attestation_score + proposer_score

/-- `get_voting_source`: Compute the voting source checkpoint in event that
block with root ``block_root`` is the head block.
```python
block = store.blocks[block_root]
current_epoch = get_current_store_epoch(store)
block_epoch = compute_epoch_at_slot(block.slot)
if current_epoch > block_epoch:
    return store.unrealized_justifications[block_root]
else:
    head_state = store.block_states[block_root]
    return head_state.current_justified_checkpoint
``` -/
def get_voting_source (store : Store Root) (block_root : Root) : Checkpoint Root :=
  let block := store.blocks block_root
  let current_epoch := get_current_store_epoch cfg store
  let block_epoch := compute_epoch_at_slot cfg block.slot
  if current_epoch > block_epoch then
    store.unrealized_justifications block_root
  else
    let head_state := store.block_states block_root
    head_state.current_justified_checkpoint

/-- Fuel-bounded worker for `filter_block_tree` (python recurses over the
children of `block_root` in `store.blocks`). Returns the viability flag and
the list of roots added to the python output dict `blocks`, in insertion
order — each child call's additions first, then `block_root` itself when
viable (dict values are always `store.blocks[root]`, so the root list carries
all information). Python's `any(children)` is list non-emptiness (non-empty
`bytes` are truthy).
```python
block = store.blocks[block_root]
children = [root for root in store.blocks if store.blocks[root].parent_root == block_root]
if any(children):
    filter_block_tree_result = [filter_block_tree(store, child, blocks) for child in children]
    if any(filter_block_tree_result):
        blocks[block_root] = block
        return True
    return False
current_epoch = get_current_store_epoch(store)
voting_source = get_voting_source(store, block_root)
correct_justified = (
    store.justified_checkpoint.epoch == GENESIS_EPOCH
    or voting_source.epoch == store.justified_checkpoint.epoch
    or voting_source.epoch + 2 >= current_epoch
)
finalized_checkpoint_block = get_checkpoint_block(
    store, block_root, store.finalized_checkpoint.epoch)
correct_finalized = (
    store.finalized_checkpoint.epoch == GENESIS_EPOCH
    or store.finalized_checkpoint.root == finalized_checkpoint_block
)
if correct_justified and correct_finalized:
    blocks[block_root] = block
    return True
return False
``` -/
def filter_block_tree_aux (store : Store Root) :
    ℕ → Root → Bool × List Root
  | 0, _ => (false, [])
  | fuel + 1, block_root =>
    let children :=
      store.block_roots.filter (fun root => (store.blocks root).parent_root = block_root)
    if children ≠ [] then
      let filter_block_tree_result :=
        children.map (fun child => filter_block_tree_aux store fuel child)
      let child_blocks : List Root :=
        (filter_block_tree_result.map Prod.snd).flatten
      if filter_block_tree_result.any Prod.fst then
        (true, child_blocks ++ [block_root])
      else
        (false, child_blocks)
    else
      let current_epoch := get_current_store_epoch cfg store
      let voting_source := get_voting_source cfg store block_root
      let correct_justified :=
        decide (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
          voting_source.epoch = store.justified_checkpoint.epoch ∨
          voting_source.epoch + 2 ≥ current_epoch)
      let finalized_checkpoint_block :=
        get_checkpoint_block cfg store block_root store.finalized_checkpoint.epoch
      let correct_finalized :=
        decide (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
          store.finalized_checkpoint.root = finalized_checkpoint_block)
      if correct_justified && correct_finalized then
        (true, [block_root])
      else
        (false, [])

/-- `get_filtered_block_tree`: Retrieve a filtered block tree from ``store``,
only returning branches whose leaf state's justified/finalized info agrees with
that in ``store``. Wrapper supplying fuel `block_roots.length + 1` (recursion
depth on a well-formed store is bounded by the number of blocks).
```python
base = store.justified_checkpoint.root
blocks: Dict[Root, BeaconBlock] = {}
filter_block_tree(store, base, blocks)
return blocks
``` -/
def get_filtered_block_tree (store : Store Root) : List Root :=
  (filter_block_tree_aux cfg store (store.block_roots.length + 1)
    store.justified_checkpoint.root).2

/-- `get_node_children` (`specs/gloas/fork-choice.md:597`). A pending
node has an EMPTY child and, if locally verified, a FULL child at the same
root. A resolved node has pending beacon children whose bid selects its
status. Candidate dict values are represented by the store and a root list. -/
def get_node_children (store : Store Root) (blocks : List Root)
    (node : ForkChoiceNode Root) : List (ForkChoiceNode Root) :=
  if node.payload_status = .pending then
    let children := [ForkChoiceNode.mk node.root .empty]
    if is_payload_verified store node.root then children ++ [ForkChoiceNode.mk node.root .full]
    else children
  else
    (blocks.filter fun root =>
      decide ((store.blocks root).parent_root = node.root ∧
        node.payload_status = get_parent_payload_status store (store.blocks root))).map
      (fun root => ForkChoiceNode.mk root .pending)

/-- Fuel worker for `get_head` (`specs/gloas/fork-choice.md:622`).
The source's lexicographic key is weight, beacon root, then payload-status
priority. Nested `toLex` preserves that ordering. -/
def get_head_aux (store : Store Root) (blocks : List Root) :
    ℕ → ForkChoiceNode Root → ForkChoiceNode Root
  | 0, head => head
  | fuel + 1, head =>
    let children := get_node_children store blocks head
    match children.argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) with
    | none => head
    | some best => get_head_aux store blocks fuel best

/-- `get_head` (`specs/gloas/fork-choice.md:622`). The descent starts
at the pending justified root. Fuel `2 * blocks.length + 2` allows a pending
and a resolved node for each beacon root, including the start root when the
filtered list is empty. -/
def get_head (store : Store Root) : ForkChoiceNode Root :=
  let blocks := get_filtered_block_tree cfg store
  get_head_aux cfg store blocks (2 * blocks.length + 2)
    (ForkChoiceNode.mk store.justified_checkpoint.root .pending)

/-- `get_latest_message_epoch` (`specs/gloas/fork-choice.md:651`).
Gloas stores the vote slot and derives its epoch. -/
def get_latest_message_epoch (latest_message : LatestMessage Root) : Epoch :=
  compute_epoch_at_slot cfg latest_message.slot

/-- `seconds_to_milliseconds`: Convert seconds to milliseconds with overflow
protection (the guard is transcribed literally although `ℕ` cannot overflow).
```python
if seconds > UINT64_MAX // 1000:
    return UINT64_MAX
return seconds * 1000
``` -/
def seconds_to_milliseconds (seconds : ℕ) : ℕ :=
  if seconds > UINT64_MAX / 1000 then UINT64_MAX
  else seconds * 1000

/-- `get_slot_component_duration_ms`: Calculate the duration of a slot
component in milliseconds.
```python
return basis_points * SLOT_DURATION_MS // BASIS_POINTS
``` -/
def get_slot_component_duration_ms (basis_points : ℕ) : ℕ :=
  basis_points * cfg.slot_duration_ms / BASIS_POINTS

/-- `get_attestation_due_ms` (`specs/gloas/fork-choice.md:725`). The
configuration stores the selected fork's `ATTESTATION_DUE_BPS_GLOAS`. -/
def get_attestation_due_ms : ℕ :=
  get_slot_component_duration_ms cfg cfg.attestation_due_bps


/-- `get_payload_attestation_due_ms` (`specs/gloas/fork-choice.md:764`). -/
def get_payload_attestation_due_ms : ℕ :=
  get_slot_component_duration_ms cfg cfg.payload_attestation_due_bps

end FastConfirmation.Spec

end
