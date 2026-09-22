import Mathlib.Data.List.MinMax
import Mathlib.Data.Prod.Lex
import FastConfirmation.Spec.Model.Types

/-!
# Spec / Model / ForkChoice

The fork-choice `Store` and the `specs/phase0/fork-choice.md` helpers the Fast
Confirmation Rule calls, transcribed 1:1 (`get_current_slot` …
`get_head`, `get_voting_source`, `get_latest_message_epoch`).

Python dicts become total functions plus (where iterated) an explicit domain
`Finset`; python's unbounded recursion/loops (`get_ancestor`,
`filter_block_tree`, `get_head`) become fuel-bounded workers whose wrappers
supply fuel sufficient on well-formed stores — see `docs/spec-model-design.md`,
decisions 3, 4, 7, 8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-- Fork-choice `Store` dataclass. Dict fields are totalized functions;
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
  block_timeliness : Root → Option Bool
  /-- Key set of the python `checkpoint_states` dict
      (`store_target_checkpoint_state` tests membership). -/
  checkpoint_state_keys : Finset (Checkpoint Root)
  checkpoint_states : Checkpoint Root → BeaconState Root
  latest_messages : ValidatorIndex → Option (LatestMessage Root)
  unrealized_justifications : Root → Checkpoint Root

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

/-- Fuel-bounded worker for `get_ancestor` (python recurses on the parent
pointer, terminating only when parent slots strictly decrease; on fuel
exhaustion we return the current node — a python-divergence point outside the
well-formed domain).
```python
block = store.blocks[node.root]
if block.slot > slot:
    parent = ForkChoiceNode(root=block.parent_root)
    return get_ancestor(store, parent, slot)
return node
``` -/
def get_ancestor_aux (store : Store Root) (slot : Slot) :
    ℕ → ForkChoiceNode Root → ForkChoiceNode Root
  | 0, node => node
  | fuel + 1, node =>
    let block := store.blocks node.root
    if block.slot > slot then
      get_ancestor_aux store slot fuel (ForkChoiceNode.mk block.parent_root)
    else node

/-- `get_ancestor`: wrapper supplying fuel `block.slot + 1`, sufficient on a
well-formed store (each step strictly decreases the walked block's slot). -/
def get_ancestor (store : Store Root) (node : ForkChoiceNode Root) (slot : Slot) :
    ForkChoiceNode Root :=
  get_ancestor_aux store slot ((store.blocks node.root).slot + 1) node

/-- `is_ancestor`:
```python
return get_ancestor(store, node, store.blocks[ancestor.root].slot) == ancestor
``` -/
def is_ancestor (store : Store Root) (node ancestor : ForkChoiceNode Root) : Bool :=
  decide (get_ancestor store node (store.blocks ancestor.root).slot = ancestor)

/-- `get_checkpoint_block`: Compute the checkpoint block for epoch ``epoch`` in
the chain of block ``root``.
```python
epoch_first_slot = compute_start_slot_at_epoch(epoch)
node = ForkChoiceNode(root=root)
return get_ancestor(store, node, epoch_first_slot).root
``` -/
def get_checkpoint_block (store : Store Root) (root : Root) (epoch : Epoch) : Root :=
  let epoch_first_slot := compute_start_slot_at_epoch cfg epoch
  let node := ForkChoiceNode.mk root
  (get_ancestor store node epoch_first_slot).root

/-- `get_supported_node`: Return a node supported by the ``message``.
```python
return ForkChoiceNode(root=message.root)
```
(The unused `store` argument is kept for signature fidelity.) -/
def get_supported_node (_store : Store Root) (message : LatestMessage Root) :
    ForkChoiceNode Root :=
  ForkChoiceNode.mk message.root

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

/-- `get_weight`:
```python
state = store.checkpoint_states[store.justified_checkpoint]
attestation_score = get_attestation_score(store, node, state)
if store.proposer_boost_root == Root():
    return attestation_score
proposer_score = Gwei(0)
proposer_boost_node = ForkChoiceNode(root=store.proposer_boost_root)
if is_ancestor(store, proposer_boost_node, node):
    proposer_score = get_proposer_score(store)
return attestation_score + proposer_score
```
(`Root()` is `Inhabited.default`.) -/
def get_weight (store : Store Root) (node : ForkChoiceNode Root) : Gwei :=
  let state := store.checkpoint_states store.justified_checkpoint
  let attestation_score := get_attestation_score cfg store node state
  if store.proposer_boost_root = default then
    attestation_score
  else
    let proposer_boost_node := ForkChoiceNode.mk store.proposer_boost_root
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

/-- `get_node_children`:
```python
return [ForkChoiceNode(root=root) for root in blocks if blocks[root].parent_root == node.root]
```
(The python `blocks` dict values are always `store.blocks[root]`, so the model
passes the root list and looks the parent up in `store` — the one signature
deviation, see `docs/spec-model-design.md` decision 8.) -/
def get_node_children (store : Store Root) (blocks : List Root)
    (node : ForkChoiceNode Root) : List (ForkChoiceNode Root) :=
  (blocks.filter (fun root => (store.blocks root).parent_root = node.root)).map
    ForkChoiceNode.mk

/-- Fuel-bounded worker for `get_head`'s descent loop. `List.argmax` over the
lexicographic key `(get_weight store child, child.root)` is python's
`max(children, key=lambda child: (get_weight(store, child), child.root))` —
the key is injective on children (distinct roots), so the maximum is unique
and order-independent.
```python
while True:
    children = get_node_children(store, blocks, head)
    if len(children) == 0:
        return head
    head = max(children, key=lambda child: (get_weight(store, child), child.root))
``` -/
def get_head_aux (store : Store Root) (blocks : List Root) :
    ℕ → ForkChoiceNode Root → ForkChoiceNode Root
  | 0, head => head
  | fuel + 1, head =>
    let children := get_node_children store blocks head
    match children.argmax
        (fun child => toLex (get_weight cfg store child, child.root)) with
    | none => head
    | some best => get_head_aux store blocks fuel best

/-- `get_head`: wrapper supplying fuel `blocks.length + 1` (the descent visits
pairwise-distinct tree nodes on a well-formed store).
```python
blocks = get_filtered_block_tree(store)
head = ForkChoiceNode(root=store.justified_checkpoint.root)
while True: ...
``` -/
def get_head (store : Store Root) : ForkChoiceNode Root :=
  let blocks := get_filtered_block_tree cfg store
  get_head_aux cfg store blocks (blocks.length + 1)
    (ForkChoiceNode.mk store.justified_checkpoint.root)

/-- `get_latest_message_epoch`: Return epoch of the ``latest_message``.
```python
return latest_message.epoch
``` -/
def get_latest_message_epoch (latest_message : LatestMessage Root) : Epoch :=
  latest_message.epoch

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

/-- `get_attestation_due_ms`:
```python
return get_slot_component_duration_ms(ATTESTATION_DUE_BPS)
``` -/
def get_attestation_due_ms : ℕ :=
  get_slot_component_duration_ms cfg cfg.attestation_due_bps

end FastConfirmation.Spec
