module
public import FastConfirmation.Spec.Model.ForkChoice

@[expose] public section

/-!
# Spec / Model / FCRStore

`FastConfirmationStore`, its initialization, and the "Misc helper functions" +
"State helpers" sections of the inherited fast-confirmation specification,
with the `specs/gloas/fast-confirmation.md` overlay.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `FastConfirmationStore`: tracks the information required by the fast
confirmation rule (see the spec's field descriptions). `store` is the
read-only fork-choice `Store` instance, "added for convenience". -/
structure FastConfirmationStore (Root : Type*) where
  store : Store Root
  confirmed_root : Root
  previous_epoch_observed_justified_checkpoint : Checkpoint Root
  current_epoch_observed_justified_checkpoint : Checkpoint Root
  previous_epoch_greatest_unrealized_checkpoint : Checkpoint Root
  previous_slot_head : Root
  current_slot_head : Root

/-- `get_fast_confirmation_store`: initialization, conservatively using
`store.finalized_checkpoint` for all fast confirmation variables.
```python
return FastConfirmationStore(
    store=store,
    confirmed_root=store.finalized_checkpoint.root,
    previous_epoch_observed_justified_checkpoint=store.finalized_checkpoint,
    current_epoch_observed_justified_checkpoint=store.finalized_checkpoint,
    previous_epoch_greatest_unrealized_checkpoint=store.finalized_checkpoint,
    previous_slot_head=store.finalized_checkpoint.root,
    current_slot_head=store.finalized_checkpoint.root,
)
``` -/
def get_fast_confirmation_store (store : Store Root) : FastConfirmationStore Root where
  store := store
  confirmed_root := store.finalized_checkpoint.root
  previous_epoch_observed_justified_checkpoint := store.finalized_checkpoint
  current_epoch_observed_justified_checkpoint := store.finalized_checkpoint
  previous_epoch_greatest_unrealized_checkpoint := store.finalized_checkpoint
  previous_slot_head := store.finalized_checkpoint.root
  current_slot_head := store.finalized_checkpoint.root

/-- `get_node_for_root` (`specs/gloas/fast-confirmation.md:26`).
Fast Confirmation confirms a beacon root through its pending node. -/
def get_node_for_root (block_root : Root) : ForkChoiceNode Root :=
  ForkChoiceNode.mk block_root .pending

/-- `get_safe_execution_block_hash`
(`specs/gloas/fast-confirmation.md:38`). Only the parent payload of the
confirmed beacon block is safe. -/
def get_safe_execution_block_hash (fcr_store : FastConfirmationStore Root) : Root :=
  (fcr_store.store.blocks fcr_store.confirmed_root).parent_block_hash

/-- `get_block_slot`: Return a slot of the block.
```python
return store.blocks[block_root].slot
``` -/
def get_block_slot (store : Store Root) (block_root : Root) : Slot :=
  (store.blocks block_root).slot

/-- `get_block_epoch`: Return an epoch of the block.
```python
return compute_epoch_at_slot(store.blocks[block_root].slot)
``` -/
def get_block_epoch (store : Store Root) (block_root : Root) : Epoch :=
  compute_epoch_at_slot cfg (store.blocks block_root).slot

/-- `get_checkpoint_for_block`: Return a checkpoint in the chain of the block
at the ``epoch``.
```python
return Checkpoint(epoch=epoch, root=get_checkpoint_block(store, block_root, epoch))
``` -/
def get_checkpoint_for_block (store : Store Root) (block_root : Root) (epoch : Epoch) :
    Checkpoint Root :=
  Checkpoint.mk epoch (get_checkpoint_block cfg store block_root epoch)

/-- `get_current_target`: Return current epoch target.
```python
head = get_head(store).root
current_epoch = get_current_store_epoch(store)
return get_checkpoint_for_block(store, head, current_epoch)
``` -/
def get_current_target (store : Store Root) : Checkpoint Root :=
  let head := (get_head cfg store).root
  let current_epoch := get_current_store_epoch cfg store
  get_checkpoint_for_block cfg store head current_epoch

/-- `is_start_slot_at_epoch`: Return ``True`` if ``slot`` is the start slot of
an epoch.
```python
return compute_slots_since_epoch_start(slot) == 0
``` -/
def is_start_slot_at_epoch (slot : Slot) : Bool :=
  decide (compute_slots_since_epoch_start cfg slot = 0)

/-- Fuel-bounded worker for `get_ancestor_roots` (python walks the parent
pointers in a while-loop). `none` models the fall-through "terminal_root is
not in the chain of block_root" (python returns `[]`); `some l` models the
in-loop `return ancestor_roots` when the parent hits `terminal_root`. The
accumulated list is oldest→newest (python `insert(0, root)` prepends as the
walk descends).
```python
root = block_root
ancestor_roots: list[Root] = []
while store.blocks[root].slot > store.blocks[terminal_root].slot:
    ancestor_roots.insert(0, root)
    root = store.blocks[root].parent_root
    if root == terminal_root:
        return ancestor_roots
return []
``` -/
def get_ancestor_roots_aux (store : Store Root) (terminal_root : Root) :
    ℕ → Root → Option (List Root)
  | 0, _ => none
  | fuel + 1, root =>
    if (store.blocks root).slot > (store.blocks terminal_root).slot then
      let next := (store.blocks root).parent_root
      if next = terminal_root then
        some [root]
      else
        (get_ancestor_roots_aux store terminal_root fuel next).map (· ++ [root])
    else none

/-- `get_ancestor_roots`: Return a list of ancestors of ``block_root``
inclusive until ``terminal_root`` exclusive (empty if `terminal_root` is not
in the chain). Wrapper supplying fuel `block.slot + 1` (sufficient on a
well-formed store) and collapsing the worker's `none` to `[]`. -/
def get_ancestor_roots (store : Store Root) (block_root terminal_root : Root) :
    List Root :=
  (get_ancestor_roots_aux store terminal_root ((store.blocks block_root).slot + 1)
    block_root).getD []

/-! ## State helpers

The spec allows implementations to override these "but the semantics MUST be
preserved"; the model transcribes them on top of the abstract `Externals`
primitives (committee shuffling, `process_slots`). -/

/-- `get_slot_committee`: Return participants of all committees in ``slot``
(MUST support committees of epochs starting from `current_epoch - 2`).
```python
head = get_head(store).root
shuffling_source = store.block_states[head]
committees_count = get_committee_count_per_slot(shuffling_source, compute_epoch_at_slot(slot))
participants: Set[ValidatorIndex] = set()
for i in range(committees_count):
    participants.update(get_beacon_committee(shuffling_source, slot, CommitteeIndex(i)))
return participants
``` -/
def get_slot_committee (store : Store Root) (slot : Slot) : Finset ValidatorIndex :=
  let head := (get_head cfg store).root
  let shuffling_source := store.block_states head
  let committees_count :=
    ext.get_committee_count_per_slot shuffling_source (compute_epoch_at_slot cfg slot)
  (Finset.range committees_count).biUnion
    (fun i => (ext.get_beacon_committee shuffling_source slot i).toFinset)

/-- `get_pulled_up_head_state`: Return the state of the head pulled up to the
current epoch if needed.
```python
head = get_head(store).root
head_state = store.block_states[head]
if get_current_epoch(head_state) < get_current_store_epoch(store):
    pulled_up_state = head_state.copy()
    process_slots(pulled_up_state, compute_start_slot_at_epoch(get_current_store_epoch(store)))
    return pulled_up_state
else:
    return head_state
``` -/
def get_pulled_up_head_state (store : Store Root) : BeaconState Root :=
  let head := (get_head cfg store).root
  let head_state := store.block_states head
  if get_current_epoch cfg head_state < get_current_store_epoch cfg store then
    ext.process_slots head_state
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
  else
    head_state

/-- `get_previous_balance_source` (used only by reconfirmation):
```python
store = fcr_store.store
return store.checkpoint_states[fcr_store.previous_epoch_observed_justified_checkpoint]
``` -/
def get_previous_balance_source (fcr_store : FastConfirmationStore Root) :
    BeaconState Root :=
  let store := fcr_store.store
  store.checkpoint_states fcr_store.previous_epoch_observed_justified_checkpoint

/-- `get_current_balance_source`:
```python
store = fcr_store.store
return store.checkpoint_states[fcr_store.current_epoch_observed_justified_checkpoint]
``` -/
def get_current_balance_source (fcr_store : FastConfirmationStore Root) :
    BeaconState Root :=
  let store := fcr_store.store
  store.checkpoint_states fcr_store.current_epoch_observed_justified_checkpoint

end FastConfirmation.Spec

end
