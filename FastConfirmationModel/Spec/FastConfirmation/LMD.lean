module
public import FastConfirmationModel.Spec.FastConfirmation.Store

@[expose] public section

/-!
# Spec / Model / LMDHelpers

The "LMD-GHOST helpers" section of `specs/phase0/fast-confirmation.md`
(`get_block_support_between_slots` … `is_confirmed_chain_safe`), transcribed
1:1 in document order. All slot ranges are inclusive of both endpoints
(python `range(start, end + 1)` = `Finset.Icc start end`, empty when
`start > end`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `get_block_support_between_slots`: Return support of the block by
validators assigned to slots between ``start_slot`` and ``end_slot``
(inclusive of both).
```python
participants: Set[ValidatorIndex] = set()
for slot in range(start_slot, end_slot + 1):
    participants.update(get_slot_committee(store, Slot(slot)))
unslashed_and_active_indices = [
    i for i in participants
    if (not balance_source.validators[i].slashed
        and is_active_validator(balance_source.validators[i], get_current_epoch(balance_source)))
]
return Gwei(sum(
    balance_source.validators[i].effective_balance
    for i in unslashed_and_active_indices
    if (i in store.latest_messages
        and store.latest_messages[i].root == block_root
        and i not in store.equivocating_indices)
))
``` -/
def get_block_support_between_slots (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root)
    (start_slot end_slot : Slot) : Gwei :=
  let participants :=
    (Finset.Icc start_slot end_slot).biUnion (fun slot => get_slot_committee cfg ext store slot)
  let unslashed_and_active_indices :=
    participants.filter (fun i =>
      !(balance_source.validators.getD i default).slashed &&
        is_active_validator (balance_source.validators.getD i default)
          (get_current_epoch cfg balance_source))
  ∑ i ∈ unslashed_and_active_indices.filter (fun i =>
      (store.latest_messages i).any (fun latest_message =>
        decide (latest_message.root = block_root) &&
          decide (i ∉ store.equivocating_indices))),
    (balance_source.validators.getD i default).effective_balance

/-- Gloas override: count votes for the parent's payload branch used by the
child and PENDING parent votes. PENDING votes support neither resolved branch.
Votes for the other resolved status support the competing branch. -/
def get_parent_payload_support_between_slots (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root)
    (payload_status : PayloadStatus) (start_slot end_slot : Slot) : Gwei :=
  let participants :=
    (Finset.Icc start_slot end_slot).biUnion (fun slot => get_slot_committee cfg ext store slot)
  let unslashed_and_active_indices :=
    participants.filter (fun i =>
      !(balance_source.validators.getD i default).slashed &&
        is_active_validator (balance_source.validators.getD i default)
          (get_current_epoch cfg balance_source))
  ∑ i ∈ unslashed_and_active_indices.filter (fun i =>
      (store.latest_messages i).any (fun latest_message =>
        decide (latest_message.root = block_root) &&
          decide (i ∉ store.equivocating_indices) &&
          decide ((get_supported_node store latest_message).payload_status = payload_status ∨
            (get_supported_node store latest_message).payload_status = .pending))),
    (balance_source.validators.getD i default).effective_balance

/-- `is_full_validator_set_covered`: Return ``True`` if the range between
``start_slot`` and ``end_slot`` (inclusive of both) includes an entire epoch.
```python
start_full_epoch = compute_epoch_at_slot(start_slot + SLOTS_PER_EPOCH - 1)
end_full_epoch = compute_epoch_at_slot(end_slot + 1)
return start_full_epoch < end_full_epoch
``` -/
def is_full_validator_set_covered (start_slot end_slot : Slot) : Bool :=
  let start_full_epoch := compute_epoch_at_slot cfg (start_slot + (cfg.slots_per_epoch - 1))
  let end_full_epoch := compute_epoch_at_slot cfg (end_slot + 1)
  decide (start_full_epoch < end_full_epoch)

/-- `adjust_committee_weight_estimate_to_ensure_safety`: Return adjusted
``estimate`` of the weight of a committee for a sequence of slots spanning an
epoch boundary that does not cover any full epoch (per-mille inflation; the
`999`/`1000` literals are the spec's own per-mille encoding).
```python
ceil = (estimate + 999) // 1000
return ceil * (1000 + COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR)
``` -/
def adjust_committee_weight_estimate_to_ensure_safety (estimate : Gwei) : Gwei :=
  let ceil := (estimate + 999) / 1000
  ceil * (1000 + cfg.committee_weight_estimation_adjustment_factor)

/-- `estimate_committee_weight_between_slots`: Return estimate of the total
weight of committees between ``start_slot`` and ``end_slot`` (inclusive of
both).
```python
if start_slot > end_slot:
    return Gwei(0)
if is_full_validator_set_covered(start_slot, end_slot):
    return total_active_balance
start_epoch = compute_epoch_at_slot(start_slot)
end_epoch = compute_epoch_at_slot(end_slot)
committee_weight = total_active_balance // Uint64(SLOTS_PER_EPOCH)
if start_epoch == end_epoch:
    return committee_weight * Uint64(end_slot - start_slot + 1)
else:
    num_slots_in_end_epoch = Uint64(compute_slots_since_epoch_start(end_slot) + 1)
    remaining_slots_in_end_epoch = Uint64(SLOTS_PER_EPOCH) - num_slots_in_end_epoch
    num_slots_in_start_epoch = Uint64(
        SLOTS_PER_EPOCH - compute_slots_since_epoch_start(start_slot)
    )
    start_epoch_weight = committee_weight * num_slots_in_start_epoch
    end_epoch_weight = committee_weight * num_slots_in_end_epoch
    start_epoch_weight_pro_rated = (
        start_epoch_weight // Uint64(SLOTS_PER_EPOCH) * remaining_slots_in_end_epoch
    )
    return adjust_committee_weight_estimate_to_ensure_safety(
        start_epoch_weight_pro_rated + end_epoch_weight
    )
``` -/
def estimate_committee_weight_between_slots (total_active_balance : Gwei)
    (start_slot end_slot : Slot) : Gwei :=
  if start_slot > end_slot then
    0
  else if is_full_validator_set_covered cfg start_slot end_slot then
    total_active_balance
  else
    let start_epoch := compute_epoch_at_slot cfg start_slot
    let end_epoch := compute_epoch_at_slot cfg end_slot
    let committee_weight := total_active_balance / cfg.slots_per_epoch
    if start_epoch = end_epoch then
      committee_weight * (end_slot - start_slot + 1)
    else
      let num_slots_in_end_epoch := compute_slots_since_epoch_start cfg end_slot + 1
      let remaining_slots_in_end_epoch := cfg.slots_per_epoch - num_slots_in_end_epoch
      let num_slots_in_start_epoch :=
        cfg.slots_per_epoch - compute_slots_since_epoch_start cfg start_slot
      let start_epoch_weight := committee_weight * num_slots_in_start_epoch
      let end_epoch_weight := committee_weight * num_slots_in_end_epoch
      let start_epoch_weight_pro_rated :=
        start_epoch_weight / cfg.slots_per_epoch * remaining_slots_in_end_epoch
      adjust_committee_weight_estimate_to_ensure_safety cfg
        (start_epoch_weight_pro_rated + end_epoch_weight)

/-- `get_equivocation_score`: Return total weight of equivocating participants
of all committees in the slots between ``start_slot`` and ``end_slot``
(inclusive of both).
```python
committee_indices: Set[ValidatorIndex] = set()
for slot in range(start_slot, end_slot + 1):
    committee_indices.update(get_slot_committee(store, Slot(slot)))
active_equivocating_indices = [
    i for i in committee_indices.intersection(store.equivocating_indices)
    if is_active_validator(balance_source.validators[i], get_current_epoch(balance_source))
]
return Gwei(sum(balance_source.validators[i].effective_balance
                for i in active_equivocating_indices))
``` -/
def get_equivocation_score (store : Store Root) (balance_source : BeaconState Root)
    (start_slot end_slot : Slot) : Gwei :=
  let committee_indices :=
    (Finset.Icc start_slot end_slot).biUnion (fun slot => get_slot_committee cfg ext store slot)
  let active_equivocating_indices :=
    (committee_indices ∩ store.equivocating_indices).filter (fun i =>
      is_active_validator (balance_source.validators.getD i default)
        (get_current_epoch cfg balance_source))
  ∑ i ∈ active_equivocating_indices,
    (balance_source.validators.getD i default).effective_balance

/-- `compute_adversarial_weight`: Return maximum possible adversarial weight in
the committees of the slots between ``start_slot`` and ``end_slot`` (inclusive
of both), assuming `CONFIRMATION_BYZANTINE_THRESHOLD` and discounting already
equivocated validators.
```python
total_active_balance = get_total_active_balance(balance_source)
maximum_weight = estimate_committee_weight_between_slots(total_active_balance, start_slot, end_slot)
max_adversarial_weight = maximum_weight // 100 * CONFIRMATION_BYZANTINE_THRESHOLD
equivocation_score = get_equivocation_score(store, balance_source, start_slot, end_slot)
if max_adversarial_weight > equivocation_score:
    return max_adversarial_weight - equivocation_score
else:
    return Gwei(0)
``` -/
def compute_adversarial_weight (store : Store Root) (balance_source : BeaconState Root)
    (start_slot end_slot : Slot) : Gwei :=
  let total_active_balance := get_total_active_balance cfg balance_source
  let maximum_weight :=
    estimate_committee_weight_between_slots cfg total_active_balance start_slot end_slot
  let max_adversarial_weight := maximum_weight / 100 * cfg.confirmation_byzantine_threshold
  let equivocation_score := get_equivocation_score cfg ext store balance_source start_slot end_slot
  if max_adversarial_weight > equivocation_score then
    max_adversarial_weight - equivocation_score
  else
    0

/-- `get_adversarial_weight`: Return maximum adversarial weight that can
support the block.
```python
current_slot = get_current_slot(store)
block = store.blocks[block_root]
if get_block_epoch(store, block_root) > get_block_epoch(store, block.parent_root):
    start_slot = compute_start_slot_at_epoch(get_block_epoch(store, block_root))
    return compute_adversarial_weight(store, balance_source, start_slot, current_slot - 1)
else:
    return compute_adversarial_weight(store, balance_source, block.slot, current_slot - 1)
``` -/
def get_adversarial_weight (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) : Gwei :=
  let current_slot := get_current_slot cfg store
  let block := store.blocks block_root
  if get_block_epoch cfg store block_root > get_block_epoch cfg store block.parent_root then
    let start_slot := compute_start_slot_at_epoch cfg (get_block_epoch cfg store block_root)
    compute_adversarial_weight cfg ext store balance_source start_slot (current_slot - 1)
  else
    compute_adversarial_weight cfg ext store balance_source block.slot (current_slot - 1)

/-- `compute_empty_slot_support_discount`: Return weight that can be discounted
during the safety threshold computation if there are empty slots preceding the
block.
```python
block = store.blocks[block_root]
parent_block = store.blocks[block.parent_root]
if parent_block.slot + 1 == block.slot:
    return Gwei(0)
parent_support_in_empty_slots = get_parent_payload_support_between_slots(
    store, balance_source, block.parent_root, get_parent_payload_status(store, block),
    parent_block.slot + 1, block.slot - 1)
adversarial_weight = compute_adversarial_weight(
    store, balance_source, parent_block.slot + 1, block.slot - 1)
if parent_support_in_empty_slots > adversarial_weight:
    return parent_support_in_empty_slots - adversarial_weight
else:
    return Gwei(0)
``` -/
def compute_empty_slot_support_discount (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root) : Gwei :=
  let block := store.blocks block_root
  let parent_block := store.blocks block.parent_root
  if parent_block.slot + 1 = block.slot then
    0
  else
    let parent_support_in_empty_slots :=
      get_parent_payload_support_between_slots cfg ext store balance_source block.parent_root
        (get_parent_payload_status store block) (parent_block.slot + 1) (block.slot - 1)
    let adversarial_weight :=
      compute_adversarial_weight cfg ext store balance_source
        (parent_block.slot + 1) (block.slot - 1)
    if parent_support_in_empty_slots > adversarial_weight then
      parent_support_in_empty_slots - adversarial_weight
    else
      0

/-- `get_support_discount`: Return weight that can be discounted during the
safety threshold computation for the block.
```python
return compute_empty_slot_support_discount(store, balance_source, block_root)
``` -/
def get_support_discount (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) : Gwei :=
  compute_empty_slot_support_discount cfg ext store balance_source block_root

/-- `compute_safety_threshold`: Compute the LMD-GHOST safety threshold for
``block_root``.
```python
current_slot = get_current_slot(store)
block = store.blocks[block_root]
parent_block = store.blocks[block.parent_root]
total_active_balance = get_total_active_balance(balance_source)
proposer_score = compute_proposer_score(balance_source)
maximum_support = estimate_committee_weight_between_slots(
    total_active_balance, parent_block.slot + 1, current_slot - 1)
support_discount = get_support_discount(store, balance_source, block_root)
adversarial_weight = get_adversarial_weight(store, balance_source, block_root)
# (maximum_support + proposer_score - support_discount) // 2 + adversarial_weight
# with an underflow guard
if support_discount < maximum_support + proposer_score + 2 * adversarial_weight:
    return (maximum_support + proposer_score + 2 * adversarial_weight - support_discount) // 2
else:
    return Gwei(0)
``` -/
def compute_safety_threshold (store : Store Root) (block_root : Root)
    (balance_source : BeaconState Root) : Gwei :=
  let current_slot := get_current_slot cfg store
  let block := store.blocks block_root
  let parent_block := store.blocks block.parent_root
  let total_active_balance := get_total_active_balance cfg balance_source
  let proposer_score := compute_proposer_score cfg balance_source
  let maximum_support :=
    estimate_committee_weight_between_slots cfg total_active_balance
      (parent_block.slot + 1) (current_slot - 1)
  let support_discount := get_support_discount cfg ext store balance_source block_root
  let adversarial_weight := get_adversarial_weight cfg ext store balance_source block_root
  if support_discount < maximum_support + proposer_score + 2 * adversarial_weight then
    (maximum_support + proposer_score + 2 * adversarial_weight - support_discount) / 2
  else
    0

/-- `is_one_confirmed`: Return ``True`` if and only if the block is LMD-GHOST
safe (support outweighs the safety threshold). Phase0 note: the spec's
optimistic-sync "MUST return False if not VALID" clause is a post-Bellatrix
concern with no phase0 counterpart — see `docs/MODELING_CHOICES.md`.
```python
support = get_attestation_score(store, get_node_for_root(block_root), balance_source)
safety_threshold = compute_safety_threshold(store, block_root, balance_source)
return support > safety_threshold
``` -/
def is_one_confirmed (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) : Bool :=
  let support := get_attestation_score cfg store (get_node_for_root block_root) balance_source
  let safety_threshold := compute_safety_threshold cfg ext store block_root balance_source
  decide (support > safety_threshold)

/-- `is_confirmed_chain_safe`: Return ``True`` if and only if all blocks of the
confirmed chain starting from `current_epoch_observed_justified_checkpoint`
are LMD-GHOST safe (the start-of-epoch reconfirmation, run with the previous
balance source).
```python
store = fcr_store.store
if fcr_store.current_epoch_observed_justified_checkpoint != get_checkpoint_for_block(
    store, confirmed_root, fcr_store.current_epoch_observed_justified_checkpoint.epoch
):
    return False
current_epoch = get_current_store_epoch(store)
if fcr_store.current_epoch_observed_justified_checkpoint.epoch + 1 >= current_epoch:
    start_root_exclusive = fcr_store.current_epoch_observed_justified_checkpoint.root
else:
    ancestor_at_previous_epoch_start = get_ancestor(
        store, get_node_for_root(confirmed_root),
        compute_start_slot_at_epoch(current_epoch - 1),
    ).root
    if get_block_epoch(store, ancestor_at_previous_epoch_start) + 1 == current_epoch:
        start_root_exclusive = store.blocks[ancestor_at_previous_epoch_start].parent_root
    else:
        start_root_exclusive = ancestor_at_previous_epoch_start
chain_roots = get_ancestor_roots(store, confirmed_root, start_root_exclusive)
return all(
    is_one_confirmed(store, get_previous_balance_source(fcr_store), root)
    for root in chain_roots
)
``` -/
def is_confirmed_chain_safe (fcr_store : FastConfirmationStore Root)
    (confirmed_root : Root) : Bool :=
  let store := fcr_store.store
  if fcr_store.current_epoch_observed_justified_checkpoint ≠
      get_checkpoint_for_block cfg store confirmed_root
        fcr_store.current_epoch_observed_justified_checkpoint.epoch then
    false
  else
    let current_epoch := get_current_store_epoch cfg store
    let start_root_exclusive :=
      if fcr_store.current_epoch_observed_justified_checkpoint.epoch + 1 ≥ current_epoch then
        fcr_store.current_epoch_observed_justified_checkpoint.root
      else
        let ancestor_at_previous_epoch_start :=
          (get_ancestor store (get_node_for_root confirmed_root)
            (compute_start_slot_at_epoch cfg (current_epoch - 1))).root
        if get_block_epoch cfg store ancestor_at_previous_epoch_start + 1 = current_epoch then
          (store.blocks ancestor_at_previous_epoch_start).parent_root
        else
          ancestor_at_previous_epoch_start
    let chain_roots := get_ancestor_roots store confirmed_root start_root_exclusive
    chain_roots.all (fun root =>
      is_one_confirmed cfg ext store (get_previous_balance_source fcr_store) root)

end FastConfirmation.Spec

end
