module
public import FastConfirmation.Spec.Model.LMDHelpers

@[expose] public section

/-!
# Frozen strong rule reference

Source: `main` commit `249dd96dfc838fc4b0a90d036a209dfd3bbac8f9` (249dd96),
read from `/home/fradamt/lean/fast-confirmation`:
* `FastConfirmation/Spec/Model/ForkChoice.lean` (`get_attestation_score`)
* `FastConfirmation/Spec/Model/LMDHelpers.lean`
* `FastConfirmation/Spec/Model/FFGHelpers.lean`
* `FastConfirmation/Spec/Model/Confirmation.lean`

The raw attestation score and three source files follow in dependency order.
Only import lines and namespace names change in the three complete copies.
The shared dependency files `FCRStore.lean`, `ForkChoice.lean`, `Types.lean`,
and `Config.lean` are byte identical in the source and this tree.
Do not change these frozen definitions.
-/


namespace FastConfirmation.Spec.Strong

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

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

end FastConfirmation.Spec.Strong

/-!
# Spec / Model / LMDHelpers

The "LMD-GHOST helpers" section of `specs/phase0/fast-confirmation.md`
(`get_block_support_between_slots` … `is_confirmed_chain_safe`), transcribed
1:1 in document order. All slot ranges are inclusive of both endpoints
(python `range(start, end + 1)` = `Finset.Icc start end`, empty when
`start > end`).
-/

namespace FastConfirmation.Spec.Strong

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

/-- `is_full_validator_set_covered`: Return ``True`` if the range between
``start_slot`` and ``end_slot`` (inclusive of both) includes an entire epoch.
```python
start_full_epoch = compute_epoch_at_slot(start_slot + (SLOTS_PER_EPOCH - 1))
end_full_epoch = compute_epoch_at_slot(Slot(end_slot + 1))
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
return Gwei(ceil * (1000 + COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR))
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
committee_weight = total_active_balance // SLOTS_PER_EPOCH
if start_epoch == end_epoch:
    return committee_weight * (end_slot - start_slot + 1)
else:
    num_slots_in_end_epoch = compute_slots_since_epoch_start(end_slot) + 1
    remaining_slots_in_end_epoch = SLOTS_PER_EPOCH - num_slots_in_end_epoch
    num_slots_in_start_epoch = SLOTS_PER_EPOCH - compute_slots_since_epoch_start(start_slot)
    start_epoch_weight = committee_weight * num_slots_in_start_epoch
    end_epoch_weight = committee_weight * num_slots_in_end_epoch
    start_epoch_weight_pro_rated = (
        start_epoch_weight // SLOTS_PER_EPOCH * remaining_slots_in_end_epoch
    )
    return adjust_committee_weight_estimate_to_ensure_safety(
        Gwei(start_epoch_weight_pro_rated + end_epoch_weight)
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
    return Gwei(max_adversarial_weight - equivocation_score)
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
    return compute_adversarial_weight(store, balance_source, start_slot, Slot(current_slot - 1))
else:
    return compute_adversarial_weight(store, balance_source, block.slot, Slot(current_slot - 1))
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
parent_support_in_empty_slots = get_block_support_between_slots(
    store, balance_source, block.parent_root, Slot(parent_block.slot + 1), Slot(block.slot - 1))
adversarial_weight = compute_adversarial_weight(
    store, balance_source, Slot(parent_block.slot + 1), Slot(block.slot - 1))
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
        (get_parent_payload_status store block)
        (parent_block.slot + 1) (block.slot - 1)
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
    total_active_balance, Slot(parent_block.slot + 1), Slot(current_slot - 1))
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
concern with no phase0 counterpart — see `docs/spec-model-design.md`.
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
        compute_start_slot_at_epoch(Epoch(current_epoch - 1)),
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

end FastConfirmation.Spec.Strong


/-!
# Spec / Model / FFGHelpers

The "FFG helpers" section of `specs/phase0/fast-confirmation.md`
(`get_current_target_score` … `will_current_target_be_justified`), transcribed
1:1 in document order.
-/

namespace FastConfirmation.Spec.Strong

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `get_current_target_score`: Return the estimate of FFG support of the
current epoch target by using LMD-GHOST votes (MUST be used no later than the
end of the current epoch).
```python
target = get_current_target(store)
state = get_pulled_up_head_state(store)
unslashed_and_active_indices = [
    i for i in get_active_validator_indices(state, get_current_epoch(state))
    if not state.validators[i].slashed
]
return Gwei(sum(
    state.validators[i].effective_balance
    for i in unslashed_and_active_indices
    if (i in store.latest_messages
        and i not in store.equivocating_indices
        and target == get_checkpoint_for_block(
            store, store.latest_messages[i].root,
            get_latest_message_epoch(store.latest_messages[i])))
))
``` -/
def get_current_target_score (store : Store Root) : Gwei :=
  let target := get_current_target cfg store
  let state := get_pulled_up_head_state cfg ext store
  let unslashed_and_active_indices :=
    (get_active_validator_indices state (get_current_epoch cfg state)).filter
      (fun i => !(state.validators.getD i default).slashed)
  ((unslashed_and_active_indices.filter fun i =>
      match store.latest_messages i with
      | none => false
      | some latest_message =>
          decide (i ∉ store.equivocating_indices) &&
            decide (target =
              get_checkpoint_for_block cfg store latest_message.root
                (get_latest_message_epoch cfg latest_message)))
    |>.map fun i => (state.validators.getD i default).effective_balance).sum

/-- `compute_honest_ffg_support_for_current_target`: Compute honest FFG support
of the current epoch target, assuming `CONFIRMATION_BYZANTINE_THRESHOLD` and
network synchrony, and taking into account votes supporting the target that
have been received thus far.
```python
current_slot = get_current_slot(store)
current_epoch = compute_epoch_at_slot(current_slot)
balance_source = get_pulled_up_head_state(store)
total_active_balance = get_total_active_balance(balance_source)
ffg_support_for_checkpoint = get_current_target_score(store)
ffg_weight_till_now = estimate_committee_weight_between_slots(
    total_active_balance, compute_start_slot_at_epoch(current_epoch), Slot(current_slot - 1))
remaining_ffg_weight = total_active_balance - ffg_weight_till_now
remaining_honest_ffg_weight = Gwei(
    remaining_ffg_weight // 100 * (100 - CONFIRMATION_BYZANTINE_THRESHOLD))
adversarial_weight = compute_adversarial_weight(
    store, balance_source, compute_start_slot_at_epoch(current_epoch), Slot(current_slot - 1))
min_honest_ffg_support = ffg_support_for_checkpoint - min(
    adversarial_weight, ffg_support_for_checkpoint)
return Gwei(min_honest_ffg_support + remaining_honest_ffg_weight)
``` -/
def compute_honest_ffg_support_for_current_target (store : Store Root) : Gwei :=
  let current_slot := get_current_slot cfg store
  let current_epoch := compute_epoch_at_slot cfg current_slot
  let balance_source := get_pulled_up_head_state cfg ext store
  let total_active_balance := get_total_active_balance cfg balance_source
  let ffg_support_for_checkpoint := get_current_target_score cfg ext store
  let ffg_weight_till_now :=
    estimate_committee_weight_between_slots cfg total_active_balance
      (compute_start_slot_at_epoch cfg current_epoch) (current_slot - 1)
  let remaining_ffg_weight := total_active_balance - ffg_weight_till_now
  let remaining_honest_ffg_weight :=
    remaining_ffg_weight / 100 * (100 - cfg.confirmation_byzantine_threshold)
  let adversarial_weight :=
    compute_adversarial_weight cfg ext store balance_source
      (compute_start_slot_at_epoch cfg current_epoch) (current_slot - 1)
  let min_honest_ffg_support :=
    ffg_support_for_checkpoint - min adversarial_weight ffg_support_for_checkpoint
  min_honest_ffg_support + remaining_honest_ffg_weight

/-- `will_no_conflicting_checkpoint_be_justified`: Return ``True`` if and only
if no checkpoint conflicting with the current target can ever be justified
(assumes all honest validators will vote for the current target from now on).
```python
if get_current_target(store) == store.unrealized_justified_checkpoint:
    return True
state = get_pulled_up_head_state(store)
total_active_balance = get_total_active_balance(state)
honest_ffg_support = compute_honest_ffg_support_for_current_target(store)
return 3 * honest_ffg_support > 1 * total_active_balance
``` -/
def will_no_conflicting_checkpoint_be_justified (store : Store Root) : Bool :=
  if get_current_target cfg store = store.unrealized_justified_checkpoint then
    true
  else
    let state := get_pulled_up_head_state cfg ext store
    let total_active_balance := get_total_active_balance cfg state
    let honest_ffg_support := compute_honest_ffg_support_for_current_target cfg ext store
    decide (3 * honest_ffg_support > 1 * total_active_balance)

/-- `will_current_target_be_justified`: Return ``True`` if and only if the
current target will eventually be justified (assumes all honest validators
will vote for the current target from now on).
```python
state = get_pulled_up_head_state(store)
total_active_balance = get_total_active_balance(state)
honest_ffg_support = compute_honest_ffg_support_for_current_target(store)
return 3 * honest_ffg_support >= 2 * total_active_balance
``` -/
def will_current_target_be_justified (store : Store Root) : Bool :=
  let state := get_pulled_up_head_state cfg ext store
  let total_active_balance := get_total_active_balance cfg state
  let honest_ffg_support := compute_honest_ffg_support_for_current_target cfg ext store
  decide (3 * honest_ffg_support ≥ 2 * total_active_balance)

end FastConfirmation.Spec.Strong


/-!
# Spec / Model / Confirmation

The top level of `specs/phase0/fast-confirmation.md`:
`update_fast_confirmation_variables`, `find_latest_confirmed_descendant`,
`get_latest_confirmed`, and the `on_fast_confirmation` handler. Python
mutation of `fcr_store` becomes state-passing
(`FastConfirmationStore → FastConfirmationStore`); the two `for … break`
loops become structural recursions over `canonical_roots` carrying the
loop-mutable accumulator (`break` = return the accumulator; loop fall-through
= recurse on the tail) — see `docs/spec-model-design.md`, decision 6.
-/

namespace FastConfirmation.Spec.Strong

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `update_fast_confirmation_variables`: updates the FCR variables. Python
mutates the three field groups **in order**; the chained record updates below
preserve that order (in particular the observed-checkpoint rotation reads the
`previous_epoch_greatest_unrealized_checkpoint` possibly written just above).
```python
store = fcr_store.store
fcr_store.previous_slot_head = fcr_store.current_slot_head
fcr_store.current_slot_head = get_head(store).root
if is_start_slot_at_epoch(Slot(get_current_slot(store) + 1)):
    fcr_store.previous_epoch_greatest_unrealized_checkpoint = store.unrealized_justified_checkpoint
if is_start_slot_at_epoch(get_current_slot(store)):
    fcr_store.previous_epoch_observed_justified_checkpoint = (
        fcr_store.current_epoch_observed_justified_checkpoint)
    fcr_store.current_epoch_observed_justified_checkpoint = (
        fcr_store.previous_epoch_greatest_unrealized_checkpoint)
``` -/
def update_fast_confirmation_variables (fcr_store : FastConfirmationStore Root) :
    FastConfirmationStore Root :=
  let store := fcr_store.store
  -- Update prev and curr slot head
  let fcr_store :=
    { fcr_store with
      previous_slot_head := fcr_store.current_slot_head
      current_slot_head := (get_head cfg store).root }
  -- Update greatest unrealized justified checkpoint at the last slot of an epoch
  let fcr_store :=
    if is_start_slot_at_epoch cfg (get_current_slot cfg store + 1) then
      { fcr_store with
        previous_epoch_greatest_unrealized_checkpoint :=
          store.unrealized_justified_checkpoint }
    else fcr_store
  -- Update observed justified checkpoints at the start of an epoch
  if is_start_slot_at_epoch cfg (get_current_slot cfg store) then
    { fcr_store with
      previous_epoch_observed_justified_checkpoint :=
        fcr_store.current_epoch_observed_justified_checkpoint
      current_epoch_observed_justified_checkpoint :=
        fcr_store.previous_epoch_greatest_unrealized_checkpoint }
  else fcr_store

/-- The first `for block_root in canonical_roots: … break` loop of
`find_latest_confirmed_descendant` (previous-epoch advancement), carrying the
loop-mutable `confirmed_root`.
```python
for block_root in canonical_roots:
    block_epoch = get_block_epoch(store, block_root)
    if block_epoch == current_epoch:
        break
    if not is_ancestor(store, get_node_for_root(fcr_store.previous_slot_head),
                       get_node_for_root(block_root)):
        break
    if not is_one_confirmed(store, get_current_balance_source(fcr_store), block_root):
        break
    confirmed_root = block_root
``` -/
def find_latest_confirmed_descendant_prev_epoch_loop
    (fcr_store : FastConfirmationStore Root) (current_epoch : Epoch) :
    List Root → Root → Root
  | [], confirmed_root => confirmed_root
  | block_root :: rest, confirmed_root =>
    let store := fcr_store.store
    let block_epoch := get_block_epoch cfg store block_root
    -- If the current epoch is reached, exit the loop
    -- as this code is meant to confirm blocks from the previous epoch
    if block_epoch = current_epoch then
      confirmed_root
    -- The algorithm can only rely on the previous head
    -- if it is a descendant of the block that is attempted to be confirmed
    else if ¬ is_ancestor store (get_node_for_root fcr_store.previous_slot_head)
        (get_node_for_root block_root) then
      confirmed_root
    else if ¬ is_one_confirmed cfg ext store (get_current_balance_source fcr_store)
        block_root then
      confirmed_root
    else
      find_latest_confirmed_descendant_prev_epoch_loop fcr_store current_epoch
        rest block_root

/-- The second `for block_root in canonical_roots: … break` loop of
`find_latest_confirmed_descendant` (tentative advancement into the current
epoch), carrying the loop-mutable `tentative_confirmed_root`.
```python
for block_root in canonical_roots:
    block_epoch = get_block_epoch(store, block_root)
    tentative_confirmed_epoch = get_block_epoch(store, tentative_confirmed_root)
    if block_epoch > tentative_confirmed_epoch:
        if not will_current_target_be_justified(store):
            break
    if not is_one_confirmed(store, get_current_balance_source(fcr_store), block_root):
        break
    tentative_confirmed_root = block_root
``` -/
def find_latest_confirmed_descendant_tentative_loop
    (fcr_store : FastConfirmationStore Root) :
    List Root → Root → Root
  | [], tentative_confirmed_root => tentative_confirmed_root
  | block_root :: rest, tentative_confirmed_root =>
    let store := fcr_store.store
    let block_epoch := get_block_epoch cfg store block_root
    let tentative_confirmed_epoch := get_block_epoch cfg store tentative_confirmed_root
    -- To confirm blocks from the current epoch ensure that
    -- current epoch target will be justified
    if block_epoch > tentative_confirmed_epoch ∧
        ¬ will_current_target_be_justified cfg ext store then
      tentative_confirmed_root
    else if ¬ is_one_confirmed cfg ext store (get_current_balance_source fcr_store)
        block_root then
      tentative_confirmed_root
    else
      find_latest_confirmed_descendant_tentative_loop fcr_store rest block_root

/-- `find_latest_confirmed_descendant`: Return the most recent confirmed block
in the suffix of the canonical chain starting from ``latest_confirmed_root``
(works correctly only if `latest_confirmed_root` is canonical and from the
previous or current epoch).
```python
store = fcr_store.store
head = get_head(store).root
current_epoch = get_current_store_epoch(store)
confirmed_root = latest_confirmed_root
if (get_block_epoch(store, confirmed_root) + 1 == current_epoch
    and get_voting_source(store, fcr_store.previous_slot_head).epoch + 2 >= current_epoch
    and (is_start_slot_at_epoch(get_current_slot(store))
         or (will_no_conflicting_checkpoint_be_justified(store)
             and (store.unrealized_justifications[fcr_store.previous_slot_head].epoch + 1
                  >= current_epoch
                  or store.unrealized_justifications[head].epoch + 1 >= current_epoch)))):
    canonical_roots = get_ancestor_roots(store, head, confirmed_root)
    <prev-epoch loop>
if (is_start_slot_at_epoch(get_current_slot(store))
        or store.unrealized_justifications[head].epoch + 1 >= current_epoch):
    canonical_roots = get_ancestor_roots(store, head, confirmed_root)
    tentative_confirmed_root = confirmed_root
    <tentative loop>
    # The tentative_confirmed_root can only be confirmed
    # if it is for sure not going to be reorged out in either the current or next epoch.
    if get_block_epoch(store, tentative_confirmed_root) == current_epoch or (
        get_voting_source(store, tentative_confirmed_root).epoch + 2 >= current_epoch
        and (is_start_slot_at_epoch(get_current_slot(store))
             or will_no_conflicting_checkpoint_be_justified(store))):
        confirmed_root = tentative_confirmed_root
return confirmed_root
``` -/
def find_latest_confirmed_descendant (fcr_store : FastConfirmationStore Root)
    (latest_confirmed_root : Root) : Root :=
  let store := fcr_store.store
  let head := (get_head cfg store).root
  let current_epoch := get_current_store_epoch cfg store
  let confirmed_root := latest_confirmed_root
  let confirmed_root :=
    if get_block_epoch cfg store confirmed_root + 1 = current_epoch ∧
        (get_voting_source cfg store fcr_store.previous_slot_head).epoch + 2 ≥
          current_epoch ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) ∨
          (will_no_conflicting_checkpoint_be_justified cfg ext store ∧
            ((store.unrealized_justifications fcr_store.previous_slot_head).epoch + 1 ≥
                current_epoch ∨
              (store.unrealized_justifications head).epoch + 1 ≥ current_epoch))) then
      -- Get suffix of the canonical chain; starting with the child of the
      -- latest_confirmed_root move towards the head in attempt to advance the
      -- confirmed block, stopping at the first unconfirmed descendant
      let canonical_roots := get_ancestor_roots store head confirmed_root
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store current_epoch
        canonical_roots confirmed_root
    else confirmed_root
  if is_start_slot_at_epoch cfg (get_current_slot cfg store) ∨
      (store.unrealized_justifications head).epoch + 1 ≥ current_epoch then
    let canonical_roots := get_ancestor_roots store head confirmed_root
    let tentative_confirmed_root :=
      find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
        canonical_roots confirmed_root
    -- The tentative_confirmed_root can only be confirmed if it is for sure
    -- not going to be reorged out in either the current or next epoch.
    if get_block_epoch cfg store tentative_confirmed_root = current_epoch ∨
        ((get_voting_source cfg store tentative_confirmed_root).epoch + 2 ≥
            current_epoch ∧
          (is_start_slot_at_epoch cfg (get_current_slot cfg store) ∨
            will_no_conflicting_checkpoint_be_justified cfg ext store)) then
      tentative_confirmed_root
    else confirmed_root
  else confirmed_root

/-- `get_latest_confirmed`: Return the most recent confirmed block by executing
the FCR algorithm (revert to finalized on broken assumptions; restart from the
observed justified checkpoint at epoch start; then attempt to advance).
```python
store = fcr_store.store
confirmed_root = fcr_store.confirmed_root
current_epoch = get_current_store_epoch(store)
head = get_head(store).root
if (get_block_epoch(store, confirmed_root) + 1 < current_epoch
    or not is_ancestor(store, get_node_for_root(head), get_node_for_root(confirmed_root))
    or (is_start_slot_at_epoch(get_current_slot(store))
        and not is_confirmed_chain_safe(fcr_store, confirmed_root))):
    confirmed_root = store.finalized_checkpoint.root
is_epoch_start = is_start_slot_at_epoch(get_current_slot(store))
observed_justified_block_slot = get_block_slot(
    store, fcr_store.current_epoch_observed_justified_checkpoint.root)
is_observed_justified_block_epoch_ok = (
    compute_epoch_at_slot(observed_justified_block_slot) + 1 == current_epoch)
is_head_unrealized_justified_ok = (
    fcr_store.current_epoch_observed_justified_checkpoint
    == store.unrealized_justifications[head])
is_confirmed_block_stale = get_block_slot(store, confirmed_root) < observed_justified_block_slot
if (is_epoch_start and is_observed_justified_block_epoch_ok
        and is_head_unrealized_justified_ok and is_confirmed_block_stale):
    confirmed_root = fcr_store.current_epoch_observed_justified_checkpoint.root
if get_block_epoch(store, confirmed_root) + 1 >= current_epoch:
    return find_latest_confirmed_descendant(fcr_store, confirmed_root)
else:
    return confirmed_root
``` -/
def get_latest_confirmed (fcr_store : FastConfirmationStore Root) : Root :=
  let store := fcr_store.store
  let confirmed_root := fcr_store.confirmed_root
  let current_epoch := get_current_store_epoch cfg store
  -- Revert to finalized block if the confirmed block is too old, is not
  -- canonical, or the confirmed chain cannot be re-confirmed at epoch start
  let head := (get_head cfg store).root
  let confirmed_root :=
    if get_block_epoch cfg store confirmed_root + 1 < current_epoch ∨
        ¬ is_ancestor store (get_node_for_root head) (get_node_for_root confirmed_root) ∨
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) ∧
          ¬ is_confirmed_chain_safe cfg ext fcr_store confirmed_root) then
      store.finalized_checkpoint.root
    else confirmed_root
  -- Restart the confirmation chain from the observed justified checkpoint
  -- when the epoch-start restart conditions are all met
  let is_epoch_start := is_start_slot_at_epoch cfg (get_current_slot cfg store)
  let observed_justified_block_slot :=
    get_block_slot store fcr_store.current_epoch_observed_justified_checkpoint.root
  let is_observed_justified_block_epoch_ok :=
    decide (compute_epoch_at_slot cfg observed_justified_block_slot + 1 = current_epoch)
  let is_head_unrealized_justified_ok :=
    decide (fcr_store.current_epoch_observed_justified_checkpoint =
      store.unrealized_justifications head)
  let is_confirmed_block_stale :=
    decide (get_block_slot store confirmed_root < observed_justified_block_slot)
  let confirmed_root :=
    if is_epoch_start && is_observed_justified_block_epoch_ok &&
        is_head_unrealized_justified_ok && is_confirmed_block_stale then
      fcr_store.current_epoch_observed_justified_checkpoint.root
    else confirmed_root
  -- Attempt to further advance the latest confirmed block
  if get_block_epoch cfg store confirmed_root + 1 ≥ current_epoch then
    find_latest_confirmed_descendant cfg ext fcr_store confirmed_root
  else
    confirmed_root

/-- `on_fast_confirmation` handler: MUST call
`update_fast_confirmation_variables` first (once per slot, in the first part
of the slot), then `get_latest_confirmed`.
```python
update_fast_confirmation_variables(fcr_store)
fcr_store.confirmed_root = get_latest_confirmed(fcr_store)
``` -/
def on_fast_confirmation (fcr_store : FastConfirmationStore Root) :
    FastConfirmationStore Root :=
  let fcr_store := update_fast_confirmation_variables cfg fcr_store
  { fcr_store with confirmed_root := get_latest_confirmed cfg ext fcr_store }

end FastConfirmation.Spec.Strong

end
