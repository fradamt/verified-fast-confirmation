import FastConfirmation.Spec.Model.FFGHelpers

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

namespace FastConfirmation.Spec

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

end FastConfirmation.Spec
