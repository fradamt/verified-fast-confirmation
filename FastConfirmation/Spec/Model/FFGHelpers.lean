module
public import FastConfirmation.Spec.Model.LMDHelpers

@[expose] public section

/-!
# Spec / Model / FFGHelpers

The "FFG helpers" section of `specs/phase0/fast-confirmation.md`
(`get_current_target_score` … `will_current_target_be_justified`), transcribed
1:1 in document order.
-/

namespace FastConfirmation.Spec

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
                (get_latest_message_epoch latest_message)))
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
    total_active_balance, compute_start_slot_at_epoch(current_epoch), current_slot - 1)
remaining_ffg_weight = total_active_balance - ffg_weight_till_now
remaining_honest_ffg_weight = (
    remaining_ffg_weight // 100 * (100 - CONFIRMATION_BYZANTINE_THRESHOLD))
adversarial_weight = compute_adversarial_weight(
    store, balance_source, compute_start_slot_at_epoch(current_epoch), current_slot - 1)
min_honest_ffg_support = saturating_sub(ffg_support_for_checkpoint, adversarial_weight)
return min_honest_ffg_support + remaining_honest_ffg_weight
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
  let min_honest_ffg_support := ffg_support_for_checkpoint - adversarial_weight
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

end FastConfirmation.Spec

end
