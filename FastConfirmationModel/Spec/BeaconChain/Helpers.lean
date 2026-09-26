module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Interval.Finset.Nat
public import FastConfirmationModel.Spec.Config
public import FastConfirmationModel.Spec.BeaconChain.Types
public import FastConfirmationModel.Execution.Externals

@[expose] public section

/-! Defines epoch, validator activity, and balance helpers used by
beacon chain and FCR. Python: `specs/phase0/beacon-chain.md`,
Beacon chain helpers. -/

namespace FastConfirmation.Spec
variable {Root : Type*}
variable (cfg : Config)
/-- `compute_epoch_at_slot`: Return the epoch number at ``slot``.
```python
return Epoch(slot // SLOTS_PER_EPOCH)
``` -/
def compute_epoch_at_slot (slot : Slot) : Epoch :=
  slot / cfg.slots_per_epoch

/-- `compute_start_slot_at_epoch`: Return the start slot of ``epoch``.
```python
return Slot(epoch * SLOTS_PER_EPOCH)
``` -/
def compute_start_slot_at_epoch (epoch : Epoch) : Slot :=
  epoch * cfg.slots_per_epoch

/-- `is_active_validator`: Check if ``validator`` is active.
```python
return validator.activation_epoch <= epoch < validator.exit_epoch
``` -/
def is_active_validator (validator : Validator) (epoch : Epoch) : Bool :=
  decide (validator.activation_epoch ≤ epoch ∧ epoch < validator.exit_epoch)

/-- `get_active_validator_indices`: Return the sequence of active validator
indices at ``epoch``.
```python
return [ValidatorIndex(i) for i, v in enumerate(state.validators) if is_active_validator(v, epoch)]
```
(`enumerate` becomes an order-preserving filter over `List.range`.) -/
def get_active_validator_indices (state : BeaconState Root) (epoch : Epoch) :
    List ValidatorIndex :=
  (List.range state.validators.length).filter
    (fun i => is_active_validator (state.validators.getD i default) epoch)

/-- `get_current_epoch`: Return the current epoch.
```python
return compute_epoch_at_slot(state.slot)
``` -/
def get_current_epoch (state : BeaconState Root) : Epoch :=
  compute_epoch_at_slot cfg state.slot

/-- `get_total_balance`: Return the combined effective balance of the
``indices``; ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by
zero.
```python
return Gwei(max(EFFECTIVE_BALANCE_INCREMENT,
                sum([state.validators[index].effective_balance for index in indices])))
``` -/
def get_total_balance (state : BeaconState Root) (indices : Finset ValidatorIndex) : Gwei :=
  max cfg.effective_balance_increment
    (∑ index ∈ indices, (state.validators.getD index default).effective_balance)

/-- `get_total_active_balance`: Return the combined effective balance of the
active validators.
```python
return get_total_balance(state, set(get_active_validator_indices(state, get_current_epoch(state))))
``` -/
def get_total_active_balance (state : BeaconState Root) : Gwei :=
  get_total_balance cfg state
    (get_active_validator_indices state (get_current_epoch cfg state)).toFinset

end FastConfirmation.Spec

end
