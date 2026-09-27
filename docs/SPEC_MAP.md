# Python specification map

The Python source is fork `fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`).
The executable definitions use `BeaconFunctionInterface` for opaque beacon and
payload calls. `BeaconExternalsPremises` states their used contracts. The
[review guide](REVIEW_GUIDE.md) maps each interface field to its premise.
The audited upstream base is `6b9bd532cca16555e2f3282d757622ebff29743e`. The fork
commit is `13f391516352f61b3ac5dcaae5be1884d104f86a`.

The table maps each Python function that has an authored Lean definition in the FCR,
Gloas fork-choice, beacon-chain, and validator sections. Gloas overrides take precedence
over inherited Phase0 functions. The rows after the validator rows are the concrete FFG
transition that the bridge runs (`ConcreteTransition.lean`).
[source_inventory.toml](../scripts/conformance/concrete/source_inventory.toml) pins the
source line of each of its 34 functions and 15 frames, and `check_source_inventory.py`
checks it. Four of these functions share the Helpers rows above them. A missing Python
function has no authored Lean definition in these Model modules. A Lean worker with an
_aux or _loop suffix has the row of its wrapper, except `filter_block_tree_aux`, which is
the Python filter_block_tree. The final rows identify data projections and the execution
model. “Faithful” means branch decisions follow Python on the modeled domain. Opaque
externals need their stated contracts.

```text
┌───────────────────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────────┐
│ Python section / function                         │ Lean declaration and file                                                │ Assessment                                                                    │
├───────────────────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────┤
│ gloas/fast-confirmation.md / get_node_for_root    │ get_node_for_root —                                                      │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ gloas/fast-confirmation.md /                      │ get_parent_payload_support_between_slots —                               │ Gloas extension: matching-status or PENDING parent votes.                     │
│ get_parent_payload_support_between_slots          │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ gloas/fast-confirmation.md /                      │ compute_empty_slot_support_discount —                                    │ Divergent from upstream: matching-status or PENDING parent votes only; public │
│ compute_empty_slot_support_discount               │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │ fork fix.                                                                     │
│ gloas/fast-confirmation.md /                      │ get_safe_execution_block_hash —                                          │ Simplified: projected store or execution hash.                                │
│ get_safe_execution_block_hash                     │ FastConfirmationModel/Spec/FastConfirmation/SafeExecutionBlock.lean      │                                                                               │
│ gloas/fork-choice.md / get_forkchoice_store       │ get_forkchoice_store — FastConfirmationModel/Spec/Handlers.lean          │ Simplified: drops the state_root assert (`AnchorCommitsToState` contract);    │
│                                                   │                                                                          │ `Root()` boost is Lean none; dict fields totalized.                           │
│ gloas/fork-choice.md / notify_ptc_messages        │ notify_ptc_messages — FastConfirmationModel/Spec/Handlers.lean           │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / is_payload_verified        │ is_payload_verified — FastConfirmationModel/Spec/ForkChoice.lean         │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / payload_timeliness         │ payload_timeliness — FastConfirmationModel/Spec/ForkChoice.lean          │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / payload_data_availability  │ payload_data_availability — FastConfirmationModel/Spec/ForkChoice.lean   │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / get_parent_payload_status  │ get_parent_payload_status — FastConfirmationModel/Spec/ForkChoice.lean   │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / is_parent_node_full        │ is_parent_node_full — FastConfirmationModel/Spec/ForkChoice.lean         │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / get_ancestor               │ get_ancestor — FastConfirmationModel/Spec/ForkChoice.lean                │ Simplified: finite loop fuel (`get_ancestor_aux`); branch order preserved.    │
│ gloas/fork-choice.md / is_ancestor                │ is_ancestor — FastConfirmationModel/Spec/ForkChoice.lean                 │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / get_checkpoint_block       │ get_checkpoint_block — FastConfirmationModel/Spec/ForkChoice.lean        │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / get_supported_node         │ get_supported_node — FastConfirmationModel/Spec/ForkChoice.lean          │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md /                            │ is_previous_slot_payload_decision —                                      │ Faithful control flow with Lean data types.                                   │
│ is_previous_slot_payload_decision                 │ FastConfirmationModel/Spec/ForkChoice.lean                               │                                                                               │
│ gloas/fork-choice.md / should_extend_payload      │ should_extend_payload — FastConfirmationModel/Spec/ForkChoice.lean       │ Faithful control flow with Lean data types. Python `Root()` (no boost) is     │
│                                                   │                                                                          │ Lean none.                                                                    │
│ gloas/fork-choice.md /                            │ get_payload_status_tiebreaker —                                          │ Faithful control flow with Lean data types.                                   │
│ get_payload_status_tiebreaker                     │ FastConfirmationModel/Spec/ForkChoice.lean                               │                                                                               │
│ gloas/fork-choice.md /                            │ should_apply_proposer_boost — FastConfirmationModel/Spec/ForkChoice.lean │ Faithful control flow with Lean data types. Python `Root()` (no boost) is     │
│ should_apply_proposer_boost                       │                                                                          │ Lean none.                                                                    │
│ gloas/fork-choice.md / get_weight                 │ get_weight — FastConfirmationModel/Spec/ForkChoice.lean                  │ Faithful control flow with Lean data types. Python `Root()` (no boost) is     │
│                                                   │                                                                          │ Lean none.                                                                    │
│ gloas/fork-choice.md / get_node_children          │ get_node_children — FastConfirmationModel/Spec/ForkChoice.lean           │ Simplified: finite loop fuel or explicit state passing; branch order          │
│                                                   │                                                                          │ preserved.                                                                    │
│ gloas/fork-choice.md / get_head                   │ get_head — FastConfirmationModel/Spec/ForkChoice.lean                    │ Simplified: finite loop fuel or explicit state passing; branch order          │
│                                                   │                                                                          │ preserved.                                                                    │
│ gloas/fork-choice.md / get_latest_message_epoch   │ get_latest_message_epoch — FastConfirmationModel/Spec/ForkChoice.lean    │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / get_attestation_due_ms     │ get_attestation_due_ms — FastConfirmationModel/Spec/ForkChoice.lean      │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md /                            │ get_payload_attestation_due_ms —                                         │ Faithful control flow with Lean data types.                                   │
│ get_payload_attestation_due_ms                    │ FastConfirmationModel/Spec/ForkChoice.lean                               │                                                                               │
│ gloas/fork-choice.md / is_head_late               │ is_head_late — FastConfirmationModel/Spec/ForkChoice.lean                │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / is_head_weak               │ is_head_weak — FastConfirmationModel/Spec/ForkChoice.lean                │ Uses state committee tables under the fixed-committee idealization.           │
│ gloas/fork-choice.md / validate_on_attestation    │ validate_on_attestation — FastConfirmationModel/Spec/Handlers.lean       │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / update_latest_messages     │ update_latest_messages — FastConfirmationModel/Spec/Handlers.lean        │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md / record_block_timeliness    │ record_block_timeliness — FastConfirmationModel/Spec/Handlers.lean       │ Faithful control flow with Lean data types.                                   │
│ gloas/fork-choice.md /                            │ get_shuffling_dependent_root — FastConfirmationModel/Spec/Handlers.lean  │ Faithful control flow with Lean data types.                                   │
│ get_shuffling_dependent_root                      │                                                                          │                                                                               │
│ gloas/fork-choice.md / update_proposer_boost_root │ update_proposer_boost_root — FastConfirmationModel/Spec/Handlers.lean    │ Faithful control flow with Lean data types. Python `Root()` (no boost) is     │
│                                                   │                                                                          │ Lean none.                                                                    │
│ gloas/fork-choice.md / on_block                   │ on_block — FastConfirmationModel/Spec/Handlers.lean                      │ Simplified: explicit handler result; rejected calls discard writes.           │
│ gloas/fork-choice.md /                            │ on_execution_payload_envelope — FastConfirmationModel/Spec/Handlers.lean │ Simplified: explicit handler result; rejected calls discard writes.           │
│ on_execution_payload_envelope                     │                                                                          │                                                                               │
│ gloas/fork-choice.md /                            │ on_payload_attestation_message —                                         │ Simplified: explicit handler result; rejected calls discard writes.           │
│ on_payload_attestation_message                    │ FastConfirmationModel/Spec/Handlers.lean                                 │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_fast_confirmation_store —                                            │ Faithful control flow with Lean data types.                                   │
│ get_fast_confirmation_store                       │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md / get_block_slot      │ get_block_slot — FastConfirmationModel/Spec/FastConfirmation/Store.lean  │ Faithful control flow with Lean data types.                                   │
│ phase0/fast-confirmation.md / get_block_epoch     │ get_block_epoch — FastConfirmationModel/Spec/FastConfirmation/Store.lean │ Faithful control flow with Lean data types.                                   │
│ phase0/fast-confirmation.md /                     │ get_checkpoint_for_block —                                               │ Faithful control flow with Lean data types.                                   │
│ get_checkpoint_for_block                          │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md / get_current_target  │ get_current_target —                                                     │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md /                     │ is_start_slot_at_epoch —                                                 │ Faithful control flow with Lean data types.                                   │
│ is_start_slot_at_epoch                            │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md / get_ancestor_roots  │ get_ancestor_roots —                                                     │ Simplified: finite loop fuel or explicit state passing; branch order          │
│                                                   │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │ preserved.                                                                    │
│ phase0/fast-confirmation.md / get_slot_committee  │ get_slot_committee —                                                     │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_pulled_up_head_state —                                               │ Faithful control flow with Lean data types.                                   │
│ get_pulled_up_head_state                          │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_previous_balance_source —                                            │ Faithful control flow with Lean data types.                                   │
│ get_previous_balance_source                       │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_current_balance_source —                                             │ Faithful control flow with Lean data types.                                   │
│ get_current_balance_source                        │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_block_support_between_slots —                                        │ Faithful control flow with Lean data types.                                   │
│ get_block_support_between_slots                   │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ is_full_validator_set_covered —                                          │ Faithful control flow with Lean data types.                                   │
│ is_full_validator_set_covered                     │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ adjust_committee_weight_estimate_to_ensure_safety —                      │ Faithful control flow with Lean data types.                                   │
│ adjust_committee_weight_estimate_to_ensure_safety │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ estimate_committee_weight_between_slots —                                │ Faithful control flow with Lean data types.                                   │
│ estimate_committee_weight_between_slots           │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_equivocation_score —                                                 │ Faithful control flow with Lean data types.                                   │
│ get_equivocation_score                            │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ compute_adversarial_weight —                                             │ Faithful control flow with Lean data types.                                   │
│ compute_adversarial_weight                        │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_adversarial_weight —                                                 │ Faithful control flow with Lean data types.                                   │
│ get_adversarial_weight                            │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_support_discount —                                                   │ Faithful control flow with Lean data types.                                   │
│ get_support_discount                              │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ compute_safety_threshold —                                               │ Faithful control flow with Lean data types.                                   │
│ compute_safety_threshold                          │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md / is_one_confirmed    │ is_one_confirmed — FastConfirmationModel/Spec/FastConfirmation/LMD.lean  │ Faithful control flow with Lean data types.                                   │
│ phase0/fast-confirmation.md /                     │ is_confirmed_chain_safe —                                                │ Faithful control flow with Lean data types.                                   │
│ is_confirmed_chain_safe                           │ FastConfirmationModel/Spec/FastConfirmation/LMD.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ get_current_target_score —                                               │ Faithful control flow with Lean data types.                                   │
│ get_current_target_score                          │ FastConfirmationModel/Spec/FastConfirmation/FFG.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ compute_honest_ffg_support_for_current_target —                          │ Faithful control flow with Lean data types.                                   │
│ compute_honest_ffg_support_for_current_target     │ FastConfirmationModel/Spec/FastConfirmation/FFG.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ will_no_conflicting_checkpoint_be_justified —                            │ Faithful control flow with Lean data types.                                   │
│ will_no_conflicting_checkpoint_be_justified       │ FastConfirmationModel/Spec/FastConfirmation/FFG.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ will_current_target_be_justified —                                       │ Faithful control flow with Lean data types.                                   │
│ will_current_target_be_justified                  │ FastConfirmationModel/Spec/FastConfirmation/FFG.lean                     │                                                                               │
│ phase0/fast-confirmation.md /                     │ update_fast_confirmation_variables —                                     │ Faithful control flow with Lean data types.                                   │
│ update_fast_confirmation_variables                │ FastConfirmationModel/Spec/FastConfirmation/Rule.lean                    │                                                                               │
│ phase0/fast-confirmation.md /                     │ find_latest_confirmed_descendant —                                       │ Simplified: finite loop fuel or explicit state passing; branch order          │
│ find_latest_confirmed_descendant                  │ FastConfirmationModel/Spec/FastConfirmation/Rule.lean                    │ preserved.                                                                    │
│ phase0/fast-confirmation.md /                     │ get_latest_confirmed —                                                   │ Simplified: finite loop fuel or explicit state passing; branch order          │
│ get_latest_confirmed                              │ FastConfirmationModel/Spec/FastConfirmation/Rule.lean                    │ preserved.                                                                    │
│ phase0/fast-confirmation.md /                     │ on_fast_confirmation —                                                   │ Simplified: explicit state passing; the handler cannot reject.                │
│ on_fast_confirmation                              │ FastConfirmationModel/Spec/FastConfirmation/Rule.lean                    │                                                                               │
│ phase0/fork-choice.md / get_slots_since_genesis   │ get_slots_since_genesis — FastConfirmationModel/Spec/ForkChoice.lean     │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / get_current_slot          │ get_current_slot — FastConfirmationModel/Spec/ForkChoice.lean            │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / get_current_store_epoch   │ get_current_store_epoch — FastConfirmationModel/Spec/ForkChoice.lean     │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md /                           │ compute_slots_since_epoch_start —                                        │ Faithful control flow with Lean data types.                                   │
│ compute_slots_since_epoch_start                   │ FastConfirmationModel/Spec/ForkChoice.lean                               │                                                                               │
│ phase0/fork-choice.md /                           │ calculate_committee_fraction —                                           │ Faithful control flow with Lean data types.                                   │
│ calculate_committee_fraction                      │ FastConfirmationModel/Spec/ForkChoice.lean                               │                                                                               │
│ phase0/fork-choice.md / get_attestation_score     │ get_attestation_score — FastConfirmationModel/Spec/ForkChoice.lean       │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / compute_proposer_score    │ compute_proposer_score — FastConfirmationModel/Spec/ForkChoice.lean      │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / get_proposer_score        │ get_proposer_score — FastConfirmationModel/Spec/ForkChoice.lean          │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / get_voting_source         │ get_voting_source — FastConfirmationModel/Spec/ForkChoice.lean           │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / get_filtered_block_tree   │ get_filtered_block_tree — FastConfirmationModel/Spec/ForkChoice.lean     │ Simplified: finite loop fuel or explicit state passing; branch order          │
│                                                   │                                                                          │ preserved.                                                                    │
│ phase0/fork-choice.md / update_checkpoints        │ update_checkpoints — FastConfirmationModel/Spec/Handlers.lean            │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md /                           │ update_unrealized_checkpoints — FastConfirmationModel/Spec/Handlers.lean │ Faithful control flow with Lean data types.                                   │
│ update_unrealized_checkpoints                     │                                                                          │                                                                               │
│ phase0/fork-choice.md / seconds_to_milliseconds   │ seconds_to_milliseconds — FastConfirmationModel/Spec/ForkChoice.lean     │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md /                           │ get_slot_component_duration_ms —                                         │ Faithful control flow with Lean data types.                                   │
│ get_slot_component_duration_ms                    │ FastConfirmationModel/Spec/ForkChoice.lean                               │                                                                               │
│ phase0/fork-choice.md / compute_pulled_up_tip     │ compute_pulled_up_tip — FastConfirmationModel/Spec/Handlers.lean         │ Faithful control flow with Lean data types.                                   │
│ phase0/fork-choice.md / on_tick_per_slot          │ on_tick_per_slot — FastConfirmationModel/Spec/Handlers.lean              │ Faithful control flow with Lean data types. Python `Root()` (no boost) is     │
│                                                   │                                                                          │ Lean none.                                                                    │
│ phase0/fork-choice.md /                           │ validate_target_epoch_against_current_time —                             │ Faithful control flow with Lean data types.                                   │
│ validate_target_epoch_against_current_time        │ FastConfirmationModel/Spec/Handlers.lean                                 │                                                                               │
│ phase0/fork-choice.md /                           │ store_target_checkpoint_state — FastConfirmationModel/Spec/Handlers.lean │ Faithful control flow with Lean data types.                                   │
│ store_target_checkpoint_state                     │                                                                          │                                                                               │
│ phase0/fork-choice.md /                           │ compute_shuffling_lookahead_start_slot —                                 │ Faithful control flow with Lean data types.                                   │
│ compute_shuffling_lookahead_start_slot            │ FastConfirmationModel/Spec/Handlers.lean                                 │                                                                               │
│ phase0/fork-choice.md /                           │ compute_shuffling_dependent_slot —                                       │ Faithful control flow with Lean data types.                                   │
│ compute_shuffling_dependent_slot                  │ FastConfirmationModel/Spec/Handlers.lean                                 │                                                                               │
│ phase0/fork-choice.md / on_tick                   │ on_tick — FastConfirmationModel/Spec/Handlers.lean                       │ Simplified: finite loop fuel for the slot catch-up loop (`on_tick_aux`); the  │
│                                                   │                                                                          │ handler cannot reject.                                                        │
│ phase0/fork-choice.md / on_attestation            │ on_attestation — FastConfirmationModel/Spec/Handlers.lean                │ Invalid calls reject atomically; Python can keep a checkpoint cache write.    │
│ phase0/fork-choice.md / on_attester_slashing      │ on_attester_slashing — FastConfirmationModel/Spec/Handlers.lean          │ Simplified: explicit handler result; rejected calls discard writes.           │
│ phase0/fork-choice.md / filter_block_tree         │ filter_block_tree_aux — FastConfirmationModel/Spec/ForkChoice.lean       │ Simplified: finite loop fuel; branch order preserved. Worker of               │
│                                                   │                                                                          │ `get_filtered_block_tree`.                                                    │
│ phase0/validator.md / Attestation data            │ honest_attestation_data —                                                │ Simplified: Gloas index rule of gloas/validator.md; the target root is read   │
│                                                   │ FastConfirmationModel/Spec/Validator/Attesting.lean                      │ with `get_checkpoint_block`, equal to `get_block_root` on accepted votes.     │
│ phase0/validator.md / Construct attestation       │ honest_attestation — FastConfirmationModel/Spec/Validator/Attesting.lean │ Simplified: one signer; the indexed form keeps the validator index; the BLS   │
│                                                   │                                                                          │ signature is absorbed.                                                        │
│ phase0/beacon-chain.md / is_active_validator      │ is_active_validator —                                                    │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/Helpers.lean                      │                                                                               │
│ phase0/beacon-chain.md /                          │ is_slashable_attestation_data —                                          │ Faithful control flow with Lean data types.                                   │
│ is_slashable_attestation_data                     │ FastConfirmationModel/Spec/BeaconChain/Types.lean                        │                                                                               │
│ phase0/beacon-chain.md / compute_epoch_at_slot    │ compute_epoch_at_slot —                                                  │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/Helpers.lean                      │                                                                               │
│ phase0/beacon-chain.md /                          │ compute_start_slot_at_epoch —                                            │ Faithful control flow with Lean data types.                                   │
│ compute_start_slot_at_epoch                       │ FastConfirmationModel/Spec/BeaconChain/Helpers.lean                      │                                                                               │
│ phase0/beacon-chain.md / get_current_epoch        │ get_current_epoch — FastConfirmationModel/Spec/BeaconChain/Helpers.lean  │ Faithful control flow with Lean data types.                                   │
│ phase0/beacon-chain.md /                          │ get_active_validator_indices —                                           │ Faithful control flow with Lean data types.                                   │
│ get_active_validator_indices                      │ FastConfirmationModel/Spec/BeaconChain/Helpers.lean                      │                                                                               │
│ phase0/beacon-chain.md / get_total_balance        │ get_total_balance — FastConfirmationModel/Spec/BeaconChain/Helpers.lean  │ Faithful control flow with Lean data types.                                   │
│ phase0/beacon-chain.md / get_total_active_balance │ get_total_active_balance —                                               │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/Helpers.lean                      │                                                                               │
│ phase0/beacon-chain.md / state_transition         │ state_transition —                                                       │ Simplified: slots, block, then the opaque validity oracle. Signature and root │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ checks are delegated; out-of-scope blocks are rejected.                       │
│ phase0/beacon-chain.md / process_slots            │ process_slots —                                                          │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ gloas/beacon-chain.md / process_slot              │ process_slot —                                                           │ Simplified: writes the current root-ring cell and clears the next             │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ availability bit; state and header hashing delegated.                         │
│ gloas/beacon-chain.md / process_epoch             │ process_epoch —                                                          │ Simplified: all 17 steps in source order; 15 steps are identity frames (last  │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ row).                                                                         │
│ altair/beacon-chain.md /                          │ process_justification_and_finalization —                                 │ Faithful control flow with Lean data types.                                   │
│ process_justification_and_finalization            │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md /                          │ weigh_justification_and_finalization —                                   │ Faithful control flow with Lean data types.                                   │
│ weigh_justification_and_finalization              │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ altair/beacon-chain.md /                          │ process_participation_flag_updates —                                     │ Faithful control flow with Lean data types.                                   │
│ process_participation_flag_updates                │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ gloas/beacon-chain.md / process_block             │ process_block —                                                          │ Simplified: parent payload, header, bid, and operations; the oracle stands    │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ for the other steps.                                                          │
│ phase0/beacon-chain.md / process_block_header     │ process_block_header —                                                   │ Simplified: slot, parent, proposer range, and slashed checks; proposer        │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ selection and hashing delegated.                                              │
│ gloas/beacon-chain.md / process_operations        │ process_operations —                                                     │ Simplified: ordered attestation fold; a block with a slashing, an exit, or a  │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ deposit is rejected (fixed scope).                                            │
│ gloas/beacon-chain.md / process_attestation       │ process_attestation —                                                    │ Simplified: all guards and the flag union; reward and builder-payment writes  │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ erased.                                                                       │
│ gloas/beacon-chain.md /                           │ get_attestation_participation_flag_indices —                             │ Faithful control flow with Lean data types.                                   │
│ get_attestation_participation_flag_indices        │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ gloas/beacon-chain.md / is_attestation_same_slot  │ is_attestation_same_slot —                                               │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ electra/beacon-chain.md / get_committee_indices   │ get_committee_indices —                                                  │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ electra/beacon-chain.md / get_attesting_indices   │ get_attesting_indices —                                                  │ Faithful control flow; committees from the fixed schedule.                    │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / get_indexed_attestation  │ get_indexed_attestation —                                                │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ altair/beacon-chain.md /                          │ get_unslashed_participating_indices —                                    │ Faithful control flow with Lean data types.                                   │
│ get_unslashed_participating_indices               │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / get_total_balance        │ get_total_balance —                                                      │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / get_total_active_balance │ get_total_active_balance —                                               │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md /                          │ get_active_validator_indices —                                           │ Faithful control flow with Lean data types.                                   │
│ get_active_validator_indices                      │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / get_previous_epoch       │ get_previous_epoch —                                                     │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / get_block_root           │ get_block_root —                                                         │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / get_block_root_at_slot   │ get_block_root_at_slot —                                                 │ Faithful control flow; extra length and uint64 guards on the admitted domain. │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ altair/beacon-chain.md / add_flag                 │ add_flag —                                                               │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ altair/beacon-chain.md / has_flag                 │ has_flag —                                                               │ Faithful control flow with Lean data types.                                   │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ phase0/beacon-chain.md / integer_squareroot       │ integer_squareroot —                                                     │ Faithful: Nat.sqrt is the floor square root.                                  │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ gloas/beacon-chain.md /                           │ is_valid_indexed_attestation —                                           │ Simplified: structural checks; BLS verification is delegated to the oracle.   │
│ is_valid_indexed_attestation                      │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ gloas/beacon-chain.md /                           │ process_parent_execution_payload —                                       │ Simplified: commitment check, then apply; nonempty parent requests are        │
│ process_parent_execution_payload                  │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ rejected (fixed scope).                                                       │
│ gloas/beacon-chain.md /                           │ apply_parent_execution_payload —                                         │ Simplified: sets parent availability and the latest block hash; requests and  │
│ apply_parent_execution_payload                    │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ builder settlement erased.                                                    │
│ gloas/beacon-chain.md /                           │ process_execution_payload_bid —                                          │ Simplified: caches the bid block hash; other checks delegated; builder        │
│ process_execution_payload_bid                     │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │ payments erased.                                                              │
│ */beacon-chain.md / 15 epoch-step frames          │ process_inactivity_updates, process_rewards_and_penalties,               │ Identity frames: in scope only while no epoch step changes a retained         │
│                                                   │ process_registry_updates, process_slashings, process_eth1_data_reset,    │ validator record.                                                             │
│                                                   │ process_pending_deposits, process_pending_consolidations,                │                                                                               │
│                                                   │ process_builder_pending_payments, process_effective_balance_updates,     │                                                                               │
│                                                   │ process_slashings_reset, process_randao_mixes_reset,                     │                                                                               │
│                                                   │ process_historical_summaries_update, process_sync_committee_updates,     │                                                                               │
│                                                   │ process_proposer_lookahead, process_ptc_window —                         │                                                                               │
│                                                   │ FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean           │                                                                               │
│ Gloas fork-choice Store                           │ FastConfirmationModel/Spec/ForkChoice.lean                               │ Simplified: projected fields used by FCR.                                     │
│ Beacon-chain state and block types                │ FastConfirmationModel/Spec/BeaconChain/Types.lean                        │ Projected state and signed objects; ordered body FFG votes are retained.      │
│ FastConfirmationStore                             │ FastConfirmationModel/Spec/FastConfirmation/Store.lean                   │ Faithful state fields with Lean totalized maps.                               │
│ Execution schedule                                │ FastConfirmationModel/Execution/ScheduledPrefixes.lean                   │ Model idealisation: finite scheduled per-node events, no Python counterpart.  │
└───────────────────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────┘
```

For `on_attestation`, the Lean handler returns no store after failed indexed validation. The scheduled run keeps the pre-call store. Python can write `checkpoint_states` before the failing assert. Accepted evidence uses handler-successful transitions, so a rejected call supplies no accepted state or cache write in Lean. The effect of Python's surviving cache write on later valid calls is not established.

The public Gloas difference is in `compute_empty_slot_support_discount`. The helper
`get_parent_payload_support_between_slots` counts only matching-status or PENDING parent
votes. A vote on the opposite resolved payload branch stays in the competing weight. Other
translations use natural-number arithmetic, totalized map reads, `List` iteration, and
explicit loop fuel. See [modeling choices](MODELING_CHOICES.md). The conformance runner
compares projected source states. It does not prove every external contract.

The `BeaconBlock.attestations` list projects `BeaconBlockBody.attestations` from both the Phase0 and Gloas beacon-chain sections. Its order is the source order. `Execution.IncludedAttestationFidelity.in_carrier_body` states membership in the accepted carrier message. The validation origin follows `store_target_checkpoint_state` in Phase0 fork choice: a keyed target block state in an honest in-horizon store is advanced with `process_slots` only if its slot precedes the target epoch start. The prepared state is not required to be keyed.
