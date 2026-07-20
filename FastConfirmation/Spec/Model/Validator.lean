import FastConfirmation.Spec.Model.Handlers

/-!
# Spec / Model / Validator

Honest validator behavior for attesting, from `specs/phase0/validator.md`
("Attesting" / "Attestation data" / "Construct attestation"): the attestation
an honest validator assigned to a slot constructs from its own store at voting
time. Block proposal duties are not modelled (the FCR's safety guarantee does
not rely on honest proposals; proposer boost is handled adversarially).

The target root uses the store's ancestor walk (`get_checkpoint_block`) in
place of the state's block-root history lookup (`get_block_root`):
`validate_on_attestation` *asserts* exactly this equality, so the two coincide
on every attestation the fork choice accepts (design decision 15).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- validator.md "Attestation data": the `AttestationData` an honest validator
assigned to `slot` (committee `index`) constructs from its store at voting
time.

- `head_block` = "the result of running the fork choice during the assigned
  slot";
- `head_state` = "the state of `head_block` processed through any empty slots
  up to the assigned slot using `process_slots(state, slot)`" (guarded: the
  python `process_slots` asserts `state.slot < slot`);
- LMD GHOST vote `beacon_block_root = hash_tree_root(head_block)`;
- FFG vote `source = head_state.current_justified_checkpoint`,
  `target = Checkpoint(get_current_epoch(head_state), epoch_boundary_block_root)`. -/
def honest_attestation_data (store : Store Root) (slot : Slot)
    (index : CommitteeIndex) : AttestationData Root :=
  let head_block := get_head cfg store
  let head_state := store.block_states head_block.root
  let head_state :=
    if head_state.slot < slot then ext.process_slots head_state slot else head_state
  { slot := slot
    index := index
    beacon_block_root := head_block.root
    source := head_state.current_justified_checkpoint
    target :=
      Checkpoint.mk (get_current_epoch cfg head_state)
        (get_checkpoint_block cfg store head_block.root
          (get_current_epoch cfg head_state)) }

/-- validator.md "Construct attestation": the wire attestation of a single
honest validator — `aggregation_bits` a singleton on the validator's committee
position, i.e. (in the indexed projection, design §12)
`attesting_indices = [validator_index]`; the BLS signature is absorbed. -/
def honest_attestation (store : Store Root) (slot : Slot) (index : CommitteeIndex)
    (validator_index : ValidatorIndex) : Attestation Root :=
  { attesting_indices := [validator_index]
    data := honest_attestation_data cfg ext store slot index }

end FastConfirmation.Spec
