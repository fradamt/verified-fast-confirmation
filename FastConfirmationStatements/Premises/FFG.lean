module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-!
Defines Phase0 voting-source coherence at FFG epoch boundaries.
These premises constrain the abstract beacon-state functions.
-/

section

/-! ## Epoch-boundary source coherence -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- Phase0 laws for `current_justified_checkpoint` across epoch boundaries.

Python sources: `specs/phase0/beacon-chain.md:1769-1782` (`state_transition`),
`:1795-1803` (`process_slots`), `:1822-1833` (`process_epoch`), `:1893-1948`
(PJF and `weigh_justification_and_finalization`), and
`specs/altair/beacon-chain.md:728-733`. Only
`weigh_justification_and_finalization` writes the checkpoint.

* `process_slots_one_boundary`: when the target is in the next epoch, one
  epoch processing runs, at the last slot of the start epoch. Its PJF reads
  the same attestations, participation, registry, and justification bits as
  eager PJF on the start state. Thus the two results agree. This is the old
  equation, restricted to one boundary.
* `process_slots_same_target_epoch`: epoch processing runs only at epoch
  ends. Two targets in the same epoch cross the same epoch ends, so they
  produce the same checkpoint.
* `state_transition_process_slots`: `state_transition` is `process_slots` to
  the block slot followed by `process_block`, and `process_block` does not
  write the checkpoint.
* `process_slots_checkpoint_epoch`: if every state that slot processing
  passes through has total active balance above one and a half
  `EFFECTIVE_BALANCE_INCREMENT`, the checkpoint either stays unchanged or
  gets an epoch at most the start epoch. An early return keeps it. The first
  epoch processing justifies at most the start epoch. Later epoch processing
  sees no new attestations (`process_slots` includes no block). For an empty
  attestation set, `get_total_balance` (`:1518`) returns one increment, and
  the balance antecedent makes the two-thirds test fail. Thus later epoch
  processing can justify only the start epoch again. Each epoch processing
  runs on the state at the last slot of its epoch, which is one of the states
  in the antecedent. The antecedent reads each intermediate state, so it also
  covers balance changes from rewards, penalties, or registry updates across
  skipped epochs. The bound `3 * increment < 2 * total` is exact: a total
  above one increment but at most one and a half increments still lets an
  empty set pass. Without the antecedent the law is false: when the total
  active balance is at most one and a half increments, an epoch with no
  attestations passes the test.

* `process_slots_two_boundaries`: from a start epoch `E` of at least
  `GENESIS_EPOCH + 2`, slot processing that crosses two or more boundaries
  gives the eager PJF checkpoint, if the registry and the total active balance
  do not change and the balance bound of `process_slots_checkpoint_epoch`
  holds at every intermediate state. The first boundary is the eager PJF, as
  in `process_slots_one_boundary`. `process_participation_flag_updates`
  (`specs/altair/beacon-chain.md:824`) moves the epoch-`E` flags to the
  previous-epoch flags. Thus the second PJF weighs the same epoch-`E`
  participants (`get_unslashed_participating_indices`, `:397`) with the same
  effective balances against the same total. It justifies epoch `E` again if
  the first PJF did, and fails otherwise. Its current-epoch flags are empty,
  so the current-epoch test fails. Later boundaries see only empty flag sets,
  and the balance bound makes their tests fail.

There is no two-boundary equation without these antecedents. PJF returns
early in epochs 0 and 1, so an epoch-1 start can keep the old checkpoint
under eager PJF and justify epoch 1 at the end of epoch 2. If the registry
changes at the first boundary (for example, effective-balance updates in
`process_effective_balance_updates`, `specs/phase0/beacon-chain.md:2216`), the
second PJF weighs the start-epoch votes with other balances and can justify
the start epoch when eager PJF does not. The laws mention only state
functions. They do not mention execution ancestry or a safety conclusion. -/
structure Phase0BoundarySourceCoherence
    (cfg : Config) (ext : BeaconFunctionInterface Root) : Prop where
  process_slots_one_boundary :
    ∀ (st : BeaconState Root) (target : Slot),
      st.slot < target →
      compute_epoch_at_slot cfg target =
        compute_epoch_at_slot cfg st.slot + 1 →
      (ext.process_slots st target).current_justified_checkpoint =
        (ext.process_justification_and_finalization st).current_justified_checkpoint
  process_slots_same_target_epoch :
    ∀ (st : BeaconState Root) (target target' : Slot),
      compute_epoch_at_slot cfg st.slot <
        compute_epoch_at_slot cfg target →
      compute_epoch_at_slot cfg target =
        compute_epoch_at_slot cfg target' →
      (ext.process_slots st target).current_justified_checkpoint =
        (ext.process_slots st target').current_justified_checkpoint
  state_transition_process_slots :
    ∀ (pre : BeaconState Root) (sb : SignedBeaconBlock Root)
      (post : BeaconState Root),
      ext.state_transition pre sb = some post →
      compute_epoch_at_slot cfg pre.slot <
        compute_epoch_at_slot cfg sb.message.slot →
      post.current_justified_checkpoint =
        (ext.process_slots pre sb.message.slot).current_justified_checkpoint
  process_slots_checkpoint_epoch :
    ∀ (st : BeaconState Root) (target : Slot),
      compute_epoch_at_slot cfg st.slot <
        compute_epoch_at_slot cfg target →
      (∀ s : Slot, st.slot < s → s ≤ target →
        3 * cfg.effective_balance_increment <
          2 * get_total_active_balance cfg (ext.process_slots st s)) →
      (ext.process_slots st target).current_justified_checkpoint =
          st.current_justified_checkpoint ∨
        (ext.process_slots st target).current_justified_checkpoint.epoch ≤
          compute_epoch_at_slot cfg st.slot
  process_slots_two_boundaries :
    ∀ (st : BeaconState Root) (target : Slot),
      GENESIS_EPOCH + 2 ≤ compute_epoch_at_slot cfg st.slot →
      compute_epoch_at_slot cfg st.slot + 2 ≤ compute_epoch_at_slot cfg target →
      (∀ s : Slot, st.slot < s → s ≤ target →
        (ext.process_slots st s).validators = st.validators ∧
        get_total_active_balance cfg (ext.process_slots st s) =
          get_total_active_balance cfg st ∧
        3 * cfg.effective_balance_increment <
          2 * get_total_active_balance cfg (ext.process_slots st s)) →
      (ext.process_slots st target).current_justified_checkpoint =
        (ext.process_justification_and_finalization st).current_justified_checkpoint

end FastConfirmation.Spec

end

section

/-! ## Same-epoch source coherence -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : BeaconFunctionInterface Root}
/-- The narrow phase0 fact hidden by the two opaque state functions.

`process_slots` invokes epoch processing only when it crosses an epoch
boundary.  Likewise, the state transition's block-processing phase does not
alter `current_justified_checkpoint`; that field can change only in the
empty-slot/epoch processing preceding the block.  Consequently both
operations preserve the checkpoint when their input and target slots are in
the same epoch.

This record is intentionally independent of an `Execution` and of all FCR
selection/safety statements. -/
structure Phase0SourceCoherence (cfg : Config) (ext : BeaconFunctionInterface Root) : Prop where
  process_slots_current_justified :
    ∀ (st : BeaconState Root) (target : Slot),
      st.slot < target →
      compute_epoch_at_slot cfg st.slot = compute_epoch_at_slot cfg target →
      (ext.process_slots st target).current_justified_checkpoint =
        st.current_justified_checkpoint
  state_transition_current_justified :
    ∀ (pre : BeaconState Root) (sb : SignedBeaconBlock Root)
      (post : BeaconState Root),
      ext.state_transition pre sb = some post →
      compute_epoch_at_slot cfg pre.slot =
        compute_epoch_at_slot cfg sb.message.slot →
      post.current_justified_checkpoint =
        pre.current_justified_checkpoint

end FastConfirmation.Spec

end

end
