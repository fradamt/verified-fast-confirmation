module
public import FastConfirmationProofs.FFG.Concrete.BridgeStore
public import FastConfirmationProofs.Execution.Trajectory.ExecutionClock
public import FastConfirmationProofs.FFG.State.Phase0BoundarySource

@[expose] public section

/-! Proves that the state-valued queries of the handlers stay in the fixed
scope when the verification horizon is the scope end
(`verification_horizon = last_epoch + 1`). Every such query reads a committed
block state, and its target slot is at or before the current store slot:

* `on_block` asserts `get_current_slot(store) >= block.slot`
  (`on_block_slot_le_current`);
* `store_target_checkpoint_state`, called by `on_attestation`, targets the
  start of `target.epoch`, and `validate_on_attestation` asserts
  `target.epoch == compute_epoch_at_slot(data.slot)` and
  `get_current_slot(store) >= data.slot + 1`
  (`validate_on_attestation_target_epoch_le`);
* `get_pulled_up_head_state` targets the start of the current store epoch;
* the honest attester processes its head state to its assigned slot, which
  is the current slot of its store (`HonestBehavior.votes_head`).

At an in-horizon store the current epoch is below the horizon, hence at most
`last_epoch`. Then the bridge runs the concrete function on the committed
state, and no fallback value enters a handler result
(`slots_query_concrete`, `transition_in_scope`). -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

omit [LinearOrder Root] in
/-- An epoch below the horizon is in the fixed scope. -/
theorem epoch_le_last_of_lt_horizon {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1) {e : Epoch}
    (h : e < E.verification_horizon) : e ≤ B.setup.scope.last_epoch := by
  rw [hscope] at h
  exact Nat.lt_succ_iff.mp h

/-- `validate_on_attestation` bounds the target epoch by the current store
epoch, also for attestations from blocks. -/
theorem validate_on_attestation_target_epoch_le {cfg : Config} {store : Store Root}
    {a : Attestation Root} {fromBlock : Bool}
    (h : validate_on_attestation cfg store a fromBlock = true) :
    a.data.target.epoch ≤ get_current_store_epoch cfg store := by
  simp only [validate_on_attestation, Bool.and_eq_true] at h
  have hnow : get_current_slot cfg store ≥ a.data.slot + 1 := of_decide_eq_true h.2
  have htarget : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot :=
    of_decide_eq_true h.1.1.1.1.1.1.1.1.2
  rw [htarget]
  exact compute_epoch_at_slot_mono (Nat.le_of_succ_le hnow)

/-- A fresh successful `on_block` asserts that the block slot is not in the
future. -/
theorem on_block_slot_le_current [Inhabited Root] {cfg : Config}
    {ext : BeaconFunctionInterface Root}
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hfresh : sb.root ∉ store.block_roots) (h : on_block cfg ext store sb = some store') :
    sb.message.slot ≤ get_current_slot cfg store := by
  by_contra hlt
  simp [on_block, hfresh, hlt] at h

/-- **In-scope slot queries.** At a bridged store whose current epoch is below
the horizon, a slot query from a known block state to a target slot after the
state slot and in an epoch at most the current store epoch runs the concrete
`process_slots` on the committed state. -/
theorem slots_query_concrete (hB : B.Admissible) {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    {store : Store Root} (hs : B.BridgedStore store)
    (hnow : get_current_store_epoch B.setup.cfg store < E.verification_horizon)
    {r : Root} (hr : r ∈ store.block_roots) {t : Slot}
    (hlt : (store.block_states r).slot < t)
    (ht : compute_epoch_at_slot B.setup.cfg t ≤ get_current_store_epoch B.setup.cfg store) :
    ∃ cs next, B.committedState r = some cs ∧
      process_slots B.setup.cfg B.setup.preset cs t = .ok next ∧
      B.interface.process_slots (store.block_states r) t = B.project next := by
  obtain ⟨cs, -, -, hcs, hstate, -, -, -, hslots⟩ := B.known_reads hB hs hr
  have hin : compute_epoch_at_slot B.setup.cfg t ≤ B.setup.scope.last_epoch :=
    ht.trans (B.epoch_le_last_of_lt_horizon hscope hnow)
  have hlt' : cs.slot < t := by
    rw [hstate] at hlt
    exact hlt
  obtain ⟨next, hnext, hread⟩ := hslots t hlt' hin
  exact ⟨cs, next, hcs, hnext, hread⟩

/-- The checkpoint-state query of a valid attestation at an in-horizon
bridged store is concrete. -/
theorem checkpoint_query_concrete (hB : B.Admissible) {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    {store : Store Root} (hs : B.BridgedStore store)
    (hnow : get_current_store_epoch B.setup.cfg store < E.verification_horizon)
    {a : Attestation Root} {fromBlock : Bool}
    (hv : validate_on_attestation B.setup.cfg store a fromBlock = true)
    (hr : a.data.target.root ∈ store.block_roots)
    (hlt : (store.block_states a.data.target.root).slot <
      compute_start_slot_at_epoch B.setup.cfg a.data.target.epoch) :
    ∃ cs next, B.committedState a.data.target.root = some cs ∧
      process_slots B.setup.cfg B.setup.preset cs
        (compute_start_slot_at_epoch B.setup.cfg a.data.target.epoch) = .ok next ∧
      B.interface.process_slots (store.block_states a.data.target.root)
        (compute_start_slot_at_epoch B.setup.cfg a.data.target.epoch) = B.project next :=
  B.slots_query_concrete hB hscope hs hnow hr hlt
    (by rw [compute_epoch_at_start_slot]; exact validate_on_attestation_target_epoch_le hv)

/-- The pulled-up head state query at an in-horizon bridged store is
concrete. -/
theorem pulled_up_query_concrete (hB : B.Admissible) {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    {store : Store Root} (hs : B.BridgedStore store)
    (hnow : get_current_store_epoch B.setup.cfg store < E.verification_horizon)
    {r : Root} (hr : r ∈ store.block_roots)
    (hlt : (store.block_states r).slot <
      compute_start_slot_at_epoch B.setup.cfg (get_current_store_epoch B.setup.cfg store)) :
    ∃ cs next, B.committedState r = some cs ∧
      process_slots B.setup.cfg B.setup.preset cs
        (compute_start_slot_at_epoch B.setup.cfg (get_current_store_epoch B.setup.cfg store)) =
          .ok next ∧
      B.interface.process_slots (store.block_states r)
        (compute_start_slot_at_epoch B.setup.cfg (get_current_store_epoch B.setup.cfg store)) =
          B.project next :=
  B.slots_query_concrete hB hscope hs hnow hr hlt (by rw [compute_epoch_at_start_slot])

/-- The honest attester's head-state query at its assigned slot, which is the
current slot of its store, is concrete. -/
theorem attester_query_concrete (hB : B.Admissible) {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    {store : Store Root} (hs : B.BridgedStore store)
    (hnow : get_current_store_epoch B.setup.cfg store < E.verification_horizon)
    {r : Root} (hr : r ∈ store.block_roots) (hlt : (store.block_states r).slot <
      get_current_slot B.setup.cfg store) :
    ∃ cs next, B.committedState r = some cs ∧
      process_slots B.setup.cfg B.setup.preset cs (get_current_slot B.setup.cfg store) =
        .ok next ∧
      B.interface.process_slots (store.block_states r) (get_current_slot B.setup.cfg store) =
        B.project next :=
  B.slots_query_concrete hB hscope hs hnow hr hlt le_rfl

/-- **No scope rejection.** At a bridged store whose current epoch is below the
horizon, the bridge does not reject a block that `on_block` may process for
being out of scope: the concrete post-state of a block at or before the
current slot is in the fixed scope. -/
theorem transition_in_scope {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    {store : Store Root}
    (hnow : get_current_store_epoch B.setup.cfg store < E.verification_horizon)
    {cp post : FFGBeaconState Root} {wire : FFGWireBlock Root}
    (hst : state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle cp wire =
      .ok post)
    (hslot : wire.slot ≤ get_current_slot B.setup.cfg store) :
    compute_epoch_at_slot B.setup.cfg post.slot ≤ B.setup.scope.last_epoch := by
  rw [(state_transition_slot hst).1]
  exact (compute_epoch_at_slot_mono hslot).trans (B.epoch_le_last_of_lt_horizon hscope hnow)

/-- The current epoch of every store of an in-horizon second is below the
horizon. -/
theorem store_epoch_lt_horizon [Inhabited Root] {cfg : Config} {ext : BeaconFunctionInterface Root}
    {E : Execution Root} {v : ValidatorIndex} {m : ℕ}
    (hm : E.WithinHorizon cfg m) :
    get_current_store_epoch cfg (E.store cfg ext v m) < E.verification_horizon := by
  unfold get_current_store_epoch
  rw [E.store_current_slot cfg ext v m]
  exact hm.2.2

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
