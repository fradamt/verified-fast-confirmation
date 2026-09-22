module
public import FastConfirmation.Spec.Proof.StoreInvariants

@[expose] public section

/-!
# Spec / Proof / Trajectory

Layer 0, clock coherence: along every execution trajectory the store clock
tracks `time_at` (`on_tick` writes its argument; no event handler touches
`time`), `genesis_time` is constant, and therefore
`get_current_slot (E.store v n) = E.slot_at n` — the store's notion of the
current slot and the execution's wall clock agree at every node and second.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## `time` is untouched by the event handlers -/

section TimeLemmas

@[simp] theorem compute_pulled_up_tip_time [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (ext : Externals Root) (store : Store Root) (block_root : Root) :
    (compute_pulled_up_tip cfg ext store block_root).time = store.time := by
  simp only [compute_pulled_up_tip]
  split_ifs <;> simp

@[simp] theorem store_target_checkpoint_state_time [LinearOrder Root]
    (cfg : Config) (ext : Externals Root) (store : Store Root)
    (target : Checkpoint Root) :
    (store_target_checkpoint_state cfg ext store target).time = store.time := by
  simp only [store_target_checkpoint_state]
  split_ifs <;> rfl

/-- Folding a `time`-preserving step preserves `time`. -/
private theorem foldl_time {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, (f s a).time = s.time) (l : List α) (s : Store Root) :
    (l.foldl f s).time = s.time := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hf]

@[simp] theorem update_latest_messages_time (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    (update_latest_messages store attesting_indices attestation).time =
      store.time := by
  simp only [update_latest_messages]
  refine foldl_time (fun s i => ?_) _ _
  dsimp only
  rcases hmi : s.latest_messages i with _ | lm <;> split_ifs <;> rfl

@[simp] theorem record_block_timeliness_time [LinearOrder Root]
    (cfg : Config) (store : Store Root) (root : Root) :
    (record_block_timeliness cfg store root).time = store.time := rfl

@[simp] theorem update_proposer_boost_root_time [LinearOrder Root] [Inhabited Root]
    (cfg : Config) (store : Store Root) (head root : Root) :
    (update_proposer_boost_root cfg store head root).time = store.time := by
  simp only [update_proposer_boost_root]
  split_ifs <;> rfl

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

theorem on_block_time {store store' : Store Root} {b : SignedBeaconBlock Root}
    (h : on_block cfg ext store b = some store') : store'.time = store.time := by
  by_cases hknown : b.root ∈ store.block_roots
  · simp [on_block, hknown] at h
    cases h
    rfl
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h
    all_goals try contradiction
    cases hst : ext.state_transition
        (store.block_states b.message.parent_root) b with
    | none => rw [hst] at h; cases h
    | some state =>
      rw [hst] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i after_ptc hptc
        cases h
        simpa using (notify_ptc_messages_frame cfg ext hptc).time

omit [Inhabited Root] in
theorem on_attestation_time {store store' : Store Root} {a : Attestation Root}
    {ifb : Bool} (h : on_attestation cfg ext store a ifb = some store') :
    store'.time = store.time := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  simp

omit [Inhabited Root] in
theorem on_attester_slashing_time {store store' : Store Root}
    {sl : AttesterSlashing Root}
    (h : on_attester_slashing ext store sl = some store') :
    store'.time = store.time := by
  simp only [on_attester_slashing] at h
  split_ifs at h
  cases h
  rfl

omit [Inhabited Root] in
theorem on_payload_attestation_message_time {store store' : Store Root}
    {message : PayloadAttestationMessage Root} {is_from_block : Bool}
    (h : on_payload_attestation_message cfg ext store message is_from_block =
      some store') : store'.time = store.time :=
  (on_payload_attestation_message_frame cfg ext h).time

omit [Inhabited Root] in
theorem on_execution_payload_envelope_time {store store' : Store Root}
    {envelope : SignedExecutionPayloadEnvelope Root} {observation : EnvelopeObservation Root}
    (h : on_execution_payload_envelope ext store envelope observation = some store') :
    store'.time = store.time := (on_execution_payload_envelope_frame ext h).time

theorem notify_ptc_messages_time {store store' : Store Root}
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : notify_ptc_messages cfg ext store state attestations = some store') :
    store'.time = store.time := (notify_ptc_messages_frame cfg ext h).time

theorem apply_event_time {store store' : Store Root} {e : Event Root}
    (h : apply_event cfg ext store e = some store') : store'.time = store.time := by
  cases e with
  | block b => exact on_block_time cfg ext h
  | attestation a ifb => exact on_attestation_time cfg ext h
  | attester_slashing s => exact on_attester_slashing_time ext h
  | execution_payload_envelope envelope observation =>
      exact on_execution_payload_envelope_time ext h
  | payload_attestation_message message ifb =>
      exact on_payload_attestation_message_time cfg ext h

/-! ## `on_tick` writes its argument -/

omit [LinearOrder Root] in
theorem on_tick_per_slot_time (store : Store Root) (time : ℕ) :
    (on_tick_per_slot cfg store time).time = time := by
  simp only [on_tick_per_slot]
  split_ifs <;> simp

omit [LinearOrder Root] in
theorem on_tick_time (store : Store Root) (time : ℕ) :
    (on_tick cfg store time).time = time := by
  simp only [on_tick]
  exact on_tick_per_slot_time cfg _ time

/-! ## Trajectory clock coherence -/

/-- The store clock tracks the execution wall clock. -/
theorem Execution.store_time (E : Execution Root) (v : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext v n).time = E.time_at n := by
  cases n with
  | zero => rfl
  | succ n =>
    change ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1)))).time = _
    rw [foldl_time (fun s e => ?_) _ _, on_tick_time]
    cases h : apply_event cfg ext s e with
    | none => rfl
    | some s' => simpa using apply_event_time cfg ext h

/-- `genesis_time` is constant along trajectories. -/
theorem Execution.store_genesis_time (E : Execution Root) (v : ValidatorIndex)
    (n : ℕ) :
    (E.store cfg ext v n).genesis_time = E.genesis_store.genesis_time :=
  (E.store_storeLE cfg ext v (Nat.zero_le n)).2.1.symm

/-- The store's current slot agrees with the execution wall clock's slot at
every node and second. -/
theorem Execution.store_current_slot (E : Execution Root) (v : ValidatorIndex)
    (n : ℕ) :
    get_current_slot cfg (E.store cfg ext v n) = E.slot_at cfg n := by
  simp only [get_current_slot, get_slots_since_genesis, Execution.slot_at,
    E.store_time cfg ext v n, E.store_genesis_time cfg ext v n]

end TimeLemmas

end FastConfirmation.Spec

end
