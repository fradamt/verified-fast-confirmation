module
public import FastConfirmation.Spec.Model.Execution

@[expose] public section

/-!
# Local verified-payload persistence

An accepted envelope writes `some envelope` at one root. Every other handler
preserves the payload map. Thus a locally verified payload remains verified
through later events and through the same node's execution trajectory.

These are consequences of the executable handlers. They need no assumptions
about honest behavior, payload validity, or delivery to another node. The
result concerns presence in the verified-envelope map, not PTC votes or the
identity of an envelope that a later accepted envelope can replace.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Every payload verified in the old store is verified in the new store. -/
def PayloadLE (old new : Store Root) : Prop :=
  ∀ root, is_payload_verified old root = true →
    is_payload_verified new root = true

namespace PayloadLE

theorem refl (store : Store Root) : PayloadLE store store := fun _ h => h

theorem trans {a b c : Store Root} (hab : PayloadLE a b) (hbc : PayloadLE b c) :
    PayloadLE a c := fun root h => hbc root (hab root h)

theorem of_payloads_eq {old new : Store Root}
    (h : new.payloads = old.payloads) : PayloadLE old new := by
  intro root hverified
  simpa only [is_payload_verified, h] using hverified

end PayloadLE

/-- A pure fold preserves the payload map when each step does. -/
private theorem foldl_payloads {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ store a, (f store a).payloads = store.payloads)
    (l : List α) (store : Store Root) :
    (l.foldl f store).payloads = store.payloads := by
  induction l generalizing store with
  | nil => rfl
  | cons a l ih => exact (ih (f store a)).trans (hf store a)

/-- A rejected bind fold cannot produce a store. -/
private theorem foldl_bind_none {α : Type*}
    (f : Store Root → α → Option (Store Root)) (l : List α) :
    l.foldl (fun (result : Option (Store Root)) a => result.bind fun store => f store a)
      none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih

/-- A successful bind fold preserves the payload map when each step does. -/
private theorem foldl_option_payloads {α : Type*}
    {f : Store Root → α → Option (Store Root)}
    (hf : ∀ store a store', f store a = some store' →
      store'.payloads = store.payloads)
    (l : List α) (store : Store Root) {store' : Store Root}
    (h : l.foldl (fun (result : Option (Store Root)) a => result.bind fun s => f s a)
        (some store) =
      some store') : store'.payloads = store.payloads := by
  induction l generalizing store with
  | nil => cases h; rfl
  | cons a l ih =>
      cases hstep : f store a with
      | none =>
          simp only [List.foldl_cons, Option.bind_some, hstep, foldl_bind_none] at h
          cases h
      | some next =>
          have htail : l.foldl
              (fun (result : Option (Store Root)) a => result.bind fun s => f s a)
              (some next) = some store' := by
            simpa only [List.foldl_cons, Option.bind_some, hstep] using h
          exact (ih (store := next) htail).trans (hf store a next hstep)

/-- A pure fold composes local payload persistence. -/
private theorem payloadLE_foldl {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ store a, PayloadLE store (f store a))
    (l : List α) (store : Store Root) : PayloadLE store (l.foldl f store) := by
  induction l generalizing store with
  | nil => exact PayloadLE.refl _
  | cons a l ih => exact (hf store a).trans (ih (f store a))

@[simp] theorem update_checkpoints_payloads (store : Store Root)
    (justified finalized : Checkpoint Root) :
    (update_checkpoints store justified finalized).payloads = store.payloads := by
  simp only [update_checkpoints]
  split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_payloads (store : Store Root)
    (justified finalized : Checkpoint Root) :
    (update_unrealized_checkpoints store justified finalized).payloads = store.payloads := by
  simp only [update_unrealized_checkpoints]
  split_ifs <;> rfl

@[simp] theorem update_latest_messages_payloads (store : Store Root)
    (indices : List ValidatorIndex) (attestation : Attestation Root) :
    (update_latest_messages store indices attestation).payloads = store.payloads := by
  simp only [update_latest_messages]
  refine foldl_payloads (fun s i => ?_) _ store
  dsimp only
  rcases hmi : s.latest_messages i with _ | message <;> split_ifs <;> rfl

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

@[simp] theorem record_block_timeliness_payloads (store : Store Root) (root : Root) :
    (record_block_timeliness cfg store root).payloads = store.payloads := rfl

@[simp] theorem update_proposer_boost_root_payloads (store : Store Root)
    (head root : Root) :
    (update_proposer_boost_root cfg store head root).payloads = store.payloads := by
  simp only [update_proposer_boost_root]
  split_ifs <;> rfl

@[simp] theorem store_target_checkpoint_state_payloads (store : Store Root)
    (target : Checkpoint Root) :
    (store_target_checkpoint_state cfg ext store target).payloads = store.payloads := by
  simp only [store_target_checkpoint_state]
  split_ifs <;> rfl

@[simp] theorem compute_pulled_up_tip_payloads (store : Store Root) (root : Root) :
    (compute_pulled_up_tip cfg ext store root).payloads = store.payloads := by
  simp only [compute_pulled_up_tip]
  split_ifs
  · rw [update_checkpoints_payloads, update_unrealized_checkpoints_payloads] <;> rfl
  · rw [update_unrealized_checkpoints_payloads] <;> rfl

@[simp] theorem on_tick_per_slot_payloads (store : Store Root) (time : ℕ) :
    (on_tick_per_slot cfg store time).payloads = store.payloads := by
  simp only [on_tick_per_slot]
  split_ifs <;> first
    | rfl
    | exact update_checkpoints_payloads _ _ _

@[simp] theorem on_tick_aux_payloads (tick_slot fuel : ℕ) (store : Store Root) :
    (on_tick_aux cfg tick_slot fuel store).payloads = store.payloads := by
  induction fuel generalizing store with
  | zero => rfl
  | succ fuel ih =>
      rw [on_tick_aux]
      split_ifs
      · exact (ih _).trans (on_tick_per_slot_payloads cfg store _)
      · rfl

@[simp] theorem on_tick_payloads (store : Store Root) (time : ℕ) :
    (on_tick cfg store time).payloads = store.payloads := by
  simp only [on_tick, on_tick_per_slot_payloads, on_tick_aux_payloads]

/-- PTC messages preserve the envelope map, including stale-slot no-ops. -/
theorem on_payload_attestation_message_payloads {store store' : Store Root}
    {message : PayloadAttestationMessage Root} {is_from_block : Bool}
    (h : on_payload_attestation_message cfg ext store message is_from_block =
      some store') : store'.payloads = store.payloads := by
  simp only [on_payload_attestation_message] at h
  split_ifs at h <;> try contradiction
  all_goals first
    | (cases h; rfl)
    | (split at h <;> (try split_ifs at h) <;> cases h <;> rfl)

/-- Both levels of block PTC notification preserve the envelope map. -/
theorem notify_ptc_messages_payloads {store store' : Store Root}
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : notify_ptc_messages cfg ext store state attestations = some store') :
    store'.payloads = store.payloads := by
  simp only [notify_ptc_messages] at h
  split_ifs at h
  · cases h; rfl
  · refine foldl_option_payloads ?_ attestations store h
    intro s a t ha
    refine foldl_option_payloads ?_ a.attesting_indices s ha
    intro s index t hi
    exact on_payload_attestation_message_payloads cfg ext hi

theorem on_attestation_payloads {store store' : Store Root}
    {attestation : Attestation Root} {is_from_block : Bool}
    (h : on_attestation cfg ext store attestation is_from_block = some store') :
    store'.payloads = store.payloads := by
  simp only [on_attestation] at h
  split_ifs at h <;> try contradiction
  cases h
  rw [update_latest_messages_payloads, store_target_checkpoint_state_payloads]

theorem on_attester_slashing_payloads {store store' : Store Root}
    {slashing : AttesterSlashing Root}
    (h : on_attester_slashing ext store slashing = some store') :
    store'.payloads = store.payloads := by
  simp only [on_attester_slashing] at h
  split_ifs at h <;> cases h <;> rfl

/-- A fresh block initializes PTC entries but does not remove envelopes. -/
theorem on_block_payloads {store store' : Store Root}
    {signed_block : SignedBeaconBlock Root}
    (h : on_block cfg ext store signed_block = some store') :
    store'.payloads = store.payloads := by
  by_cases hknown : signed_block.root ∈ store.block_roots
  · simp only [on_block, if_pos hknown] at h
    cases h
    rfl
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h <;> try contradiction
    cases hst : ext.state_transition
        (store.block_states signed_block.message.parent_root) signed_block with
    | none => rw [hst] at h; cases h
    | some state =>
      rw [hst] at h
      let added : Store Root :=
        { store with
          block_roots := store.block_roots ++ [signed_block.root]
          blocks := Function.update store.blocks signed_block.root signed_block.message
          block_states := Function.update store.block_states signed_block.root state
          payload_timeliness_vote := Function.update store.payload_timeliness_vote
            signed_block.root (some (List.replicate cfg.ptc_size none))
          payload_data_availability_vote := Function.update store.payload_data_availability_vote
            signed_block.root (some (List.replicate cfg.ptc_size none)) }
      change (match notify_ptc_messages cfg ext added state signed_block.message.payload_attestations with
        | none => none
        | some notified => some (compute_pulled_up_tip cfg ext
            (update_checkpoints
              (update_proposer_boost_root cfg
                (record_block_timeliness cfg notified signed_block.root)
                (get_head cfg store).root signed_block.root)
              state.current_justified_checkpoint state.finalized_checkpoint)
            signed_block.root)) = some store' at h
      cases hn : notify_ptc_messages cfg ext added state signed_block.message.payload_attestations with
      | none => rw [hn] at h; cases h
      | some notified =>
        rw [hn] at h
        cases h
        rw [compute_pulled_up_tip_payloads, update_checkpoints_payloads,
          update_proposer_boost_root_payloads, record_block_timeliness_payloads,
          notify_ptc_messages_payloads cfg ext hn] <;> rfl

/-- The FULL-parent guard precedes state transition and insertion. Freshness
excludes the successful duplicate-root no-op, which does not run that guard. -/
theorem on_block_fresh_full_parent_verified {store store' : Store Root}
    {signed_block : SignedBeaconBlock Root}
    (hfresh : signed_block.root ∉ store.block_roots)
    (hfull : is_parent_node_full store signed_block.message = true)
    (h : on_block cfg ext store signed_block = some store') :
    is_payload_verified store signed_block.message.parent_root = true := by
  cases hpayload : is_payload_verified store signed_block.message.parent_root with
  | true => rfl
  | false =>
      have hrejected : on_block cfg ext store signed_block = none := by
        simp [on_block, hfresh, hfull, hpayload]
      rw [hrejected] at h
      cases h

/-- The verified FULL-parent payload remains present after block processing. -/
theorem on_block_fresh_full_parent_verified_post {store store' : Store Root}
    {signed_block : SignedBeaconBlock Root}
    (hfresh : signed_block.root ∉ store.block_roots)
    (hfull : is_parent_node_full store signed_block.message = true)
    (h : on_block cfg ext store signed_block = some store') :
    is_payload_verified store' signed_block.message.parent_root = true :=
  (PayloadLE.of_payloads_eq (on_block_payloads cfg ext h))
    signed_block.message.parent_root
    (on_block_fresh_full_parent_verified cfg ext hfresh hfull h)

/-- An accepted envelope can replace one envelope, but cannot make a root absent. -/
theorem on_execution_payload_envelope_payloadLE {store store' : Store Root}
    {envelope : SignedExecutionPayloadEnvelope Root} {observation : EnvelopeObservation Root}
    (h : on_execution_payload_envelope ext store envelope observation = some store') :
    PayloadLE store store' := by
  simp only [on_execution_payload_envelope] at h
  split_ifs at h <;> try contradiction
  cases h
  intro root hverified
  by_cases hroot : root = envelope.message.beacon_block_root
  · subst root
    simp [is_payload_verified]
  · simpa [is_payload_verified, Function.update_apply, hroot] using hverified

/-- Every successful event preserves locally verified payloads. -/
theorem apply_event_payloadLE {store store' : Store Root} {event : Event Root}
    (h : apply_event cfg ext store event = some store') : PayloadLE store store' := by
  cases event with
  | block signed_block =>
      exact PayloadLE.of_payloads_eq (on_block_payloads cfg ext h)
  | attestation attestation is_from_block =>
      exact PayloadLE.of_payloads_eq (on_attestation_payloads cfg ext h)
  | attester_slashing slashing =>
      exact PayloadLE.of_payloads_eq (on_attester_slashing_payloads ext h)
  | execution_payload_envelope envelope observation =>
      exact on_execution_payload_envelope_payloadLE ext h
  | payload_attestation_message message is_from_block =>
      exact PayloadLE.of_payloads_eq (on_payload_attestation_message_payloads cfg ext h)

/-- Rejected events return the old store and also preserve verified payloads. -/
theorem apply_event_getD_payloadLE (store : Store Root) (event : Event Root) :
    PayloadLE store ((apply_event cfg ext store event).getD store) := by
  cases h : apply_event cfg ext store event with
  | none => exact PayloadLE.refl _
  | some store' => exact apply_event_payloadLE cfg ext h

/-- One execution second preserves locally verified payloads. -/
theorem Execution.store_payloadLE_succ (E : Execution Root)
    (validator : ValidatorIndex) (n : ℕ) :
    PayloadLE (E.store cfg ext validator n) (E.store cfg ext validator (n + 1)) := by
  change PayloadLE (E.store cfg ext validator n)
    ((E.schedule validator (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext validator n) (E.time_at (n + 1))))
  exact (PayloadLE.of_payloads_eq (on_tick_payloads cfg _ _)).trans
    (payloadLE_foldl (fun store event => apply_event_getD_payloadLE cfg ext store event) _ _)

/-- Local verified-payload presence is monotone across any execution interval. -/
theorem Execution.store_payloadLE (E : Execution Root) (validator : ValidatorIndex)
    {n m : ℕ} (hnm : n ≤ m) :
    PayloadLE (E.store cfg ext validator n) (E.store cfg ext validator m) := by
  induction m with
  | zero => cases Nat.le_zero.mp hnm; exact PayloadLE.refl _
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans
          (E.store_payloadLE_succ cfg ext validator m)
      · cases Nat.le_antisymm hnm hge
        exact PayloadLE.refl _

/-- Pointwise form of local payload persistence for later head-choice proofs. -/
theorem Execution.is_payload_verified_mono (E : Execution Root)
    (validator : ValidatorIndex) {n m : ℕ} (hnm : n ≤ m) {root : Root}
    (h : is_payload_verified (E.store cfg ext validator n) root = true) :
    is_payload_verified (E.store cfg ext validator m) root = true :=
  E.store_payloadLE cfg ext validator hnm root h

end FastConfirmation.Spec

end
