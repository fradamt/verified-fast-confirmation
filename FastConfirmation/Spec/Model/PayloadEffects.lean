module
public import FastConfirmation.Spec.Model.Handlers

@[expose] public section

/-!
# Payload handler preservation

The envelope and PTC handlers change only the three payload maps. The frame
relation below records every other field without an assumption about payload
validity or delivery. Block PTC notification preserves the same relation.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Remove the three fields that payload handlers can change. -/
def Store.withoutPayloadFields (store : Store Root) : Store Root :=
  { store with
    payloads := fun _ => none
    payload_timeliness_vote := fun _ => none
    payload_data_availability_vote := fun _ => none }

/-- Every non-payload field is equal in the two stores. -/
def PayloadFrame (old new : Store Root) : Prop :=
  new.withoutPayloadFields = old.withoutPayloadFields

namespace PayloadFrame

theorem refl (store : Store Root) : PayloadFrame store store := rfl

theorem trans {a b c : Store Root} (hab : PayloadFrame a b)
    (hbc : PayloadFrame b c) : PayloadFrame a c := Eq.trans hbc hab

theorem time {old new : Store Root} (h : PayloadFrame old new) :
    new.time = old.time :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.time h

theorem genesis_time {old new : Store Root} (h : PayloadFrame old new) :
    new.genesis_time = old.genesis_time :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.genesis_time h

theorem justified_checkpoint {old new : Store Root} (h : PayloadFrame old new) :
    new.justified_checkpoint = old.justified_checkpoint :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.justified_checkpoint h

theorem finalized_checkpoint {old new : Store Root} (h : PayloadFrame old new) :
    new.finalized_checkpoint = old.finalized_checkpoint :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.finalized_checkpoint h

theorem unrealized_justified_checkpoint {old new : Store Root} (h : PayloadFrame old new) :
    new.unrealized_justified_checkpoint = old.unrealized_justified_checkpoint :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.unrealized_justified_checkpoint h

theorem unrealized_finalized_checkpoint {old new : Store Root} (h : PayloadFrame old new) :
    new.unrealized_finalized_checkpoint = old.unrealized_finalized_checkpoint :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.unrealized_finalized_checkpoint h

theorem proposer_boost_root {old new : Store Root} (h : PayloadFrame old new) :
    new.proposer_boost_root = old.proposer_boost_root :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.proposer_boost_root h

theorem equivocating_indices {old new : Store Root} (h : PayloadFrame old new) :
    new.equivocating_indices = old.equivocating_indices :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.equivocating_indices h

theorem block_roots {old new : Store Root} (h : PayloadFrame old new) :
    new.block_roots = old.block_roots :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.block_roots h

theorem blocks {old new : Store Root} (h : PayloadFrame old new) :
    new.blocks = old.blocks :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.blocks h

theorem block_states {old new : Store Root} (h : PayloadFrame old new) :
    new.block_states = old.block_states :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.block_states h

theorem block_timeliness {old new : Store Root} (h : PayloadFrame old new) :
    new.block_timeliness = old.block_timeliness :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.block_timeliness h

theorem checkpoint_state_keys {old new : Store Root} (h : PayloadFrame old new) :
    new.checkpoint_state_keys = old.checkpoint_state_keys :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.checkpoint_state_keys h

theorem checkpoint_states {old new : Store Root} (h : PayloadFrame old new) :
    new.checkpoint_states = old.checkpoint_states :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.checkpoint_states h

theorem latest_messages {old new : Store Root} (h : PayloadFrame old new) :
    new.latest_messages = old.latest_messages :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.latest_messages h

theorem unrealized_justifications {old new : Store Root} (h : PayloadFrame old new) :
    new.unrealized_justifications = old.unrealized_justifications :=
  congrArg (a₁ := new.withoutPayloadFields) (a₂ := old.withoutPayloadFields)
    Store.unrealized_justifications h

end PayloadFrame

/-- A rejected accumulated computation remains rejected under the bind fold. -/
private theorem foldl_bind_none {α : Type*}
    (f : Store Root → α → Option (Store Root)) (l : List α) :
    l.foldl (fun (result : Option (Store Root)) a => result.bind fun store => f store a)
      none = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change l.foldl (fun (result : Option (Store Root)) a => result.bind fun store => f store a)
      none = none
    exact ih

/-- Successful fallible folds preserve a frame preserved by each step. -/
theorem payloadFrame_foldl {α : Type*} {f : Store Root → α → Option (Store Root)}
    (hf : ∀ store a store', f store a = some store' → PayloadFrame store store')
    (l : List α) (store : Store Root) {store' : Store Root}
    (h : l.foldl (fun (result : Option (Store Root)) a => result.bind fun s => f s a) (some store) =
      some store') : PayloadFrame store store' := by
  induction l generalizing store with
  | nil =>
    cases h
    exact PayloadFrame.refl _
  | cons a l ih =>
    cases hstep : f store a with
    | none =>
      simp only [List.foldl_cons, Option.bind_some, hstep, foldl_bind_none] at h
      cases h
    | some next =>
      have htail : l.foldl (fun (result : Option (Store Root)) a => result.bind fun s => f s a)
          (some next) = some store' := by
        simpa only [List.foldl_cons, Option.bind_some, hstep] using h
      exact (hf store a next hstep).trans (ih (store := next) htail)

variable [LinearOrder Root] (cfg : Config) (ext : Externals Root)

/-- PTC messages change only the two vote maps. -/
theorem on_payload_attestation_message_frame {store store' : Store Root}
    {message : PayloadAttestationMessage Root} {is_from_block : Bool}
    (h : on_payload_attestation_message cfg ext store message is_from_block =
      some store') : PayloadFrame store store' := by
  simp only [on_payload_attestation_message] at h
  split_ifs at h <;> try contradiction
  all_goals first
    | (cases h; rfl)
    | (split at h <;> (try split_ifs at h) <;> cases h <;> rfl)

/-- An accepted envelope changes only the payload map. -/
theorem on_execution_payload_envelope_frame {store store' : Store Root}
    {envelope : SignedExecutionPayloadEnvelope Root}
    {observation : EnvelopeObservation Root}
    (h : on_execution_payload_envelope ext store envelope observation = some store') :
    PayloadFrame store store' := by
  simp only [on_execution_payload_envelope] at h
  split_ifs at h <;> cases h <;> rfl

/-- Block PTC notification preserves all non-payload fields. -/
theorem notify_ptc_messages_frame [Inhabited Root] {store store' : Store Root}
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : notify_ptc_messages cfg ext store state attestations = some store') :
    PayloadFrame store store' := by
  simp only [notify_ptc_messages] at h
  split_ifs at h
  · cases h
    exact PayloadFrame.refl _
  · refine payloadFrame_foldl ?_ attestations store h
    intro s a t ha
    refine payloadFrame_foldl ?_ a.attesting_indices s ha
    intro s idx t hi
    exact on_payload_attestation_message_frame cfg ext hi

end FastConfirmation.Spec

end
