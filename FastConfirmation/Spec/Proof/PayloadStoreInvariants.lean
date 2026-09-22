module
public import FastConfirmation.Spec.Proof.StoreInvariants

@[expose] public section

/-!
# Payload map domains

Every known block has two PTC vote lists of the configured length. Unknown
blocks have no vote entries. Stored envelopes name their own map key, and that
key is a known block. Initialization and all handlers preserve these facts.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- A PTC map has exactly the block domain and the configured list length. -/
def VoteMapWellFormed (cfg : Config) (roots : List Root)
    (votes : Root → Option (List (Option Bool))) : Prop :=
  ∀ root, match votes root with
    | none => root ∉ roots
    | some values => root ∈ roots ∧ values.length = cfg.ptc_size

/-- Payload map coherence, with no payload delivery premise. -/
def PayloadMapsWellFormed (cfg : Config) (store : Store Root) : Prop :=
  (∀ root envelope, store.payloads root = some envelope →
    root ∈ store.block_roots ∧ envelope.beacon_block_root = root) ∧
  VoteMapWellFormed cfg store.block_roots store.payload_timeliness_vote ∧
  VoteMapWellFormed cfg store.block_roots store.payload_data_availability_vote

namespace VoteMapWellFormed

variable {cfg : Config} {roots : List Root}
    {votes : Root → Option (List (Option Bool))}

theorem get (h : VoteMapWellFormed cfg roots votes) {root : Root}
    (hknown : root ∈ roots) :
    ∃ values, votes root = some values ∧ values.length = cfg.ptc_size := by
  have hr := h root
  cases hv : votes root with
  | none => simp only [hv] at hr; exact (hr hknown).elim
  | some values =>
    exact ⟨values, rfl, (show root ∈ roots ∧ values.length = cfg.ptc_size by
      simpa only [hv] using hr).2⟩

theorem update [DecidableEq Root] (h : VoteMapWellFormed cfg roots votes)
    {root : Root} {values : List (Option Bool)} (hknown : root ∈ roots)
    (hlen : values.length = cfg.ptc_size) :
    VoteMapWellFormed cfg roots (Function.update votes root (some values)) := by
  intro r
  by_cases hr : r = root
  · subst r
    simpa only [Function.update_self] using And.intro hknown hlen
  · simpa only [Function.update_of_ne hr] using h r

theorem insert [DecidableEq Root] (h : VoteMapWellFormed cfg roots votes)
    (root : Root) : VoteMapWellFormed cfg (roots ++ [root])
      (Function.update votes root (some (List.replicate cfg.ptc_size none))) := by
  intro r
  by_cases hr : r = root
  · subst r
    simp [Function.update_apply]
  · simpa only [Function.update_of_ne hr, List.mem_append, List.mem_singleton,
      hr, or_false] using h r

end VoteMapWellFormed

namespace PayloadMapsWellFormed

variable {cfg : Config} {store : Store Root}

theorem update_votes [DecidableEq Root] (h : PayloadMapsWellFormed cfg store)
    {root : Root} {timeliness availability : List (Option Bool)}
    (hknown : root ∈ store.block_roots)
    (htime : timeliness.length = cfg.ptc_size)
    (hdata : availability.length = cfg.ptc_size) :
    PayloadMapsWellFormed cfg
      { store with
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          root (some timeliness)
        payload_data_availability_vote :=
          Function.update store.payload_data_availability_vote root (some availability) } :=
  ⟨h.1, h.2.1.update hknown htime, h.2.2.update hknown hdata⟩

theorem insert_block [DecidableEq Root] (h : PayloadMapsWellFormed cfg store)
    (root : Root) (block : BeaconBlock Root) (state : BeaconState Root) :
    PayloadMapsWellFormed cfg
      { store with
        block_roots := store.block_roots ++ [root]
        blocks := Function.update store.blocks root block
        block_states := Function.update store.block_states root state
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote :=
          Function.update store.payload_data_availability_vote
            root (some (List.replicate cfg.ptc_size none)) } := by
  refine ⟨?_, h.2.1.insert root, h.2.2.insert root⟩
  intro r envelope he
  obtain ⟨hknown, hroot⟩ := h.1 r envelope he
  exact ⟨List.subset_append_left _ _ hknown, hroot⟩

theorem insert_envelope [DecidableEq Root] (h : PayloadMapsWellFormed cfg store)
    (envelope : ExecutionPayloadEnvelope Root)
    (hknown : envelope.beacon_block_root ∈ store.block_roots) :
    PayloadMapsWellFormed cfg
      { store with
        payloads := Function.update store.payloads
          envelope.beacon_block_root (some envelope) } := by
  refine ⟨?_, h.2⟩
  intro r e he
  by_cases hr : r = envelope.beacon_block_root
  · subst r
    simp only [Function.update_self, Option.some.injEq] at he
    cases he
    exact ⟨hknown, rfl⟩
  · exact h.1 r e (by simpa only [Function.update_of_ne hr] using he)

end PayloadMapsWellFormed

/-- Replacing list entries preserves list length, including repeated positions. -/
private theorem length_foldl_set (positions : List Nat) (votes : List (Option Bool))
    (value : Bool) :
    (positions.foldl (fun values i => values.set i (some value)) votes).length =
      votes.length := by
  induction positions generalizing votes with
  | nil => rfl
  | cons i positions ih =>
    simpa only [List.foldl_cons, ih, List.length_set]

variable [LinearOrder Root] (cfg : Config) (ext : Externals Root)

theorem get_forkchoice_store_payloadMaps [Inhabited Root]
    (state : BeaconState Root) (block : SignedBeaconBlock Root) :
    PayloadMapsWellFormed cfg (get_forkchoice_store cfg state block) := by
  refine ⟨?_, ?_, ?_⟩
  · intro root envelope h
    cases h
  all_goals
    intro root
    by_cases hr : root = block.root
    · subst root
      simp [get_forkchoice_store, Function.update_apply]
    · simp [get_forkchoice_store, Function.update_apply, hr]

theorem on_payload_attestation_message_payloadMaps {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store)
    {message : PayloadAttestationMessage Root} {is_from_block : Bool}
    (h : on_payload_attestation_message cfg ext store message is_from_block =
      some store') : PayloadMapsWellFormed cfg store' := by
  by_cases hknown : message.data.beacon_block_root ∈ store.block_roots
  · obtain ⟨timeliness, ht, htl⟩ := hWF.2.1.get hknown
    obtain ⟨availability, ha, hal⟩ := hWF.2.2.get hknown
    simp only [on_payload_attestation_message, ht, ha] at h
    split_ifs at h <;> try contradiction
    all_goals cases h
    all_goals first
      | exact hWF
      | exact hWF.update_votes hknown
          ((length_foldl_set _ _ _).trans htl)
          ((length_foldl_set _ _ _).trans hal)
  · simp [on_payload_attestation_message, hknown] at h

theorem on_execution_payload_envelope_payloadMaps {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store)
    {envelope : SignedExecutionPayloadEnvelope Root} {observation : EnvelopeObservation Root}
    (h : on_execution_payload_envelope ext store envelope observation = some store') :
    PayloadMapsWellFormed cfg store' := by
  by_cases hknown : envelope.message.beacon_block_root ∈ store.block_roots
  · simp only [on_execution_payload_envelope] at h
    split_ifs at h <;> try contradiction
    cases h
    exact hWF.insert_envelope envelope.message hknown
  · simp [on_execution_payload_envelope, hknown] at h

/-- The invariant passes through a fallible fold when every accepted step preserves it. -/
private theorem payloadMaps_foldl {α : Type*}
    {f : Store Root → α → Option (Store Root)}
    (hf : ∀ store a store', PayloadMapsWellFormed cfg store →
      f store a = some store' → PayloadMapsWellFormed cfg store')
    (l : List α) {store store' : Store Root} (hWF : PayloadMapsWellFormed cfg store)
    (h : l.foldl (fun (result : Option (Store Root)) a => result.bind fun s => f s a) (some store) =
      some store') : PayloadMapsWellFormed cfg store' := by
  have hnone : ∀ l : List α,
      l.foldl (fun (result : Option (Store Root)) a => result.bind fun s => f s a) none = none := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => exact ih
  induction l generalizing store with
  | nil => cases h; exact hWF
  | cons a l ih =>
    cases hstep : f store a with
    | none =>
      simp only [List.foldl_cons, Option.bind_some, hstep, hnone] at h
      cases h
    | some next =>
      have htail : l.foldl (fun (result : Option (Store Root)) a => result.bind fun s => f s a)
          (some next) = some store' := by
        simpa only [List.foldl_cons, Option.bind_some, hstep] using h
      exact ih (store := next) (hf store a next hWF hstep) htail

theorem notify_ptc_messages_payloadMaps [Inhabited Root] {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store)
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : notify_ptc_messages cfg ext store state attestations = some store') :
    PayloadMapsWellFormed cfg store' := by
  simp only [notify_ptc_messages] at h
  split_ifs at h
  · cases h
    exact hWF
  · refine payloadMaps_foldl cfg ?_ attestations hWF h
    intro s a t hs ha
    refine payloadMaps_foldl cfg ?_ a.attesting_indices hs ha
    intro s idx t hs hi
    exact on_payload_attestation_message_payloadMaps cfg ext hs hi

theorem update_checkpoints_payloadMaps {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (jc fc : Checkpoint Root) :
    PayloadMapsWellFormed cfg (update_checkpoints store jc fc) := by
  simp only [update_checkpoints]
  split_ifs <;> exact hWF

theorem update_unrealized_checkpoints_payloadMaps {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (jc fc : Checkpoint Root) :
    PayloadMapsWellFormed cfg (update_unrealized_checkpoints store jc fc) := by
  simp only [update_unrealized_checkpoints]
  split_ifs <;> exact hWF

theorem compute_pulled_up_tip_payloadMaps {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (root : Root) :
    PayloadMapsWellFormed cfg (compute_pulled_up_tip cfg ext store root) := by
  simp only [compute_pulled_up_tip]
  split_ifs
  · apply update_checkpoints_payloadMaps
    apply update_unrealized_checkpoints_payloadMaps
    exact hWF
  · apply update_unrealized_checkpoints_payloadMaps
    exact hWF

theorem record_block_timeliness_payloadMaps {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (root : Root) :
    PayloadMapsWellFormed cfg (record_block_timeliness cfg store root) := hWF

theorem update_proposer_boost_root_payloadMaps [Inhabited Root] {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (head root : Root) :
    PayloadMapsWellFormed cfg (update_proposer_boost_root cfg store head root) := by
  simp only [update_proposer_boost_root]
  split_ifs <;> exact hWF

theorem on_block_payloadMaps [Inhabited Root] {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) {block : SignedBeaconBlock Root}
    (h : on_block cfg ext store block = some store') :
    PayloadMapsWellFormed cfg store' := by
  by_cases hknown : block.root ∈ store.block_roots
  · simp [on_block, hknown] at h
    cases h
    exact hWF
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h
    all_goals try contradiction
    cases hst : ext.state_transition
        (store.block_states block.message.parent_root) block with
    | none => rw [hst] at h; cases h
    | some state =>
      rw [hst] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i after_ptc hptc
        cases h
        apply compute_pulled_up_tip_payloadMaps
        apply update_checkpoints_payloadMaps
        apply update_proposer_boost_root_payloadMaps
        apply record_block_timeliness_payloadMaps
        exact notify_ptc_messages_payloadMaps cfg ext
          (hWF.insert_block block.root block.message state) hptc

theorem store_target_checkpoint_state_payloadMaps {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (target : Checkpoint Root) :
    PayloadMapsWellFormed cfg (store_target_checkpoint_state cfg ext store target) := by
  simp only [store_target_checkpoint_state]
  split_ifs <;> exact hWF

private theorem payloadMaps_pure_foldl {α : Type*}
    {f : Store Root → α → Store Root}
    (hf : ∀ store a, PayloadMapsWellFormed cfg store → PayloadMapsWellFormed cfg (f store a))
    (l : List α) {store : Store Root} (hWF : PayloadMapsWellFormed cfg store) :
    PayloadMapsWellFormed cfg (l.foldl f store) := by
  induction l generalizing store with
  | nil => exact hWF
  | cons a l ih => exact ih (store := f store a) (hf store a hWF)

theorem update_latest_messages_payloadMaps {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (indices : List ValidatorIndex)
    (attestation : Attestation Root) :
    PayloadMapsWellFormed cfg (update_latest_messages store indices attestation) := by
  simp only [update_latest_messages]
  refine payloadMaps_pure_foldl cfg ?_ _ hWF
  intro s i hs
  dsimp only
  cases hmessage : s.latest_messages i <;> split_ifs <;> exact hs

theorem on_attestation_payloadMaps {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) {attestation : Attestation Root}
    {is_from_block : Bool}
    (h : on_attestation cfg ext store attestation is_from_block = some store') :
    PayloadMapsWellFormed cfg store' := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  exact update_latest_messages_payloadMaps cfg
    (store_target_checkpoint_state_payloadMaps cfg ext hWF _) _ _

theorem on_attester_slashing_payloadMaps {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) {slashing : AttesterSlashing Root}
    (h : on_attester_slashing ext store slashing = some store') :
    PayloadMapsWellFormed cfg store' := by
  simp only [on_attester_slashing] at h
  split_ifs at h
  cases h
  exact hWF

theorem on_tick_per_slot_payloadMaps [Inhabited Root] {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (time : Nat) :
    PayloadMapsWellFormed cfg (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;> first
    | exact hWF
    | (apply update_checkpoints_payloadMaps; exact hWF)

theorem on_tick_aux_payloadMaps [Inhabited Root] (tick_slot fuel : Nat)
    {store : Store Root} (hWF : PayloadMapsWellFormed cfg store) :
    PayloadMapsWellFormed cfg (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel generalizing store with
  | zero => exact hWF
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · exact ih (store := on_tick_per_slot cfg store
        (store.genesis_time + (get_current_slot cfg store + 1) * cfg.slot_duration_ms / 1000))
        (on_tick_per_slot_payloadMaps cfg hWF _)
    · exact hWF

theorem on_tick_payloadMaps [Inhabited Root] {store : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) (time : Nat) :
    PayloadMapsWellFormed cfg (on_tick cfg store time) :=
  on_tick_per_slot_payloadMaps cfg (on_tick_aux_payloadMaps cfg _ _ hWF) time

theorem apply_event_payloadMaps [Inhabited Root] {store store' : Store Root}
    (hWF : PayloadMapsWellFormed cfg store) {event : Event Root}
    (h : apply_event cfg ext store event = some store') :
    PayloadMapsWellFormed cfg store' := by
  cases event with
  | block block => exact on_block_payloadMaps cfg ext hWF h
  | attestation attestation is_from_block => exact on_attestation_payloadMaps cfg ext hWF h
  | attester_slashing slashing => exact on_attester_slashing_payloadMaps cfg ext hWF h
  | execution_payload_envelope envelope observation =>
    exact on_execution_payload_envelope_payloadMaps cfg ext hWF h
  | payload_attestation_message message is_from_block =>
    exact on_payload_attestation_message_payloadMaps cfg ext hWF h

/-- Payload map coherence follows from coherent initialization along every schedule. -/
theorem Execution.store_payloadMaps [Inhabited Root] (E : Execution Root)
    (hgenesis : PayloadMapsWellFormed cfg E.genesis_store)
    (validator : ValidatorIndex) (n : Nat) :
    PayloadMapsWellFormed cfg (E.store cfg ext validator n) := by
  induction n with
  | zero => exact hgenesis
  | succ n ih =>
    change PayloadMapsWellFormed cfg
      ((E.schedule validator (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext validator n) (E.time_at (n + 1))))
    refine payloadMaps_pure_foldl cfg ?_ _ (on_tick_payloadMaps cfg ih _)
    intro store event hWF
    cases hevent : apply_event cfg ext store event with
    | none => exact hWF
    | some store' => exact apply_event_payloadMaps cfg ext hWF hevent

end FastConfirmation.Spec

end
