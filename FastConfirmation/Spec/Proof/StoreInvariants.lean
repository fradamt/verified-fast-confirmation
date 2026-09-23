module
public import FastConfirmation.Spec.Model.Execution
public import FastConfirmation.Spec.Model.PayloadEffects
public import FastConfirmation.Spec.Proof.ModelFacts

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Spec / Proof / StoreInvariants

Pure consequences of the handler definitions: the store-extension order `StoreLE`
(what grows monotonically along any handler application) and its preservation
by every handler, hence along every execution trajectory; plus the
field-projection simp lemmas for the record-update helpers that later layers
reuse.

No behavioral assumptions enter here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- The store-extension order: what any single handler application can only
grow. `StoreLE old new` tracks: the block set grows, `genesis_time` is
constant, the equivocation set grows, and latest messages are only ever
replaced by messages at the same or a later slot. -/
def StoreLE (old new : Store Root) : Prop :=
  old.block_roots ⊆ new.block_roots ∧
  old.genesis_time = new.genesis_time ∧
  old.equivocating_indices ⊆ new.equivocating_indices ∧
  ∀ i m, old.latest_messages i = some m →
    ∃ m', new.latest_messages i = some m' ∧ m.slot ≤ m'.slot

namespace StoreLE

theorem refl (s : Store Root) : StoreLE s s :=
  ⟨List.Subset.refl _, rfl, Finset.Subset.refl _, fun _ m h => ⟨m, h, le_rfl⟩⟩

theorem trans {a b c : Store Root} (hab : StoreLE a b) (hbc : StoreLE b c) :
    StoreLE a c := by
  obtain ⟨h1, h2, h3, h4⟩ := hab
  obtain ⟨g1, g2, g3, g4⟩ := hbc
  refine ⟨h1.trans g1, h2.trans g2, h3.trans g3, fun i m hm => ?_⟩
  obtain ⟨m', hm', hle⟩ := h4 i m hm
  obtain ⟨m'', hm'', hle'⟩ := g4 i m' hm'
  exact ⟨m'', hm'', hle.trans hle'⟩

/-- Slot-monotone latest messages also have monotone derived epochs. -/
theorem latest_message_epoch_mono (cfg : Config) {old new : Store Root}
    (h : StoreLE old new) (i : ValidatorIndex) (m : LatestMessage Root)
    (hm : old.latest_messages i = some m) :
    ∃ m', new.latest_messages i = some m' ∧
      get_latest_message_epoch cfg m ≤ get_latest_message_epoch cfg m' := by
  obtain ⟨m', hm', hslot⟩ := h.2.2.2 i m hm
  exact ⟨m', hm', Nat.div_le_div_right hslot⟩

end StoreLE

/-- `StoreLE` for a store update that leaves all four tracked fields equal. -/
private theorem storeLE_untouched {s t : Store Root}
    (h1 : s.block_roots = t.block_roots) (h2 : s.genesis_time = t.genesis_time)
    (h3 : s.equivocating_indices = t.equivocating_indices)
    (h4 : s.latest_messages = t.latest_messages) : StoreLE s t :=
  ⟨h1 ▸ List.Subset.refl _, h2, h3 ▸ Finset.Subset.refl _,
    fun _ m hm => ⟨m, h4 ▸ hm, le_rfl⟩⟩

/-- Folding a `StoreLE`-preserving step preserves `StoreLE`. -/
private theorem storeLE_foldl {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, StoreLE s (f s a)) (l : List α) (s : Store Root) :
    StoreLE s (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact StoreLE.refl s
  | cons a l ih => exact (hf s a).trans (ih (f s a))

/-! ## Field-projection lemmas for the record-update helpers -/

section FieldLemmas

variable (store : Store Root) (jc fc : Checkpoint Root)

@[simp] theorem update_checkpoints_block_roots :
    (update_checkpoints store jc fc).block_roots = store.block_roots := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_checkpoints_genesis_time :
    (update_checkpoints store jc fc).genesis_time = store.genesis_time := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_checkpoints_equivocating_indices :
    (update_checkpoints store jc fc).equivocating_indices =
      store.equivocating_indices := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_checkpoints_latest_messages :
    (update_checkpoints store jc fc).latest_messages = store.latest_messages := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_checkpoints_time :
    (update_checkpoints store jc fc).time = store.time := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_block_roots :
    (update_unrealized_checkpoints store jc fc).block_roots = store.block_roots := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_genesis_time :
    (update_unrealized_checkpoints store jc fc).genesis_time = store.genesis_time := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_equivocating_indices :
    (update_unrealized_checkpoints store jc fc).equivocating_indices =
      store.equivocating_indices := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_latest_messages :
    (update_unrealized_checkpoints store jc fc).latest_messages =
      store.latest_messages := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_time :
    (update_unrealized_checkpoints store jc fc).time = store.time := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

end FieldLemmas

/-- The tracked fields are untouched by `update_checkpoints`. -/
theorem update_checkpoints_storeLE (store : Store Root) (jc fc : Checkpoint Root) :
    StoreLE store (update_checkpoints store jc fc) :=
  storeLE_untouched (by simp) (by simp) (by simp) (by simp)

theorem update_unrealized_checkpoints_storeLE (store : Store Root)
    (jc fc : Checkpoint Root) :
    StoreLE store (update_unrealized_checkpoints store jc fc) :=
  storeLE_untouched (by simp) (by simp) (by simp) (by simp)

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
theorem compute_pulled_up_tip_storeLE (store : Store Root) (block_root : Root) :
    StoreLE store (compute_pulled_up_tip cfg ext store block_root) := by
  simp only [compute_pulled_up_tip]
  split_ifs
  · refine StoreLE.trans ?_ (update_checkpoints_storeLE _ _ _)
    refine StoreLE.trans ?_ (update_unrealized_checkpoints_storeLE _ _ _)
    exact storeLE_untouched rfl rfl rfl rfl
  · refine StoreLE.trans ?_ (update_unrealized_checkpoints_storeLE _ _ _)
    exact storeLE_untouched rfl rfl rfl rfl

omit [LinearOrder Root] in
theorem on_tick_per_slot_storeLE (store : Store Root) (time : ℕ) :
    StoreLE store (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact storeLE_untouched rfl rfl rfl rfl
      | · refine StoreLE.trans ?_ (update_checkpoints_storeLE _ _ _)
          exact storeLE_untouched rfl rfl rfl rfl

omit [LinearOrder Root] in
theorem on_tick_aux_storeLE (tick_slot fuel : ℕ) (store : Store Root) :
    StoreLE store (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel generalizing store with
  | zero => exact StoreLE.refl store
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · exact (on_tick_per_slot_storeLE cfg store _).trans (ih _)
    · exact StoreLE.refl store

omit [LinearOrder Root] in
theorem on_tick_storeLE (store : Store Root) (time : ℕ) :
    StoreLE store (on_tick cfg store time) := by
  simp only [on_tick]
  exact (on_tick_aux_storeLE cfg _ _ store).trans
    (on_tick_per_slot_storeLE cfg _ time)

omit [Inhabited Root] in
theorem store_target_checkpoint_state_storeLE (store : Store Root)
    (target : Checkpoint Root) :
    StoreLE store (store_target_checkpoint_state cfg ext store target) := by
  simp only [store_target_checkpoint_state]
  split_ifs <;> exact storeLE_untouched rfl rfl rfl rfl

omit [LinearOrder Root] [Inhabited Root] in
theorem update_latest_messages_storeLE (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    StoreLE store (update_latest_messages store attesting_indices attestation) := by
  simp only [update_latest_messages]
  refine storeLE_foldl (fun s i => ?_) _ store
  dsimp only
  rcases hmi : s.latest_messages i with _ | lm
  · split_ifs with h
    · refine ⟨List.Subset.refl _, rfl, Finset.Subset.refl _, fun j m hm => ?_⟩
      rcases eq_or_ne j i with rfl | hji
      · simp [hmi] at hm
      · exact ⟨m, by simpa [Function.update_apply, hji] using hm, le_rfl⟩
    · simp at h
  · split_ifs with h
    · refine ⟨List.Subset.refl _, rfl, Finset.Subset.refl _, fun j m hm => ?_⟩
      rcases eq_or_ne j i with rfl | hne
      · rw [hmi] at hm
        obtain rfl : lm = m := by injection hm
        have hlt : lm.slot < attestation.data.slot := by simpa using h
        exact ⟨⟨attestation.data.slot, attestation.data.beacon_block_root,
            decide (attestation.data.index = 1)⟩,
          by simp, le_of_lt hlt⟩
      · exact ⟨m, by simpa [Function.update_apply, hne] using hm, le_rfl⟩
    · exact StoreLE.refl _

omit [Inhabited Root] in
theorem on_attestation_storeLE {store store' : Store Root}
    {attestation : Attestation Root} {is_from_block : Bool}
    (h : on_attestation cfg ext store attestation is_from_block = some store') :
    StoreLE store store' := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  exact (store_target_checkpoint_state_storeLE cfg ext store _).trans
    (update_latest_messages_storeLE _ _ _)

omit [Inhabited Root] in
theorem on_attester_slashing_storeLE {store store' : Store Root}
    {attester_slashing : AttesterSlashing Root}
    (h : on_attester_slashing ext store attester_slashing = some store') :
    StoreLE store store' := by
  simp only [on_attester_slashing] at h
  split_ifs at h
  cases h
  exact ⟨List.Subset.refl _, rfl, Finset.subset_union_left,
    fun i m hm => ⟨m, hm, le_rfl⟩⟩

omit [Inhabited Root] in
theorem record_block_timeliness_storeLE (store : Store Root) (root : Root) :
    StoreLE store (record_block_timeliness cfg store root) := by
  simp only [record_block_timeliness]
  exact storeLE_untouched rfl rfl rfl rfl

theorem update_proposer_boost_root_storeLE (store : Store Root) (head root : Root) :
    StoreLE store (update_proposer_boost_root cfg store head root) := by
  simp only [update_proposer_boost_root]
  split_ifs
  · exact storeLE_untouched rfl rfl rfl rfl
  · exact StoreLE.refl _

/- Payload-only handlers leave the store-extension fields equal. -/
omit [LinearOrder Root] [Inhabited Root] in
theorem PayloadFrame.storeLE {store store' : Store Root}
    (h : PayloadFrame store store') : StoreLE store store' :=
  storeLE_untouched h.block_roots.symm h.genesis_time.symm
    h.equivocating_indices.symm h.latest_messages.symm

omit [Inhabited Root] in
theorem on_payload_attestation_message_storeLE {store store' : Store Root}
    {message : PayloadAttestationMessage Root} {is_from_block : Bool}
    (h : on_payload_attestation_message cfg ext store message is_from_block =
      some store') : StoreLE store store' :=
  (on_payload_attestation_message_frame cfg ext h).storeLE

omit [Inhabited Root] in
theorem on_execution_payload_envelope_storeLE {store store' : Store Root}
    {envelope : SignedExecutionPayloadEnvelope Root} {observation : EnvelopeObservation Root}
    (h : on_execution_payload_envelope ext store envelope observation = some store') :
    StoreLE store store' :=
  (on_execution_payload_envelope_frame ext h).storeLE

theorem notify_ptc_messages_storeLE {store store' : Store Root}
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : notify_ptc_messages cfg ext store state attestations = some store') :
    StoreLE store store' := (notify_ptc_messages_frame cfg ext h).storeLE

theorem on_block_storeLE {store store' : Store Root}
    {signed_block : SignedBeaconBlock Root}
    (h : on_block cfg ext store signed_block = some store') :
    StoreLE store store' := by
  by_cases hknown : signed_block.root ∈ store.block_roots
  · simp [on_block, hknown] at h
    cases h
    exact StoreLE.refl _
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h
    all_goals try contradiction
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
      cases hptc : notify_ptc_messages cfg ext added state signed_block.message.payload_attestations with
      | none => rw [hptc] at h; cases h
      | some after_ptc =>
        rw [hptc] at h
        cases h
        refine StoreLE.trans ?_ (compute_pulled_up_tip_storeLE cfg ext _ _)
        refine StoreLE.trans ?_ (update_checkpoints_storeLE _ _ _)
        refine StoreLE.trans ?_ (update_proposer_boost_root_storeLE cfg _ _ _)
        refine StoreLE.trans ?_ (record_block_timeliness_storeLE cfg _ _)
        refine StoreLE.trans ?_ (notify_ptc_messages_storeLE cfg ext hptc)
        exact ⟨List.subset_append_left _ _, rfl, Finset.Subset.refl _,
          fun i m hm => ⟨m, hm, le_rfl⟩⟩

theorem apply_event_storeLE {store store' : Store Root} {event : Event Root}
    (h : apply_event cfg ext store event = some store') :
    StoreLE store store' := by
  cases event with
  | block b => exact on_block_storeLE cfg ext h
  | attestation a ifb => exact on_attestation_storeLE cfg ext h
  | attester_slashing s => exact on_attester_slashing_storeLE ext h
  | execution_payload_envelope envelope observation =>
      exact on_execution_payload_envelope_storeLE ext h
  | payload_attestation_message message ifb =>
      exact on_payload_attestation_message_storeLE cfg ext h

/-- One step of the event fold extends the store. -/
theorem apply_event_getD_storeLE (store : Store Root) (event : Event Root) :
    StoreLE store ((apply_event cfg ext store event).getD store) := by
  cases h : apply_event cfg ext store event with
  | none => exact StoreLE.refl store
  | some s' => exact apply_event_storeLE cfg ext h

/-- Trajectories extend the store step by step. -/
theorem Execution.store_storeLE_succ (E : Execution Root) (v : ValidatorIndex)
    (n : ℕ) : StoreLE (E.store cfg ext v n) (E.store cfg ext v (n + 1)) := by
  change StoreLE (E.store cfg ext v n)
    ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
  exact (on_tick_storeLE cfg _ _).trans
    (storeLE_foldl (fun s e => apply_event_getD_storeLE cfg ext s e) _ _)

/-- Trajectories extend the store across any time span. -/
theorem Execution.store_storeLE (E : Execution Root) (v : ValidatorIndex)
    {n m : ℕ} (hnm : n ≤ m) :
    StoreLE (E.store cfg ext v n) (E.store cfg ext v m) := by
  induction m with
  | zero => cases Nat.le_zero.mp hnm; exact StoreLE.refl _
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (E.store_storeLE_succ cfg ext v m)
    · cases Nat.le_antisymm hnm hge; exact StoreLE.refl _

end FastConfirmation.Spec

end
