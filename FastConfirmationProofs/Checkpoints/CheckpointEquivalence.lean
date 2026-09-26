module
public import FastConfirmationProofs.Checkpoints.CheckpointMarginInputs
public import FastConfirmationProofs.Execution.Delivery.Delivery
public import FastConfirmationModel.Execution.PayloadFrame

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / Identities

Proves reflexivity and transitivity for checkpoint agreement across stores.

This module contains `SameCkpt`, `refl`, `trans` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section A — the store-epoch trajectory invariant

The justified and unrealized-justified checkpoint epochs never sit in a future
epoch. Both are tracked together (`CkptEpochLe`): `on_tick`'s epoch-boundary
pull-up raises the justified checkpoint to the store's own *unrealized* justified
checkpoint, so the invariant on the justified epoch is not self-contained — the
unrealized epoch bound is the load-bearing companion.

The tracking mirrors `Delivery.BlocksSlotLe`: a fixed slot bound `SL`, both
checkpoint epochs `≤ compute_epoch_at_slot SL`, carried through `on_tick` + the
event fold at each second and re-anchored at the wall-clock slot `slot_at n`. -/

/-- Two stores agree on both checkpoints the invariant tracks (justified and
unrealized-justified). The `SameBlocks` analog for the checkpoint fields: most
handler helpers leave both untouched, so the invariant rides across them. -/
def SameCkpt (s t : Store Root) : Prop :=
  s.justified_checkpoint = t.justified_checkpoint ∧
  s.unrealized_justified_checkpoint = t.unrealized_justified_checkpoint

namespace SameCkpt

theorem refl (s : Store Root) : SameCkpt s s := ⟨rfl, rfl⟩

theorem trans {a b c : Store Root} (hab : SameCkpt a b) (hbc : SameCkpt b c) :
    SameCkpt a c := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

/-- Folding a `SameCkpt`-preserving step preserves `SameCkpt`. -/
theorem foldl {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, SameCkpt s (f s a)) (l : List α) (s : Store Root) :
    SameCkpt s (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact SameCkpt.refl s
  | cons a l ih => exact (hf s a).trans (ih (f s a))

end SameCkpt

/-- Payload and PTC writes preserve both tracked checkpoints. -/
theorem PayloadFrame.sameCkpt {store store' : Store Root}
    (h : PayloadFrame store store') : SameCkpt store store' :=
  ⟨h.justified_checkpoint.symm, h.unrealized_justified_checkpoint.symm⟩

/-- The store-epoch bound tracked along a trajectory: both checkpoints the
invariant follows have epoch at most `compute_epoch_at_slot SL`. -/
def CkptEpochLe (cfg : Config) (SL : Slot) (s : Store Root) : Prop :=
  s.justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg SL ∧
  s.unrealized_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg SL

/-- `CkptEpochLe` rides across a `SameCkpt` step. -/
theorem CkptEpochLe.of_sameCkpt {cfg : Config} {SL : Slot} {s t : Store Root}
    (h : SameCkpt s t) (hs : CkptEpochLe cfg SL s) : CkptEpochLe cfg SL t := by
  obtain ⟨hj, hu⟩ := h
  exact ⟨hj ▸ hs.1, hu ▸ hs.2⟩

/-- `CkptEpochLe` weakens to a larger slot bound (`compute_epoch_at_slot` monotone). -/
theorem CkptEpochLe.mono {cfg : Config} {SL SL' : Slot} {s : Store Root}
    (hle : SL ≤ SL') (hs : CkptEpochLe cfg SL s) : CkptEpochLe cfg SL' s := by
  have hmono : compute_epoch_at_slot cfg SL ≤ compute_epoch_at_slot cfg SL' :=
    Nat.div_le_div_right hle
  exact ⟨le_trans hs.1 hmono, le_trans hs.2 hmono⟩

/-! ### Field lemmas — `update_checkpoints` / `update_unrealized_checkpoints` (generic) -/

theorem update_checkpoints_unrealized_justified (store : Store Root) (jc fc : Checkpoint Root) :
    (update_checkpoints store jc fc).unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
  simp only [update_checkpoints]; split_ifs <;> rfl

theorem update_unrealized_checkpoints_justified (store : Store Root) (jc fc : Checkpoint Root) :
    (update_unrealized_checkpoints store jc fc).justified_checkpoint =
      store.justified_checkpoint := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

theorem update_latest_messages_sameCkpt (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    SameCkpt store (update_latest_messages store attesting_indices attestation) := by
  simp only [update_latest_messages]
  refine SameCkpt.foldl (fun s i => ?_) _ store
  dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

/-- `update_checkpoints` keeps both tracked epochs `≤ CE(SL)` when the adopted
justified checkpoint is itself within the bound: the justified epoch becomes the
larger of the two (both bounded), the unrealized epoch is untouched. -/
theorem update_checkpoints_CkptEpochLe (cfg : Config) (SL : Slot) (store : Store Root)
    (jc fc : Checkpoint Root) (hjc : jc.epoch ≤ compute_epoch_at_slot cfg SL)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (update_checkpoints store jc fc) := by
  refine ⟨?_, ?_⟩
  · simp only [update_checkpoints]
    split_ifs <;> first | exact hjc | exact h.1
  · rw [update_checkpoints_unrealized_justified]; exact h.2

/-- `update_unrealized_checkpoints` keeps both tracked epochs `≤ CE(SL)` when the
adopted unrealized-justified checkpoint is within the bound: the unrealized epoch
becomes the larger of the two (both bounded), the justified epoch is untouched. -/
theorem update_unrealized_checkpoints_CkptEpochLe (cfg : Config) (SL : Slot)
    (store : Store Root) (ujc ufc : Checkpoint Root)
    (hujc : ujc.epoch ≤ compute_epoch_at_slot cfg SL) (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (update_unrealized_checkpoints store ujc ufc) := by
  refine ⟨?_, ?_⟩
  · rw [update_unrealized_checkpoints_justified]; exact h.1
  · simp only [update_unrealized_checkpoints]
    split_ifs <;> first | exact hujc | exact h.2

/-! ### Field lemmas — the transparent helpers leave both checkpoints untouched -/

variable [LinearOrder Root] [Inhabited Root]

omit [Inhabited Root] in
theorem record_block_timeliness_sameCkpt (cfg : Config) (store : Store Root) (root : Root) :
    SameCkpt store (record_block_timeliness cfg store root) := by
  simp only [record_block_timeliness]; exact ⟨rfl, rfl⟩

theorem update_proposer_boost_root_sameCkpt (cfg : Config) (store : Store Root)
    (head root : Root) : SameCkpt store (update_proposer_boost_root cfg store head root) := by
  simp only [update_proposer_boost_root]; split_ifs <;> exact ⟨rfl, rfl⟩

omit [Inhabited Root] in
theorem store_target_checkpoint_state_sameCkpt (cfg : Config) (ext : BeaconFunctionInterface Root)
    (store : Store Root) (target : Checkpoint Root) :
    SameCkpt store (store_target_checkpoint_state cfg ext store target) := by
  simp only [store_target_checkpoint_state]; split_ifs <;> exact ⟨rfl, rfl⟩

/-! ### Epoch bound for pulled-up justification

The store-epoch invariant is preserved by every handler using
`BeaconExternalsPremises.state_transition_checkpoint_epoch` — **except**
`compute_pulled_up_tip`, whose `update_checkpoints`/`update_unrealized_checkpoints`
adopt `process_justification_and_finalization(block_state).current_justified_checkpoint`,
whose epoch requires a separate bound. `PjfCheckpointEpoch` is the
companion of `state_transition_checkpoint_epoch`: epoch processing justifies no
future epoch (the real `process_justification_and_finalization` only ever
justifies the current or previous epoch of the state it runs on). It is supplied
by `BeaconExternalsPremises.pjf_checkpoint_epoch`, definitionally the same `Prop`.
Both laws hold only for a state whose checkpoints are not in a future epoch
(`CheckpointEpochsSane`). The store invariant `KeyedStatesSane` gives this
antecedent for every keyed block state; the anchor state is its base case. -/

/-- Epoch processing justifies no future epoch: for a state whose justified
checkpoint is not in a future epoch, `pjf`'s current-justified checkpoint has
epoch at most the state's own epoch. The companion of
`BeaconExternalsPremises.state_transition_checkpoint_epoch`; supplied by the
field `BeaconExternalsPremises.pjf_checkpoint_epoch` (definitionally identical). -/
def PjfCheckpointEpoch (cfg : Config) (ext : BeaconFunctionInterface Root) : Prop :=
  ∀ st : BeaconState Root,
    st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot →
    (ext.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg st.slot

/-- A successful state transition from a state whose checkpoints are not in a
future epoch keeps both checkpoints at most the block epoch. Supplied by the
field `BeaconExternalsPremises.state_transition_checkpoint_epoch`
(definitionally identical). -/
def StateTransitionCheckpointEpoch (cfg : Config) (ext : BeaconFunctionInterface Root) :
    Prop :=
  ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
    st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot →
    st.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot →
    ext.state_transition st b = some st' →
      st'.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot ∧
      st'.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot

/-- A state's justified and finalized checkpoints are not in a future epoch of
the state. -/
def CheckpointEpochsSane (cfg : Config) (st : BeaconState Root) : Prop :=
  st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot ∧
  st.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot

/-- Every keyed block state of the store satisfies `CheckpointEpochsSane`. -/
def KeyedStatesSane (cfg : Config) (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots, CheckpointEpochsSane cfg (store.block_states r)

omit [LinearOrder Root] [Inhabited Root] in
/-- `KeyedStatesSane` reads only the block-identity fields. -/
theorem KeyedStatesSane.of_sameBlocks {cfg : Config} {s t : Store Root}
    (h : SameBlocks s t) (hs : KeyedStatesSane cfg s) : KeyedStatesSane cfg t := by
  intro r hr
  rw [← h.2.2]
  exact hs r (by rw [h.1]; exact hr)

omit [Inhabited Root] in
/-- A successful transition from a sane pre-state gives a sane post-state. -/
theorem CheckpointEpochsSane.of_state_transition {cfg : Config}
    {ext : BeaconFunctionInterface Root}
    (hst_ckpt : StateTransitionCheckpointEpoch cfg ext)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    {st st' : BeaconState Root} {b : SignedBeaconBlock Root}
    (hpre : CheckpointEpochsSane cfg st) (h : ext.state_transition st b = some st') :
    CheckpointEpochsSane cfg st' := by
  have hpost := hst_ckpt st b st' hpre.1 hpre.2 h
  unfold CheckpointEpochsSane
  rw [hst_slot st b st' h]
  exact hpost

/-! ### `compute_pulled_up_tip` preserves the store-epoch bound -/

omit [Inhabited Root] in
/-- `compute_pulled_up_tip` keeps both tracked epochs `≤ CE(SL)` when the pulled-up
state's justified checkpoint is within the bound (`hpjf_bound`, supplied by
`PjfCheckpointEpoch` + the block-slot bound at the call site). The
unrealized-justifications write is `SameCkpt`; the `update_unrealized_checkpoints`
and guarded `update_checkpoints` both adopt the pulled-up state's justified
checkpoint, bounded by `hpjf_bound`. -/
theorem compute_pulled_up_tip_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root) (SL : Slot)
    (store : Store Root) (block_root : Root)
    (hpjf_bound :
      (ext.process_justification_and_finalization
        (store.block_states block_root)).current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg SL)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (compute_pulled_up_tip cfg ext store block_root) := by
  simp only [compute_pulled_up_tip]
  split_ifs with hlt
  · refine update_checkpoints_CkptEpochLe cfg SL _ _ _ hpjf_bound ?_
    refine update_unrealized_checkpoints_CkptEpochLe cfg SL _ _ _ hpjf_bound ?_
    exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h
  · refine update_unrealized_checkpoints_CkptEpochLe cfg SL _ _ _ hpjf_bound ?_
    exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h

/-! ### The event handlers preserve the store-epoch bound -/

omit [Inhabited Root] in
/-- `on_attestation` preserves the bound: it only writes `checkpoint_states` /
`latest_messages`, both `SameCkpt`. -/
theorem on_attestation_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root) (SL : Slot)
    {store store' : Store Root} {a : Attestation Root} {ifb : Bool}
    (h : CkptEpochLe cfg SL store) (hh : on_attestation cfg ext store a ifb = some store') :
    CkptEpochLe cfg SL store' := by
  simp only [on_attestation] at hh
  split_ifs at hh
  cases hh
  exact CkptEpochLe.of_sameCkpt (update_latest_messages_sameCkpt _ _ _)
    (CkptEpochLe.of_sameCkpt (store_target_checkpoint_state_sameCkpt cfg ext store _) h)

omit [Inhabited Root] in
/-- `on_attester_slashing` preserves the bound: it only grows
`equivocating_indices`, `SameCkpt`. -/
theorem on_attester_slashing_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root) (SL : Slot)
    {store store' : Store Root} {asl : AttesterSlashing Root}
    (h : CkptEpochLe cfg SL store)
    (hh : on_attester_slashing ext store asl = some store') :
    CkptEpochLe cfg SL store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h

omit [Inhabited Root] in
theorem on_payload_attestation_message_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root)
    (SL : Slot) {store store' : Store Root} {message : PayloadAttestationMessage Root}
    {is_from_block : Bool} (h : CkptEpochLe cfg SL store)
    (hh : on_payload_attestation_message cfg ext store message is_from_block = some store') :
    CkptEpochLe cfg SL store' :=
  CkptEpochLe.of_sameCkpt (on_payload_attestation_message_frame cfg ext hh).sameCkpt h

omit [Inhabited Root] in
theorem on_execution_payload_envelope_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root)
    (SL : Slot) {store store' : Store Root} {envelope : SignedExecutionPayloadEnvelope Root}
    {observation : EnvelopeObservation Root} (h : CkptEpochLe cfg SL store)
    (hh : on_execution_payload_envelope ext store envelope observation = some store') :
    CkptEpochLe cfg SL store' :=
  CkptEpochLe.of_sameCkpt (on_execution_payload_envelope_frame ext hh).sameCkpt h

/-- `on_block` preserves the store-epoch bound. The parent state is keyed, so
it is sane (`KeyedStatesSane`). The block's own justified checkpoint (from
`state_transition`) is bounded by the block epoch, which is at most `SL` by the
not-future gate; the pulled-up tip's justified checkpoint is bounded by
`PjfCheckpointEpoch` at the block's post-state slot. -/
theorem on_block_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root) (SL : Slot)
    (hst_ckpt : StateTransitionCheckpointEpoch cfg ext)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hpjf : PjfCheckpointEpoch cfg ext)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hcur : get_current_slot cfg store ≤ SL) (h : CkptEpochLe cfg SL store)
    (hsane : KeyedStatesSane cfg store)
    (hh : on_block cfg ext store sb = some store') :
    CkptEpochLe cfg SL store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · have hge : sb.message.slot ≤ get_current_slot cfg store := by
      by_contra hfuture
      simp [on_block, hknown, hfuture] at hh
    have hparent : sb.message.parent_root ∈ store.block_roots := by
      by_contra hp
      simp [on_block, hknown, hp] at hh
    simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      dsimp only at hh
      split at hh
      · cases hh
      · rename_i after_ptc hptc
        cases hh
        have hframe := notify_ptc_messages_frame cfg ext hptc
        have hblkSL : compute_epoch_at_slot cfg sb.message.slot ≤ compute_epoch_at_slot cfg SL :=
          Nat.div_le_div_right (le_trans hge hcur)
        have hpost := CheckpointEpochsSane.of_state_transition hst_ckpt hst_slot
          (hsane _ hparent) hst
        have hcjc : state.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg SL :=
          le_trans ((hst_ckpt _ _ _ (hsane _ hparent).1 (hsane _ hparent).2 hst).1) hblkSL
        refine compute_pulled_up_tip_CkptEpochLe cfg ext SL _ sb.root ?_ ?_
        · rw [← (update_checkpoints_sameBlocks _ _ _).2.2,
              ← (update_proposer_boost_root_sameBlocks cfg _ _ _).2.2,
              ← (record_block_timeliness_sameBlocks cfg _ _).2.2,
              hframe.block_states]
          simp only [Function.update_self]
          refine le_trans (hpjf state hpost.1) ?_
          rw [hst_slot _ _ _ hst]; exact hblkSL
        · refine update_checkpoints_CkptEpochLe cfg SL _ _ _ hcjc ?_
          refine CkptEpochLe.of_sameCkpt (update_proposer_boost_root_sameCkpt cfg _ _ _) ?_
          refine CkptEpochLe.of_sameCkpt (record_block_timeliness_sameCkpt cfg _ _) ?_
          refine CkptEpochLe.of_sameCkpt hframe.sameCkpt ?_
          exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h

/-- `on_block` keeps every keyed state sane: the new key holds the transition
result from the keyed parent state. -/
theorem on_block_keyedStatesSane (cfg : Config) (ext : BeaconFunctionInterface Root)
    (hst_ckpt : StateTransitionCheckpointEpoch cfg ext)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hsane : KeyedStatesSane cfg store)
    (hh : on_block cfg ext store sb = some store') :
    KeyedStatesSane cfg store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact hsane
  · have hparent : sb.message.parent_root ∈ store.block_roots := by
      by_contra hp
      simp [on_block, hknown, hp] at hh
    simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      dsimp only at hh
      split at hh
      · cases hh
      · rename_i after_ptc hptc
        cases hh
        have hpost := CheckpointEpochsSane.of_state_transition hst_ckpt hst_slot
          (hsane _ hparent) hst
        refine KeyedStatesSane.of_sameBlocks ((notify_ptc_messages_sameBlocks cfg ext hptc).trans
          ((record_block_timeliness_sameBlocks cfg _ _).trans
            ((update_proposer_boost_root_sameBlocks cfg _ _ _).trans
              ((update_checkpoints_sameBlocks _ _ _).trans
                (compute_pulled_up_tip_sameBlocks cfg ext _ _))))) ?_
        intro r hr
        simp only [Function.update_apply]
        split_ifs with hrb
        · exact hpost
        · apply hsane
          simp only [List.mem_append, List.mem_singleton] at hr
          exact hr.resolve_right hrb

/-- One dispatched event keeps every keyed state sane. -/
theorem apply_event_keyedStatesSane (cfg : Config) (ext : BeaconFunctionInterface Root)
    (hst_ckpt : StateTransitionCheckpointEpoch cfg ext)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    {store store' : Store Root} {e : Event Root}
    (hsane : KeyedStatesSane cfg store)
    (he : apply_event cfg ext store e = some store') :
    KeyedStatesSane cfg store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_keyedStatesSane cfg ext hst_ckpt hst_slot hsane he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact KeyedStatesSane.of_sameBlocks (on_attestation_sameBlocks cfg ext he) hsane
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact KeyedStatesSane.of_sameBlocks (on_attester_slashing_sameBlocks ext he) hsane
  | execution_payload_envelope envelope observation =>
    exact KeyedStatesSane.of_sameBlocks (on_execution_payload_envelope_sameBlocks ext he) hsane
  | payload_attestation_message message is_from_block =>
    exact KeyedStatesSane.of_sameBlocks (on_payload_attestation_message_sameBlocks cfg ext he)
      hsane

/-- One dispatched event preserves the bound (needs the current-slot bound for
the `on_block` case, re-established across the fold). -/
theorem apply_event_CkptEpochLe (cfg : Config) (ext : BeaconFunctionInterface Root) (SL : Slot)
    (hst_ckpt : StateTransitionCheckpointEpoch cfg ext)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hpjf : PjfCheckpointEpoch cfg ext)
    {store store' : Store Root} {e : Event Root}
    (hcur : get_current_slot cfg store ≤ SL) (h : CkptEpochLe cfg SL store)
    (hsane : KeyedStatesSane cfg store)
    (he : apply_event cfg ext store e = some store') :
    CkptEpochLe cfg SL store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_CkptEpochLe cfg ext SL hst_ckpt hst_slot hpjf hcur h hsane he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_CkptEpochLe cfg ext SL h he
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact on_attester_slashing_CkptEpochLe cfg ext SL h he
  | execution_payload_envelope envelope observation =>
    exact on_execution_payload_envelope_CkptEpochLe cfg ext SL h he
  | payload_attestation_message message is_from_block =>
    exact on_payload_attestation_message_CkptEpochLe cfg ext SL h he

/-! ### `on_tick` preserves the store-epoch bound

`on_tick`'s only checkpoint write is `on_tick_per_slot`'s epoch-boundary
`update_checkpoints`, which adopts the store's own *unrealized*-justified
checkpoint — bounded by the second `CkptEpochLe` conjunct. It touches neither the
unrealized-justified checkpoint nor the current slot's epoch bound, so no
slot-arithmetic is needed. -/

omit [LinearOrder Root] in
theorem on_tick_per_slot_CkptEpochLe (cfg : Config) (SL : Slot) (store : Store Root) (time : ℕ)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h
      | exact update_checkpoints_CkptEpochLe cfg SL _ _ _
          (CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h).2 (CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h)

omit [LinearOrder Root] in
theorem on_tick_aux_CkptEpochLe (cfg : Config) (SL : Slot) (tick_slot fuel : ℕ)
    (store : Store Root) (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel generalizing store with
  | zero => exact h
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · exact ih _ (on_tick_per_slot_CkptEpochLe cfg SL store _ h)
    · exact h

omit [LinearOrder Root] in
theorem on_tick_CkptEpochLe (cfg : Config) (SL : Slot) (store : Store Root) (time : ℕ)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_CkptEpochLe cfg SL _ time (on_tick_aux_CkptEpochLe cfg SL _ _ _ h)

/-! ### The event fold and the trajectory invariant -/

/-- Folding a second's scheduled events preserves the bound: every event keeps
the store's current slot fixed (`apply_event_current_slot`), so the
current-slot bound is re-established at each step. -/
theorem CkptEpochLe_foldl (cfg : Config) (ext : BeaconFunctionInterface Root) (SL : Slot)
    (hst_ckpt : StateTransitionCheckpointEpoch cfg ext)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hpjf : PjfCheckpointEpoch cfg ext) :
    ∀ (l : List (Event Root)) (s : Store Root),
      get_current_slot cfg s ≤ SL → CkptEpochLe cfg SL s → KeyedStatesSane cfg s →
      CkptEpochLe cfg SL
          (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) ∧
        KeyedStatesSane cfg
          (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ h hsane; exact ⟨h, hsane⟩
  | cons e l ih =>
    intro s hcur h hsane
    rw [List.foldl_cons]
    cases he : apply_event cfg ext s e with
    | none => simp only [Option.getD_none]; exact ih s hcur h hsane
    | some s' =>
      simp only [Option.getD_some]
      refine ih s' ?_
        (apply_event_CkptEpochLe cfg ext SL hst_ckpt hst_slot hpjf hcur h hsane he)
        (apply_event_keyedStatesSane cfg ext hst_ckpt hst_slot hsane he)
      rw [apply_event_current_slot cfg ext he]; exact hcur

/-- **The store-epoch invariant.** At every node and second of a trajectory whose
genesis store is a `get_forkchoice_store`, both tracked checkpoint epochs are at
most `compute_epoch_at_slot (slot_at n)`, and every keyed block state is sane.
Mirrors `Delivery.store_blocksSlotLe`'s induction exactly (genesis anchor slot
from `get_current_slot_get_forkchoice_store`; step weakens the bound by
`slot_at_mono`, rides `on_tick`, folds the events). The anchor state is sane by
`BeaconExternalsPremises.anchor_state_checkpoint_epoch`. -/
theorem Execution.store_CkptEpochLe_keyedStatesSane (E : Execution Root) (cfg : Config)
    (ext : BeaconFunctionInterface Root)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    CkptEpochLe cfg (E.slot_at cfg n) (E.store cfg ext v n) ∧
      KeyedStatesSane cfg (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg, _⟩ := hgen
    have hcur0 : E.slot_at cfg 0 = ast.slot := by
      have h1 := E.store_current_slot cfg ext v 0
      rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hg,
        get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at h1
      exact h1.symm
    have hanchor := hec.anchor_state_checkpoint_epoch
    simp only [Execution.anchor_state, hg, get_forkchoice_store, Function.update_self]
      at hanchor
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hg]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hcur0]; exact le_of_eq (by simp only [get_forkchoice_store, get_current_epoch])
    · rw [hcur0]; exact le_of_eq (by simp only [get_forkchoice_store, get_current_epoch])
    · intro r hr
      simp only [get_forkchoice_store, List.mem_singleton] at hr
      subst r
      simpa only [get_forkchoice_store, Function.update_self] using hanchor
  | succ n ih =>
    change CkptEpochLe cfg (E.slot_at cfg (n + 1))
        ((E.schedule v (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1)))) ∧
      KeyedStatesSane cfg
        ((E.schedule v (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    have ih' : CkptEpochLe cfg (E.slot_at cfg (n + 1)) (E.store cfg ext v n) :=
      ih.1.mono (E.slot_at_mono cfg (Nat.le_succ n))
    have hontick : CkptEpochLe cfg (E.slot_at cfg (n + 1))
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) :=
      on_tick_CkptEpochLe cfg (E.slot_at cfg (n + 1)) _ _ ih'
    have hticksane : KeyedStatesSane cfg
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) :=
      KeyedStatesSane.of_sameBlocks (on_tick_sameBlocks cfg _ _) ih.2
    have hontickgen :
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))).genesis_time =
          E.genesis_store.genesis_time := by
      rw [← (on_tick_storeLE cfg (E.store cfg ext v n) (E.time_at (n + 1))).2.1,
        E.store_genesis_time cfg ext v n]
    have honticksl :
        get_current_slot cfg (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) =
          E.slot_at cfg (n + 1) := by
      rw [get_current_slot, get_slots_since_genesis, on_tick_time, hontickgen, Execution.slot_at]
    exact CkptEpochLe_foldl cfg ext (E.slot_at cfg (n + 1))
      hec.state_transition_checkpoint_epoch hec.state_transition_slot
      hec.pjf_checkpoint_epoch _ _ (le_of_eq honticksl) hontick hticksane

/-- **The store-epoch invariant.** At every node and second of a trajectory whose
genesis store is a `get_forkchoice_store`, both tracked checkpoint epochs are at
most `compute_epoch_at_slot (slot_at n)`. -/
theorem Execution.store_CkptEpochLe (E : Execution Root) (cfg : Config) (ext : BeaconFunctionInterface Root)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    CkptEpochLe cfg (E.slot_at cfg n) (E.store cfg ext v n) :=
  (E.store_CkptEpochLe_keyedStatesSane cfg ext hec hdiv hgen v n).1

/-- **The store-epoch bound** (Remainder item-2 residual, closed outright from the
frozen field `BeaconExternalsPremises.pjf_checkpoint_epoch` via `PjfCheckpointEpoch`): a
store's justified checkpoint never sits in a future epoch. -/
theorem Execution.store_justified_epoch_le (E : Execution Root) (cfg : Config)
    (ext : BeaconFunctionInterface Root) (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext v n).justified_checkpoint.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  have hb := E.store_CkptEpochLe cfg ext hec hdiv hgen v n
  simp only [get_current_store_epoch]
  rw [E.store_current_slot cfg ext v n]
  exact hb.1


/-! ## Section B — `hspan`: the saturated `Jspec` lower bound (EXPLICIT tiny-`TAB` edge)

`VoteLanding.boost_dilution` consumes the saturated-regime `Jspec` lower bound
`hJlb σ' : 2·(boost+1) ≤ Jspec lo σ'` for every `σ'` at least two epochs past `es`
(the post-`T1` saturation regime, where the confirmation window covers a full
epoch). This is the genuine tiny-`TAB` edge: without a nondegeneracy floor a total
active balance below `4·(boost+1)` leaves no honest weight to dominate twice the
proposer boost, and the bound genuinely fails.

It is delivered modulo two explicit coherence inputs (no new assumption fields):

* `hnondeg` — the nondegeneracy `4·(boost+1) ≤ total_active` (the tiny-`TAB`
  exclusion the task calls for);
* `hcov` — the full-epoch honest-coverage floor `total_active ≤ 2·Jspec lo σ'` on
  the saturated span. It follows from `committee_coverage` (a span covering a full
  epoch contains every active validator, so its honest weight is
  `≥ (100−CBT)/100 ≥ 1/2` of `total_active`) + `span_fraction`; the `Finset`
  coverage-weight identity `weight(active) = total_active` is the residual, **explicit**
  (not delivered here). -/


variable (E : Execution Root)




variable (cfg : Config) (ext : BeaconFunctionInterface Root)



end FastConfirmation.Spec

end
