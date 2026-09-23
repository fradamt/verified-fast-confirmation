module
public import FastConfirmationProofs.Execution.Delivery.Registry
public import FastConfirmationModel.Execution.PayloadFrame

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / Preservation

This module proves preservation of the derivable `WellFormedStore` fields along every execution
trajectory from the `get_forkchoice_store` base.

Three of the four structural fields are pure handler-local consequences and
are delivered here as trajectory theorems:

* `block_roots_nodup` — `on_block`'s append-if-absent keeps the key list
  duplicate-free; the other handlers never touch it.
* `time_ge_genesis` — the store clock equals `time_at` and `genesis_time` is
  constant (from `Proof/Trajectory`), so `≥ genesis` reduces to the base.
* `block_state_slot_eq` — `on_block` stores the transition post-state at the
  new block, and `BeaconExternalsPremises.state_transition_slot` lands it on the
  block's slot; the other handlers leave `blocks`/`block_states` alone.

The fourth field, `parent_slot_lt`, is **not** derivable from
`WellFormedStore` + `BeaconExternalsPremises` alone: adding a fresh root that an
existing block already names as its `parent_root` can break a child's
parent-slot ordering. Known blocks return without a write. Fresh roots need
the wire-block root injectivity and block provenance of `WellFormedExecution` (`BlockAgreement`). Its trajectory-level
proof is supplied by `WFTrajectory`.

The block-identity fields (`block_roots`, `blocks`, `block_states`) are the
only ones the derivable core reads, so the workhorse is `SameBlocks`: the
relation "these two stores carry the same block identity", preserved by every
store helper except `on_block`'s block insertion, and handled explicitly
there.

No behavioral assumptions enter beyond the sanctioned
`BeaconExternalsPremises.state_transition_slot` and the genesis `WellFormedStore`
witness.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Two stores carry the same block identity: equal key list, equal totalized
`blocks` map, equal totalized `block_states` map. The derivable core reads no
other store field of a block, so any helper that is `SameBlocks`-related to its
input preserves the core. -/
def SameBlocks (s t : Store Root) : Prop :=
  s.block_roots = t.block_roots ∧ s.blocks = t.blocks ∧ s.block_states = t.block_states

namespace SameBlocks

theorem refl (s : Store Root) : SameBlocks s s := ⟨rfl, rfl, rfl⟩

theorem trans {a b c : Store Root} (h1 : SameBlocks a b) (h2 : SameBlocks b c) :
    SameBlocks a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

end SameBlocks

/-- Payload map writes leave all three block-identity fields equal. -/
theorem PayloadFrame.sameBlocks {store store' : Store Root}
    (h : PayloadFrame store store') : SameBlocks store store' :=
  ⟨h.block_roots.symm, h.blocks.symm, h.block_states.symm⟩

/-- Folding a `SameBlocks`-preserving step keeps the block identity. -/
private theorem sameBlocks_foldl {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, SameBlocks s (f s a)) (l : List α) (s : Store Root) :
    SameBlocks s (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact SameBlocks.refl s
  | cons a l ih => exact (hf s a).trans (ih (f s a))

/-! ## `SameBlocks` for the block-identity-preserving helpers -/

theorem update_checkpoints_sameBlocks (store : Store Root) (jc fc : Checkpoint Root) :
    SameBlocks store (update_checkpoints store jc fc) := by
  simp only [update_checkpoints]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem update_unrealized_checkpoints_sameBlocks (store : Store Root)
    (jc fc : Checkpoint Root) :
    SameBlocks store (update_unrealized_checkpoints store jc fc) := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem update_latest_messages_sameBlocks (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    SameBlocks store (update_latest_messages store attesting_indices attestation) := by
  simp only [update_latest_messages]
  refine sameBlocks_foldl (fun s i => ?_) _ store
  dsimp only
  rcases hmi : s.latest_messages i with _ | lm <;> split_ifs <;> exact ⟨rfl, rfl, rfl⟩

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
theorem store_target_checkpoint_state_sameBlocks (store : Store Root)
    (target : Checkpoint Root) :
    SameBlocks store (store_target_checkpoint_state cfg ext store target) := by
  simp only [store_target_checkpoint_state]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

omit [Inhabited Root] in
theorem record_block_timeliness_sameBlocks (store : Store Root) (root : Root) :
    SameBlocks store (record_block_timeliness cfg store root) := by
  simp only [record_block_timeliness]; exact ⟨rfl, rfl, rfl⟩

theorem update_proposer_boost_root_sameBlocks (store : Store Root) (head root : Root) :
    SameBlocks store (update_proposer_boost_root cfg store head root) := by
  simp only [update_proposer_boost_root]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

omit [LinearOrder Root] in
theorem on_tick_per_slot_sameBlocks (store : Store Root) (time : ℕ) :
    SameBlocks store (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact ⟨rfl, rfl, rfl⟩
      | · refine SameBlocks.trans ?_ (update_checkpoints_sameBlocks _ _ _)
          exact ⟨rfl, rfl, rfl⟩

omit [LinearOrder Root] in
theorem on_tick_aux_sameBlocks (tick_slot fuel : ℕ) (store : Store Root) :
    SameBlocks store (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel generalizing store with
  | zero => exact SameBlocks.refl store
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · exact (on_tick_per_slot_sameBlocks cfg store _).trans (ih _)
    · exact SameBlocks.refl store

omit [LinearOrder Root] in
theorem on_tick_sameBlocks (store : Store Root) (time : ℕ) :
    SameBlocks store (on_tick cfg store time) := by
  simp only [on_tick]
  exact (on_tick_aux_sameBlocks cfg _ _ store).trans
    (on_tick_per_slot_sameBlocks cfg _ time)

omit [Inhabited Root] in
theorem compute_pulled_up_tip_sameBlocks (store : Store Root) (block_root : Root) :
    SameBlocks store (compute_pulled_up_tip cfg ext store block_root) := by
  simp only [compute_pulled_up_tip]
  split_ifs
  · refine SameBlocks.trans ?_ (update_checkpoints_sameBlocks _ _ _)
    refine SameBlocks.trans ?_ (update_unrealized_checkpoints_sameBlocks _ _ _)
    exact ⟨rfl, rfl, rfl⟩
  · refine SameBlocks.trans ?_ (update_unrealized_checkpoints_sameBlocks _ _ _)
    exact ⟨rfl, rfl, rfl⟩

omit [Inhabited Root] in
theorem on_payload_attestation_message_sameBlocks {store store' : Store Root}
    {message : PayloadAttestationMessage Root} {is_from_block : Bool}
    (h : on_payload_attestation_message cfg ext store message is_from_block = some store') :
    SameBlocks store store' := (on_payload_attestation_message_frame cfg ext h).sameBlocks

omit [Inhabited Root] in
theorem on_execution_payload_envelope_sameBlocks {store store' : Store Root}
    {envelope : SignedExecutionPayloadEnvelope Root} {observation : EnvelopeObservation Root}
    (h : on_execution_payload_envelope ext store envelope observation = some store') :
    SameBlocks store store' := (on_execution_payload_envelope_frame ext h).sameBlocks

theorem notify_ptc_messages_sameBlocks {store store' : Store Root}
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : notify_ptc_messages cfg ext store state attestations = some store') :
    SameBlocks store store' := (notify_ptc_messages_frame cfg ext h).sameBlocks

/-! ## The handler-preserved core -/

/-- The `WellFormedStore` fields that are pure handler-local consequences: the
key list is duplicate-free, and every known block's stored state sits at that
block's slot. Both are preserved by every fork-choice handler, so they hold
along every trajectory from a `WellFormedStore` base. (The remaining
`WellFormedStore` fields — `time_ge_genesis` and the checkpoint facts — are
handled separately: `time_ge_genesis` directly at the trajectory level below,
the checkpoint facts not at all here; see the file header.) -/
def WellFormedStoreCore (store : Store Root) : Prop :=
  store.block_roots.Nodup ∧
  ∀ r ∈ store.block_roots, (store.block_states r).slot = (store.blocks r).slot

omit [LinearOrder Root] [Inhabited Root] in
/-- `SameBlocks` carries the core across: the two invariant clauses read only
the block-identity fields. -/
theorem SameBlocks.wellFormedStoreCore {s t : Store Root} (h : SameBlocks s t)
    (hs : WellFormedStoreCore s) : WellFormedStoreCore t := by
  obtain ⟨hbr, hb, hbs⟩ := h
  simp only [WellFormedStoreCore, ← hbr, ← hb, ← hbs]
  exact hs

/-! ## `SameBlocks` for the block-identity-preserving handlers -/

omit [Inhabited Root] in
theorem on_attestation_sameBlocks {store store' : Store Root}
    {attestation : Attestation Root} {is_from_block : Bool}
    (h : on_attestation cfg ext store attestation is_from_block = some store') :
    SameBlocks store store' := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  exact (store_target_checkpoint_state_sameBlocks cfg ext store _).trans
    (update_latest_messages_sameBlocks _ _ _)

omit [Inhabited Root] in
theorem on_attester_slashing_sameBlocks {store store' : Store Root}
    {attester_slashing : AttesterSlashing Root}
    (h : on_attester_slashing ext store attester_slashing = some store') :
    SameBlocks store store' := by
  simp only [on_attester_slashing] at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-! ## `WellFormedStoreCore` preservation by the block-identity-preserving helpers

Each of these helpers is `SameBlocks`-related to its input, so the core rides
across by `SameBlocks.wellFormedStoreCore`. They are the ops `on_block` chains
*after* its block insertion, plus `on_tick`. -/

omit [LinearOrder Root] [Inhabited Root] in
theorem update_checkpoints_wellFormedStoreCore (store : Store Root)
    (jc fc : Checkpoint Root) (h : WellFormedStoreCore store) :
    WellFormedStoreCore (update_checkpoints store jc fc) :=
  (update_checkpoints_sameBlocks store jc fc).wellFormedStoreCore h

omit [Inhabited Root] in
theorem record_block_timeliness_wellFormedStoreCore (store : Store Root) (root : Root)
    (h : WellFormedStoreCore store) :
    WellFormedStoreCore (record_block_timeliness cfg store root) :=
  (record_block_timeliness_sameBlocks cfg store root).wellFormedStoreCore h

theorem update_proposer_boost_root_wellFormedStoreCore (store : Store Root)
    (head root : Root) (h : WellFormedStoreCore store) :
    WellFormedStoreCore (update_proposer_boost_root cfg store head root) :=
  (update_proposer_boost_root_sameBlocks cfg store head root).wellFormedStoreCore h

omit [Inhabited Root] in
theorem compute_pulled_up_tip_wellFormedStoreCore (store : Store Root)
    (block_root : Root) (h : WellFormedStoreCore store) :
    WellFormedStoreCore (compute_pulled_up_tip cfg ext store block_root) :=
  (compute_pulled_up_tip_sameBlocks cfg ext store block_root).wellFormedStoreCore h

omit [LinearOrder Root] in
theorem on_tick_wellFormedStoreCore (store : Store Root) (time : ℕ)
    (h : WellFormedStoreCore store) :
    WellFormedStoreCore (on_tick cfg store time) :=
  (on_tick_sameBlocks cfg store time).wellFormedStoreCore h

/-! ## `WellFormedStoreCore` preservation by `on_block`

The one handler that writes `blocks`/`block_states`/`block_roots`. Its block
insertion keeps both core clauses: the key-list stays duplicate-free
(append-only, and only if absent); and the new block's stored state sits at its
slot because `state_transition` lands the post-state on the block's slot
(`BeaconExternalsPremises.state_transition_slot`, taken here as a hypothesis). The
post-insertion tail (`record_block_timeliness`, `update_proposer_boost_root`,
`update_checkpoints`, `compute_pulled_up_tip`) is block-identity-preserving, so
the core rides across it by the helper lemmas above. -/
theorem on_block_wellFormedStoreCore
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    {store store' : Store Root} {signed_block : SignedBeaconBlock Root}
    (h : WellFormedStoreCore store)
    (hh : on_block cfg ext store signed_block = some store') :
    WellFormedStoreCore store' := by
  by_cases hknown : signed_block.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    cases hst : ext.state_transition
        (store.block_states signed_block.message.parent_root) signed_block with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      dsimp only at hh
      split at hh
      · cases hh
      · rename_i after_ptc hptc
        cases hh
        apply compute_pulled_up_tip_wellFormedStoreCore
        apply update_checkpoints_wellFormedStoreCore
        apply update_proposer_boost_root_wellFormedStoreCore
        apply record_block_timeliness_wellFormedStoreCore
        apply (notify_ptc_messages_sameBlocks cfg ext hptc).wellFormedStoreCore
        obtain ⟨hnd, hbss⟩ := h
        have hsloteq : state.slot = signed_block.message.slot := hst_slot _ _ _ hst
        refine ⟨?_, fun r hr => ?_⟩
        · exact hnd.append (List.nodup_singleton _)
            (List.disjoint_singleton.mpr hknown)
        · simp only [Function.update_apply]
          split_ifs with hrb
          · exact hsloteq
          · apply hbss
            simp only [List.mem_append, List.mem_singleton] at hr
            exact hr.resolve_right hrb

/-! ## `apply_event` dispatch and the trajectory-level core

Event dispatch preserves the core. The block case is
`on_block_wellFormedStoreCore`; every other handler preserves block identity,
so the core passes across `SameBlocks`. -/

/-- One wire message preserves the handler-local core (the block case needs the
sanctioned `state_transition_slot`). -/
theorem apply_event_wellFormedStoreCore
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    {store store' : Store Root} {event : Event Root}
    (h : WellFormedStoreCore store)
    (he : apply_event cfg ext store event = some store') :
    WellFormedStoreCore store' := by
  cases event with
  | block b => exact on_block_wellFormedStoreCore cfg ext hst_slot h he
  | attestation a ifb => exact (on_attestation_sameBlocks cfg ext he).wellFormedStoreCore h
  | attester_slashing s => exact (on_attester_slashing_sameBlocks ext he).wellFormedStoreCore h
  | execution_payload_envelope envelope observation =>
    exact (on_execution_payload_envelope_sameBlocks ext he).wellFormedStoreCore h
  | payload_attestation_message message is_from_block =>
    exact (on_payload_attestation_message_sameBlocks cfg ext he).wellFormedStoreCore h

/-- One step of the event fold preserves the core (a rejected event leaves the
store unchanged). -/
private theorem apply_event_getD_wellFormedStoreCore
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (store : Store Root) (event : Event Root) (h : WellFormedStoreCore store) :
    WellFormedStoreCore ((apply_event cfg ext store event).getD store) := by
  cases he : apply_event cfg ext store event with
  | none => rw [Option.getD_none]; exact h
  | some s' =>
    rw [Option.getD_some]
    exact apply_event_wellFormedStoreCore cfg ext hst_slot h he

omit [LinearOrder Root] [Inhabited Root] in
/-- Folding a core-preserving step keeps the core. -/
private theorem wellFormedStoreCore_foldl {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, WellFormedStoreCore s → WellFormedStoreCore (f s a))
    (l : List α) (s : Store Root) (hs : WellFormedStoreCore s) :
    WellFormedStoreCore (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons a l ih => exact ih (f s a) (hf s a hs)

omit [Inhabited Root] in
/-- Extract the handler-local core from the full store invariant. -/
theorem WellFormedStore.core {store : Store Root} (h : WellFormedStore store) :
    WellFormedStoreCore store :=
  ⟨h.block_roots_nodup, h.block_state_slot_eq⟩

/-- The core holds at every node and second of any trajectory whose genesis
store carries it. `hst_slot` is `BeaconExternalsPremises.state_transition_slot`; the
genesis premise is discharged by `wellFormedStore_get_forkchoice_store` (via
`WellFormedStore.core`) when the genesis store is a `get_forkchoice_store`. -/
theorem Execution.store_wellFormedStoreCore (E : Execution Root)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hbase : WellFormedStoreCore E.genesis_store)
    (v : ValidatorIndex) (n : ℕ) :
    WellFormedStoreCore (E.store cfg ext v n) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    change WellFormedStoreCore
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    refine wellFormedStoreCore_foldl
      (fun s e hs => apply_event_getD_wellFormedStoreCore cfg ext hst_slot s e hs) _ _ ?_
    exact on_tick_wellFormedStoreCore cfg _ _ ih


/-! ## `parent_slot_lt` preservation by `on_block` (handler-level)

The fourth `WellFormedStore` field. `on_block`'s block insertion preserves it,
but only once two provenance premises are supplied — that the new block's root
is fresh (`hfresh`) and is named by no existing block (`hno_child`). Both hold
by wire-block root injectivity (`WellFormedExecution`, `BlockAgreement`) but are **not**
handler-local, so they enter as explicit hypotheses here and the
*trajectory-level* discharge is supplied by `WFTrajectory` using
`BlockAgreement`. The ordering itself comes from
`BeaconExternalsPremises.state_transition_pre_slot_lt` (parent state slot < new block
slot) composed with `block_state_slot_eq` (parent state slot = parent block
slot). -/

/-- Parent pointers strictly decrease slots within the store (the shape of
`WellFormedStore.parent_slot_lt`). -/
def ParentSlotLt (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots,
    (store.blocks r).parent_root ∈ store.block_roots →
      (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot

omit [LinearOrder Root] [Inhabited Root] in
/-- `SameBlocks` carries the parent-slot order across: it reads only
`block_roots` and `blocks`. -/
theorem SameBlocks.parentSlotLt {s t : Store Root} (h : SameBlocks s t)
    (hs : ParentSlotLt s) : ParentSlotLt t := by
  obtain ⟨hbr, hb, _⟩ := h
  simp only [ParentSlotLt, ← hbr, ← hb]
  exact hs

omit [Inhabited Root] in
/-- Extract the parent-slot order from the full store invariant. -/
theorem WellFormedStore.parentSlotLt {store : Store Root} (h : WellFormedStore store) :
    ParentSlotLt store :=
  h.parent_slot_lt

omit [Inhabited Root] in
/-- Block insertion at a fresh, unreferenced root preserves the parent-slot
order. The new block's parent is an older block (a fresh root differs from any
member, so `parent ≠ root`) at a strictly smaller slot (`hpre`, via
`block_state_slot_eq`); and no older block names the fresh root as parent
(`hno_child`), so every older edge keeps its old witness. -/
theorem parentSlotLt_insert (store : Store Root) (block_root : Root)
    (block : BeaconBlock Root) (state : BeaconState Root)
    (hpar : ParentSlotLt store)
    (hbss : ∀ r ∈ store.block_roots, (store.block_states r).slot = (store.blocks r).slot)
    (hfresh : block_root ∉ store.block_roots)
    (hno_child : ∀ r ∈ store.block_roots, (store.blocks r).parent_root ≠ block_root)
    (hpar_in : block.parent_root ∈ store.block_roots)
    (hpre : (store.block_states block.parent_root).slot < block.slot) :
    ParentSlotLt { store with
      block_roots := store.block_roots ++ [block_root]
      blocks := Function.update store.blocks block_root block
      block_states := Function.update store.block_states block_root state } := by
  intro r hr hpr
  simp only [List.mem_append, List.mem_singleton, Function.update_apply] at hr hpr ⊢
  rcases hr with hr | heq
  · have hrne : ¬ r = block_root := fun h => hfresh (h ▸ hr)
    rw [if_neg hrne] at hpr ⊢
    rcases hpr with hpr | hpr
    · rw [if_neg (hno_child r hr)]
      exact hpar r hr hpr
    · exact absurd hpr (hno_child r hr)
  · subst r
    rw [if_pos rfl]
    have hpne : ¬ block.parent_root = block_root := fun h => hfresh (h ▸ hpar_in)
    rw [if_neg hpne, ← hbss block.parent_root hpar_in]
    exact hpre

/-- `on_block` preserves the parent-slot order, given the input store's order
(`hpar`) and slot alignment (`hcore`), the sanctioned
`state_transition_pre_slot_lt` (`hst_pre_lt`), and the two provenance premises
`hfresh`/`hno_child`. The post-insertion tail is block-identity-preserving, so
the order rides across it by `SameBlocks.parentSlotLt`; the insertion itself is
`parentSlotLt_insert`. -/
theorem on_block_parentSlotLt
    (hst_pre_lt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st.slot < b.message.slot)
    {store store' : Store Root} {signed_block : SignedBeaconBlock Root}
    (hcore : WellFormedStoreCore store) (hpar : ParentSlotLt store)
    (hfresh : signed_block.root ∉ store.block_roots)
    (hno_child : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ≠ signed_block.root)
    (hh : on_block cfg ext store signed_block = some store') :
    ParentSlotLt store' := by
  have hpar_in : signed_block.message.parent_root ∈ store.block_roots := by
    by_contra habsent
    simp [on_block, hfresh, habsent] at hh
  simp only [on_block, if_neg hfresh] at hh
  split_ifs at hh
  all_goals try contradiction
  cases hst : ext.state_transition
      (store.block_states signed_block.message.parent_root) signed_block with
  | none => rw [hst] at hh; cases hh
  | some state =>
    rw [hst] at hh
    dsimp only at hh
    split at hh
    · cases hh
    · rename_i after_ptc hptc
      cases hh
      refine (compute_pulled_up_tip_sameBlocks cfg ext _ _).parentSlotLt ?_
      refine (update_checkpoints_sameBlocks _ _ _).parentSlotLt ?_
      refine (update_proposer_boost_root_sameBlocks cfg _ _ _).parentSlotLt ?_
      refine (record_block_timeliness_sameBlocks cfg _ _).parentSlotLt ?_
      refine (notify_ptc_messages_sameBlocks cfg ext hptc).parentSlotLt ?_
      obtain ⟨_, hbss⟩ := hcore
      have hpre : (store.block_states signed_block.message.parent_root).slot
          < signed_block.message.slot := hst_pre_lt _ _ _ hst
      exact parentSlotLt_insert store signed_block.root signed_block.message state
        hpar hbss hfresh hno_child hpar_in hpre

end FastConfirmation.Spec

end
