module
public import FastConfirmation.Spec.Model.Assumptions
public import FastConfirmation.Spec.Proof.Clock
public import FastConfirmation.Spec.Proof.EconomicRounding
public import FastConfirmation.Spec.Model.PayloadEffects

@[expose] public section

/-!
# Spec / Proof / Registry

Registry constancy along execution trajectories: every state an honest node's
store carries — every `block_states` entry over `block_roots`, every
`checkpoint_states` entry over `checkpoint_state_keys` — has
`validators = E.registry`.

The trusted `get_forkchoice_store` initialization seeds this at the genesis
store; every handler preserves it (`ExternalsCoherence`'s
registry-preservation facts move it through `on_block`'s state transition and
`on_attestation`'s `process_slots` checkpoint-state write); so it holds at
every node and second. The payoff (`get_total_active_balance` of every balance
source the rule reads equals the anchor's `E.total_active`) needs the
static-set's epoch-independent activity to move `get_total_active_balance`'s
`get_current_epoch` read between states at different slots.

No behavioral assumptions enter beyond genesis initialization and
`ExternalsCoherence`; store monotonicity of the tracked fields is the
mechanism. `StaticValidatorSet` is needed only by the later active-balance
corollaries, not to seed registry constancy.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Registry constancy of a store: every block state (over the known block
roots) and every checkpoint state (over the cached checkpoint keys) is on the
registry `reg`. The two ∀-clauses mirror the two `block_states` /
`checkpoint_states` dicts the fork choice reads validator weights from. -/
def RegistryConstant (reg : List Validator) (store : Store Root) : Prop :=
  (∀ r ∈ store.block_roots, (store.block_states r).validators = reg) ∧
  (∀ c ∈ store.checkpoint_state_keys, (store.checkpoint_states c).validators = reg)

namespace RegistryConstant

/-- `RegistryConstant` depends only on the four fields `block_roots`,
`block_states`, `checkpoint_state_keys`, `checkpoint_states`; transfer it
across any store agreeing on those. -/
theorem of_eq {reg : List Validator} {store store' : Store Root}
    (h : RegistryConstant reg store)
    (hbr : store'.block_roots = store.block_roots)
    (hbs : store'.block_states = store.block_states)
    (hck : store'.checkpoint_state_keys = store.checkpoint_state_keys)
    (hcs : store'.checkpoint_states = store.checkpoint_states) :
    RegistryConstant reg store' :=
  ⟨by rw [hbr, hbs]; exact h.1, by rw [hck, hcs]; exact h.2⟩

/-- Payload and PTC writes preserve all registry-bearing state fields. -/
theorem of_payloadFrame {reg : List Validator} {store store' : Store Root}
    (h : RegistryConstant reg store) (hf : PayloadFrame store store') :
    RegistryConstant reg store' :=
  h.of_eq hf.block_roots hf.block_states hf.checkpoint_state_keys hf.checkpoint_states

end RegistryConstant

/-! ## Field-projection lemmas for the checkpoint-update helpers

The `block_roots` cases live upstream (`StoreInvariants`); these add the
`block_states` / `checkpoint_state_keys` / `checkpoint_states` cases the
registry invariant reads. -/

@[simp] theorem update_checkpoints_block_states (store : Store Root)
    (jc fc : Checkpoint Root) :
    (update_checkpoints store jc fc).block_states = store.block_states := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_checkpoints_checkpoint_state_keys (store : Store Root)
    (jc fc : Checkpoint Root) :
    (update_checkpoints store jc fc).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_checkpoints_checkpoint_states (store : Store Root)
    (jc fc : Checkpoint Root) :
    (update_checkpoints store jc fc).checkpoint_states = store.checkpoint_states := by
  simp only [update_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_block_states (store : Store Root)
    (jc fc : Checkpoint Root) :
    (update_unrealized_checkpoints store jc fc).block_states = store.block_states := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_checkpoint_state_keys (store : Store Root)
    (jc fc : Checkpoint Root) :
    (update_unrealized_checkpoints store jc fc).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

@[simp] theorem update_unrealized_checkpoints_checkpoint_states (store : Store Root)
    (jc fc : Checkpoint Root) :
    (update_unrealized_checkpoints store jc fc).checkpoint_states =
      store.checkpoint_states := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

/-- Folding a `RegistryConstant`-preserving step preserves `RegistryConstant`. -/
theorem registryConstant_foldl {reg : List Validator} {α : Type*}
    {f : Store Root → α → Store Root}
    (hf : ∀ s a, RegistryConstant reg s → RegistryConstant reg (f s a))
    (l : List α) (s : Store Root) (h : RegistryConstant reg s) :
    RegistryConstant reg (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact h
  | cons a l ih => exact ih (f s a) (hf s a h)

/-! ## `RegistryConstant` preservation by the four-field-preserving helpers -/

theorem update_checkpoints_registryConstant {reg : List Validator} (store : Store Root)
    (jc fc : Checkpoint Root) (h : RegistryConstant reg store) :
    RegistryConstant reg (update_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp) (by simp) (by simp)

theorem update_unrealized_checkpoints_registryConstant {reg : List Validator}
    (store : Store Root) (jc fc : Checkpoint Root) (h : RegistryConstant reg store) :
    RegistryConstant reg (update_unrealized_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp) (by simp) (by simp)

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
theorem record_block_timeliness_registryConstant {reg : List Validator}
    (store : Store Root) (root : Root) (h : RegistryConstant reg store) :
    RegistryConstant reg (record_block_timeliness cfg store root) :=
  h.of_eq rfl rfl rfl rfl

theorem update_proposer_boost_root_registryConstant {reg : List Validator}
    (store : Store Root) (head root : Root) (h : RegistryConstant reg store) :
    RegistryConstant reg (update_proposer_boost_root cfg store head root) := by
  refine h.of_eq ?_ ?_ ?_ ?_ <;>
    (simp only [update_proposer_boost_root]; split_ifs <;> rfl)

omit [Inhabited Root] in
theorem compute_pulled_up_tip_registryConstant {reg : List Validator}
    (store : Store Root) (block_root : Root) (h : RegistryConstant reg store) :
    RegistryConstant reg (compute_pulled_up_tip cfg ext store block_root) := by
  refine h.of_eq ?_ ?_ ?_ ?_ <;>
    (simp only [compute_pulled_up_tip]; split_ifs <;> simp)

omit [LinearOrder Root] [Inhabited Root] in
theorem update_latest_messages_registryConstant {reg : List Validator}
    (store : Store Root) (attesting_indices : List ValidatorIndex)
    (attestation : Attestation Root) (h : RegistryConstant reg store) :
    RegistryConstant reg
      (update_latest_messages store attesting_indices attestation) := by
  simp only [update_latest_messages]
  refine registryConstant_foldl (fun s i hs => ?_) _ store h
  refine hs.of_eq ?_ ?_ ?_ ?_ <;>
    · dsimp only
      rcases hmi : s.latest_messages i with _ | lm <;> split_ifs <;> rfl

/-! ## `RegistryConstant` preservation by `store_target_checkpoint_state`

The one checkpoint-state write in the handlers: the newly cached state is the
target block's state (optionally pulled up by `process_slots`, which preserves
the registry), so it stays on `reg` provided the target block is known — which
`validate_on_attestation` guarantees at the `on_attestation` call site. -/

omit [Inhabited Root] in
theorem store_target_checkpoint_state_registryConstant {reg : List Validator}
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      (ext.process_slots st s).validators = st.validators)
    (store : Store Root) (target : Checkpoint Root)
    (hknown : target.root ∈ store.block_roots) (h : RegistryConstant reg store) :
    RegistryConstant reg (store_target_checkpoint_state cfg ext store target) := by
  obtain ⟨hblk, hchk⟩ := h
  simp only [store_target_checkpoint_state]
  split_ifs with hnew hslot <;>
    first
      | exact ⟨hblk, hchk⟩
      | · refine ⟨hblk, fun c hc => ?_⟩
          rw [Finset.mem_insert] at hc
          simp only [Function.update_apply]
          split_ifs with hct
          · first
              | (rw [hps]; exact hblk _ hknown)
              | exact hblk _ hknown
          · exact hchk c (hc.resolve_left hct)

omit [Inhabited Root] in
/-- `validate_on_attestation` asserts the attestation's FFG target block is
known — the fact `store_target_checkpoint_state` needs to keep its checkpoint
write on the registry. -/
theorem validate_on_attestation_target_known {store : Store Root}
    {attestation : Attestation Root} {is_from_block : Bool}
    (h : validate_on_attestation cfg store attestation is_from_block = true) :
    attestation.data.target.root ∈ store.block_roots := by
  simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

/-! ## Handler-level `RegistryConstant` preservation -/

omit [Inhabited Root] in
theorem on_attester_slashing_registryConstant {reg : List Validator}
    {store store' : Store Root} {attester_slashing : AttesterSlashing Root}
    (h : RegistryConstant reg store)
    (hh : on_attester_slashing ext store attester_slashing = some store') :
    RegistryConstant reg store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl rfl

omit [Inhabited Root] in
theorem on_attestation_registryConstant {reg : List Validator}
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      (ext.process_slots st s).validators = st.validators)
    {store store' : Store Root} {attestation : Attestation Root} {is_from_block : Bool}
    (h : RegistryConstant reg store)
    (hh : on_attestation cfg ext store attestation is_from_block = some store') :
    RegistryConstant reg store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  have hknown := validate_on_attestation_target_known cfg hv
  exact update_latest_messages_registryConstant _ _ _
    (store_target_checkpoint_state_registryConstant cfg ext hps store _ hknown h)

theorem notify_ptc_messages_registryConstant {reg : List Validator}
    {store store' : Store Root} {state : BeaconState Root}
    {attestations : List (IndexedPayloadAttestation Root)}
    (h : RegistryConstant reg store)
    (hh : notify_ptc_messages cfg ext store state attestations = some store') :
    RegistryConstant reg store' := h.of_payloadFrame (notify_ptc_messages_frame cfg ext hh)

omit [Inhabited Root] in
theorem on_payload_attestation_message_registryConstant {reg : List Validator}
    {store store' : Store Root} {message : PayloadAttestationMessage Root}
    {is_from_block : Bool} (h : RegistryConstant reg store)
    (hh : on_payload_attestation_message cfg ext store message is_from_block = some store') :
    RegistryConstant reg store' :=
  h.of_payloadFrame (on_payload_attestation_message_frame cfg ext hh)

omit [Inhabited Root] in
theorem on_execution_payload_envelope_registryConstant {reg : List Validator}
    {store store' : Store Root} {envelope : SignedExecutionPayloadEnvelope Root}
    {observation : EnvelopeObservation Root} (h : RegistryConstant reg store)
    (hh : on_execution_payload_envelope ext store envelope observation = some store') :
    RegistryConstant reg store' :=
  h.of_payloadFrame (on_execution_payload_envelope_frame ext hh)

theorem on_block_registryConstant {reg : List Validator}
    (hst_reg : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.validators = st.validators)
    {store store' : Store Root} {signed_block : SignedBeaconBlock Root}
    (h : RegistryConstant reg store)
    (hh : on_block cfg ext store signed_block = some store') :
    RegistryConstant reg store' := by
  by_cases hknown : signed_block.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · have hpar : signed_block.message.parent_root ∈ store.block_roots := by
      by_contra habsent
      simp [on_block, hknown, habsent] at hh
    simp only [on_block, if_neg hknown] at hh
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
        apply compute_pulled_up_tip_registryConstant
        apply update_checkpoints_registryConstant
        apply update_proposer_boost_root_registryConstant
        apply record_block_timeliness_registryConstant
        refine notify_ptc_messages_registryConstant cfg ext ?_ hptc
        obtain ⟨hblk, hchk⟩ := h
        refine ⟨fun r hr => ?_, hchk⟩
        simp only [Function.update_apply]
        split_ifs with hrb
        · rw [hst_reg _ _ _ hst]; exact hblk _ hpar
        · apply hblk
          simp only [List.mem_append, List.mem_singleton] at hr
          exact hr.resolve_right hrb

/-! ## `RegistryConstant` preservation by `on_tick` -/

omit [LinearOrder Root] in
theorem on_tick_per_slot_registryConstant {reg : List Validator} (store : Store Root)
    (time : ℕ) (h : RegistryConstant reg store) :
    RegistryConstant reg (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact h.of_eq rfl rfl rfl rfl
      | exact update_checkpoints_registryConstant _ _ _ (h.of_eq rfl rfl rfl rfl)

omit [LinearOrder Root] in
theorem on_tick_aux_registryConstant {reg : List Validator} (tick_slot fuel : ℕ) :
    ∀ store : Store Root, RegistryConstant reg store →
      RegistryConstant reg (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
    intro store h
    rw [on_tick_aux]
    split_ifs
    · exact ih _ (on_tick_per_slot_registryConstant cfg _ _ h)
    · exact h

omit [LinearOrder Root] in
theorem on_tick_registryConstant {reg : List Validator} (store : Store Root) (time : ℕ)
    (h : RegistryConstant reg store) :
    RegistryConstant reg (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_registryConstant cfg _ _
    (on_tick_aux_registryConstant cfg _ _ _ h)

/-! ## Event dispatch and the trajectory invariant -/

theorem apply_event_registryConstant {reg : List Validator}
    (hst_reg : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.validators = st.validators)
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      (ext.process_slots st s).validators = st.validators)
    {store store' : Store Root} {event : Event Root} (h : RegistryConstant reg store)
    (hh : apply_event cfg ext store event = some store') :
    RegistryConstant reg store' := by
  cases event with
  | block b => exact on_block_registryConstant cfg ext hst_reg h hh
  | attestation a ifb => exact on_attestation_registryConstant cfg ext hps h hh
  | attester_slashing s => exact on_attester_slashing_registryConstant ext h hh
  | execution_payload_envelope envelope observation =>
    exact on_execution_payload_envelope_registryConstant ext h hh
  | payload_attestation_message message is_from_block =>
    exact on_payload_attestation_message_registryConstant cfg ext h hh

/-- One step of the event fold preserves `RegistryConstant`. -/
theorem apply_event_getD_registryConstant {reg : List Validator}
    (hst_reg : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.validators = st.validators)
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      (ext.process_slots st s).validators = st.validators)
    (store : Store Root) (event : Event Root) (h : RegistryConstant reg store) :
    RegistryConstant reg ((apply_event cfg ext store event).getD store) := by
  cases heq : apply_event cfg ext store event with
  | none => simpa using h
  | some s' => simpa using apply_event_registryConstant cfg ext hst_reg hps h heq

/-- The trusted fork-choice initialization puts the same anchor state in both
state maps, and `Execution.registry` is that anchor state's validator list. -/
theorem Execution.genesis_registryConstant (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    RegistryConstant E.registry E.genesis_store := by
  obtain ⟨ast, ablk, hgeq⟩ := hgen
  simp only [RegistryConstant]
  constructor
  · intro r hr
    rw [hgeq] at hr ⊢
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    subst r
    simp only [Execution.registry, Execution.anchor_state, hgeq,
      get_forkchoice_store, Function.update_self]
  · intro c hc
    rw [hgeq] at hc ⊢
    simp only [get_forkchoice_store, Finset.mem_singleton] at hc
    subst c
    simp only [Execution.registry, Execution.anchor_state, hgeq,
      get_forkchoice_store, Function.update_self]

/-- Registry constancy holds at every node and second: the mechanically seeded
genesis invariant propagates along the whole trajectory. -/
theorem Execution.registryConstant (E : Execution Root)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    ∀ v ∈ E.honest, ∀ n, RegistryConstant E.registry (E.store cfg ext v n) := by
  intro v _ n
  induction n with
  | zero => exact E.genesis_registryConstant cfg hgen
  | succ n ih =>
    change RegistryConstant E.registry ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    refine registryConstant_foldl
      (fun s e hs => apply_event_getD_registryConstant cfg ext
        hec.state_transition_registry hec.process_slots_registry s e hs) _ _ ?_
    exact on_tick_registryConstant cfg _ _ ih

/-! ## State-slot bounds for every balance source

Every state in either keyed store map is at or before the execution clock.
This is the reachability fact needed to specialize horizon-bounded activity
constancy at the epochs actually read by `get_total_active_balance` and
`compute_proposer_score`. -/

/-- All keyed block and checkpoint states lie no later than slot `SL`. -/
def StateSlotsLE (SL : Slot) (store : Store Root) : Prop :=
  (∀ r ∈ store.block_roots, (store.block_states r).slot ≤ SL) ∧
  (∀ c ∈ store.checkpoint_state_keys, (store.checkpoint_states c).slot ≤ SL)

namespace StateSlotsLE

omit [LinearOrder Root] [Inhabited Root] in
/-- Weaken a state-slot bound to a later slot. -/
theorem mono {SL SL' : Slot} {store : Store Root} (h : StateSlotsLE SL store)
    (hSL : SL ≤ SL') : StateSlotsLE SL' store :=
  ⟨fun r hr => le_trans (h.1 r hr) hSL,
    fun c hc => le_trans (h.2 c hc) hSL⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- Transfer the bound across stores agreeing on its four observed fields. -/
theorem of_eq {SL : Slot} {store store' : Store Root}
    (h : StateSlotsLE SL store)
    (hbr : store'.block_roots = store.block_roots)
    (hbs : store'.block_states = store.block_states)
    (hck : store'.checkpoint_state_keys = store.checkpoint_state_keys)
    (hcs : store'.checkpoint_states = store.checkpoint_states) :
    StateSlotsLE SL store' :=
  ⟨by rw [hbr, hbs]; exact h.1, by rw [hck, hcs]; exact h.2⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- Payload and PTC writes preserve all stored-state slot bounds. -/
theorem of_payloadFrame {SL : Slot} {store store' : Store Root}
    (h : StateSlotsLE SL store) (hf : PayloadFrame store store') :
    StateSlotsLE SL store' :=
  h.of_eq hf.block_roots hf.block_states hf.checkpoint_state_keys hf.checkpoint_states

end StateSlotsLE

omit [LinearOrder Root] [Inhabited Root] in
/-- Folding a `StateSlotsLE`-preserving step preserves the bound. -/
theorem stateSlotsLE_foldl {α : Type*} {SL : Slot}
    {f : Store Root → α → Store Root}
    (hf : ∀ s a, StateSlotsLE SL s → StateSlotsLE SL (f s a))
    (l : List α) (s : Store Root) (h : StateSlotsLE SL s) :
    StateSlotsLE SL (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact h
  | cons a l ih => exact ih (f s a) (hf s a h)

omit [LinearOrder Root] [Inhabited Root] in
/-- Folding steps that preserve the store-clock and state-slot bounds preserves
both bounds. -/
theorem currentSlot_stateSlotsLE_foldl {α : Type*} {SL : Slot}
    {f : Store Root → α → Store Root}
    (hf : ∀ s a, get_current_slot cfg s ≤ SL ∧ StateSlotsLE SL s →
      get_current_slot cfg (f s a) ≤ SL ∧ StateSlotsLE SL (f s a))
    (l : List α) (s : Store Root)
    (h : get_current_slot cfg s ≤ SL ∧ StateSlotsLE SL s) :
    get_current_slot cfg (l.foldl f s) ≤ SL ∧ StateSlotsLE SL (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact h
  | cons a l ih => exact ih (f s a) (hf s a h)

omit [LinearOrder Root] [Inhabited Root] in
theorem update_checkpoints_stateSlotsLE {SL : Slot} (store : Store Root)
    (jc fc : Checkpoint Root) (h : StateSlotsLE SL store) :
    StateSlotsLE SL (update_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp) (by simp) (by simp)

omit [LinearOrder Root] [Inhabited Root] in
theorem update_unrealized_checkpoints_stateSlotsLE {SL : Slot} (store : Store Root)
    (jc fc : Checkpoint Root) (h : StateSlotsLE SL store) :
    StateSlotsLE SL (update_unrealized_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp) (by simp) (by simp)

omit [Inhabited Root] in
theorem record_block_timeliness_stateSlotsLE {SL : Slot} (store : Store Root)
    (root : Root) (h : StateSlotsLE SL store) :
    StateSlotsLE SL (record_block_timeliness cfg store root) :=
  h.of_eq rfl rfl rfl rfl

theorem update_proposer_boost_root_stateSlotsLE {SL : Slot} (store : Store Root)
    (head root : Root) (h : StateSlotsLE SL store) :
    StateSlotsLE SL (update_proposer_boost_root cfg store head root) := by
  refine h.of_eq ?_ ?_ ?_ ?_ <;>
    (simp only [update_proposer_boost_root]; split_ifs <;> rfl)

omit [Inhabited Root] in
theorem compute_pulled_up_tip_stateSlotsLE {SL : Slot} (store : Store Root)
    (block_root : Root) (h : StateSlotsLE SL store) :
    StateSlotsLE SL (compute_pulled_up_tip cfg ext store block_root) := by
  refine h.of_eq ?_ ?_ ?_ ?_ <;>
    (simp only [compute_pulled_up_tip]; split_ifs <;> simp)

omit [LinearOrder Root] [Inhabited Root] in
theorem update_latest_messages_stateSlotsLE {SL : Slot} (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root)
    (h : StateSlotsLE SL store) :
    StateSlotsLE SL (update_latest_messages store attesting_indices attestation) := by
  simp only [update_latest_messages]
  refine stateSlotsLE_foldl (fun s i hs => ?_) _ store h
  refine hs.of_eq ?_ ?_ ?_ ?_ <;>
    · dsimp only
      rcases hmi : s.latest_messages i with _ | lm <;> split_ifs <;> rfl

omit [Inhabited Root] in
/-- Caching a known checkpoint target preserves the state-slot bound when the
target epoch's start slot is within the same execution-clock bound. -/
theorem store_target_checkpoint_state_stateSlotsLE {SL : Slot}
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      st.slot < s → (ext.process_slots st s).slot = s)
    (store : Store Root) (target : Checkpoint Root)
    (hknown : target.root ∈ store.block_roots)
    (htarget : compute_start_slot_at_epoch cfg target.epoch ≤ SL)
    (h : StateSlotsLE SL store) :
    StateSlotsLE SL (store_target_checkpoint_state cfg ext store target) := by
  obtain ⟨hblk, hchk⟩ := h
  simp only [store_target_checkpoint_state]
  split_ifs with hnew hslot <;>
    first
      | exact ⟨hblk, hchk⟩
      | · refine ⟨hblk, fun c hc => ?_⟩
          rw [Finset.mem_insert] at hc
          simp only [Function.update_apply]
          split_ifs with hct
          · first
              | (rw [hps _ _ hslot]; exact htarget)
              | exact hblk _ hknown
          · exact hchk c (hc.resolve_left hct)

omit [Inhabited Root] in
theorem on_attester_slashing_stateSlotsLE {SL : Slot}
    {store store' : Store Root} {attester_slashing : AttesterSlashing Root}
    (h : StateSlotsLE SL store)
    (hh : on_attester_slashing ext store attester_slashing = some store') :
    StateSlotsLE SL store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl rfl

omit [Inhabited Root] in
theorem on_attestation_stateSlotsLE {SL : Slot} {store store' : Store Root}
    {attestation : Attestation Root} {is_from_block : Bool}
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      st.slot < s → (ext.process_slots st s).slot = s)
    (hcur : get_current_slot cfg store ≤ SL) (h : StateSlotsLE SL store)
    (hh : on_attestation cfg ext store attestation is_from_block = some store') :
    StateSlotsLE SL store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hepoch : attestation.data.target.epoch = compute_epoch_at_slot cfg attestation.data.slot := by
    tauto
  have hknown : attestation.data.target.root ∈ store.block_roots := by tauto
  have hgate : attestation.data.slot + 1 ≤ get_current_slot cfg store := by tauto
  have htarget : compute_start_slot_at_epoch cfg attestation.data.target.epoch ≤ SL := by
    rw [hepoch]
    refine le_trans ?_ (le_trans (Nat.le_succ _) (le_trans hgate hcur))
    exact Nat.div_mul_le_self _ _
  exact update_latest_messages_stateSlotsLE _ _ _
    (store_target_checkpoint_state_stateSlotsLE cfg ext hps
      store _ hknown htarget h)

theorem notify_ptc_messages_stateSlotsLE {SL : Slot}
    {store store' : Store Root} {state : BeaconState Root}
    {attestations : List (IndexedPayloadAttestation Root)} (h : StateSlotsLE SL store)
    (hh : notify_ptc_messages cfg ext store state attestations = some store') :
    StateSlotsLE SL store' := h.of_payloadFrame (notify_ptc_messages_frame cfg ext hh)

omit [Inhabited Root] in
theorem on_payload_attestation_message_stateSlotsLE {SL : Slot}
    {store store' : Store Root} {message : PayloadAttestationMessage Root}
    {is_from_block : Bool} (h : StateSlotsLE SL store)
    (hh : on_payload_attestation_message cfg ext store message is_from_block = some store') :
    StateSlotsLE SL store' :=
  h.of_payloadFrame (on_payload_attestation_message_frame cfg ext hh)

omit [Inhabited Root] in
theorem on_execution_payload_envelope_stateSlotsLE {SL : Slot}
    {store store' : Store Root} {envelope : SignedExecutionPayloadEnvelope Root}
    {observation : EnvelopeObservation Root} (h : StateSlotsLE SL store)
    (hh : on_execution_payload_envelope ext store envelope observation = some store') :
    StateSlotsLE SL store' :=
  h.of_payloadFrame (on_execution_payload_envelope_frame ext hh)

theorem on_block_stateSlotsLE {SL : Slot}
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    {store store' : Store Root} {signed_block : SignedBeaconBlock Root}
    (hcur : get_current_slot cfg store ≤ SL) (h : StateSlotsLE SL store)
    (hh : on_block cfg ext store signed_block = some store') :
    StateSlotsLE SL store' := by
  by_cases hknown : signed_block.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · have hslot : signed_block.message.slot ≤ get_current_slot cfg store := by
      by_contra hfuture
      simp [on_block, hknown, hfuture] at hh
    simp only [on_block, if_neg hknown] at hh
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
        apply compute_pulled_up_tip_stateSlotsLE
        apply update_checkpoints_stateSlotsLE
        apply update_proposer_boost_root_stateSlotsLE
        apply record_block_timeliness_stateSlotsLE
        refine notify_ptc_messages_stateSlotsLE cfg ext ?_ hptc
        obtain ⟨hblk, hchk⟩ := h
        refine ⟨fun r hr => ?_, hchk⟩
        simp only [Function.update_apply]
        split_ifs with hrb
        · rw [hst_slot _ _ _ hst]
          exact le_trans hslot hcur
        · apply hblk
          simp only [List.mem_append, List.mem_singleton] at hr
          exact hr.resolve_right hrb

omit [LinearOrder Root] in
theorem on_tick_per_slot_stateSlotsLE {SL : Slot} (store : Store Root)
    (time : ℕ) (h : StateSlotsLE SL store) :
    StateSlotsLE SL (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact h.of_eq rfl rfl rfl rfl
      | exact update_checkpoints_stateSlotsLE _ _ _ (h.of_eq rfl rfl rfl rfl)

omit [LinearOrder Root] in
theorem on_tick_aux_stateSlotsLE {SL : Slot} (tick_slot fuel : ℕ) :
    ∀ store : Store Root, StateSlotsLE SL store →
      StateSlotsLE SL (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
    intro store h
    rw [on_tick_aux]
    split_ifs
    · exact ih _ (on_tick_per_slot_stateSlotsLE cfg _ _ h)
    · exact h

omit [LinearOrder Root] in
theorem on_tick_stateSlotsLE {SL : Slot} (store : Store Root) (time : ℕ)
    (h : StateSlotsLE SL store) : StateSlotsLE SL (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_stateSlotsLE cfg _ _
    (on_tick_aux_stateSlotsLE cfg _ _ _ h)

/-- Applying an event preserves `get_current_slot`. -/
theorem apply_event_current_slot {store store' : Store Root} {event : Event Root}
    (hh : apply_event cfg ext store event = some store') :
    get_current_slot cfg store' = get_current_slot cfg store := by
  simp only [get_current_slot, get_slots_since_genesis]
  rw [apply_event_time cfg ext hh]
  exact congrArg (fun g =>
      GENESIS_SLOT + (store.time - g) * 1000 / cfg.slot_duration_ms)
    (apply_event_storeLE cfg ext hh).2.1.symm

theorem apply_event_stateSlotsLE {SL : Slot}
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      st.slot < s → (ext.process_slots st s).slot = s)
    {store store' : Store Root} {event : Event Root}
    (hcur : get_current_slot cfg store ≤ SL) (h : StateSlotsLE SL store)
    (hh : apply_event cfg ext store event = some store') :
    StateSlotsLE SL store' := by
  cases event with
  | block b => exact on_block_stateSlotsLE cfg ext hst_slot hcur h hh
  | attestation a ifb =>
      exact on_attestation_stateSlotsLE cfg ext hps hcur h hh
  | attester_slashing s => exact on_attester_slashing_stateSlotsLE ext h hh
  | execution_payload_envelope envelope observation =>
    exact on_execution_payload_envelope_stateSlotsLE ext h hh
  | payload_attestation_message message is_from_block =>
    exact on_payload_attestation_message_stateSlotsLE cfg ext h hh

/-- One event-fold step preserves both the state-slot and clock bounds. -/
theorem apply_event_getD_stateSlotsLE {SL : Slot}
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hps : ∀ (st : BeaconState Root) (s : Slot),
      st.slot < s → (ext.process_slots st s).slot = s)
    (store : Store Root) (event : Event Root)
    (h : get_current_slot cfg store ≤ SL ∧ StateSlotsLE SL store) :
    get_current_slot cfg ((apply_event cfg ext store event).getD store) ≤ SL ∧
      StateSlotsLE SL ((apply_event cfg ext store event).getD store) := by
  cases heq : apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
      simp only [Option.getD_some]
      refine ⟨?_, ?_⟩
      · rw [apply_event_current_slot cfg ext heq]
        exact h.1
      · exact apply_event_stateSlotsLE cfg ext hst_slot hps h.1 h.2 heq

private theorem get_current_slot_get_forkchoice_store_registry
    (hdiv : 1000 ∣ cfg.slot_duration_ms) (ast : BeaconState Root)
    (ablk : SignedBeaconBlock Root) :
    get_current_slot cfg (get_forkchoice_store cfg ast ablk) = ast.slot := by
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk
      have := cfg.slot_duration_ms_pos
      omega
    · exact h
  have h1000k : 0 < 1000 * k := by omega
  simp only [get_current_slot, get_slots_since_genesis, get_forkchoice_store, GENESIS_SLOT,
    Nat.zero_add, Nat.add_sub_cancel_left]
  rw [hk, mul_assoc, Nat.mul_div_cancel_left _ (by omega : (0 : ℕ) < 1000),
    mul_comm (k * ast.slot) 1000, ← mul_assoc, Nat.mul_div_cancel_left _ h1000k]

/-- Every keyed block/checkpoint state at an honest execution store is bounded
by that store's execution-clock slot. -/
theorem Execution.stateSlotsLE (E : Execution Root)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) :
    StateSlotsLE (E.slot_at cfg n) (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgeq⟩ := hgen
  induction n with
  | zero =>
    change StateSlotsLE (E.slot_at cfg 0) E.genesis_store
    have hcur := E.store_current_slot cfg ext v 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcur
    rw [hgeq, get_current_slot_get_forkchoice_store_registry cfg hdiv] at hcur
    rw [hgeq]
    constructor
    · intro r hr
      simp only [get_forkchoice_store, List.mem_singleton] at hr
      subst r
      simpa only [get_forkchoice_store, Function.update_self] using le_of_eq hcur
    · intro c hc
      simp only [get_forkchoice_store, Finset.mem_singleton] at hc
      subst c
      simpa only [get_forkchoice_store, Function.update_self] using le_of_eq hcur
  | succ n ih =>
    change StateSlotsLE (E.slot_at cfg (n + 1))
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    have ih' : StateSlotsLE (E.slot_at cfg (n + 1)) (E.store cfg ext v n) :=
      ih.mono (E.slot_at_mono cfg (Nat.le_succ n))
    have htick : StateSlotsLE (E.slot_at cfg (n + 1))
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) :=
      on_tick_stateSlotsLE cfg _ _ ih'
    have htickgen :
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))).genesis_time =
          E.genesis_store.genesis_time := by
      rw [← (on_tick_storeLE cfg (E.store cfg ext v n) (E.time_at (n + 1))).2.1,
        E.store_genesis_time cfg ext v n]
    have hcurTick : get_current_slot cfg
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) =
        E.slot_at cfg (n + 1) := by
      rw [get_current_slot, get_slots_since_genesis, on_tick_time, htickgen,
        Execution.slot_at]
    exact (currentSlot_stateSlotsLE_foldl cfg
      (fun s e hs => apply_event_getD_stateSlotsLE cfg ext
        hec.state_transition_slot hec.process_slots_slot s e hs)
      (E.schedule v (n + 1)) _ ⟨le_of_eq hcurTick, htick⟩).2

/-- The trusted anchor state is no later than the execution clock at second
zero. -/
theorem Execution.anchor_state_slot_le (E : Execution Root)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    E.anchor_state.slot ≤ E.slot_at cfg 0 := by
  obtain ⟨ast, ablk, hgeq⟩ := hgen
  have hcur : get_current_slot cfg E.genesis_store = E.slot_at cfg 0 := by
    simp only [get_current_slot, get_slots_since_genesis, Execution.slot_at,
      Execution.time_at, Nat.add_zero]
  rw [hgeq, get_current_slot_get_forkchoice_store_registry cfg hdiv] at hcur
  rw [Execution.anchor_state, hgeq]
  simpa only [get_forkchoice_store, Function.update_self] using le_of_eq hcur

omit [LinearOrder Root] [Inhabited Root] in
/-- Activity constancy inside the execution's explicit verification horizon.
The former compatibility theorem recovered an all-epoch statement by combining
an unbounded `ℕ` clock with an impossible finite clock bound; callers must now
supply the two genuine horizon guards. -/
theorem StaticValidatorSet.registry_activity_constant
    {cfg : Config} {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    (i : ValidatorIndex) (e e' : Epoch)
    (he : e < E.verification_horizon)
    (he' : e' < E.verification_horizon) :
      is_active_validator (E.registry.getD i default) e =
        is_active_validator (E.registry.getD i default) e' :=
  hsv.activity_constant i e e' he he'

/-! ## Corollary: total active balance is anchored

`get_total_active_balance` reads validator activity at the state's *own*
`get_current_epoch`; two states on the same registry with epoch-independent
activity (the static-set idealization) therefore have equal total active
balance, even at different slots. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Two states on the same registry whose validators have the same activity at
their respective current epochs agree on `get_total_active_balance`. -/
theorem get_total_active_balance_congr {st st' : BeaconState Root}
    (hval : st.validators = st'.validators)
    (hact : ∀ i : ValidatorIndex,
      is_active_validator (st.validators.getD i default) (get_current_epoch cfg st) =
        is_active_validator (st'.validators.getD i default) (get_current_epoch cfg st')) :
    get_total_active_balance cfg st = get_total_active_balance cfg st' := by
  have hidx : get_active_validator_indices st (get_current_epoch cfg st)
      = get_active_validator_indices st' (get_current_epoch cfg st') := by
    unfold get_active_validator_indices
    rw [hval]
    apply List.filter_congr
    intro i _
    have hi := hact i
    rw [hval] at hi
    exact hi
  simp only [get_total_active_balance, get_total_balance, hidx, hval]

/-- Every block state an honest node's store carries has the anchor's total
active balance (`E.total_active`). -/
theorem Execution.block_states_total_active_balance (E : Execution Root)
    (hsv : StaticValidatorSet cfg E) (hec : ExternalsCoherence cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (r : Root)
    (hr : r ∈ (E.store cfg ext v n).block_roots)
    (hn : E.WithinHorizon cfg n)
    (hdiv : 1000 ∣ cfg.slot_duration_ms := by assumption)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
        exact ⟨_, _, by assumption⟩) :
    get_total_active_balance cfg ((E.store cfg ext v n).block_states r) =
      get_total_active_balance cfg E.anchor_state := by
  have hrc := (E.registryConstant cfg ext hec hgen v hv n).1 r hr
  have hslot := (E.stateSlotsLE cfg ext hdiv hec hgen v n).1 r hr
  have hanchor := E.anchor_state_slot_le cfg hdiv hgen
  have hanchorN : E.anchor_state.slot ≤ E.slot_at cfg n :=
    le_trans hanchor (E.slot_at_mono cfg (Nat.zero_le n))
  apply get_total_active_balance_congr cfg
  · rw [hrc]
    rfl
  · intro i
    rw [hrc]
    simpa only [get_current_epoch] using
      hsv.activity_constant_of_slot_le (cfg := cfg) hslot hanchorN hn.2.2 hn.2.2

/-- Every cached checkpoint state an honest node's store carries has the
anchor's total active balance (`E.total_active`). -/
theorem Execution.checkpoint_states_total_active_balance (E : Execution Root)
    (hsv : StaticValidatorSet cfg E) (hec : ExternalsCoherence cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (c : Checkpoint Root)
    (hc : c ∈ (E.store cfg ext v n).checkpoint_state_keys)
    (hn : E.WithinHorizon cfg n)
    (hdiv : 1000 ∣ cfg.slot_duration_ms := by assumption)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
        exact ⟨_, _, by assumption⟩) :
    get_total_active_balance cfg ((E.store cfg ext v n).checkpoint_states c) =
      get_total_active_balance cfg E.anchor_state := by
  have hrc := (E.registryConstant cfg ext hec hgen v hv n).2 c hc
  have hslot := (E.stateSlotsLE cfg ext hdiv hec hgen v n).2 c hc
  have hanchor := E.anchor_state_slot_le cfg hdiv hgen
  have hanchorN : E.anchor_state.slot ≤ E.slot_at cfg n :=
    le_trans hanchor (E.slot_at_mono cfg (Nat.zero_le n))
  apply get_total_active_balance_congr cfg
  · rw [hrc]
    rfl
  · intro i
    rw [hrc]
    simpa only [get_current_epoch] using
      hsv.activity_constant_of_slot_le (cfg := cfg) hslot hanchorN hn.2.2 hn.2.2

/-! ## Derived: post-floor estimate domination -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The exact post-`//100` inequality consumed by the confirmation arithmetic.
It is not a probabilistic premise: ordinary estimate soundness plus phase0
effective-balance quantization prove it.  Keeping the projection-shaped theorem
name preserves existing dot-notation call sites. -/
theorem ByzantineBound.estimate_dominates {cfg : Config} {E : Execution Root}
    (hbb : ByzantineBound cfg E) :
    ∀ a b : Slot, E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
      E.weight (E.span_committee a b) ≤
      100 * (estimate_committee_weight_between_slots cfg (E.total_active cfg) a b / 100) :=
  fun a b ha hb => estimate_floor_dominates cfg E hbb _
    (hbb.estimate_sound a b ha hb)

/-! ## Derived: the old `span_bound`

`ByzantineBound`'s primitive probabilistic pair is
`{span_fraction, estimate_sound}`. The old `span_bound` field
(`byz(span) ≤ (estimate // 100) * CONFIRMATION_BYZANTINE_THRESHOLD`) is exactly
`span_fraction` (`100·byz ≤ C·W`) composed with `estimate_dominates`
(`W ≤ 100·(estimate // 100)`): `100·byz ≤ C·W ≤ C·100·(estimate // 100) =
100·((estimate // 100)·C)`, cancel `100`. Kept as a `ByzantineBound.span_bound`
theorem so the existing `hbb.span_bound a b` dot-notation call sites
(`Discount`, `HonestWeight`, `QuorumAccounting`) keep working — `cfg`/`E` stay
*implicit*, matching the old field projection so the trailing `_ _` bind
`a`/`b`. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The Byzantine committee weight of a span is within
the budget `compute_adversarial_weight` allots before its equivocation discount —
the old `span_bound` field, obtained from `span_fraction` composed with the
derived `estimate_dominates` (`100·byz ≤ C·W ≤ 100·((estimate // 100)·C)`,
cancel `100`). -/
theorem ByzantineBound.span_bound {cfg : Config} {E : Execution Root}
    (hbb : ByzantineBound cfg E) :
    ∀ a b : Slot,
      E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
      E.weight ((E.span_committee a b).filter (fun i => i ∉ E.honest)) ≤
        estimate_committee_weight_between_slots cfg (E.total_active cfg) a b / 100 *
          cfg.confirmation_byzantine_threshold := by
  intro a b ha hb
  have h100 : 0 < 100 := by omega
  have h3 : 100 * E.weight ((E.span_committee a b).filter (fun i => i ∉ E.honest))
      ≤ 100 * (cfg.confirmation_byzantine_threshold *
          (estimate_committee_weight_between_slots cfg (E.total_active cfg) a b / 100)) := by
    calc 100 * E.weight ((E.span_committee a b).filter (fun i => i ∉ E.honest))
        ≤ cfg.confirmation_byzantine_threshold * E.weight (E.span_committee a b) :=
          hbb.span_fraction a b ha hb
      _ ≤ cfg.confirmation_byzantine_threshold *
            (100 * (estimate_committee_weight_between_slots cfg (E.total_active cfg) a b / 100)) :=
          Nat.mul_le_mul le_rfl (hbb.estimate_dominates a b ha hb)
      _ = 100 * (cfg.confirmation_byzantine_threshold *
            (estimate_committee_weight_between_slots cfg (E.total_active cfg) a b / 100)) :=
          mul_left_comm _ _ _
  have h4 := Nat.le_of_mul_le_mul_left h3 h100
  rw [Nat.mul_comm]
  exact h4

end FastConfirmation.Spec

end
