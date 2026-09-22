import FastConfirmation.Spec.Proof.Registry

/-!
The totalized block-state map retains `default` outside its keyed domain.
This is a consequence of initialization and handlers. Together with the
default-state validity contract, it turns a successful indexed check at a
block-state read into a keyed, reachable validation state.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

def UnknownBlockStatesDefault (store : Store Root) : Prop :=
  ∀ root, root ∉ store.block_roots → store.block_states root = default

theorem UnknownBlockStatesDefault.of_eq {store store' : Store Root}
    (h : UnknownBlockStatesDefault store)
    (hroots : store'.block_roots = store.block_roots)
    (hstates : store'.block_states = store.block_states) :
    UnknownBlockStatesDefault store' := by
  intro root hroot
  rw [hroots] at hroot
  rw [hstates]
  exact h root hroot

theorem unknownBlockStatesDefault_foldl {α : Type*}
    {f : Store Root → α → Store Root}
    (hf : ∀ store event, UnknownBlockStatesDefault store →
      UnknownBlockStatesDefault (f store event))
    (events : List α) (store : Store Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (events.foldl f store) := by
  induction events generalizing store with
  | nil => exact h
  | cons event events ih => exact ih _ (hf store event h)

theorem update_checkpoints_unknownBlockStatesDefault (store : Store Root)
    (justified finalized : Checkpoint Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (update_checkpoints store justified finalized) :=
  h.of_eq (by simp) (by simp)

theorem update_unrealized_checkpoints_unknownBlockStatesDefault (store : Store Root)
    (justified finalized : Checkpoint Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (update_unrealized_checkpoints store justified finalized) :=
  h.of_eq (by simp) (by simp)

theorem record_block_timeliness_unknownBlockStatesDefault (store : Store Root)
    (root : Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (record_block_timeliness cfg store root) :=
  h.of_eq rfl rfl

theorem update_proposer_boost_root_unknownBlockStatesDefault (store : Store Root)
    (head root : Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (update_proposer_boost_root cfg store head root) := by
  refine h.of_eq ?_ ?_ <;>
    (simp only [update_proposer_boost_root]; split_ifs <;> rfl)

theorem compute_pulled_up_tip_unknownBlockStatesDefault (store : Store Root)
    (root : Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (compute_pulled_up_tip cfg ext store root) := by
  refine h.of_eq ?_ ?_ <;>
    (simp only [compute_pulled_up_tip]; split_ifs <;> simp)

theorem update_latest_messages_unknownBlockStatesDefault (store : Store Root)
    (indices : List ValidatorIndex) (attestation : Attestation Root)
    (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (update_latest_messages store indices attestation) := by
  simp only [update_latest_messages]
  refine unknownBlockStatesDefault_foldl (fun current index hcurrent => ?_) _ store h
  refine hcurrent.of_eq ?_ ?_ <;>
    (dsimp only; cases hmessage : current.latest_messages index <;> split_ifs <;> rfl)

theorem store_target_checkpoint_state_unknownBlockStatesDefault (store : Store Root)
    (target : Checkpoint Root) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (store_target_checkpoint_state cfg ext store target) := by
  refine h.of_eq ?_ ?_ <;>
    (simp only [store_target_checkpoint_state]; split_ifs <;> rfl)

theorem on_attestation_unknownBlockStatesDefault {store store' : Store Root}
    {attestation : Attestation Root} {fromBlock : Bool}
    (h : UnknownBlockStatesDefault store)
    (hsuccess : on_attestation cfg ext store attestation fromBlock = some store') :
    UnknownBlockStatesDefault store' := by
  simp only [on_attestation] at hsuccess
  split_ifs at hsuccess
  cases hsuccess
  exact update_latest_messages_unknownBlockStatesDefault _ _ _
    (store_target_checkpoint_state_unknownBlockStatesDefault cfg ext _ _ h)

theorem on_attester_slashing_unknownBlockStatesDefault {store store' : Store Root}
    {slashing : AttesterSlashing Root} (h : UnknownBlockStatesDefault store)
    (hsuccess : on_attester_slashing ext store slashing = some store') :
    UnknownBlockStatesDefault store' := by
  simp only [on_attester_slashing] at hsuccess
  split_ifs at hsuccess
  cases hsuccess
  exact h.of_eq rfl rfl

theorem on_block_unknownBlockStatesDefault {store store' : Store Root}
    {block : SignedBeaconBlock Root} (h : UnknownBlockStatesDefault store)
    (hsuccess : on_block cfg ext store block = some store') :
    UnknownBlockStatesDefault store' := by
  by_cases hknown : block.root ∈ store.block_roots
  · simp [on_block, hknown] at hsuccess
    cases hsuccess
    exact h
  · simp only [on_block, if_neg hknown] at hsuccess
    split_ifs at hsuccess with hparent hslot hfinalized hcheckpoint
    all_goals try contradiction
    cases htransition : ext.state_transition
        (store.block_states block.message.parent_root) block with
    | none => rw [htransition] at hsuccess; cases hsuccess
    | some state =>
      rw [htransition] at hsuccess
      cases hsuccess
      apply compute_pulled_up_tip_unknownBlockStatesDefault
      apply update_checkpoints_unknownBlockStatesDefault
      apply update_proposer_boost_root_unknownBlockStatesDefault
      apply record_block_timeliness_unknownBlockStatesDefault
      intro root hroot
      simp only [List.mem_append, List.mem_singleton, not_or] at hroot
      simp only [Function.update_apply]
      rw [if_neg hroot.2]
      exact h root hroot.1

theorem on_tick_per_slot_unknownBlockStatesDefault (store : Store Root)
    (time : Nat) (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact h.of_eq rfl rfl
      | exact update_checkpoints_unknownBlockStatesDefault _ _ _ (h.of_eq rfl rfl)

theorem on_tick_aux_unknownBlockStatesDefault (tickSlot fuel : Nat) :
    ∀ store : Store Root, UnknownBlockStatesDefault store →
      UnknownBlockStatesDefault (on_tick_aux cfg tickSlot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
    intro store h
    rw [on_tick_aux]
    split_ifs
    · exact ih _ (on_tick_per_slot_unknownBlockStatesDefault cfg _ _ h)
    · exact h

theorem on_tick_unknownBlockStatesDefault (store : Store Root) (time : Nat)
    (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_unknownBlockStatesDefault cfg _ _
    (on_tick_aux_unknownBlockStatesDefault cfg _ _ _ h)

theorem apply_event_unknownBlockStatesDefault (store : Store Root) (event : Event Root)
    (h : UnknownBlockStatesDefault store) :
    UnknownBlockStatesDefault ((apply_event cfg ext store event).getD store) := by
  cases event with
  | block block =>
    simp only [apply_event]
    cases hresult : on_block cfg ext store block with
    | none => exact h
    | some result => exact on_block_unknownBlockStatesDefault cfg ext h hresult
  | attestation attestation fromBlock =>
    simp only [apply_event]
    cases hresult : on_attestation cfg ext store attestation fromBlock with
    | none => exact h
    | some result => exact on_attestation_unknownBlockStatesDefault cfg ext h hresult
  | attester_slashing slashing =>
    simp only [apply_event]
    cases hresult : on_attester_slashing ext store slashing with
    | none => exact h
    | some result => exact on_attester_slashing_unknownBlockStatesDefault ext h hresult

theorem get_forkchoice_store_unknownBlockStatesDefault
    (state : BeaconState Root) (block : SignedBeaconBlock Root) :
    UnknownBlockStatesDefault (get_forkchoice_store cfg state block) := by
  intro root hroot
  simp only [get_forkchoice_store, List.mem_singleton] at hroot ⊢
  simp [Function.update_apply, hroot]

theorem Execution.unknownBlockStatesDefault_store {E : Execution Root}
    (hgen : ∃ state block, E.genesis_store = get_forkchoice_store cfg state block)
    (node : ValidatorIndex) (second : Nat) :
    UnknownBlockStatesDefault (E.store cfg ext node second) := by
  induction second with
  | zero =>
    obtain ⟨state, block, hgen⟩ := hgen
    change UnknownBlockStatesDefault E.genesis_store
    rw [hgen]
    exact get_forkchoice_store_unknownBlockStatesDefault cfg state block
  | succ second ih =>
    exact unknownBlockStatesDefault_foldl
      (apply_event_unknownBlockStatesDefault cfg ext) _ _
      (on_tick_unknownBlockStatesDefault cfg _ _ ih)

theorem Execution.ScheduledEventPrefix.unknownBlockStatesDefault
    {E : Execution Root} (p : E.ScheduledEventPrefix)
    (hgen : ∃ state block, E.genesis_store = get_forkchoice_store cfg state block) :
    UnknownBlockStatesDefault (p.store cfg ext) :=
  unknownBlockStatesDefault_foldl (apply_event_unknownBlockStatesDefault cfg ext) _ _
    (on_tick_unknownBlockStatesDefault cfg _ _
      (E.unknownBlockStatesDefault_store cfg ext hgen p.node p.previousSecond))

end FastConfirmation.Spec
