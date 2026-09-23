module
public import FastConfirmation.Spec.Model.FFGStateSemantics
public import FastConfirmation.Spec.Model.PayloadEffects
public import FastConfirmation.Spec.Proof.ModelFacts

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Spec / Proof / FFGStateTrajectory

Handler induction for the block-local FFG projection.  The model-level
coherence record states only genesis and successful-transition equations.
This file proves that every root in every reachable store carries the exact
projected post-state and eager-pull-up values, including the value written to
`unrealized_justifications`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E : Execution Root} {anchor : Checkpoint Root}

/-- The four exact equations carried by the finite block-state dictionary.
This component is separated because `on_block` installs the new block state
before `compute_pulled_up_tip` installs its unrealized-map entry. -/
structure FFGBlockStateProjection (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop where
  block_state_gj : ∀ r ∈ store.block_roots,
    (store.block_states r).current_justified_checkpoint = S.GJ r
  block_state_gf : ∀ r ∈ store.block_roots,
    (store.block_states r).finalized_checkpoint = S.GF r
  pulled_up_gu : ∀ r ∈ store.block_roots,
    (ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint = S.GU r
  pulled_up_guf : ∀ r ∈ store.block_roots,
    (ext.process_justification_and_finalization
      (store.block_states r)).finalized_checkpoint = S.GUF r

/-- Exact correspondence between a fork-choice store and the block-local FFG
projection at every root in the store's finite block domain. -/
structure FFGStoreProjection (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop where
  block_state_gj : ∀ r ∈ store.block_roots,
    (store.block_states r).current_justified_checkpoint = S.GJ r
  block_state_gf : ∀ r ∈ store.block_roots,
    (store.block_states r).finalized_checkpoint = S.GF r
  pulled_up_gu : ∀ r ∈ store.block_roots,
    (ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint = S.GU r
  pulled_up_guf : ∀ r ∈ store.block_roots,
    (ext.process_justification_and_finalization
      (store.block_states r)).finalized_checkpoint = S.GUF r
  unrealized_justification : ∀ r ∈ store.block_roots,
    store.unrealized_justifications r = S.GU r

namespace FFGStoreProjection

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}


/-- Transport the projection across a store operation that leaves its block
domain, block-state map, and per-root unrealized-justification map equal. -/
theorem of_eq {store store' : Store Root}
    (h : FFGStoreProjection cfg ext S store)
    (hroots : store'.block_roots = store.block_roots)
    (hstates : store'.block_states = store.block_states)
    (hunrealized : store'.unrealized_justifications =
      store.unrealized_justifications) :
    FFGStoreProjection cfg ext S store' := by
  constructor <;> intro r hr
  · rw [hroots] at hr
    rw [hstates]
    exact h.block_state_gj r hr
  · rw [hroots] at hr
    rw [hstates]
    exact h.block_state_gf r hr
  · rw [hroots] at hr
    rw [hstates]
    exact h.pulled_up_gu r hr
  · rw [hroots] at hr
    rw [hstates]
    exact h.pulled_up_guf r hr
  · rw [hroots] at hr
    rw [hunrealized]
    exact h.unrealized_justification r hr

end FFGStoreProjection

namespace FFGBlockStateProjection

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}

/-- Transport block-state equations across an operation preserving the block
domain and block-state map. -/
theorem of_eq {store store' : Store Root}
    (h : FFGBlockStateProjection cfg ext S store)
    (hroots : store'.block_roots = store.block_roots)
    (hstates : store'.block_states = store.block_states) :
    FFGBlockStateProjection cfg ext S store' := by
  constructor <;> intro r hr
  all_goals
    rw [hroots] at hr
    rw [hstates]
  · exact h.block_state_gj r hr
  · exact h.block_state_gf r hr
  · exact h.pulled_up_gu r hr
  · exact h.pulled_up_guf r hr

end FFGBlockStateProjection

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}

/-! ## Block-identity-preserving helpers -/

theorem update_checkpoints_ffgBlockStateProjection
    (store : Store Root) (jc fc : Checkpoint Root)
    (h : FFGBlockStateProjection cfg ext S store) :
    FFGBlockStateProjection cfg ext S (update_checkpoints store jc fc) := by
  apply h.of_eq <;>
    (simp only [update_checkpoints]; split_ifs <;> rfl)

theorem record_block_timeliness_ffgBlockStateProjection
    (store : Store Root) (r : Root)
    (h : FFGBlockStateProjection cfg ext S store) :
    FFGBlockStateProjection cfg ext S
      (record_block_timeliness cfg store r) :=
  h.of_eq rfl rfl

theorem update_proposer_boost_root_ffgBlockStateProjection
    (store : Store Root) (head r : Root)
    (h : FFGBlockStateProjection cfg ext S store) :
    FFGBlockStateProjection cfg ext S
      (update_proposer_boost_root cfg store head r) := by
  apply h.of_eq <;>
    (simp only [update_proposer_boost_root]; split_ifs <;> rfl)

theorem update_checkpoints_ffgStoreProjection
    (store : Store Root) (jc fc : Checkpoint Root)
    (h : FFGStoreProjection cfg ext S store) :
    FFGStoreProjection cfg ext S (update_checkpoints store jc fc) := by
  apply h.of_eq <;>
    (simp only [update_checkpoints]; split_ifs <;> rfl)




theorem store_target_checkpoint_state_ffgStoreProjection
    (store : Store Root) (target : Checkpoint Root)
    (h : FFGStoreProjection cfg ext S store) :
    FFGStoreProjection cfg ext S
      (store_target_checkpoint_state cfg ext store target) := by
  apply h.of_eq <;>
    (simp only [store_target_checkpoint_state]; split_ifs <;> rfl)

theorem update_latest_messages_ffgStoreProjection
    (store : Store Root) (indices : List ValidatorIndex)
    (a : Attestation Root) (h : FFGStoreProjection cfg ext S store) :
    FFGStoreProjection cfg ext S (update_latest_messages store indices a) := by
  simp only [update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h.of_eq rfl rfl rfl

/-- Eager pull-up turns exact block-state equations plus exact old map entries
away from the updated root into a complete store projection.  This is the
intermediate state used by `on_block`: the new root's map value need not be
correct until this helper performs its mandated write. -/
theorem compute_pulled_up_tip_ffgStoreProjection_of_blockState
    (store : Store Root) (r : Root)
    (hstate : FFGBlockStateProjection cfg ext S store)
    (hmap : ∀ x ∈ store.block_roots, x ≠ r →
      store.unrealized_justifications x = S.GU x)
    (hr : r ∈ store.block_roots) :
    FFGStoreProjection cfg ext S
      (compute_pulled_up_tip cfg ext store r) := by
  have hroots : (compute_pulled_up_tip cfg ext store r).block_roots =
      store.block_roots := by
    simp only [compute_pulled_up_tip]
    split_ifs <;> simp only [update_checkpoints, update_unrealized_checkpoints] <;>
      split_ifs <;> rfl
  have hstates : (compute_pulled_up_tip cfg ext store r).block_states =
      store.block_states := by
    simp only [compute_pulled_up_tip]
    split_ifs <;> simp only [update_checkpoints, update_unrealized_checkpoints] <;>
      split_ifs <;> rfl
  constructor <;> intro x hx
  · rw [hroots] at hx
    rw [hstates]
    exact hstate.block_state_gj x hx
  · rw [hroots] at hx
    rw [hstates]
    exact hstate.block_state_gf x hx
  · rw [hroots] at hx
    rw [hstates]
    exact hstate.pulled_up_gu x hx
  · rw [hroots] at hx
    rw [hstates]
    exact hstate.pulled_up_guf x hx
  · rw [hroots] at hx
    have hunrealized :
        (compute_pulled_up_tip cfg ext store r).unrealized_justifications =
          Function.update store.unrealized_justifications r
            (ext.process_justification_and_finalization
              (store.block_states r)).current_justified_checkpoint := by
      simp only [compute_pulled_up_tip]
      split_ifs <;>
        simp only [update_checkpoints, update_unrealized_checkpoints] <;>
        split_ifs <;> rfl
    rw [hunrealized, Function.update_apply]
    split_ifs with hxr
    · subst x
      exact hstate.pulled_up_gu r hr
    · exact hmap x hx hxr


/-! ## Event handlers -/

/-- A successful scheduled block handler preserves the exact projection. -/
theorem on_block_ffgStoreProjection
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hscheduled : ∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n)
    (h : FFGStoreProjection cfg ext S store)
    (hh : on_block cfg ext store sb = some store') :
    FFGStoreProjection cfg ext S store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    cases hst : ext.state_transition
        (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      let added : Store Root :=
        { store with
          block_roots := store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root state
          payload_timeliness_vote := Function.update store.payload_timeliness_vote
            sb.root (some (List.replicate cfg.ptc_size none))
          payload_data_availability_vote := Function.update store.payload_data_availability_vote
            sb.root (some (List.replicate cfg.ptc_size none)) }
      change (match notify_ptc_messages cfg ext added state sb.message.payload_attestations with
        | none => none
        | some notified => some (compute_pulled_up_tip cfg ext
            (update_checkpoints
              (update_proposer_boost_root cfg
                (record_block_timeliness cfg notified sb.root)
                (get_head cfg store).root sb.root)
              state.current_justified_checkpoint state.finalized_checkpoint) sb.root)) =
          some store' at hh
      cases hn : notify_ptc_messages cfg ext added state sb.message.payload_attestations with
      | none => rw [hn] at hh; cases hh
      | some notified =>
        rw [hn] at hh
        cases hh
        have hf := notify_ptc_messages_frame cfg ext hn
        apply compute_pulled_up_tip_ffgStoreProjection_of_blockState
        · apply update_checkpoints_ffgBlockStateProjection
          apply update_proposer_boost_root_ffgBlockStateProjection
          apply record_block_timeliness_ffgBlockStateProjection
          refine FFGBlockStateProjection.of_eq ?_ hf.block_roots hf.block_states
          constructor <;> intro r hr
          · simp only [added, Function.update_apply]
            split_ifs with hrs
            · subst r
              exact hcoh.transition_gj _ _ _ hscheduled hst
            · apply h.block_state_gj
              simp only [added, List.mem_append, List.mem_singleton] at hr
              exact hr.resolve_right hrs
          · simp only [added, Function.update_apply]
            split_ifs with hrs
            · subst r
              exact hcoh.transition_gf _ _ _ hscheduled hst
            · apply h.block_state_gf
              simp only [added, List.mem_append, List.mem_singleton] at hr
              exact hr.resolve_right hrs
          · simp only [added, Function.update_apply]
            split_ifs with hrs
            · subst r
              exact hcoh.transition_gu _ _ _ hscheduled hst
            · apply h.pulled_up_gu
              simp only [added, List.mem_append, List.mem_singleton] at hr
              exact hr.resolve_right hrs
          · simp only [added, Function.update_apply]
            split_ifs with hrs
            · subst r
              exact hcoh.transition_guf _ _ _ hscheduled hst
            · apply h.pulled_up_guf
              simp only [added, List.mem_append, List.mem_singleton] at hr
              exact hr.resolve_right hrs
        · intro r hr hrs
          simp only [update_checkpoints, update_proposer_boost_root,
            record_block_timeliness] at hr ⊢
          split_ifs at hr ⊢
          all_goals
            rw [hf.block_roots] at hr
            rw [hf.unrealized_justifications]
            apply h.unrealized_justification
            simp only [added, List.mem_append, List.mem_singleton] at hr
            exact hr.resolve_right hrs
        · simp only [update_checkpoints, update_proposer_boost_root,
            record_block_timeliness]
          split_ifs
          all_goals
            rw [hf.block_roots]
            exact List.mem_append_right _ (List.mem_singleton_self _)

theorem on_attestation_ffgStoreProjection
    {store store' : Store Root} {a : Attestation Root} {is_from_block : Bool}
    (h : FFGStoreProjection cfg ext S store)
    (hh : on_attestation cfg ext store a is_from_block = some store') :
    FFGStoreProjection cfg ext S store' := by
  simp only [on_attestation] at hh
  split_ifs at hh
  cases hh
  apply update_latest_messages_ffgStoreProjection
  exact store_target_checkpoint_state_ffgStoreProjection _ _ h

theorem on_attester_slashing_ffgStoreProjection
    {store store' : Store Root} {sl : AttesterSlashing Root}
    (h : FFGStoreProjection cfg ext S store)
    (hh : on_attester_slashing ext store sl = some store') :
    FFGStoreProjection cfg ext S store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl

/-! ## Ticks and execution induction -/

theorem on_tick_per_slot_ffgStoreProjection
    (store : Store Root) (time : ℕ)
    (h : FFGStoreProjection cfg ext S store) :
    FFGStoreProjection cfg ext S (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
    | exact h.of_eq rfl rfl rfl
    | exact update_checkpoints_ffgStoreProjection _ _ _
        (h.of_eq rfl rfl rfl)

theorem on_tick_aux_ffgStoreProjection (tick_slot fuel : ℕ) :
    ∀ store : Store Root, FFGStoreProjection cfg ext S store →
      FFGStoreProjection cfg ext S (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
      intro store h
      rw [on_tick_aux]
      split_ifs
      · exact ih _ (on_tick_per_slot_ffgStoreProjection _ _ h)
      · exact h

theorem on_tick_ffgStoreProjection (store : Store Root) (time : ℕ)
    (h : FFGStoreProjection cfg ext S store) :
    FFGStoreProjection cfg ext S (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_ffgStoreProjection _ _
    (on_tick_aux_ffgStoreProjection _ _ _ h)

theorem apply_event_getD_ffgStoreProjection
    (hcoh : FFGTransitionCoherence cfg ext S)
    (store : Store Root) (event : Event Root)
    (hscheduled : event ∈ E.schedule w n)
    (h : FFGStoreProjection cfg ext S store) :
    FFGStoreProjection cfg ext S
      ((apply_event cfg ext store event).getD store) := by
  cases heq : apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
    simp only [Option.getD_some]
    cases event with
    | block sb =>
        exact on_block_ffgStoreProjection hcoh
          ⟨w, n, hscheduled⟩ h heq
    | attestation a ifb =>
        exact on_attestation_ffgStoreProjection h heq
    | attester_slashing sl =>
        exact on_attester_slashing_ffgStoreProjection h heq
    | execution_payload_envelope envelope observation =>
        have hf := on_execution_payload_envelope_frame ext heq
        exact h.of_eq hf.block_roots hf.block_states hf.unrealized_justifications
    | payload_attestation_message message ifb =>
        have hf := on_payload_attestation_message_frame cfg ext heq
        exact h.of_eq hf.block_roots hf.block_states hf.unrealized_justifications

namespace Execution

private theorem ffgStoreProjection_foldl
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ) :
    ∀ (events : List (Event Root))
      (_hevents : events ⊆ E.schedule w n)
      (store : Store Root),
      FFGStoreProjection cfg ext S store →
      FFGStoreProjection cfg ext S
        (events.foldl
          (fun st event => (apply_event cfg ext st event).getD st) store) := by
  intro events
  induction events with
  | nil => intro _ store h; exact h
  | cons event rest ih =>
      intro hevents store h
      rw [List.foldl_cons]
      apply ih
      · exact fun x hx => hevents (List.mem_cons_of_mem _ hx)
      · exact apply_event_getD_ffgStoreProjection hcoh store event
          (hevents (List.mem_cons_self)) h

/-- Every reachable execution store has the exact FFG projection. -/
theorem ffgStoreProjection
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ) :
    FFGStoreProjection cfg ext S (E.store cfg ext w n) := by
  induction n with
  | zero =>
      change FFGStoreProjection cfg ext S E.genesis_store
      exact ⟨hcoh.genesis_gj, hcoh.genesis_gf,
        hcoh.genesis_gu, hcoh.genesis_guf,
        hcoh.genesis_unrealized_justification⟩
  | succ n ih =>
      change FFGStoreProjection cfg ext S
        ((E.schedule w (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1))))
      apply ffgStoreProjection_foldl hcoh w (n + 1)
        (E.schedule w (n + 1)) (List.Subset.refl _)
      exact on_tick_ffgStoreProjection _ _ ih





/-- Exact per-root unrealized-justification map in every reachable store. -/
theorem unrealized_justification_eq
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ)
    {r : Root} (hr : r ∈ (E.store cfg ext w n).block_roots) :
    (E.store cfg ext w n).unrealized_justifications r = S.GU r :=
  (E.ffgStoreProjection hcoh w n).unrealized_justification r hr


end Execution

end FastConfirmation.Spec

end
