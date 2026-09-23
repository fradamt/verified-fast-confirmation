module
public import FastConfirmation.Spec.Model.FFGStateSemantics
public import FastConfirmation.Spec.Model.PayloadEffects
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Spec / Proof / AcceptedFFGStateTrajectory

Handler induction for the accepted block-local FFG projection at exact
per-second schedule prefixes.  The semantic state and its coherence are fixed
before the prefix.  Successful block events construct an
`Execution.AcceptedBlockTransition` at their exact list index; rejected
events leave the projection unchanged.  This file does not model delayed
inboxes or arbitrary global action traces.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : AcceptedChainFFGState cfg ext E anchor}

/-- The four exact block-state equations, separated from the per-root
unrealized-justification map while `on_block` installs a root. -/
structure AcceptedFFGBlockStateProjection
    (S : AcceptedChainFFGState cfg ext E anchor)
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

/-- Exact accepted-state projection at every root in one concrete store. -/
structure AcceptedFFGStoreProjection
    (S : AcceptedChainFFGState cfg ext E anchor)
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

namespace AcceptedFFGStoreProjection


theorem of_eq {store store' : Store Root}
    (h : AcceptedFFGStoreProjection S store)
    (hroots : store'.block_roots = store.block_roots)
    (hstates : store'.block_states = store.block_states)
    (hunrealized : store'.unrealized_justifications =
      store.unrealized_justifications) :
    AcceptedFFGStoreProjection S store' := by
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

end AcceptedFFGStoreProjection

namespace AcceptedFFGBlockStateProjection

theorem of_eq {store store' : Store Root}
    (h : AcceptedFFGBlockStateProjection S store)
    (hroots : store'.block_roots = store.block_roots)
    (hstates : store'.block_states = store.block_states) :
    AcceptedFFGBlockStateProjection S store' := by
  constructor <;> intro r hr
  all_goals
    rw [hroots] at hr
    rw [hstates]
  · exact h.block_state_gj r hr
  · exact h.block_state_gf r hr
  · exact h.pulled_up_gu r hr
  · exact h.pulled_up_guf r hr

end AcceptedFFGBlockStateProjection

/-! ## Block-identity-preserving helpers -/

theorem update_checkpoints_acceptedFFGBlockStateProjection
    (store : Store Root) (jc fc : Checkpoint Root)
    (h : AcceptedFFGBlockStateProjection S store) :
    AcceptedFFGBlockStateProjection S
      (update_checkpoints store jc fc) := by
  apply h.of_eq <;>
    (simp only [update_checkpoints]; split_ifs <;> rfl)

theorem record_block_timeliness_acceptedFFGBlockStateProjection
    (store : Store Root) (r : Root)
    (h : AcceptedFFGBlockStateProjection S store) :
    AcceptedFFGBlockStateProjection S
      (record_block_timeliness cfg store r) :=
  h.of_eq rfl rfl

theorem update_proposer_boost_root_acceptedFFGBlockStateProjection
    (store : Store Root) (head r : Root)
    (h : AcceptedFFGBlockStateProjection S store) :
    AcceptedFFGBlockStateProjection S
      (update_proposer_boost_root cfg store head r) := by
  apply h.of_eq <;>
    (simp only [update_proposer_boost_root]; split_ifs <;> rfl)

theorem update_checkpoints_acceptedFFGStoreProjection
    (store : Store Root) (jc fc : Checkpoint Root)
    (h : AcceptedFFGStoreProjection S store) :
    AcceptedFFGStoreProjection S (update_checkpoints store jc fc) := by
  apply h.of_eq <;>
    (simp only [update_checkpoints]; split_ifs <;> rfl)




theorem store_target_checkpoint_state_acceptedFFGStoreProjection
    (store : Store Root) (target : Checkpoint Root)
    (h : AcceptedFFGStoreProjection S store) :
    AcceptedFFGStoreProjection S
      (store_target_checkpoint_state cfg ext store target) := by
  apply h.of_eq <;>
    (simp only [store_target_checkpoint_state]; split_ifs <;> rfl)

theorem update_latest_messages_acceptedFFGStoreProjection
    (store : Store Root) (indices : List ValidatorIndex)
    (a : Attestation Root) (h : AcceptedFFGStoreProjection S store) :
    AcceptedFFGStoreProjection S
      (update_latest_messages store indices a) := by
  simp only [update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h.of_eq rfl rfl rfl

theorem compute_pulled_up_tip_acceptedFFGStoreProjection_of_blockState
    (store : Store Root) (r : Root)
    (hstate : AcceptedFFGBlockStateProjection S store)
    (hmap : ∀ x ∈ store.block_roots, x ≠ r →
      store.unrealized_justifications x = S.GU x)
    (hr : r ∈ store.block_roots) :
    AcceptedFFGStoreProjection S
      (compute_pulled_up_tip cfg ext store r) := by
  have hroots : (compute_pulled_up_tip cfg ext store r).block_roots =
      store.block_roots := by
    simp only [compute_pulled_up_tip]
    split_ifs <;>
      simp only [update_checkpoints, update_unrealized_checkpoints] <;>
      split_ifs <;> rfl
  have hstates : (compute_pulled_up_tip cfg ext store r).block_states =
      store.block_states := by
    simp only [compute_pulled_up_tip]
    split_ifs <;>
      simp only [update_checkpoints, update_unrealized_checkpoints] <;>
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

private theorem on_block_acceptedFFGStoreProjection_of_selectors
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgj : post.current_justified_checkpoint = S.GJ sb.root)
    (hgf : post.finalized_checkpoint = S.GF sb.root)
    (hgu : (ext.process_justification_and_finalization
      post).current_justified_checkpoint =
      S.GU sb.root)
    (hguf : (ext.process_justification_and_finalization
      post).finalized_checkpoint = S.GUF sb.root)
    (h : AcceptedFFGStoreProjection S store)
    (hh : on_block cfg ext store sb = some store') :
    AcceptedFFGStoreProjection S store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [on_block, if_pos hknown] at hh
    cases hh
    exact h
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
    rw [hst] at hh
    let added : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote := Function.update store.payload_data_availability_vote
          sb.root (some (List.replicate cfg.ptc_size none)) }
    change (match notify_ptc_messages cfg ext added post sb.message.payload_attestations with
      | none => none
      | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
          (FastConfirmation.Spec.update_checkpoints
            (FastConfirmation.Spec.update_proposer_boost_root cfg
              (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
              (get_head cfg store).root sb.root)
            post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
        some store' at hh
    cases hn : notify_ptc_messages cfg ext added post sb.message.payload_attestations with
    | none => rw [hn] at hh; cases hh
    | some notified =>
      rw [hn] at hh
      cases hh
      have hf := notify_ptc_messages_frame cfg ext hn
      apply compute_pulled_up_tip_acceptedFFGStoreProjection_of_blockState
      · apply update_checkpoints_acceptedFFGBlockStateProjection
        apply update_proposer_boost_root_acceptedFFGBlockStateProjection
        apply record_block_timeliness_acceptedFFGBlockStateProjection
        refine AcceptedFFGBlockStateProjection.of_eq ?_ hf.block_roots hf.block_states
        constructor <;> intro r hr
        · simp only [added, Function.update_apply]
          split_ifs with hrs
          · subst r
            exact hgj
          · apply h.block_state_gj
            simp only [added, List.mem_append, List.mem_singleton] at hr
            exact hr.resolve_right hrs
        · simp only [added, Function.update_apply]
          split_ifs with hrs
          · subst r
            exact hgf
          · apply h.block_state_gf
            simp only [added, List.mem_append, List.mem_singleton] at hr
            exact hr.resolve_right hrs
        · simp only [added, Function.update_apply]
          split_ifs with hrs
          · subst r
            exact hgu
          · apply h.pulled_up_gu
            simp only [added, List.mem_append, List.mem_singleton] at hr
            exact hr.resolve_right hrs
        · simp only [added, Function.update_apply]
          split_ifs with hrs
          · subst r
            exact hguf
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

/-- A concrete accepted block transition preserves the exact projection.
The coherence law is applied to this transition value itself, never to an
arbitrary invocation of the opaque state-transition function. -/
theorem acceptedBlockTransition_acceptedFFGStoreProjection
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedFFGStoreProjection S (t.atPrefix.store cfg ext)) :
    AcceptedFFGStoreProjection S t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨hknown, hsame⟩ | ⟨post, hst, hinserted⟩)
  · rw [hsame]
    exact h
  · apply on_block_acceptedFFGStoreProjection_of_selectors hst
    · rw [← hinserted]
      exact hcoh.transition_gj t
    · rw [← hinserted]
      exact hcoh.transition_gf t
    · rw [← hinserted]
      exact hcoh.transition_gu t
    · rw [← hinserted]
      exact hcoh.transition_guf t
    · exact h
    · exact t.accepted

theorem on_attestation_acceptedFFGStoreProjection
    {store store' : Store Root} {a : Attestation Root}
    {is_from_block : Bool}
    (h : AcceptedFFGStoreProjection S store)
    (hh : on_attestation cfg ext store a is_from_block = some store') :
    AcceptedFFGStoreProjection S store' := by
  simp only [on_attestation] at hh
  split_ifs at hh
  cases hh
  apply update_latest_messages_acceptedFFGStoreProjection
  exact store_target_checkpoint_state_acceptedFFGStoreProjection _ _ h

theorem on_attester_slashing_acceptedFFGStoreProjection
    {store store' : Store Root} {sl : AttesterSlashing Root}
    (h : AcceptedFFGStoreProjection S store)
    (hh : on_attester_slashing ext store sl = some store') :
    AcceptedFFGStoreProjection S store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl

/-! ## Ticks -/

theorem on_tick_per_slot_acceptedFFGStoreProjection
    (store : Store Root) (time : ℕ)
    (h : AcceptedFFGStoreProjection S store) :
    AcceptedFFGStoreProjection S (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
    | exact h.of_eq rfl rfl rfl
    | exact update_checkpoints_acceptedFFGStoreProjection _ _ _
        (h.of_eq rfl rfl rfl)

theorem on_tick_aux_acceptedFFGStoreProjection (tick_slot fuel : ℕ) :
    ∀ store : Store Root, AcceptedFFGStoreProjection S store →
      AcceptedFFGStoreProjection S
        (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
      intro store h
      rw [on_tick_aux]
      split_ifs
      · exact ih _ (on_tick_per_slot_acceptedFFGStoreProjection _ _ h)
      · exact h

theorem on_tick_acceptedFFGStoreProjection
    (store : Store Root) (time : ℕ)
    (h : AcceptedFFGStoreProjection S store) :
    AcceptedFFGStoreProjection S (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_acceptedFFGStoreProjection _ _
    (on_tick_aux_acceptedFFGStoreProjection _ _ _ h)

/-! ## Exact prefix and boundary induction -/

namespace Execution

/-- Every exact `take k` prefix of a concrete scheduled second preserves the
accepted projection from the ticked boundary store.  The list index is kept
explicit so successful block events construct an exact accepted transition. -/
private theorem acceptedFFGStoreProjection_take
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : AcceptedFFGStoreProjection S
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      AcceptedFFGStoreProjection S
        (((E.schedule w (n + 1)).take k).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) := by
  intro k hk
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
      have hklt : k < (E.schedule w (n + 1)).length := by omega
      have hkle : k ≤ (E.schedule w (n + 1)).length := Nat.le_of_lt hklt
      let p : E.ScheduledEventPrefix :=
        { node := w
          previousSecond := n
          processedCount := k
          count_le := hkle }
      have hp : AcceptedFFGStoreProjection S (p.store cfg ext) := by
        exact ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedFFGStoreProjection S
        ((p.successor hklt).store cfg ext)
      rw [hsucc]
      cases heq : apply_event cfg ext (p.store cfg ext)
          nextEvent with
      | none => simpa using hp
      | some store' =>
        simp only [Option.getD_some]
        cases hevent : nextEvent with
        | block sb =>
            let t : E.AcceptedBlockTransition cfg ext :=
              { atPrefix := p
                signedBlock := sb
                event_at := by
                  have hget :
                      (E.schedule w (n + 1))[k]? = some nextEvent := by
                    simp [nextEvent, List.getElem?_eq_getElem hklt]
                  rw [hget, hevent]
                postStore := store'
                accepted := by
                  simpa [apply_event, hevent] using heq }
            exact acceptedBlockTransition_acceptedFFGStoreProjection hcoh t hp
        | attestation a fromBlock =>
            exact on_attestation_acceptedFFGStoreProjection hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact on_attester_slashing_acceptedFFGStoreProjection hp
              (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope envelope observation =>
            have hf := on_execution_payload_envelope_frame ext
              (by simpa [apply_event, hevent] using heq)
            exact hp.of_eq hf.block_roots hf.block_states hf.unrealized_justifications
        | payload_attestation_message message fromBlock =>
            have hf := on_payload_attestation_message_frame cfg ext
              (by simpa [apply_event, hevent] using heq)
            exact hp.of_eq hf.block_roots hf.block_states hf.unrealized_justifications

/-- Every ordinary boundary snapshot has the accepted-state FFG projection. -/
theorem acceptedFFGStoreProjection
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ) :
    AcceptedFFGStoreProjection S (E.store cfg ext w n) := by
  induction n with
  | zero =>
      change AcceptedFFGStoreProjection S E.genesis_store
      exact ⟨hcoh.genesis_gj, hcoh.genesis_gf,
        hcoh.genesis_gu, hcoh.genesis_guf,
        hcoh.genesis_unrealized_justification⟩
  | succ n ih =>
      change AcceptedFFGStoreProjection S
        ((E.schedule w (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.acceptedFFGStoreProjection_take hcoh w n
          (on_tick_acceptedFFGStoreProjection _ _ ih)
          (E.schedule w (n + 1)).length le_rfl

/-- Every exact in-second schedule prefix has the same accepted-state FFG
projection selected before the prefix. -/
theorem ScheduledEventPrefix.acceptedFFGStoreProjection
    (p : E.ScheduledEventPrefix)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S) :
    AcceptedFFGStoreProjection S (p.store cfg ext) := by
  apply E.acceptedFFGStoreProjection_take hcoh p.node p.previousSecond
  · exact on_tick_acceptedFFGStoreProjection _ _
      (E.acceptedFFGStoreProjection hcoh p.node p.previousSecond)
  · exact p.count_le

/-- Exact projection for every store in the per-second causal domain. -/
theorem CausalStore.acceptedFFGStoreProjection
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S) :
    AcceptedFFGStoreProjection S store := by
  cases hstore with
  | genesis => exact E.acceptedFFGStoreProjection hcoh 0 0
  | scheduledPrefix p => exact p.acceptedFFGStoreProjection hcoh

namespace ExactPrefixAcceptedFFGSemantics


/-- Bundle-indexed projection of every store in the exact causal domain. -/
theorem causalStoreProjection
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    AcceptedFFGStoreProjection B.state store :=
  hstore.acceptedFFGStoreProjection
    B.coherence.toAcceptedFFGSelectorCoherence


end ExactPrefixAcceptedFFGSemantics

/-! ## Boundary selector corollaries -/





theorem accepted_unrealized_justification_eq
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ)
    {r : Root} (hr : r ∈ (E.store cfg ext w n).block_roots) :
    (E.store cfg ext w n).unrealized_justifications r = S.GU r :=
  (E.acceptedFFGStoreProjection hcoh w n).unrealized_justification r hr


end Execution

end FastConfirmation.Spec

end
