module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGStateTrajectory
public import FastConfirmationProofs.FFG.State.ProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Observer global FFG checkpoint trajectory

This observer-only induction follows the four store-global FFG checkpoint fields through exact
causal schedule prefixes.  Its semantic state is selected before the
store/prefix quantifier.  Every non-anchor origin keeps both membership in the
exact store and an exact accepted block carrier; successful block steps use an
`Execution.AcceptedBlockTransition`, never an arbitrary state-transition call.

The final consumers deliberately separate two facts:

* selector evidence is AU with its formed-checkpoint carrier and accepted
  temporal evidence intact;
* checkpoint-root knownness additionally needs executable boundary-walk
  evidence in the concrete store.
-/

namespace FastConfirmation.Spec
namespace ObserverFFG

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {obs : ValidatorIndex}
variable {S : Execution.ObserverFFGContent cfg ext E anchor}

/-! ## Store-global accepted origin predicates -/

def AcceptedGlobalJustifiedOrigin
    (S : FastConfirmation.Spec.Execution.ObserverFFGContent cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧
      (c = S.GJ r ∨ c = S.GU r)

def AcceptedGlobalUnrealizedJustifiedOrigin
    (S : FastConfirmation.Spec.Execution.ObserverFFGContent cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧ c = S.GU r

def AcceptedGlobalFinalizedOrigin
    (S : FastConfirmation.Spec.Execution.ObserverFFGContent cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧
      (c = S.GF r ∨ c = S.GUF r)

def AcceptedGlobalUnrealizedFinalizedOrigin
    (S : FastConfirmation.Spec.Execution.ObserverFFGContent cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧ c = S.GUF r

/-- Exact accepted provenance for the four store-global checkpoint fields. -/
structure AcceptedFFGGlobalCheckpointOrigins
    (S : FastConfirmation.Spec.Execution.ObserverFFGContent cfg ext E anchor)
    (store : Store Root) : Prop where
  justified : AcceptedGlobalJustifiedOrigin S store
    store.justified_checkpoint
  unrealized_justified : AcceptedGlobalUnrealizedJustifiedOrigin S store
    store.unrealized_justified_checkpoint
  finalized : AcceptedGlobalFinalizedOrigin S store
    store.finalized_checkpoint
  unrealized_finalized : AcceptedGlobalUnrealizedFinalizedOrigin S store
    store.unrealized_finalized_checkpoint

namespace AcceptedFFGGlobalCheckpointOrigins

/-- Transport origins to a checkpoint-identical store which contains the old
block domain.  Exact accepted carriers are independent of the mutable store
record and therefore survive this transport. -/
private theorem of_extension {store store' : Store Root}
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hsub : store.block_roots ⊆ store'.block_roots)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint)
    (hf : store'.finalized_checkpoint = store.finalized_checkpoint)
    (huf : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    AcceptedFFGGlobalCheckpointOrigins S store' := by
  constructor
  · rcases h.justified with hanchor | ⟨r, ⟨hr, hb⟩, hlocal⟩
    · exact Or.inl (hj.trans hanchor)
    · exact Or.inr ⟨r, ⟨hsub hr, hb⟩,
        hlocal.elim (fun hgj => Or.inl (hj.trans hgj))
          (fun hgu => Or.inr (hj.trans hgu))⟩
  · rcases h.unrealized_justified with
      hanchor | ⟨r, ⟨hr, hb⟩, hlocal⟩
    · exact Or.inl (huj.trans hanchor)
    · exact Or.inr ⟨r, ⟨hsub hr, hb⟩, huj.trans hlocal⟩
  · rcases h.finalized with hanchor | ⟨r, ⟨hr, hb⟩, hlocal⟩
    · exact Or.inl (hf.trans hanchor)
    · exact Or.inr ⟨r, ⟨hsub hr, hb⟩,
        hlocal.elim (fun hgf => Or.inl (hf.trans hgf))
          (fun hguf => Or.inr (hf.trans hguf))⟩
  · rcases h.unrealized_finalized with
      hanchor | ⟨r, ⟨hr, hb⟩, hlocal⟩
    · exact Or.inl (huf.trans hanchor)
    · exact Or.inr ⟨r, ⟨hsub hr, hb⟩, huf.trans hlocal⟩

private theorem update_checkpoints (store : Store Root)
    (jc fc : Checkpoint Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hjc : AcceptedGlobalJustifiedOrigin S store jc)
    (hfc : AcceptedGlobalFinalizedOrigin S store fc) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.update_checkpoints store jc fc) := by
  let store' := FastConfirmation.Spec.update_checkpoints store jc fc
  have hroots : store'.block_roots = store.block_roots := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hjField : store'.justified_checkpoint =
      if jc.epoch > store.justified_checkpoint.epoch then jc
      else store.justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hfField : store'.finalized_checkpoint =
      if fc.epoch > store.finalized_checkpoint.epoch then fc
      else store.finalized_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hujField : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hufField : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  change AcceptedFFGGlobalCheckpointOrigins S store'
  constructor
  · unfold AcceptedGlobalJustifiedOrigin Execution.AcceptedCarrierIn at hjc ⊢
    rw [hroots, hjField]
    split_ifs
    · exact hjc
    · exact h.justified
  · unfold AcceptedGlobalUnrealizedJustifiedOrigin
      Execution.AcceptedCarrierIn at ⊢
    rw [hroots, hujField]
    exact h.unrealized_justified
  · unfold AcceptedGlobalFinalizedOrigin Execution.AcceptedCarrierIn at hfc ⊢
    rw [hroots, hfField]
    split_ifs
    · exact hfc
    · exact h.finalized
  · unfold AcceptedGlobalUnrealizedFinalizedOrigin
      Execution.AcceptedCarrierIn at ⊢
    rw [hroots, hufField]
    exact h.unrealized_finalized

private theorem update_unrealized_checkpoints (store : Store Root)
    (ujc ufc : Checkpoint Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hujc : AcceptedGlobalUnrealizedJustifiedOrigin S store ujc)
    (hufc : AcceptedGlobalUnrealizedFinalizedOrigin S store ufc) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc) := by
  let store' := FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc
  have hroots : store'.block_roots = store.block_roots := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hjField : store'.justified_checkpoint = store.justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hfField : store'.finalized_checkpoint = store.finalized_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hujField : store'.unrealized_justified_checkpoint =
      if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
      else store.unrealized_justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hufField : store'.unrealized_finalized_checkpoint =
      if ufc.epoch > store.unrealized_finalized_checkpoint.epoch then ufc
      else store.unrealized_finalized_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  change AcceptedFFGGlobalCheckpointOrigins S store'
  constructor
  · unfold AcceptedGlobalJustifiedOrigin Execution.AcceptedCarrierIn at ⊢
    rw [hroots, hjField]
    exact h.justified
  · unfold AcceptedGlobalUnrealizedJustifiedOrigin
      Execution.AcceptedCarrierIn at hujc ⊢
    rw [hroots, hujField]
    split_ifs
    · exact hujc
    · exact h.unrealized_justified
  · unfold AcceptedGlobalFinalizedOrigin Execution.AcceptedCarrierIn at ⊢
    rw [hroots, hfField]
    exact h.finalized
  · unfold AcceptedGlobalUnrealizedFinalizedOrigin
      Execution.AcceptedCarrierIn at hufc ⊢
    rw [hroots, hufField]
    split_ifs
    · exact hufc
    · exact h.unrealized_finalized

/-- Exact origin preservation by eager pull-up at an accepted known root. -/
private theorem compute_pulled_up_tip (store : Store Root) (r : Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hr : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r)
    (hgu : (ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint = S.GU r)
    (hguf : (ext.process_justification_and_finalization
      (store.block_states r)).finalized_checkpoint = S.GUF r) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) := by
  simp only [FastConfirmation.Spec.compute_pulled_up_tip, hgu, hguf]
  split_ifs
  · apply AcceptedFFGGlobalCheckpointOrigins.update_checkpoints
    · apply AcceptedFFGGlobalCheckpointOrigins.update_unrealized_checkpoints
      · exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
      · exact Or.inr ⟨r, ⟨by simpa using hr.1, hr.2⟩, rfl⟩
      · exact Or.inr ⟨r, ⟨by simpa using hr.1, hr.2⟩, rfl⟩
    · exact Or.inr ⟨r, ⟨by simpa using hr.1, hr.2⟩, Or.inr rfl⟩
    · exact Or.inr ⟨r, ⟨by simpa using hr.1, hr.2⟩, Or.inr rfl⟩
  · apply AcceptedFFGGlobalCheckpointOrigins.update_unrealized_checkpoints
    · exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
    · exact Or.inr ⟨r, ⟨by simpa using hr.1, hr.2⟩, rfl⟩
    · exact Or.inr ⟨r, ⟨by simpa using hr.1, hr.2⟩, rfl⟩

private theorem record_block_timeliness (store : Store Root) (r : Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.record_block_timeliness cfg store r) := by
  simp only [FastConfirmation.Spec.record_block_timeliness]
  exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

private theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;> exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

private theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

private theorem update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;>
        exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

private theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {is_from_block : Bool}
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    AcceptedFFGGlobalCheckpointOrigins S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact update_latest_messages _ _ _
    (store_target_checkpoint_state _ _ h)

private theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root}
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl = some store') :
    AcceptedFFGGlobalCheckpointOrigins S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

private theorem unrealizedJustified_to_justified {store : Store Root}
    {c : Checkpoint Root}
    (h : AcceptedGlobalUnrealizedJustifiedOrigin S store c) :
    AcceptedGlobalJustifiedOrigin S store c := by
  rcases h with hanchor | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor
  · exact Or.inr ⟨r, hr, Or.inr hgu⟩

private theorem unrealizedFinalized_to_finalized {store : Store Root}
    {c : Checkpoint Root}
    (h : AcceptedGlobalUnrealizedFinalizedOrigin S store c) :
    AcceptedGlobalFinalizedOrigin S store c := by
  rcases h with hanchor | ⟨r, hr, hguf⟩
  · exact Or.inl hanchor
  · exact Or.inr ⟨r, hr, Or.inr hguf⟩

private theorem on_tick_per_slot (store : Store Root) (time : ℕ)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  split_ifs
  all_goals
    first
    | exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
    | · apply AcceptedFFGGlobalCheckpointOrigins.update_checkpoints
        · exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
        · exact unrealizedJustified_to_justified
            (by simpa using h.unrealized_justified)
        · exact unrealizedFinalized_to_finalized
            (by simpa using h.unrealized_finalized)

private theorem on_tick_aux (tick_slot fuel : ℕ) :
    ∀ store : Store Root, AcceptedFFGGlobalCheckpointOrigins S store →
      AcceptedFFGGlobalCheckpointOrigins S
        (FastConfirmation.Spec.on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
      intro store h
      rw [FastConfirmation.Spec.on_tick_aux]
      split_ifs
      · exact ih _ (on_tick_per_slot _ _ h)
      · exact h

private theorem on_tick (store : Store Root) (time : ℕ)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.on_tick cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick]
  exact on_tick_per_slot _ _ (on_tick_aux _ _ _ h)

/-! ## Successful accepted block steps -/

private theorem on_block_of_selectors
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (haccepted : E.AcceptedRoot cfg ext sb.root)
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgj : post.current_justified_checkpoint = S.GJ sb.root)
    (hgf : post.finalized_checkpoint = S.GF sb.root)
    (hgu : (ext.process_justification_and_finalization
      post).current_justified_checkpoint = S.GU sb.root)
    (hguf : (ext.process_justification_and_finalization
      post).finalized_checkpoint = S.GUF sb.root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    AcceptedFFGGlobalCheckpointOrigins S store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [FastConfirmation.Spec.on_block, if_pos hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
    rw [hst] at hh
    let added : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote :=
          Function.update store.payload_data_availability_vote
            sb.root (some (List.replicate cfg.ptc_size none)) }
    let finish (notified : Store Root) :=
      FastConfirmation.Spec.compute_pulled_up_tip cfg ext
        (FastConfirmation.Spec.update_checkpoints
          (FastConfirmation.Spec.update_proposer_boost_root cfg
            (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
            (get_head cfg store).root sb.root)
          post.current_justified_checkpoint post.finalized_checkpoint) sb.root
    change (match notify_ptc_messages cfg ext added post sb.message.payload_attestations with
      | none => none
      | some notified => some (finish notified)) = some store' at hh
    have hadded : AcceptedFFGGlobalCheckpointOrigins S added := by
      apply h.of_extension
      · intro r hr
        change r ∈ store.block_roots ++ [sb.root]
        exact List.mem_append_left _ hr
      all_goals rfl
    have haddedRoot : sb.root ∈ added.block_roots := by
      exact List.mem_append_right _ (List.mem_singleton_self _)
    cases hnotify : notify_ptc_messages cfg ext added post sb.message.payload_attestations with
    | none =>
        simp only [hnotify] at hh
        cases hh
    | some notified =>
        simp only [hnotify] at hh
        have hframe : PayloadFrame added notified :=
          notify_ptc_messages_frame cfg ext hnotify
        have hnotified : AcceptedFFGGlobalCheckpointOrigins S notified :=
          hadded.of_extension
            (by simpa only [hframe.block_roots] using
              (List.Subset.refl added.block_roots))
            hframe.justified_checkpoint hframe.unrealized_justified_checkpoint
            hframe.finalized_checkpoint hframe.unrealized_finalized_checkpoint
        have hnotifiedRoot : sb.root ∈ notified.block_roots := by
          rw [hframe.block_roots]
          exact haddedRoot
        let staged := FastConfirmation.Spec.record_block_timeliness cfg notified sb.root
        let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
          (get_head cfg store).root sb.root
        let realized := FastConfirmation.Spec.update_checkpoints boosted
          post.current_justified_checkpoint post.finalized_checkpoint
        suffices hresult : AcceptedFFGGlobalCheckpointOrigins S
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
          have heq : finish notified = store' := Option.some.inj hh
          exact heq ▸ hresult
        have hstaged : AcceptedFFGGlobalCheckpointOrigins S staged :=
          record_block_timeliness notified sb.root hnotified
        have hboosted : AcceptedFFGGlobalCheckpointOrigins S boosted :=
          update_proposer_boost_root staged (get_head cfg store).root sb.root hstaged
        have hboostedRoot : sb.root ∈ boosted.block_roots := by
          simp only [boosted, staged,
            FastConfirmation.Spec.update_proposer_boost_root,
            FastConfirmation.Spec.record_block_timeliness]
          split_ifs
          all_goals exact hnotifiedRoot
        have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
            boosted sb.root :=
          ⟨hboostedRoot, haccepted.exists_blockAt⟩
        have hrealized : AcceptedFFGGlobalCheckpointOrigins S realized := by
          apply update_checkpoints
          · exact hboosted
          · exact Or.inr ⟨sb.root, hcarrier, Or.inl hgj⟩
          · exact Or.inr ⟨sb.root, hcarrier, Or.inl hgf⟩
        have hsameRoots : realized.block_roots = added.block_roots := by
          simp only [realized, boosted, staged,
            FastConfirmation.Spec.update_checkpoints,
            FastConfirmation.Spec.update_proposer_boost_root,
            FastConfirmation.Spec.record_block_timeliness]
          split_ifs <;> exact hframe.block_roots
        have hsameStates : realized.block_states = added.block_states := by
          simp only [realized, boosted, staged,
            FastConfirmation.Spec.update_checkpoints,
            FastConfirmation.Spec.update_proposer_boost_root,
            FastConfirmation.Spec.record_block_timeliness]
          split_ifs <;> exact hframe.block_states
        have hrealizedCarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
            realized sb.root :=
          ⟨by rw [hsameRoots]; exact haddedRoot, haccepted.exists_blockAt⟩
        apply compute_pulled_up_tip realized sb.root hrealized hrealizedCarrier
        · rw [hsameStates]
          simp only [added, Function.update_self]
          exact hgu
        · rw [hsameStates]
          simp only [added, Function.update_self]
          exact hguf

/-- A concrete exact accepted block transition preserves global origins. -/
private theorem acceptedBlockTransition
    (hcoh : FastConfirmation.Spec.Execution.ObserverFFGSelectorCoherence cfg ext E obs S)
    (t : E.AcceptedBlockTransition cfg ext)
    (ht : t.atPrefix.node = obs)
    (h : AcceptedFFGGlobalCheckpointOrigins S (t.atPrefix.store cfg ext)) :
    AcceptedFFGGlobalCheckpointOrigins S t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨_hknown, hsame⟩ | ⟨post, hst, hinserted⟩)
  · rw [hsame]
    exact h
  · apply on_block_of_selectors t.root_accepted hst
    · rw [← hinserted]
      exact hcoh.transition_gj t ht
    · rw [← hinserted]
      exact hcoh.transition_gf t ht
    · rw [← hinserted]
      exact hcoh.transition_gu t ht
    · rw [← hinserted]
      exact hcoh.transition_guf t ht
    · exact h
    · exact t.accepted

end AcceptedFFGGlobalCheckpointOrigins

/-! ## Exact prefix and causal-store induction -/

namespace Execution

private theorem acceptedFFGGlobalCheckpointOrigins_take
    (hcoh : FastConfirmation.Spec.Execution.ObserverFFGSelectorCoherence cfg ext E obs S)
    (w : ValidatorIndex) (n : ℕ) (hw : w = obs)
    (hbase : AcceptedFFGGlobalCheckpointOrigins S
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      AcceptedFFGGlobalCheckpointOrigins S
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
      have hp : AcceptedFFGGlobalCheckpointOrigins S (p.store cfg ext) :=
        ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedFFGGlobalCheckpointOrigins S
        ((p.successor hklt).store cfg ext)
      rw [hsucc]
      cases heq : apply_event cfg ext (p.store cfg ext) nextEvent with
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
            exact AcceptedFFGGlobalCheckpointOrigins.acceptedBlockTransition
              hcoh t hw hp
        | attestation a fromBlock =>
            exact AcceptedFFGGlobalCheckpointOrigins.on_attestation hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact AcceptedFFGGlobalCheckpointOrigins.on_attester_slashing hp
              (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope envelope observation =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_execution_payload_envelope_frame ext (by simpa [apply_event, hevent] using heq)
            exact hp.of_extension
              (by simpa only [hf.block_roots] using
                (List.Subset.refl (p.store cfg ext).block_roots))
              hf.justified_checkpoint hf.unrealized_justified_checkpoint
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint
        | payload_attestation_message message isFromBlock =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_payload_attestation_message_frame cfg ext (by simpa [apply_event, hevent] using heq)
            exact hp.of_extension
              (by simpa only [hf.block_roots] using
                (List.Subset.refl (p.store cfg ext).block_roots))
              hf.justified_checkpoint hf.unrealized_justified_checkpoint
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint

/-- Every ordinary execution boundary has accepted global checkpoint origins
for the one semantic state selected before the boundary. -/
theorem acceptedFFGGlobalCheckpointOrigins
    (hcoh : FastConfirmation.Spec.Execution.ObserverFFGSelectorCoherence cfg ext E obs S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) (hw : w = obs) :
    AcceptedFFGGlobalCheckpointOrigins S (E.store cfg ext w n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgeq, _hslot⟩ := hgen
      change AcceptedFFGGlobalCheckpointOrigins S E.genesis_store
      rw [hgeq] at hanchor ⊢
      constructor <;> apply Or.inl <;>
        simpa only [get_forkchoice_store] using hanchor.symm
  | succ n ih =>
      change AcceptedFFGGlobalCheckpointOrigins S
        ((E.schedule w (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1))))
      simpa only [List.take_length] using
        acceptedFFGGlobalCheckpointOrigins_take (E := E) hcoh w n hw
          (AcceptedFFGGlobalCheckpointOrigins.on_tick _ _ ih)
          (E.schedule w (n + 1)).length le_rfl

/-- Every exact in-second prefix has accepted global checkpoint origins with
the semantic state fixed before the prefix. -/
theorem ScheduledEventPrefix.acceptedFFGGlobalCheckpointOrigins
    (p : E.ScheduledEventPrefix) (hp : p.node = obs)
    (hcoh : FastConfirmation.Spec.Execution.ObserverFFGSelectorCoherence cfg ext E obs S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGGlobalCheckpointOrigins S (p.store cfg ext) := by
  apply acceptedFFGGlobalCheckpointOrigins_take (E := E) hcoh
    p.node p.previousSecond hp
  · exact AcceptedFFGGlobalCheckpointOrigins.on_tick _ _
      (FastConfirmation.Spec.ObserverFFG.Execution.acceptedFFGGlobalCheckpointOrigins (E := E) hcoh hgen hanchor
        p.node p.previousSecond hp)
  · exact p.count_le

/-- Accepted global origins at every store in the exact causal domain. -/
theorem observerCausalStore_origins
    {store : Store Root} (hstore : E.ObserverCausalStore cfg ext obs store)
    (hcoh : FastConfirmation.Spec.Execution.ObserverFFGSelectorCoherence cfg ext E obs S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGGlobalCheckpointOrigins S store := by
  cases hstore with
  | genesis =>
      exact FastConfirmation.Spec.ObserverFFG.Execution.acceptedFFGGlobalCheckpointOrigins (E := E) hcoh hgen hanchor obs 0 rfl
  | scheduledPrefix p hp =>
      exact ScheduledEventPrefix.acceptedFFGGlobalCheckpointOrigins p hp hcoh hgen hanchor

end Execution


end ObserverFFG
end FastConfirmation.Spec
end
