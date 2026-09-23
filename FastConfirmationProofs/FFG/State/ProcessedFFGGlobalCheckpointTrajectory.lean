module
public import FastConfirmationProofs.FFG.State.ProcessedFFGStateTrajectory
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted global FFG checkpoint trajectory

This module follows the four store-global FFG checkpoint fields through exact
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

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : AcceptedChainFFGState cfg ext E anchor}

namespace Execution

/-- A selector origin known in this exact store, together with an exact block
carrier accepted by some causal prefix.  The accepted message is kept
existential because a later successful duplicate delivery may overwrite the
store's same-root entry. -/
def AcceptedCarrierIn (E : Execution Root) (store : Store Root)
    (r : Root) : Prop :=
  r ∈ store.block_roots ∧
    ∃ b : BeaconBlock Root, E.AcceptedBlockAt cfg ext r b

namespace AcceptedCarrierIn

theorem known {store : Store Root} {r : Root}
    (h : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r) :
    r ∈ store.block_roots := h.1

theorem acceptedRoot {store : Store Root} {r : Root}
    (h : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r) :
    E.AcceptedRoot cfg ext r := by
  obtain ⟨_, hb⟩ := h.2
  exact hb.acceptedRoot

theorem of_causal_known {store : Store Root}
    (hstore : E.CausalStore cfg ext store) {r : Root}
    (hr : r ∈ store.block_roots) :
    E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
  ⟨hr, store.blocks r,
    E.acceptedBlockAt_of_causal_known cfg ext hstore hr⟩

end AcceptedCarrierIn

end Execution

/-! ## Store-global accepted origin predicates -/

def AcceptedGlobalJustifiedOrigin
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧
      (c = S.GJ r ∨ c = S.GU r)

def AcceptedGlobalUnrealizedJustifiedOrigin
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧ c = S.GU r

def AcceptedGlobalFinalizedOrigin
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧
      (c = S.GF r ∨ c = S.GUF r)

def AcceptedGlobalUnrealizedFinalizedOrigin
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧ c = S.GUF r

/-- Exact accepted provenance for the four store-global checkpoint fields. -/
structure AcceptedFFGGlobalCheckpointOrigins
    (S : AcceptedChainFFGState cfg ext E anchor)
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
theorem of_extension {store store' : Store Root}
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

theorem update_checkpoints (store : Store Root)
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

theorem update_unrealized_checkpoints (store : Store Root)
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
theorem compute_pulled_up_tip (store : Store Root) (r : Root)
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

theorem record_block_timeliness (store : Store Root) (r : Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.record_block_timeliness cfg store r) := by
  simp only [FastConfirmation.Spec.record_block_timeliness]
  exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;> exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root)
    (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    AcceptedFFGGlobalCheckpointOrigins S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

theorem update_latest_messages (store : Store Root)
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

theorem on_attestation {store store' : Store Root}
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

theorem on_attester_slashing {store store' : Store Root}
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

theorem on_tick_per_slot (store : Store Root) (time : ℕ)
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

theorem on_tick_aux (tick_slot fuel : ℕ) :
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

theorem on_tick (store : Store Root) (time : ℕ)
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
theorem acceptedBlockTransition
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedFFGGlobalCheckpointOrigins S (t.atPrefix.store cfg ext)) :
    AcceptedFFGGlobalCheckpointOrigins S t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨_hknown, hsame⟩ | ⟨post, hst, hinserted⟩)
  · rw [hsame]
    exact h
  · apply on_block_of_selectors t.root_accepted hst
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

end AcceptedFFGGlobalCheckpointOrigins

/-! ## Exact prefix and causal-store induction -/

namespace Execution

private theorem acceptedFFGGlobalCheckpointOrigins_take
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ)
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
              hcoh t hp
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
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
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
        E.acceptedFFGGlobalCheckpointOrigins_take hcoh w n
          (AcceptedFFGGlobalCheckpointOrigins.on_tick _ _ ih)
          (E.schedule w (n + 1)).length le_rfl

/-- Every exact in-second prefix has accepted global checkpoint origins with
the semantic state fixed before the prefix. -/
theorem ScheduledEventPrefix.acceptedFFGGlobalCheckpointOrigins
    (p : E.ScheduledEventPrefix)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGGlobalCheckpointOrigins S (p.store cfg ext) := by
  apply E.acceptedFFGGlobalCheckpointOrigins_take hcoh
    p.node p.previousSecond
  · exact AcceptedFFGGlobalCheckpointOrigins.on_tick _ _
      (E.acceptedFFGGlobalCheckpointOrigins hcoh hgen hanchor
        p.node p.previousSecond)
  · exact p.count_le

/-- Accepted global origins at every store in the exact causal domain. -/
theorem CausalStore.acceptedFFGGlobalCheckpointOrigins
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGGlobalCheckpointOrigins S store := by
  cases hstore with
  | genesis =>
      exact E.acceptedFFGGlobalCheckpointOrigins hcoh hgen hanchor 0 0
  | scheduledPrefix p =>
      exact p.acceptedFFGGlobalCheckpointOrigins hcoh hgen hanchor

end Execution

/-! ## Accepted selector carriers and checkpoint-root knownness -/

/-- A global selector has AU at a same-store accepted tip, with the particular
formed carrier, its acceptance, and its full included/temporal evidence kept
as named witnesses.  This is strictly more informative than a bare descent
claim. -/
structure AcceptedSelectorAUCarrier
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) where
  tip : Root
  carrier : Root
  tip_carrier :
    E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store tip
  au : S.AU cfg ext tip c
  tip_descends_carrier : E.RootDescends tip carrier
  carrier_accepted : E.AcceptedRoot cfg ext carrier
  formed_evidence : AcceptedFormedCheckpointEvidence cfg ext E
    S.includedAttestations.Included anchor carrier c

/-- Proposition-level ownership of one named accepted selector carrier. -/
def AcceptedSelectorAUEvidence
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  Nonempty (AcceptedSelectorAUCarrier S store c)

namespace AcceptedSelectorAUEvidence

theorem of_AU {store : Store Root} {tip : Root} {c : Checkpoint Root}
    (htip : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store tip)
    (hAU : S.AU cfg ext tip c) :
    AcceptedSelectorAUEvidence S store c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨⟨tip, carrier, htip, ⟨carrier, hdesc, hformed⟩, hdesc,
    S.formed_carrier_accepted hformed, S.formed_evidence hformed⟩⟩

end AcceptedSelectorAUEvidence

namespace AcceptedSelectorAUCarrier

/-- AU selector evidence does not by itself assert same-store checkpoint-root
knownness.  With causal checkpoint reflection and the concrete boundary walk,
that distinct executable claim follows exactly. -/
theorem checkpointRoot_known
    {store : Store Root} {c : Checkpoint Root}
    (h : AcceptedSelectorAUCarrier S store c)
    (hcoh : AcceptedFFGTransitionCoherence cfg ext S)
    (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg c.epoch) h.tip) :
    c.root ∈ store.block_roots := by
  have hcheckpoint := hcoh.au_checkpoint_of_known hstore h.tip
    h.tip_carrier.known c h.au
  have hroot : c.root = get_checkpoint_block cfg store h.tip c.epoch := by
    have := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block] using this
  rw [hroot]
  exact (get_ancestor_spec hparent hwalk).1

end AcceptedSelectorAUCarrier

namespace AcceptedFFGGlobalCheckpointOrigins

/-- Store-local justified selector consumer.  Same-store installer knownness,
AU, the formed carrier, and exact accepted formation evidence are all retained. -/
theorem justified_anchor_or_AUEvidence
    {store : Store Root} (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    store.justified_checkpoint = anchor ∨
      AcceptedSelectorAUEvidence S store store.justified_checkpoint := by
  rcases h.justified with hanchor | ⟨r, hr, hgj | hgu⟩
  · exact Or.inl hanchor
  · right
    apply AcceptedSelectorAUEvidence.of_AU hr
    rw [hgj]
    exact S.gj_AU cfg ext hr.acceptedRoot
  · right
    apply AcceptedSelectorAUEvidence.of_AU hr
    rw [hgu]
    exact S.gu_AU cfg ext hr.acceptedRoot

/-- Finalized analogue of `justified_anchor_or_AUEvidence`, preserving the
exact formed carrier rather than erasing it to descent alone. -/
theorem finalized_anchor_or_AUEvidence
    {store : Store Root} (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    store.finalized_checkpoint = anchor ∨
      AcceptedSelectorAUEvidence S store store.finalized_checkpoint := by
  rcases h.finalized with hanchor | ⟨r, hr, hgf | hguf⟩
  · exact Or.inl hanchor
  · right
    apply AcceptedSelectorAUEvidence.of_AU hr
    rw [hgf]
    exact S.gf_AU cfg ext hr.acceptedRoot
  · right
    apply AcceptedSelectorAUEvidence.of_AU hr
    rw [hguf]
    exact S.guf_AU cfg ext hr.acceptedRoot

end AcceptedFFGGlobalCheckpointOrigins

/-! ## Full production bundle consumers -/

/-- The existing accepted block-local trajectory paired with the new accepted
store-global origin trajectory at one exact store. -/
structure AcceptedFFGGlobalStoreProjection
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop where
  blockLocal : AcceptedFFGStoreProjection S store
  storeGlobal : AcceptedFFGGlobalCheckpointOrigins S store

namespace ExactPrefixAcceptedFFGSemantics

/-- One preselected production state projects both block-local selectors and
store-global origins at every exact causal store. -/
theorem causalStoreGlobalProjection
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    AcceptedFFGGlobalStoreProjection B.state store :=
  ⟨Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection B hstore,
    hstore.acceptedFFGGlobalCheckpointOrigins
      B.coherence.toAcceptedFFGSelectorCoherence hgen hanchor⟩


/-- Production justified-selector consumer at an arbitrary exact causal store.
The conclusion is AU carrier evidence, not a mislabeled checkpoint-knownness
claim. -/
theorem globalJustified_anchor_or_AUEvidence
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.justified_checkpoint = B.anchor ∨
      AcceptedSelectorAUEvidence B.state store
        store.justified_checkpoint :=
  (B.causalStoreGlobalProjection hgen hanchor hstore).storeGlobal
    |>.justified_anchor_or_AUEvidence

/-- Production finalized-selector consumer with the same explicit accepted
carrier and included/temporal formation evidence. -/
theorem globalFinalized_anchor_or_AUEvidence
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.finalized_checkpoint = B.anchor ∨
      AcceptedSelectorAUEvidence B.state store
        store.finalized_checkpoint :=
  (B.causalStoreGlobalProjection hgen hanchor hstore).storeGlobal
    |>.finalized_anchor_or_AUEvidence



end ExactPrefixAcceptedFFGSemantics

end FastConfirmation.Spec

end
