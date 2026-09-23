module
public import FastConfirmationProofs.FFG.SelectedSource.FFGEndpointRealization
public import FastConfirmationModel.Execution.PayloadFrame

public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Global FFG checkpoint trajectory

`FFGStateTrajectory` identifies the block-local realized and eager-pull-up
checkpoints stored at every known root.  This file follows the four
store-global checkpoint fields through the executable handlers.  In
particular, it records which block-local selector installed each global
checkpoint instead of assuming an endpoint selector bound.

The trusted checkpoint-sync anchor is kept as an explicit exceptional
origin.  This is necessary: the anchor is installed by
`get_forkchoice_store`, not by an in-segment state transition.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E : Execution Root} {anchor : Checkpoint Root}

/-! ## Store-global origin predicates -/

/-- A realized store-global justified checkpoint is either the trusted
anchor, a block post-state `GJ`, or an eager pull-up `GU` which was realized
by an epoch transition / old-block insertion. -/
def GlobalJustifiedOrigin (S : ChainFFGState cfg E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r ∈ store.block_roots, c = S.GJ r ∨ c = S.GU r

/-- The store-global unrealized justified checkpoint is either the trusted
anchor or the eager pull-up `GU` of a known block. -/
def GlobalUnrealizedJustifiedOrigin (S : ChainFFGState cfg E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨ ∃ r ∈ store.block_roots, c = S.GU r

/-- A realized store-global finalized checkpoint is either the trusted
anchor, a block post-state `GF`, or an eager pull-up `GUF`. -/
def GlobalFinalizedOrigin (S : ChainFFGState cfg E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r ∈ store.block_roots, c = S.GF r ∨ c = S.GUF r

/-- The store-global unrealized finalized checkpoint is either the trusted
anchor or the eager pull-up `GUF` of a known block. -/
def GlobalUnrealizedFinalizedOrigin (S : ChainFFGState cfg E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨ ∃ r ∈ store.block_roots, c = S.GUF r

/-- The four provenance components, separated from the epoch-maximality
components needed by the voting-source bound. -/
structure FFGGlobalCheckpointOrigins (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop where
  justified : GlobalJustifiedOrigin cfg S store store.justified_checkpoint
  unrealized_justified : GlobalUnrealizedJustifiedOrigin cfg S store
    store.unrealized_justified_checkpoint
  finalized : GlobalFinalizedOrigin cfg S store store.finalized_checkpoint
  unrealized_finalized : GlobalUnrealizedFinalizedOrigin cfg S store
    store.unrealized_finalized_checkpoint

/-- The handler-driven global checkpoint ledger.  The two epoch-dominance
fields are the maxima which are true before the next epoch transition:
every known `GJ` has already been offered to `update_checkpoints`, and every
known `GU` has already been offered to `update_unrealized_checkpoints`.

The stronger statement that an *old* block's `GU` has been realized globally
is separated below because its tick proof depends on clock progression, not
only on the four checkpoint-writing helpers. -/
structure FFGGlobalCheckpointLedger (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop where
  justified_origin :
    GlobalJustifiedOrigin cfg S store store.justified_checkpoint
  unrealized_justified_origin :
    GlobalUnrealizedJustifiedOrigin cfg S store
      store.unrealized_justified_checkpoint
  finalized_origin :
    GlobalFinalizedOrigin cfg S store store.finalized_checkpoint
  unrealized_finalized_origin :
    GlobalUnrealizedFinalizedOrigin cfg S store
      store.unrealized_finalized_checkpoint
  gj_epoch_le_justified : ∀ r ∈ store.block_roots,
    (S.GJ r).epoch ≤ store.justified_checkpoint.epoch
  gu_epoch_le_unrealized : ∀ r ∈ store.block_roots,
    (S.GU r).epoch ≤ store.unrealized_justified_checkpoint.epoch


/-- Forget the two maximum fields. -/
def FFGGlobalCheckpointLedger.origins
    {S : ChainFFGState cfg E anchor} {store : Store Root}
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointOrigins cfg S store :=
  ⟨h.justified_origin, h.unrealized_justified_origin,
    h.finalized_origin, h.unrealized_finalized_origin⟩

namespace FFGGlobalCheckpointOrigins

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}

/-- Transport origins to a checkpoint-identical store whose block domain
contains the old block domain. -/
theorem of_extension {store store' : Store Root}
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hsub : store.block_roots ⊆ store'.block_roots)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint)
    (hf : store'.finalized_checkpoint = store.finalized_checkpoint)
    (huf : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    FFGGlobalCheckpointOrigins cfg S store' := by
  constructor
  · rcases h.justified with hanchor | ⟨r, hr, hlocal⟩
    · exact Or.inl (hj.trans hanchor)
    · rcases hlocal with hgj | hgu
      · exact Or.inr ⟨r, hsub hr, Or.inl (hj.trans hgj)⟩
      · exact Or.inr ⟨r, hsub hr, Or.inr (hj.trans hgu)⟩
  · rcases h.unrealized_justified with hanchor | ⟨r, hr, hlocal⟩
    · exact Or.inl (huj.trans hanchor)
    · exact Or.inr ⟨r, hsub hr, huj.trans hlocal⟩
  · rcases h.finalized with hanchor | ⟨r, hr, hlocal⟩
    · exact Or.inl (hf.trans hanchor)
    · rcases hlocal with hgf | hguf
      · exact Or.inr ⟨r, hsub hr, Or.inl (hf.trans hgf)⟩
      · exact Or.inr ⟨r, hsub hr, Or.inr (hf.trans hguf)⟩
  · rcases h.unrealized_finalized with hanchor | ⟨r, hr, hlocal⟩
    · exact Or.inl (huf.trans hanchor)
    · exact Or.inr ⟨r, hsub hr, huf.trans hlocal⟩

/-- Payload handlers preserve the block domain and the checkpoint fields. -/
theorem of_payloadFrame {store store' : Store Root}
    (h : FFGGlobalCheckpointOrigins cfg S store) (hf : PayloadFrame store store') :
    FFGGlobalCheckpointOrigins cfg S store' := by
  apply h.of_extension
  · simpa only [hf.block_roots] using (List.Subset.refl store.block_roots)
  · exact hf.justified_checkpoint
  · exact hf.unrealized_justified_checkpoint
  · exact hf.finalized_checkpoint
  · exact hf.unrealized_finalized_checkpoint

theorem update_checkpoints (store : Store Root) (jc fc : Checkpoint Root)
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hjc : GlobalJustifiedOrigin cfg S store jc)
    (hfc : GlobalFinalizedOrigin cfg S store fc) :
    FFGGlobalCheckpointOrigins cfg S (FastConfirmation.Spec.update_checkpoints
      store jc fc) := by
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
  change FFGGlobalCheckpointOrigins cfg S store'
  constructor
  · unfold GlobalJustifiedOrigin at hjc ⊢
    rw [hroots, hjField]
    split_ifs
    · exact hjc
    · exact h.justified
  · unfold GlobalUnrealizedJustifiedOrigin at ⊢
    rw [hroots, hujField]
    exact h.unrealized_justified
  · unfold GlobalFinalizedOrigin at hfc ⊢
    rw [hroots, hfField]
    split_ifs
    · exact hfc
    · exact h.finalized
  · unfold GlobalUnrealizedFinalizedOrigin at ⊢
    rw [hroots, hufField]
    exact h.unrealized_finalized

theorem update_unrealized_checkpoints (store : Store Root)
    (ujc ufc : Checkpoint Root)
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hujc : GlobalUnrealizedJustifiedOrigin cfg S store ujc)
    (hufc : GlobalUnrealizedFinalizedOrigin cfg S store ufc) :
    FFGGlobalCheckpointOrigins cfg S
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
  change FFGGlobalCheckpointOrigins cfg S store'
  constructor
  · unfold GlobalJustifiedOrigin at ⊢
    rw [hroots, hjField]
    exact h.justified
  · unfold GlobalUnrealizedJustifiedOrigin at hujc ⊢
    rw [hroots, hujField]
    split_ifs
    · exact hujc
    · exact h.unrealized_justified
  · unfold GlobalFinalizedOrigin at ⊢
    rw [hroots, hfField]
    exact h.finalized
  · unfold GlobalUnrealizedFinalizedOrigin at hufc ⊢
    rw [hroots, hufField]
    split_ifs
    · exact hufc
    · exact h.unrealized_finalized

/-- Exact origin preservation by eager pull-up at a known root. -/
theorem compute_pulled_up_tip (store : Store Root) (r : Root)
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hr : r ∈ store.block_roots)
    (hgu : (ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint = S.GU r)
    (hguf : (ext.process_justification_and_finalization
      (store.block_states r)).finalized_checkpoint = S.GUF r) :
    FFGGlobalCheckpointOrigins cfg S
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) := by
  simp only [FastConfirmation.Spec.compute_pulled_up_tip, hgu, hguf]
  split_ifs
  · apply FFGGlobalCheckpointOrigins.update_checkpoints
    · apply FFGGlobalCheckpointOrigins.update_unrealized_checkpoints
      · exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
      · exact Or.inr ⟨r, hr, rfl⟩
      · exact Or.inr ⟨r, hr, rfl⟩
    · exact Or.inr ⟨r, by simpa, Or.inr rfl⟩
    · exact Or.inr ⟨r, by simpa, Or.inr rfl⟩
  · apply FFGGlobalCheckpointOrigins.update_unrealized_checkpoints
    · exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
    · exact Or.inr ⟨r, hr, rfl⟩
    · exact Or.inr ⟨r, hr, rfl⟩

theorem record_block_timeliness (store : Store Root) (r : Root)
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
      (FastConfirmation.Spec.record_block_timeliness cfg store r) := by
  simp only [FastConfirmation.Spec.record_block_timeliness]
  exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;> exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl


theorem update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
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








/-- A successful scheduled block insertion preserves exact global checkpoint
origins.  The proof follows the handler order: install `GJ/GF`, then install
`GU/GUF`, and finally realize the latter pair immediately when the inserted
block is already from an older epoch. -/
theorem on_block
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hscheduled : ∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n)
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    FFGGlobalCheckpointOrigins cfg S store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [FastConfirmation.Spec.on_block, if_pos hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
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
        | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
            (FastConfirmation.Spec.update_checkpoints
              (FastConfirmation.Spec.update_proposer_boost_root cfg
                (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
                (get_head cfg store).root sb.root)
              state.current_justified_checkpoint state.finalized_checkpoint) sb.root)) =
          some store' at hh
      cases hn : notify_ptc_messages cfg ext added state sb.message.payload_attestations with
      | none => rw [hn] at hh; cases hh
      | some notified =>
        rw [hn] at hh
        cases hh
        have hframe := notify_ptc_messages_frame cfg ext hn
        let staged := FastConfirmation.Spec.record_block_timeliness cfg notified sb.root
        let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
          (get_head cfg store).root sb.root
        let realized := FastConfirmation.Spec.update_checkpoints boosted
          state.current_justified_checkpoint state.finalized_checkpoint
        suffices hresult : FFGGlobalCheckpointOrigins cfg S
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
          exact hresult
        have hadded : FFGGlobalCheckpointOrigins cfg S added := by
          apply h.of_extension
          · intro r hr
            exact List.mem_append_left _ hr
          all_goals rfl
        have hstaged : FFGGlobalCheckpointOrigins cfg S staged :=
          FFGGlobalCheckpointOrigins.record_block_timeliness notified sb.root
            (hadded.of_payloadFrame hframe)
        have hboosted : FFGGlobalCheckpointOrigins cfg S boosted :=
          FFGGlobalCheckpointOrigins.update_proposer_boost_root staged
            (get_head cfg store).root sb.root hstaged
        have haddedRoot : sb.root ∈ added.block_roots := by
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hboostedRoot : sb.root ∈ boosted.block_roots := by
          have hs := hframe.sameBlocks.trans
            ((FastConfirmation.Spec.record_block_timeliness_sameBlocks
              cfg notified sb.root).trans
            (FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
              staged (get_head cfg store).root sb.root))
          rw [← hs.1]
          exact haddedRoot
        have hrealized : FFGGlobalCheckpointOrigins cfg S realized := by
          apply FFGGlobalCheckpointOrigins.update_checkpoints
          · exact hboosted
          · exact Or.inr ⟨sb.root, hboostedRoot, Or.inl
              (hcoh.transition_gj _ _ _ hscheduled hst)⟩
          · exact Or.inr ⟨sb.root, hboostedRoot, Or.inl
              (hcoh.transition_gf _ _ _ hscheduled hst)⟩
        have hsame : SameBlocks added realized :=
          hframe.sameBlocks.trans
            ((FastConfirmation.Spec.record_block_timeliness_sameBlocks
              cfg notified sb.root).trans
            ((FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
              staged (get_head cfg store).root sb.root).trans
              (FastConfirmation.Spec.update_checkpoints_sameBlocks boosted
                state.current_justified_checkpoint state.finalized_checkpoint)))
        have hrealizedRoot : sb.root ∈ realized.block_roots := by
          rw [← hsame.1]
          exact haddedRoot
        apply FFGGlobalCheckpointOrigins.compute_pulled_up_tip realized sb.root
          hrealized hrealizedRoot
        · rw [← hsame.2.2]
          simp only [added, Function.update_self]
          exact hcoh.transition_gu _ _ _ hscheduled hst
        · rw [← hsame.2.2]
          simp only [added, Function.update_self]
          exact hcoh.transition_guf _ _ _ hscheduled hst


end FFGGlobalCheckpointOrigins

namespace Execution

variable (E : Execution Root)







end Execution

namespace FFGGlobalCheckpointLedger

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}

/-! Small monotonicity facts for the two checkpoint-writing helpers.  Keeping
these facts explicit avoids hiding the temporal argument below in a large
handler simplification. -/

private theorem justified_epoch_le_update_checkpoints
    (store : Store Root) (jc fc : Checkpoint Root) :
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint.epoch := by
  have hfield :
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with hj
  · exact Nat.le_of_lt hj
  · exact Nat.le_refl _

private theorem candidate_epoch_le_update_checkpoints
    (store : Store Root) (jc fc : Checkpoint Root) :
    jc.epoch ≤
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint.epoch := by
  have hfield :
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with hj
  · exact Nat.le_refl _
  · exact Nat.le_of_not_gt hj

private theorem unrealized_epoch_le_update_unrealized
    (store : Store Root) (ujc ufc : Checkpoint Root) :
    store.unrealized_justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint.epoch := by
  have hfield :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint =
        if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
        else store.unrealized_justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with huj
  · exact Nat.le_of_lt huj
  · exact Nat.le_refl _

private theorem candidate_epoch_le_update_unrealized
    (store : Store Root) (ujc ufc : Checkpoint Root) :
    ujc.epoch ≤
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint.epoch := by
  have hfield :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint =
        if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
        else store.unrealized_justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with huj
  · exact Nat.le_refl _
  · exact Nat.le_of_not_gt huj

private theorem update_unrealized_justified_eq
    (store : Store Root) (ujc ufc : Checkpoint Root) :
    (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).justified_checkpoint =
      store.justified_checkpoint := by
  simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
  split_ifs <;> rfl

private theorem update_checkpoints_unrealized_justified_eq
    (store : Store Root) (jc fc : Checkpoint Root) :
    (FastConfirmation.Spec.update_checkpoints store jc fc).unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
  simp only [FastConfirmation.Spec.update_checkpoints]
  split_ifs <;> rfl

private theorem justified_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r).justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledJ : pulled.justified_checkpoint = store.justified_checkpoint := by
    exact (update_unrealized_justified_eq recorded
      state.current_justified_checkpoint state.finalized_checkpoint).trans rfl
  change store.justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled).justified_checkpoint.epoch
  split_ifs
  · exact (congrArg Checkpoint.epoch hpulledJ).symm.le.trans
      (justified_epoch_le_update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint)
  · exact (congrArg Checkpoint.epoch hpulledJ).symm.le

private theorem unrealized_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    store.unrealized_justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r).unrealized_justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hbase : store.unrealized_justified_checkpoint.epoch ≤
      pulled.unrealized_justified_checkpoint.epoch := by
    exact (unrealized_epoch_le_update_unrealized recorded
      state.current_justified_checkpoint state.finalized_checkpoint)
  change store.unrealized_justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled).unrealized_justified_checkpoint.epoch
  split_ifs
  · rw [update_checkpoints_unrealized_justified_eq]
    exact hbase
  · exact hbase

private theorem pulled_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    (ext.process_justification_and_finalization
        (store.block_states r)).current_justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r).unrealized_justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hbase : state.current_justified_checkpoint.epoch ≤
      pulled.unrealized_justified_checkpoint.epoch :=
    candidate_epoch_le_update_unrealized recorded
      state.current_justified_checkpoint state.finalized_checkpoint
  change state.current_justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled).unrealized_justified_checkpoint.epoch
  split_ifs
  · rw [update_checkpoints_unrealized_justified_eq]
    exact hbase
  · exact hbase



/-! ## Transport across checkpoint/block-domain preserving steps -/

/-- Transport the ledger across a helper which preserves the block domain and
the four global checkpoint fields. -/
theorem of_eq {store store' : Store Root}
    (h : FFGGlobalCheckpointLedger cfg S store)
    (hroots : store'.block_roots = store.block_roots)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint)
    (hf : store'.finalized_checkpoint = store.finalized_checkpoint)
    (huf : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    FFGGlobalCheckpointLedger cfg S store' := by
  constructor
  · unfold GlobalJustifiedOrigin at ⊢
    rw [hroots, hj]
    exact h.justified_origin
  · unfold GlobalUnrealizedJustifiedOrigin at ⊢
    rw [hroots, huj]
    exact h.unrealized_justified_origin
  · unfold GlobalFinalizedOrigin at ⊢
    rw [hroots, hf]
    exact h.finalized_origin
  · unfold GlobalUnrealizedFinalizedOrigin at ⊢
    rw [hroots, huf]
    exact h.unrealized_finalized_origin
  · intro r hr
    rw [hroots] at hr
    rw [hj]
    exact h.gj_epoch_le_justified r hr
  · intro r hr
    rw [hroots] at hr
    rw [huj]
    exact h.gu_epoch_le_unrealized r hr




/-! ## Pure checkpoint-update steps -/



/-! ## Tick preservation -/





theorem on_tick_per_slot_current_slot
    (store : Store Root) (time : ℕ) :
    get_current_slot cfg (FastConfirmation.Spec.on_tick_per_slot cfg store time) =
      get_current_slot cfg { store with time := time } := by
  simp only [get_current_slot, get_slots_since_genesis,
    FastConfirmation.Spec.on_tick_per_slot_time]
  rw [← (FastConfirmation.Spec.on_tick_per_slot_storeLE cfg store time).2.1]



theorem current_slot_at_next_boundary
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (store : Store Root) :
    get_current_slot cfg
        { store with
          time := store.genesis_time +
            (get_current_slot cfg store + 1) * cfg.slot_duration_ms / 1000 } =
      get_current_slot cfg store + 1 := by
  obtain ⟨secondsPerSlot, hduration⟩ := hdiv
  have hsecondsPos : 0 < secondsPerSlot := by
    have hdurationPos := cfg.slot_duration_ms_pos
    rw [hduration] at hdurationPos
    omega
  let nextSlot := get_current_slot cfg store + 1
  have hmilliseconds :
      nextSlot * cfg.slot_duration_ms / 1000 =
        nextSlot * secondsPerSlot := by
    rw [hduration]
    calc
      nextSlot * (1000 * secondsPerSlot) / 1000 =
          (1000 * (nextSlot * secondsPerSlot)) / 1000 := by
            congr 1
            ac_rfl
      _ = nextSlot * secondsPerSlot :=
        Nat.mul_div_cancel_left _ (by omega : (0 : ℕ) < 1000)
  have htarget :
      get_current_slot cfg
          { store with
            time := store.genesis_time +
              (get_current_slot cfg store + 1) * cfg.slot_duration_ms / 1000 } =
        (store.genesis_time +
            (get_current_slot cfg store + 1) * cfg.slot_duration_ms / 1000 -
          store.genesis_time) * 1000 / cfg.slot_duration_ms := by
    simp only [get_current_slot, get_slots_since_genesis, GENESIS_SLOT,
      Nat.zero_add]
  rw [htarget]
  change ((store.genesis_time +
      nextSlot * cfg.slot_duration_ms / 1000 - store.genesis_time) * 1000 /
        cfg.slot_duration_ms) = nextSlot
  rw [hmilliseconds, Nat.add_sub_cancel_left, hduration]
  calc
    nextSlot * secondsPerSlot * 1000 / (1000 * secondsPerSlot) =
        nextSlot * (1000 * secondsPerSlot) / (1000 * secondsPerSlot) := by
          congr 1
          ac_rfl
    _ = nextSlot := Nat.mul_div_cancel nextSlot (by omega)

theorem on_tick_aux_eq_of_not_lt
    (tickSlot fuel : ℕ) (store : Store Root)
    (h : ¬ get_current_slot cfg store < tickSlot) :
    FastConfirmation.Spec.on_tick_aux cfg tickSlot fuel store = store := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [FastConfirmation.Spec.on_tick_aux, if_neg h]

theorem on_tick_aux_one_slot
    (store : Store Root) (s : Slot)
    (hslot : get_current_slot cfg store = s)
    (hdiv : 1000 ∣ cfg.slot_duration_ms) :
    FastConfirmation.Spec.on_tick_aux cfg (s + 1) (s + 2) store =
      FastConfirmation.Spec.on_tick_per_slot cfg store
        (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000) := by
  have hfuel : s + 2 = (s + 1) + 1 := rfl
  rw [hfuel, FastConfirmation.Spec.on_tick_aux]
  rw [if_pos (by rw [hslot]; exact Nat.lt_succ_self _)]
  rw [hslot]
  let stepped := FastConfirmation.Spec.on_tick_per_slot cfg store
    (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000)
  have hstepped : get_current_slot cfg stepped = s + 1 := by
    rw [on_tick_per_slot_current_slot]
    simpa only [hslot] using current_slot_at_next_boundary
      (cfg := cfg) hdiv store
  rw [FastConfirmation.Spec.on_tick_aux]
  rw [if_neg (by rw [hstepped]; exact Nat.lt_irrefl _)]




/-! ## Event-handler preservation -/

theorem record_block_timeliness (store : Store Root) (r : Root)
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S
      (FastConfirmation.Spec.record_block_timeliness cfg store r) := by
  simp only [FastConfirmation.Spec.record_block_timeliness]
  exact h.of_eq rfl rfl rfl rfl rfl

theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;> exact h.of_eq rfl rfl rfl rfl rfl


theorem update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h.of_eq rfl rfl rfl rfl rfl



/-- A successful scheduled block insertion offers the new post-state `GJ`
to the realized maximum and the new eager `GU` to the unrealized maximum.
All older roots retain their previous bounds. -/
theorem on_block
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hscheduled : ∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n)
    (h : FFGGlobalCheckpointLedger cfg S store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    FFGGlobalCheckpointLedger cfg S store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [FastConfirmation.Spec.on_block, if_pos hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
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
        | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
            (FastConfirmation.Spec.update_checkpoints
              (FastConfirmation.Spec.update_proposer_boost_root cfg
                (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
                (get_head cfg store).root sb.root)
              state.current_justified_checkpoint state.finalized_checkpoint) sb.root)) =
          some store' at hh
      cases hn : notify_ptc_messages cfg ext added state sb.message.payload_attestations with
      | none => rw [hn] at hh; cases hh
      | some notified =>
        rw [hn] at hh
        cases hh
        have hframe := notify_ptc_messages_frame cfg ext hn
        let staged := FastConfirmation.Spec.record_block_timeliness cfg notified sb.root
        let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
          (get_head cfg store).root sb.root
        let realized := FastConfirmation.Spec.update_checkpoints boosted
          state.current_justified_checkpoint state.finalized_checkpoint
        suffices hresult : FFGGlobalCheckpointLedger cfg S
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
          exact hresult
        have hsub : store.block_roots ⊆ added.block_roots := by
          intro r hr
          exact List.mem_append_left _ hr
        have haddedRoot : sb.root ∈ added.block_roots := by
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hrootCases : ∀ r ∈ added.block_roots,
            r ∈ store.block_roots ∨ r = sb.root := by
          intro r hr
          simpa only [added, List.mem_append, List.mem_singleton] using hr
        have haddedOrigins : FFGGlobalCheckpointOrigins cfg S added := by
          apply h.origins.of_extension hsub <;> rfl
        have hstagedOrigins : FFGGlobalCheckpointOrigins cfg S staged :=
          FFGGlobalCheckpointOrigins.record_block_timeliness notified sb.root
            (haddedOrigins.of_payloadFrame hframe)
        have hboostedOrigins : FFGGlobalCheckpointOrigins cfg S boosted :=
          FFGGlobalCheckpointOrigins.update_proposer_boost_root staged
            (get_head cfg store).root sb.root hstagedOrigins
        have hboostedRoot : sb.root ∈ boosted.block_roots := by
          have hs := hframe.sameBlocks.trans
            ((FastConfirmation.Spec.record_block_timeliness_sameBlocks
              cfg notified sb.root).trans
            (FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
              staged (get_head cfg store).root sb.root))
          rw [← hs.1]
          exact haddedRoot
        have hrealizedOrigins : FFGGlobalCheckpointOrigins cfg S realized := by
          apply FFGGlobalCheckpointOrigins.update_checkpoints
          · exact hboostedOrigins
          · exact Or.inr ⟨sb.root, hboostedRoot, Or.inl
              (hcoh.transition_gj _ _ _ hscheduled hst)⟩
          · exact Or.inr ⟨sb.root, hboostedRoot, Or.inl
              (hcoh.transition_gf _ _ _ hscheduled hst)⟩
        have hsame : SameBlocks added realized :=
          hframe.sameBlocks.trans
            ((FastConfirmation.Spec.record_block_timeliness_sameBlocks
              cfg notified sb.root).trans
            ((FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
              staged (get_head cfg store).root sb.root).trans
              (FastConfirmation.Spec.update_checkpoints_sameBlocks boosted
                state.current_justified_checkpoint state.finalized_checkpoint)))
        have hrealizedRoot : sb.root ∈ realized.block_roots := by
          rw [← hsame.1]
          exact haddedRoot
        have hrealizedState : realized.block_states sb.root = state := by
          rw [← hsame.2.2]
          simp only [added, Function.update_self]
        have hresultOrigins : FFGGlobalCheckpointOrigins cfg S
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) := by
          apply FFGGlobalCheckpointOrigins.compute_pulled_up_tip realized sb.root
            hrealizedOrigins hrealizedRoot
          · rw [← hsame.2.2]
            simp only [added, Function.update_self]
            exact hcoh.transition_gu _ _ _ hscheduled hst
          · rw [← hsame.2.2]
            simp only [added, Function.update_self]
            exact hcoh.transition_guf _ _ _ hscheduled hst
        have hboostedJ : boosted.justified_checkpoint =
            store.justified_checkpoint := by
          simp only [boosted, staged, added,
            FastConfirmation.Spec.update_proposer_boost_root,
            FastConfirmation.Spec.record_block_timeliness]
          split_ifs <;> exact hframe.justified_checkpoint
        have hboostedUJ : boosted.unrealized_justified_checkpoint =
            store.unrealized_justified_checkpoint := by
          simp only [boosted, staged, added,
            FastConfirmation.Spec.update_proposer_boost_root,
            FastConfirmation.Spec.record_block_timeliness]
          split_ifs <;> exact hframe.unrealized_justified_checkpoint
        have hrealizedUJ : realized.unrealized_justified_checkpoint =
            boosted.unrealized_justified_checkpoint := by
          simp only [realized, FastConfirmation.Spec.update_checkpoints]
          split_ifs <;> rfl
        have hfinalRoots :
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root).block_roots =
              added.block_roots := by
          have hp := FastConfirmation.Spec.compute_pulled_up_tip_sameBlocks
            cfg ext realized sb.root
          exact hp.1.symm.trans hsame.1.symm
        refine ⟨hresultOrigins.justified, hresultOrigins.unrealized_justified,
          hresultOrigins.finalized, hresultOrigins.unrealized_finalized, ?_, ?_⟩
        · intro r hr
          rw [hfinalRoots] at hr
          rcases hrootCases r hr with hrold | rfl
          · exact (h.gj_epoch_le_justified r hrold).trans
              ((congrArg Checkpoint.epoch hboostedJ.symm).le.trans
                ((justified_epoch_le_update_checkpoints boosted
                    state.current_justified_checkpoint state.finalized_checkpoint).trans
                  (justified_epoch_le_compute_pulled_up_tip
                    (cfg := cfg) (ext := ext) realized sb.root)))
          · rw [← hcoh.transition_gj _ _ _ hscheduled hst]
            exact (candidate_epoch_le_update_checkpoints boosted
                state.current_justified_checkpoint state.finalized_checkpoint).trans
              (justified_epoch_le_compute_pulled_up_tip
                (cfg := cfg) (ext := ext) realized sb.root)
        · intro r hr
          rw [hfinalRoots] at hr
          rcases hrootCases r hr with hrold | rfl
          · exact (h.gu_epoch_le_unrealized r hrold).trans
              ((congrArg Checkpoint.epoch hboostedUJ.symm).le.trans
                ((congrArg Checkpoint.epoch hrealizedUJ.symm).le.trans
                  (unrealized_epoch_le_compute_pulled_up_tip
                    (cfg := cfg) (ext := ext) realized sb.root)))
          · rw [← hcoh.transition_gu _ _ _ hscheduled hst]
            rw [← hrealizedState]
            exact pulled_epoch_le_compute_pulled_up_tip
              (cfg := cfg) (ext := ext) realized sb.root








end FFGGlobalCheckpointLedger

namespace Execution

variable (E : Execution Root)








end Execution

end FastConfirmation.Spec

end
