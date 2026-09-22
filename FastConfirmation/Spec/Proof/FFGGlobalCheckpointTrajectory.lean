import FastConfirmation.Spec.Proof.FFGEndpointRealization

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

/-- Every block which is old enough for `get_voting_source` to read `GU` has
had that eager checkpoint pulled into the realized global maximum. -/
def OldGURealized (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots,
    get_block_epoch cfg store r < get_current_store_epoch cfg store →
      (S.GU r).epoch ≤ store.justified_checkpoint.epoch

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

theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root)
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
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

theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {is_from_block : Bool}
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    FFGGlobalCheckpointOrigins cfg S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact update_latest_messages _ _ _
    (store_target_checkpoint_state _ _ h)

theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root}
    (h : FFGGlobalCheckpointOrigins cfg S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl = some store') :
    FFGGlobalCheckpointOrigins cfg S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl

private theorem unrealizedJustified_to_justified {store : Store Root}
    {c : Checkpoint Root}
    (h : GlobalUnrealizedJustifiedOrigin cfg S store c) :
    GlobalJustifiedOrigin cfg S store c := by
  rcases h with hanchor | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor
  · exact Or.inr ⟨r, hr, Or.inr hgu⟩

private theorem unrealizedFinalized_to_finalized {store : Store Root}
    {c : Checkpoint Root}
    (h : GlobalUnrealizedFinalizedOrigin cfg S store c) :
    GlobalFinalizedOrigin cfg S store c := by
  rcases h with hanchor | ⟨r, hr, hguf⟩
  · exact Or.inl hanchor
  · exact Or.inr ⟨r, hr, Or.inr hguf⟩

theorem on_tick_per_slot (store : Store Root) (time : ℕ)
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  split_ifs
  all_goals
    first
    | exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
    | · apply FFGGlobalCheckpointOrigins.update_checkpoints
        · exact h.of_extension (List.Subset.refl _) rfl rfl rfl rfl
        · exact unrealizedJustified_to_justified
            (by simpa using h.unrealized_justified)
        · exact unrealizedFinalized_to_finalized
            (by simpa using h.unrealized_finalized)

theorem on_tick_aux (tick_slot fuel : ℕ) :
    ∀ store : Store Root, FFGGlobalCheckpointOrigins cfg S store →
      FFGGlobalCheckpointOrigins cfg S
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
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
      (FastConfirmation.Spec.on_tick cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick]
  exact on_tick_per_slot _ _ (on_tick_aux _ _ _ h)

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
      cases hh
      have hsub : store.block_roots ⊆
          (if sb.root ∈ store.block_roots then store.block_roots
            else store.block_roots ++ [sb.root]) := by
        intro r hr
        by_cases hrs : sb.root ∈ store.block_roots
        · simpa [hrs] using hr
        · simp [hrs, hr]
      have hroot : sb.root ∈
          (if sb.root ∈ store.block_roots then store.block_roots
            else store.block_roots ++ [sb.root]) := by
        by_cases hrs : sb.root ∈ store.block_roots
        · simpa [hrs] using hrs
        · simp [hrs]
      let added : Store Root :=
        { store with
          block_roots := if sb.root ∈ store.block_roots then
              store.block_roots else store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root state }
      let staged := FastConfirmation.Spec.record_block_timeliness cfg added sb.root
      let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := FastConfirmation.Spec.update_checkpoints boosted
        state.current_justified_checkpoint state.finalized_checkpoint
      suffices hresult : FFGGlobalCheckpointOrigins cfg S
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
        dsimp only [realized, boosted, staged, added] at hresult ⊢
        split_ifs at hresult <;> exact hresult
      have hadded : FFGGlobalCheckpointOrigins cfg S added := by
        apply h.of_extension
        · simpa only [added] using hsub
        all_goals rfl
      have hstaged : FFGGlobalCheckpointOrigins cfg S staged :=
        FFGGlobalCheckpointOrigins.record_block_timeliness added sb.root hadded
      have hboosted : FFGGlobalCheckpointOrigins cfg S boosted :=
        FFGGlobalCheckpointOrigins.update_proposer_boost_root staged
          (get_head cfg store).root sb.root hstaged
      have haddedRoot : sb.root ∈ added.block_roots := by
        simpa only [added] using hroot
      have hboostedRoot : sb.root ∈ boosted.block_roots := by
        have hs := (FastConfirmation.Spec.record_block_timeliness_sameBlocks
          cfg added sb.root).trans
          (FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
            staged (get_head cfg store).root sb.root)
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
        (FastConfirmation.Spec.record_block_timeliness_sameBlocks
          cfg added sb.root).trans
          ((FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
            staged (get_head cfg store).root sb.root).trans
            (FastConfirmation.Spec.update_checkpoints_sameBlocks boosted
              state.current_justified_checkpoint state.finalized_checkpoint))
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

theorem apply_event_getD
    (hcoh : FFGTransitionCoherence cfg ext S)
    (store : Store Root) (event : Event Root)
    (hscheduled : event ∈ E.schedule w n)
    (h : FFGGlobalCheckpointOrigins cfg S store) :
    FFGGlobalCheckpointOrigins cfg S
      ((FastConfirmation.Spec.apply_event cfg ext store event).getD store) := by
  cases heq : FastConfirmation.Spec.apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
    simp only [Option.getD_some]
    cases event with
    | block sb =>
        exact on_block hcoh ⟨w, n, hscheduled⟩ h heq
    | attestation a is_from_block =>
        exact on_attestation h heq
    | attester_slashing sl =>
        exact on_attester_slashing h heq

end FFGGlobalCheckpointOrigins

namespace Execution

variable (E : Execution Root)

private theorem slot_at_succ_le
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (n : ℕ) :
    E.slot_at cfg (n + 1) ≤ E.slot_at cfg n + 1 := by
  have hdivKeep := hdiv
  obtain ⟨secondsPerSlot, hduration⟩ := hdivKeep
  have hsecondsPos : 0 < secondsPerSlot := by
    have hdurationPos := cfg.slot_duration_ms_pos
    rw [hduration] at hdurationPos
    omega
  have hdenPos : 0 < cfg.slot_duration_ms / 1000 := by
    rw [hduration, Nat.mul_div_cancel_left secondsPerSlot
      (by omega : (0 : ℕ) < 1000)]
    exact hsecondsPos
  rw [E.slot_at_eq cfg hdiv, E.slot_at_eq cfg hdiv]
  have hnum : E.genesis_store.time + (n + 1) -
        E.genesis_store.genesis_time =
      (E.genesis_store.time + n - E.genesis_store.genesis_time) + 1 := by
    omega
  rw [hnum]
  let a := E.genesis_store.time + n - E.genesis_store.genesis_time
  calc
    (a + 1) / (cfg.slot_duration_ms / 1000) ≤
        (a + cfg.slot_duration_ms / 1000) /
          (cfg.slot_duration_ms / 1000) :=
      Nat.div_le_div_right (by omega)
    _ = a / (cfg.slot_duration_ms / 1000) + 1 :=
      Nat.add_div_right a hdenPos

private theorem globalCheckpointOrigins_foldl
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ) :
    ∀ (events : List (Event Root)), events ⊆ E.schedule w n →
      ∀ store : Store Root, FFGGlobalCheckpointOrigins cfg S store →
        FFGGlobalCheckpointOrigins cfg S
          (events.foldl (fun st event =>
            (FastConfirmation.Spec.apply_event cfg ext st event).getD st) store) := by
  intro events
  induction events with
  | nil => intro _ store h; exact h
  | cons event rest ih =>
      intro hevents store h
      rw [List.foldl_cons]
      apply ih
      · exact fun x hx => hevents (List.mem_cons_of_mem _ hx)
      · exact FFGGlobalCheckpointOrigins.apply_event_getD hcoh store event
          (hevents List.mem_cons_self) h

/-- Every reachable store-global checkpoint has exact handler provenance:
trusted anchor, block-state `GJ/GF`, or eager-pull-up `GU/GUF`. -/
theorem globalCheckpointOrigins
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    FFGGlobalCheckpointOrigins cfg S (E.store cfg ext w n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgeq, _hslot⟩ := hgen
      change FFGGlobalCheckpointOrigins cfg S E.genesis_store
      rw [hgeq] at hanchor ⊢
      constructor <;> apply Or.inl <;>
        simpa only [get_forkchoice_store] using hanchor.symm
  | succ n ih =>
      change FFGGlobalCheckpointOrigins cfg S
        ((E.schedule w (n + 1)).foldl
          (fun store event =>
            (FastConfirmation.Spec.apply_event cfg ext store event).getD store)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      apply globalCheckpointOrigins_foldl (cfg := cfg) (ext := ext)
        (E := E) hcoh w (n + 1)
        (E.schedule w (n + 1)) (List.Subset.refl _)
      exact FFGGlobalCheckpointOrigins.on_tick _ _ ih

/-- The realized global justified checkpoint is either the trusted anchor or
is AU at a known concrete block which installed it. -/
theorem globalJustified_anchor_or_known_AU
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext w n).justified_checkpoint = anchor ∨
      ∃ r ∈ (E.store cfg ext w n).block_roots,
        S.AU cfg r (E.store cfg ext w n).justified_checkpoint := by
  rcases (globalCheckpointOrigins (cfg := cfg) (ext := ext) (E := E)
    hcoh hgen hanchor w n).justified with
    hanchor | ⟨r, hr, hgj | hgu⟩
  · exact Or.inl hanchor
  · right
    refine ⟨r, hr, ?_⟩
    rw [hgj]
    exact S.gj_AU cfg r ⟨_, E.blockAt_of_store_known cfg ext hr⟩
  · right
    refine ⟨r, hr, ?_⟩
    rw [hgu]
    exact S.gu_AU cfg r ⟨_, E.blockAt_of_store_known cfg ext hr⟩

/-- The finalized global checkpoint has the analogous exact `GF/GUF`
carrier provenance.  The AU conclusion uses the semantic invariant
`AF ⊆ AU`; no free finalized-root assumption is introduced. -/
theorem globalFinalized_anchor_or_known_AU
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext w n).finalized_checkpoint = anchor ∨
      ∃ r ∈ (E.store cfg ext w n).block_roots,
        S.AU cfg r (E.store cfg ext w n).finalized_checkpoint := by
  rcases (globalCheckpointOrigins (cfg := cfg) (ext := ext) (E := E)
    hcoh hgen hanchor w n).finalized with
    hanchor | ⟨r, hr, hgf | hguf⟩
  · exact Or.inl hanchor
  · right
    refine ⟨r, hr, ?_⟩
    rw [hgf]
    exact S.gf_AU cfg r ⟨_, E.blockAt_of_store_known cfg ext hr⟩
  · right
    refine ⟨r, hr, ?_⟩
    rw [hguf]
    exact S.guf_AU cfg r ⟨_, E.blockAt_of_store_known cfg ext hr⟩

/-- Minimal checkpoint-sync boundary premise.  It asks only that the trusted
anchor block represent a block at or before its declared epoch boundary; it
does not require the anchor epoch or slot to be genesis.  Together with the
ordinary slot/epoch relation this is exactly boundary alignment. -/
def TrustedAnchorBoundaryAligned : Prop :=
  (E.genesis_store.blocks anchor.root).slot ≤
    compute_start_slot_at_epoch cfg anchor.epoch

/-- Global finalized provenance plus a boundary-aligned trusted anchor
discharges `FinalizedBoundaryRealization` at every honest endpoint. -/
theorem finalizedBoundaryRealization_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hHm : E.WithinHorizon cfg m) :
    FinalizedBoundaryRealization cfg (E.store cfg ext w m) := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  have hanchorRoot : anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : anchor.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext w m).blocks anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hA.wellFormed hgenEq w m
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hwf : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      hgen hA.wellFormed.anchor_parent_unscheduled w m
  rcases globalFinalized_anchor_or_known_AU (cfg := cfg) (ext := ext)
      (E := E) hcoh hgenShort hanchor w m with
    hfinalAnchor | ⟨carrier, hcarrier, hAU⟩
  · constructor
    · rw [hfinalAnchor]
      exact hanchorMem
    · rw [hfinalAnchor, hanchorBlock]
      exact hboundary'
  · have hanchorEpochLe : anchor.epoch ≤
        (E.store cfg ext w m).finalized_checkpoint.epoch := by
      obtain ⟨hcert⟩ := S.certifiedJustified_of_AU cfg hAU
      exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
    have hstartLe : compute_start_slot_at_epoch cfg anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch := by
      exact Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks anchor.root).slot carrier :=
      E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence
        hgen w m anchor.root hanchorMem carrier hcarrier
    have hwalk : WalkKnown (E.store cfg ext w m)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext w m).finalized_checkpoint.epoch) carrier := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    exact E.finalizedBoundaryRealization_of_ffgAU cfg ext hcoh hw hHm
      hwf hcarrier hAU hwalk

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

private theorem pulled_epoch_le_realized_of_old
    (store : Store Root) (r : Root)
    (hold : get_block_epoch cfg store r <
      get_current_store_epoch cfg store) :
    (ext.process_justification_and_finalization
        (store.block_states r)).current_justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r).justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledSame : SameBlocks recorded pulled :=
    FastConfirmation.Spec.update_unrealized_checkpoints_sameBlocks recorded
      state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledBlocks : pulled.blocks = store.blocks :=
    hpulledSame.2.1.symm.trans rfl
  have hpulledTime : pulled.time = store.time := by
    exact (FastConfirmation.Spec.update_unrealized_checkpoints_time recorded
      state.current_justified_checkpoint state.finalized_checkpoint).trans rfl
  have hpulledGenesis : pulled.genesis_time = store.genesis_time := by
    exact (FastConfirmation.Spec.update_unrealized_checkpoints_genesis_time recorded
      state.current_justified_checkpoint state.finalized_checkpoint).trans rfl
  have hpulledCurrent : get_current_store_epoch cfg pulled =
      get_current_store_epoch cfg store := by
    simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg hpulledTime hpulledGenesis)
  have hpull : compute_epoch_at_slot cfg (pulled.blocks r).slot <
      get_current_store_epoch cfg pulled := by
    simpa only [get_block_epoch, hpulledBlocks, hpulledCurrent] using hold
  change state.current_justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled).justified_checkpoint.epoch
  rw [if_pos hpull]
  exact candidate_epoch_le_update_checkpoints pulled
    state.current_justified_checkpoint state.finalized_checkpoint

private theorem compute_pulled_up_tip_current_epoch
    (store : Store Root) (r : Root) :
    get_current_store_epoch cfg
        (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) =
      get_current_store_epoch cfg store := by
  simp only [get_current_store_epoch]
  exact congrArg (compute_epoch_at_slot cfg)
    (get_current_slot_congr cfg
      (FastConfirmation.Spec.compute_pulled_up_tip_time cfg ext store r)
      (FastConfirmation.Spec.compute_pulled_up_tip_storeLE cfg ext store r).2.1.symm)

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

/-- An unrealized justified origin is also an admissible realized global
origin when `update_checkpoints` pulls it up at an epoch transition. -/
theorem unrealizedJustified_to_justified {store : Store Root}
    {c : Checkpoint Root}
    (h : GlobalUnrealizedJustifiedOrigin cfg S store c) :
    GlobalJustifiedOrigin cfg S store c := by
  rcases h with hanchor | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor
  · exact Or.inr ⟨r, hr, Or.inr hgu⟩

/-- The finalized analogue of `unrealizedJustified_to_justified`. -/
theorem unrealizedFinalized_to_finalized {store : Store Root}
    {c : Checkpoint Root}
    (h : GlobalUnrealizedFinalizedOrigin cfg S store c) :
    GlobalFinalizedOrigin cfg S store c := by
  rcases h with hanchor | ⟨r, hr, hguf⟩
  · exact Or.inl hanchor
  · exact Or.inr ⟨r, hr, Or.inr hguf⟩

/-! ## Pure checkpoint-update steps -/

theorem update_checkpoints (store : Store Root) (jc fc : Checkpoint Root)
    (h : FFGGlobalCheckpointLedger cfg S store)
    (hjc : GlobalJustifiedOrigin cfg S store jc)
    (hfc : GlobalFinalizedOrigin cfg S store fc) :
    FFGGlobalCheckpointLedger cfg S (update_checkpoints store jc fc) := by
  have hroots : (FastConfirmation.Spec.update_checkpoints store jc fc).block_roots =
      store.block_roots := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hjField :
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hfField :
      (FastConfirmation.Spec.update_checkpoints store jc fc).finalized_checkpoint =
        if fc.epoch > store.finalized_checkpoint.epoch then fc
        else store.finalized_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have huEq :
      (FastConfirmation.Spec.update_checkpoints store jc fc).unrealized_justified_checkpoint =
        store.unrealized_justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hufEq :
      (FastConfirmation.Spec.update_checkpoints store jc fc).unrealized_finalized_checkpoint =
        store.unrealized_finalized_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hjOld : store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.update_checkpoints store jc fc).justified_checkpoint.epoch := by
    rw [hjField]
    split_ifs with hj
    · exact Nat.le_of_lt hj
    · exact Nat.le_refl _
  constructor
  · unfold GlobalJustifiedOrigin at hjc ⊢
    rw [hroots]
    rw [hjField]
    split_ifs
    · exact hjc
    · exact h.justified_origin
  · unfold GlobalUnrealizedJustifiedOrigin at ⊢
    rw [huEq, hroots]
    exact h.unrealized_justified_origin
  · unfold GlobalFinalizedOrigin at hfc ⊢
    rw [hroots]
    rw [hfField]
    split_ifs
    · exact hfc
    · exact h.finalized_origin
  · unfold GlobalUnrealizedFinalizedOrigin at ⊢
    rw [hufEq, hroots]
    exact h.unrealized_finalized_origin
  · intro r hr
    rw [hroots] at hr
    exact (h.gj_epoch_le_justified r hr).trans hjOld
  · intro r hr
    rw [hroots] at hr
    rw [huEq]
    exact h.gu_epoch_le_unrealized r hr

theorem update_unrealized_checkpoints (store : Store Root)
    (ujc ufc : Checkpoint Root)
    (h : FFGGlobalCheckpointLedger cfg S store)
    (hujc : GlobalUnrealizedJustifiedOrigin cfg S store ujc)
    (hufc : GlobalUnrealizedFinalizedOrigin cfg S store ufc) :
    FFGGlobalCheckpointLedger cfg S
      (update_unrealized_checkpoints store ujc ufc) := by
  have hroots :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).block_roots =
        store.block_roots := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hjEq :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).justified_checkpoint =
        store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hfEq :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).finalized_checkpoint =
        store.finalized_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have huField :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint =
        if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
        else store.unrealized_justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hufField :
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_finalized_checkpoint =
        if ufc.epoch > store.unrealized_finalized_checkpoint.epoch then ufc
        else store.unrealized_finalized_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have huOld : store.unrealized_justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint.epoch := by
    rw [huField]
    split_ifs with hu
    · exact Nat.le_of_lt hu
    · exact Nat.le_refl _
  constructor
  · unfold GlobalJustifiedOrigin at ⊢
    rw [hjEq, hroots]
    exact h.justified_origin
  · unfold GlobalUnrealizedJustifiedOrigin at hujc ⊢
    rw [hroots]
    rw [huField]
    split_ifs
    · exact hujc
    · exact h.unrealized_justified_origin
  · unfold GlobalFinalizedOrigin at ⊢
    rw [hfEq, hroots]
    exact h.finalized_origin
  · unfold GlobalUnrealizedFinalizedOrigin at hufc ⊢
    rw [hroots]
    rw [hufField]
    split_ifs
    · exact hufc
    · exact h.unrealized_finalized_origin
  · intro r hr
    rw [hroots] at hr
    rw [hjEq]
    exact h.gj_epoch_le_justified r hr
  · intro r hr
    rw [hroots] at hr
    exact (h.gu_epoch_le_unrealized r hr).trans huOld

/-! ## Tick preservation -/

private theorem oldGU_of_sameBlocks
    {store store' : Store Root}
    (h : OldGURealized cfg S store)
    (hsame : SameBlocks store store')
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (hepoch : get_current_store_epoch cfg store' ≤
      get_current_store_epoch cfg store) :
    OldGURealized cfg S store' := by
  intro r hr hrold
  have hr' : r ∈ store.block_roots := by
    rw [hsame.1]
    exact hr
  have hblock : get_block_epoch cfg store r =
      get_block_epoch cfg store' r := by
    simp only [get_block_epoch]
    rw [hsame.2.1]
  have hrold' : get_block_epoch cfg store r <
      get_current_store_epoch cfg store := by
    rw [hblock]
    exact hrold.trans_le hepoch
  rw [hj]
  exact h r hr' hrold'

/-- Crossing to a different epoch in exactly one slot lands at its boundary. -/
private theorem slots_since_succ_eq_zero_of_epoch_lt (s : Slot)
    (h : compute_epoch_at_slot cfg s <
      compute_epoch_at_slot cfg (s + 1)) :
    compute_slots_since_epoch_start cfg (s + 1) = 0 := by
  change s / cfg.slots_per_epoch <
    (s + 1) / cfg.slots_per_epoch at h
  have hq : s / cfg.slots_per_epoch + 1 ≤
      (s + 1) / cfg.slots_per_epoch := Nat.succ_le_of_lt h
  have hlo : (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch ≤
      s + 1 :=
    (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hq
  have hhi : s <
      (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch :=
    (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).mp
      (Nat.lt_succ_self (s / cfg.slots_per_epoch))
  have heq : s + 1 =
      (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch := by
    exact Nat.le_antisymm (Nat.succ_le_of_lt hhi) hlo
  simp only [compute_slots_since_epoch_start,
    compute_start_slot_at_epoch, compute_epoch_at_slot]
  rw [heq, Nat.mul_div_cancel _ cfg.slots_per_epoch_pos]
  exact Nat.sub_self _

private theorem epoch_succ_le_of_slots_since_ne_zero (s : Slot)
    (h : compute_slots_since_epoch_start cfg (s + 1) ≠ 0) :
    compute_epoch_at_slot cfg (s + 1) ≤
      compute_epoch_at_slot cfg s := by
  by_contra hle
  exact h (slots_since_succ_eq_zero_of_epoch_lt (cfg := cfg) s
    (Nat.lt_of_not_ge hle))

theorem on_tick_per_slot_current_slot
    (store : Store Root) (time : ℕ) :
    get_current_slot cfg (FastConfirmation.Spec.on_tick_per_slot cfg store time) =
      get_current_slot cfg { store with time := time } := by
  simp only [get_current_slot, get_slots_since_genesis,
    FastConfirmation.Spec.on_tick_per_slot_time]
  rw [← (FastConfirmation.Spec.on_tick_per_slot_storeLE cfg store time).2.1]

theorem oldGU_on_tick_per_slot_same
    (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store)
    (h : OldGURealized cfg S store) :
    OldGURealized cfg S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  apply oldGU_of_sameBlocks h
    (FastConfirmation.Spec.on_tick_per_slot_sameBlocks cfg store time)
  · simp only [FastConfirmation.Spec.on_tick_per_slot]
    rw [hcurrent]
    simp
  · simp only [get_current_store_epoch]
    rw [on_tick_per_slot_current_slot, hcurrent]

theorem oldGU_on_tick_per_slot_next
    (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store + 1)
    (hledger : FFGGlobalCheckpointLedger cfg S store)
    (h : OldGURealized cfg S store) :
    OldGURealized cfg S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  have hadvance : get_current_slot cfg { store with time := time } >
      get_current_slot cfg store := by
    rw [hcurrent]
    exact Nat.lt_succ_self _
  by_cases hstart : compute_slots_since_epoch_start cfg
      (get_current_slot cfg store + 1) = 0
  · intro r hr _hrold
    have hsame := FastConfirmation.Spec.on_tick_per_slot_sameBlocks
      cfg store time
    have hr' : r ∈ store.block_roots := by
      rw [hsame.1]
      exact hr
    have hpull : store.unrealized_justified_checkpoint.epoch ≤
        (FastConfirmation.Spec.on_tick_per_slot cfg store time).justified_checkpoint.epoch := by
      have hstart' : compute_slots_since_epoch_start cfg
          (get_current_slot cfg { store with time := time }) = 0 := by
        rw [hcurrent]
        exact hstart
      simp only [FastConfirmation.Spec.on_tick_per_slot]
      rw [if_pos hadvance, if_pos ⟨hadvance, hstart'⟩]
      exact candidate_epoch_le_update_checkpoints _ _ _
    exact (hledger.gu_epoch_le_unrealized r hr').trans hpull
  · apply oldGU_of_sameBlocks h
      (FastConfirmation.Spec.on_tick_per_slot_sameBlocks cfg store time)
    · have hstart' : compute_slots_since_epoch_start cfg
          (get_current_slot cfg { store with time := time }) ≠ 0 := by
        rw [hcurrent]
        exact hstart
      simp only [FastConfirmation.Spec.on_tick_per_slot]
      rw [if_pos hadvance, if_neg (fun hpull => hstart' hpull.2)]
    · simp only [get_current_store_epoch]
      rw [on_tick_per_slot_current_slot, hcurrent]
      exact epoch_succ_le_of_slots_since_ne_zero
        (cfg := cfg) (get_current_slot cfg store) hstart

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

theorem on_tick_per_slot (store : Store Root) (time : ℕ)
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S (on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  split_ifs
  all_goals
    first
    | exact h.of_eq rfl rfl rfl rfl rfl
    | · apply FFGGlobalCheckpointLedger.update_checkpoints
        · apply h.of_eq <;> rfl
        · exact unrealizedJustified_to_justified
            (by simpa using h.unrealized_justified_origin)
        · exact unrealizedFinalized_to_finalized
            (by simpa using h.unrealized_finalized_origin)

theorem on_tick_aux (tick_slot fuel : ℕ) :
    ∀ store : Store Root, FFGGlobalCheckpointLedger cfg S store →
      FFGGlobalCheckpointLedger cfg S
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
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S (FastConfirmation.Spec.on_tick cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick]
  exact on_tick_per_slot _ _ (on_tick_aux _ _ _ h)

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

theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root)
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
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

theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {is_from_block : Bool}
    (h : FFGGlobalCheckpointLedger cfg S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    FFGGlobalCheckpointLedger cfg S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact update_latest_messages _ _ _
    (store_target_checkpoint_state _ _ h)

theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root}
    (h : FFGGlobalCheckpointLedger cfg S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl = some store') :
    FFGGlobalCheckpointLedger cfg S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl rfl rfl

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
      cases hh
      let added : Store Root :=
        { store with
          block_roots := if sb.root ∈ store.block_roots then
              store.block_roots else store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root state }
      let staged := FastConfirmation.Spec.record_block_timeliness cfg added sb.root
      let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := FastConfirmation.Spec.update_checkpoints boosted
        state.current_justified_checkpoint state.finalized_checkpoint
      suffices hresult : FFGGlobalCheckpointLedger cfg S
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
        dsimp only [realized, boosted, staged, added] at hresult ⊢
        split_ifs at hresult <;> exact hresult
      have hsub : store.block_roots ⊆ added.block_roots := by
        intro r hr
        by_cases hrs : sb.root ∈ store.block_roots
        · simpa [added, hrs] using hr
        · simp [added, hrs, hr]
      have haddedRoot : sb.root ∈ added.block_roots := by
        by_cases hrs : sb.root ∈ store.block_roots
        · simpa [added, hrs] using hrs
        · simp [added, hrs]
      have hrootCases : ∀ r ∈ added.block_roots,
          r ∈ store.block_roots ∨ r = sb.root := by
        intro r hr
        by_cases hrs : sb.root ∈ store.block_roots
        · exact Or.inl (by simpa [added, hrs] using hr)
        · simpa [added, hrs, List.mem_append, List.mem_singleton] using hr
      have haddedOrigins : FFGGlobalCheckpointOrigins cfg S added := by
        apply h.origins.of_extension hsub <;> rfl
      have hstagedOrigins : FFGGlobalCheckpointOrigins cfg S staged :=
        FFGGlobalCheckpointOrigins.record_block_timeliness added sb.root
          haddedOrigins
      have hboostedOrigins : FFGGlobalCheckpointOrigins cfg S boosted :=
        FFGGlobalCheckpointOrigins.update_proposer_boost_root staged
          (get_head cfg store).root sb.root hstagedOrigins
      have hboostedRoot : sb.root ∈ boosted.block_roots := by
        have hs := (FastConfirmation.Spec.record_block_timeliness_sameBlocks
          cfg added sb.root).trans
          (FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
            staged (get_head cfg store).root sb.root)
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
        (FastConfirmation.Spec.record_block_timeliness_sameBlocks
          cfg added sb.root).trans
          ((FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
            staged (get_head cfg store).root sb.root).trans
            (FastConfirmation.Spec.update_checkpoints_sameBlocks boosted
              state.current_justified_checkpoint state.finalized_checkpoint))
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
        split_ifs <;> rfl
      have hboostedUJ : boosted.unrealized_justified_checkpoint =
          store.unrealized_justified_checkpoint := by
        simp only [boosted, staged, added,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> rfl
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

/-- The old-tip part of the ledger is preserved separately: the inserted tip
is eagerly realized when old, while every other root keeps its block epoch
and benefits from monotonicity of the global justified checkpoint. -/
theorem oldGU_on_block
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hscheduled : ∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n)
    (h : OldGURealized cfg S store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    OldGURealized cfg S store' := by
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
      cases hh
      let added : Store Root :=
        { store with
          block_roots := if sb.root ∈ store.block_roots then
              store.block_roots else store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root state }
      let staged := FastConfirmation.Spec.record_block_timeliness cfg added sb.root
      let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := FastConfirmation.Spec.update_checkpoints boosted
        state.current_justified_checkpoint state.finalized_checkpoint
      suffices hresult : OldGURealized cfg S
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
        dsimp only [realized, boosted, staged, added] at hresult ⊢
        split_ifs at hresult <;> exact hresult
      have hrootCases : ∀ r ∈ added.block_roots,
          r ∈ store.block_roots ∨ r = sb.root := by
        intro r hr
        by_cases hrs : sb.root ∈ store.block_roots
        · exact Or.inl (by simpa [added, hrs] using hr)
        · simpa [added, hrs, List.mem_append, List.mem_singleton] using hr
      have hsame : SameBlocks added realized :=
        (FastConfirmation.Spec.record_block_timeliness_sameBlocks
          cfg added sb.root).trans
          ((FastConfirmation.Spec.update_proposer_boost_root_sameBlocks cfg
            staged (get_head cfg store).root sb.root).trans
            (FastConfirmation.Spec.update_checkpoints_sameBlocks boosted
              state.current_justified_checkpoint state.finalized_checkpoint))
      have hpulled := FastConfirmation.Spec.compute_pulled_up_tip_sameBlocks
        cfg ext realized sb.root
      have hsameFinal : SameBlocks added
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) :=
        hsame.trans hpulled
      have hrealizedState : realized.block_states sb.root = state := by
        rw [← hsame.2.2]
        simp only [added, Function.update_self]
      have hboostedJ : boosted.justified_checkpoint =
          store.justified_checkpoint := by
        simp only [boosted, staged, added,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> rfl
      have hrealizedTime : realized.time = store.time := by
        simp only [realized, boosted, staged, added,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> rfl
      have hrealizedGenesis : realized.genesis_time = store.genesis_time := by
        simp only [realized, boosted, staged, added,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> rfl
      have hrealizedCurrent : get_current_store_epoch cfg realized =
          get_current_store_epoch cfg store := by
        simp only [get_current_store_epoch, get_current_slot,
          get_slots_since_genesis, hrealizedTime, hrealizedGenesis]
      intro r hr hrold
      have hrAdded : r ∈ added.block_roots := by
        rw [hsameFinal.1]
        exact hr
      by_cases hrNe : r ≠ sb.root
      · have hrOld : r ∈ store.block_roots :=
          (hrootCases r hrAdded).resolve_right hrNe
        have hblock :
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root).blocks r =
              store.blocks r := by
          rw [← hsameFinal.2.1]
          simp only [added, Function.update_apply, if_neg hrNe]
        have hcurrent : get_current_store_epoch cfg
              (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) =
            get_current_store_epoch cfg store := by
          exact (compute_pulled_up_tip_current_epoch
              (cfg := cfg) (ext := ext) realized sb.root).trans
            hrealizedCurrent
        have hrold' : get_block_epoch cfg store r <
            get_current_store_epoch cfg store := by
          simpa only [get_block_epoch, hblock, hcurrent] using hrold
        have hfinalMono : store.justified_checkpoint.epoch ≤
            (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root).justified_checkpoint.epoch := by
          exact (congrArg Checkpoint.epoch hboostedJ.symm).le.trans
            ((justified_epoch_le_update_checkpoints boosted
                state.current_justified_checkpoint state.finalized_checkpoint).trans
              (justified_epoch_le_compute_pulled_up_tip
                (cfg := cfg) (ext := ext) realized sb.root))
        exact (h r hrOld hrold').trans hfinalMono
      · have hre : r = sb.root := Classical.not_not.mp hrNe
        subst r
        have htipOld : get_block_epoch cfg realized sb.root <
            get_current_store_epoch cfg realized := by
          have hblock := congrArg (fun blocks =>
            compute_epoch_at_slot cfg (blocks sb.root).slot) hpulled.2.1
          have hcurrent := compute_pulled_up_tip_current_epoch
            (cfg := cfg) (ext := ext) realized sb.root
          simpa only [get_block_epoch, hblock, hcurrent] using hrold
        rw [← hcoh.transition_gu _ _ _ hscheduled hst]
        rw [← hrealizedState]
        exact pulled_epoch_le_realized_of_old
          (cfg := cfg) (ext := ext) realized sb.root htipOld

theorem oldGU_store_target_checkpoint_state
    (store : Store Root) (target : Checkpoint Root)
    (h : OldGURealized cfg S store) :
    OldGURealized cfg S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> exact h

theorem oldGU_update_latest_messages
    (store : Store Root) (indices : List ValidatorIndex) (a : Attestation Root)
    (h : OldGURealized cfg S store) :
    OldGURealized cfg S
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h

theorem oldGU_on_attestation
    {store store' : Store Root} {a : Attestation Root}
    {is_from_block : Bool}
    (h : OldGURealized cfg S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    OldGURealized cfg S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact oldGU_update_latest_messages _ _ _
    (oldGU_store_target_checkpoint_state _ _ h)

theorem oldGU_on_attester_slashing
    {store store' : Store Root} {sl : AttesterSlashing Root}
    (h : OldGURealized cfg S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl = some store') :
    OldGURealized cfg S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h

theorem oldGU_apply_event_getD
    (hcoh : FFGTransitionCoherence cfg ext S)
    (store : Store Root) (event : Event Root)
    (hscheduled : event ∈ E.schedule w n)
    (h : OldGURealized cfg S store) :
    OldGURealized cfg S
      ((FastConfirmation.Spec.apply_event cfg ext store event).getD store) := by
  cases heq : FastConfirmation.Spec.apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
    simp only [Option.getD_some]
    cases event with
    | block sb => exact oldGU_on_block hcoh ⟨w, n, hscheduled⟩ h heq
    | attestation a is_from_block => exact oldGU_on_attestation h heq
    | attester_slashing sl => exact oldGU_on_attester_slashing h heq

theorem apply_event_getD
    (hcoh : FFGTransitionCoherence cfg ext S)
    (store : Store Root) (event : Event Root)
    (hscheduled : event ∈ E.schedule w n)
    (h : FFGGlobalCheckpointLedger cfg S store) :
    FFGGlobalCheckpointLedger cfg S
      ((FastConfirmation.Spec.apply_event cfg ext store event).getD store) := by
  cases heq : FastConfirmation.Spec.apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
    simp only [Option.getD_some]
    cases event with
    | block sb => exact on_block hcoh ⟨w, n, hscheduled⟩ h heq
    | attestation a is_from_block => exact on_attestation h heq
    | attester_slashing sl => exact on_attester_slashing h heq

end FFGGlobalCheckpointLedger

namespace Execution

variable (E : Execution Root)

private theorem globalCheckpointLedger_foldl
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ) :
    ∀ (events : List (Event Root)), events ⊆ E.schedule w n →
      ∀ store : Store Root, FFGGlobalCheckpointLedger cfg S store →
        FFGGlobalCheckpointLedger cfg S
          (events.foldl (fun st event =>
            (FastConfirmation.Spec.apply_event cfg ext st event).getD st) store) := by
  intro events
  induction events with
  | nil => intro _ store h; exact h
  | cons event rest ih =>
      intro hevents store h
      rw [List.foldl_cons]
      apply ih
      · exact fun x hx => hevents (List.mem_cons_of_mem _ hx)
      · exact FFGGlobalCheckpointLedger.apply_event_getD hcoh store event
          (hevents List.mem_cons_self) h

/-- Every known `GJ` and `GU` has been offered to its corresponding global
maximum at every reachable store. -/
theorem globalCheckpointLedger
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    FFGGlobalCheckpointLedger cfg S (E.store cfg ext w n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq, hslot⟩ := hgen
      change FFGGlobalCheckpointLedger cfg S E.genesis_store
      have hanchorEpoch : anchor.epoch =
          compute_epoch_at_slot cfg ablk.message.slot := by
        have hepoch := congrArg Checkpoint.epoch hanchor
        rw [hgenEq] at hepoch
        simpa only [get_forkchoice_store, get_current_epoch, hslot] using hepoch
      have hrootAt : E.BlockAt ablk.root ablk.message := by
        left
        constructor
        · rw [hgenEq]
          simp only [get_forkchoice_store, List.mem_singleton]
        · rw [hgenEq]
          simp only [get_forkchoice_store, Function.update_self]
      rw [hgenEq] at hanchor ⊢
      constructor
      · exact Or.inl (by
          simpa only [get_forkchoice_store] using hanchor.symm)
      · exact Or.inl (by
          simpa only [get_forkchoice_store] using hanchor.symm)
      · exact Or.inl (by
          simpa only [get_forkchoice_store] using hanchor.symm)
      · exact Or.inl (by
          simpa only [get_forkchoice_store] using hanchor.symm)
      · intro r hr
        have hre : r = ablk.root := by
          simpa only [get_forkchoice_store, List.mem_singleton] using hr
        subst r
        rcases S.gj_anchor_or_before hrootAt with hgj | hbefore
        · rw [hgj, hanchor]
        · rw [← hanchor, hanchorEpoch]
          exact Nat.le_of_lt hbefore
      · intro r hr
        have hre : r = ablk.root := by
          simpa only [get_forkchoice_store, List.mem_singleton] using hr
        subst r
        change (S.GU ablk.root).epoch ≤
          (get_forkchoice_store cfg ast ablk).justified_checkpoint.epoch
        rw [← hanchor, hanchorEpoch]
        exact S.au_epoch_le_block hrootAt
          (S.gu_AU cfg ablk.root ⟨ablk.message, hrootAt⟩)
  | succ n ih =>
      change FFGGlobalCheckpointLedger cfg S
        ((E.schedule w (n + 1)).foldl
          (fun store event =>
            (FastConfirmation.Spec.apply_event cfg ext store event).getD store)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      apply globalCheckpointLedger_foldl (cfg := cfg) (ext := ext)
        (E := E) hcoh w (n + 1)
        (E.schedule w (n + 1)) (List.Subset.refl _)
      exact FFGGlobalCheckpointLedger.on_tick _ _ ih

private theorem oldGU_on_execution_tick
    {S : ChainFFGState cfg E anchor}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (w : ValidatorIndex) (n : ℕ)
    (hledger : FFGGlobalCheckpointLedger cfg S (E.store cfg ext w n))
    (hold : OldGURealized cfg S (E.store cfg ext w n)) :
    OldGURealized cfg S
      (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
        (E.time_at (n + 1))) := by
  let store := E.store cfg ext w n
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hs : get_current_slot cfg store = s := by
    simpa only [store, s] using E.store_current_slot cfg ext w n
  have hsnext : s ≤ next := E.slot_at_mono cfg (Nat.le_succ n)
  have hnextLe : next ≤ s + 1 := E.slot_at_succ_le cfg hdiv hgenTime n
  have htickSlot :
      (E.time_at (n + 1) - store.genesis_time) * 1000 /
          cfg.slot_duration_ms = next := by
    simp only [store, next, Execution.slot_at, GENESIS_SLOT, Nat.zero_add,
      E.store_genesis_time cfg ext w n]
  have htargetCurrent : get_current_slot cfg
      { store with time := E.time_at (n + 1) } = next := by
    simp only [get_current_slot, get_slots_since_genesis, GENESIS_SLOT,
      Nat.zero_add]
    exact htickSlot
  have hcases : next = s ∨ next = s + 1 := by
    by_cases heq : next = s
    · exact Or.inl heq
    · right
      exact Nat.le_antisymm hnextLe
        (Nat.succ_le_of_lt (lt_of_le_of_ne hsnext (Ne.symm heq)))
  simp only [FastConfirmation.Spec.on_tick]
  rw [htickSlot]
  rcases hcases with hsame | hnext
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1) store =
        store := by
      apply FFGGlobalCheckpointLedger.on_tick_aux_eq_of_not_lt
      rw [hsame, ← hs]
      exact Nat.lt_irrefl _
    rw [haux]
    apply FFGGlobalCheckpointLedger.oldGU_on_tick_per_slot_same store
      (E.time_at (n + 1))
    · rw [htargetCurrent, hsame, ← hs]
    · exact hold
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1) store =
        FastConfirmation.Spec.on_tick_per_slot cfg store
          (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000) := by
      rw [hnext]
      exact FFGGlobalCheckpointLedger.on_tick_aux_one_slot store s hs hdiv
    rw [haux]
    let boundaryTime := store.genesis_time +
      (s + 1) * cfg.slot_duration_ms / 1000
    let stepped := FastConfirmation.Spec.on_tick_per_slot cfg store boundaryTime
    have hboundaryCurrent : get_current_slot cfg
        { store with time := boundaryTime } = get_current_slot cfg store + 1 := by
      simpa only [boundaryTime, hs] using
        FFGGlobalCheckpointLedger.current_slot_at_next_boundary
          (cfg := cfg) hdiv store
    have hsteppedOld : OldGURealized cfg S stepped := by
      exact FFGGlobalCheckpointLedger.oldGU_on_tick_per_slot_next
        store boundaryTime hboundaryCurrent hledger hold
    have hsteppedCurrent : get_current_slot cfg stepped = next := by
      rw [FFGGlobalCheckpointLedger.on_tick_per_slot_current_slot,
        hboundaryCurrent, hs, ← hnext]
    have hfinalCurrent : get_current_slot cfg
        { stepped with time := E.time_at (n + 1) } =
          get_current_slot cfg stepped := by
      calc
        get_current_slot cfg { stepped with time := E.time_at (n + 1) } =
            get_current_slot cfg { store with time := E.time_at (n + 1) } := by
          have hg : stepped.genesis_time = store.genesis_time :=
            (FastConfirmation.Spec.on_tick_per_slot_storeLE
              cfg store boundaryTime).2.1.symm
          exact get_current_slot_congr cfg (s :=
              { stepped with time := E.time_at (n + 1) })
            (t := { store with time := E.time_at (n + 1) }) rfl hg
        _ = next := htargetCurrent
        _ = get_current_slot cfg stepped := hsteppedCurrent.symm
    exact FFGGlobalCheckpointLedger.oldGU_on_tick_per_slot_same stepped
      (E.time_at (n + 1)) hfinalCurrent hsteppedOld

private theorem globalOldGU_foldl
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ) :
    ∀ (events : List (Event Root)), events ⊆ E.schedule w n →
      ∀ store : Store Root, OldGURealized cfg S store →
        OldGURealized cfg S
          (events.foldl (fun st event =>
            (FastConfirmation.Spec.apply_event cfg ext st event).getD st) store) := by
  intro events
  induction events with
  | nil => intro _ store h; exact h
  | cons event rest ih =>
      intro hevents store h
      rw [List.foldl_cons]
      apply ih
      · exact fun x hx => hevents (List.mem_cons_of_mem _ hx)
      · exact FFGGlobalCheckpointLedger.oldGU_apply_event_getD hcoh store event
          (hevents List.mem_cons_self) h

/-- Every known tip which is old at a reachable store has had its `GU`
offered to the realized global justified checkpoint. -/
theorem globalOldGURealized
    {S : ChainFFGState cfg E anchor}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    OldGURealized cfg S (E.store cfg ext w n) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _⟩ := hgen
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq, hslot⟩ := hgen
      change OldGURealized cfg S E.genesis_store
      rw [hgenEq]
      intro r hr hrold
      have hre : r = ablk.root := by
        simpa only [get_forkchoice_store, List.mem_singleton] using hr
      subst r
      have hblock :
          (get_forkchoice_store cfg ast ablk).blocks ablk.root = ablk.message := by
        simp only [get_forkchoice_store, Function.update_self]
      have hcurrent := get_current_slot_get_forkchoice_store cfg hdiv ast ablk
      have himpossible : compute_epoch_at_slot cfg ablk.message.slot <
          compute_epoch_at_slot cfg ast.slot := by
        simpa only [get_block_epoch, get_current_store_epoch, hblock,
          hcurrent] using hrold
      rw [hslot] at himpossible
      exact (Nat.lt_irrefl _ himpossible).elim
  | succ n ih =>
      change OldGURealized cfg S
        ((E.schedule w (n + 1)).foldl
          (fun store event =>
            (FastConfirmation.Spec.apply_event cfg ext store event).getD store)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      apply globalOldGU_foldl (cfg := cfg) (ext := ext) (E := E)
        hcoh w (n + 1) (E.schedule w (n + 1)) (List.Subset.refl _)
      exact oldGU_on_execution_tick (cfg := cfg) (ext := ext) (E := E)
        hdiv hgenTime w n
        (globalCheckpointLedger (cfg := cfg) (ext := ext) (E := E)
          hcoh hgen hanchor w n) ih

/-- The executable voting-source selector is never above the realized global
justified checkpoint when it selects a source from a prior epoch. -/
theorem source_realized_le_justified_of_globalTrajectory
    {S : ChainFFGState cfg E anchor}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : ℕ) :
    ∀ tip : Root, tip ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks tip).slot ≤
        get_current_slot cfg (E.store cfg ext w m) →
      (get_voting_source cfg (E.store cfg ext w m) tip).epoch <
        get_current_store_epoch cfg (E.store cfg ext w m) →
      (get_voting_source cfg (E.store cfg ext w m) tip).epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch := by
  intro tip htip _htipSlot _hsourceOld
  rw [E.get_voting_source_eq hcoh w m htip]
  by_cases htipOld : get_current_store_epoch cfg (E.store cfg ext w m) >
      compute_epoch_at_slot cfg ((E.store cfg ext w m).blocks tip).slot
  · rw [if_pos htipOld]
    exact (globalOldGURealized (cfg := cfg) (ext := ext) (E := E)
      hdiv hcoh hgen hanchor w m) tip htip
      (by simpa only [get_block_epoch] using htipOld)
  · rw [if_neg htipOld]
    exact (globalCheckpointLedger (cfg := cfg) (ext := ext) (E := E)
      hcoh hgen hanchor w m).gj_epoch_le_justified tip htip

/-- Complete reachable-store realization of both executable FFG endpoint
selectors, derived from the handler trajectory rather than assumed as a
selector bound. -/
theorem endpointSelectorRealization_of_globalTrajectory
    {S : ChainFFGState cfg E anchor}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : ℕ) :
    EndpointSelectorRealization cfg E anchor (E.store cfg ext w m) := by
  constructor
  · exact E.votingSource_certified_of_ffgState cfg ext hcoh w m
  · exact source_realized_le_justified_of_globalTrajectory
      (cfg := cfg) (ext := ext) (E := E)
      hdiv hcoh hgen hanchor w m

end Execution

end FastConfirmation.Spec
