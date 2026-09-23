module
public import FastConfirmation.Spec.Proof.AcceptedFFGGlobalCheckpointTrajectory
public import FastConfirmation.Spec.Proof.ModelFacts

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Accepted-domain justified-checkpoint maximality

This module derives the epoch upper bound used by the paper's justified-source
arguments from the executable handlers.  It deliberately uses the accepted
causal-prefix semantics rather than the migration-only scheduled-root state.

Two invariants are kept separate because the handler has a real transient
stage between them:

* every accepted known `GJ` has been offered to the realized justified
  maximum, and every accepted known `GU` to the unrealized maximum;
* when a block is from a prior epoch, its `GU` has also been pulled into the
  realized justified maximum.

The second invariant is advanced at executable epoch-boundary ticks.  A
successful block insertion establishes it for the inserted root through that
same call's `compute_pulled_up_tip`; rejected or merely scheduled blocks never
enter the proof domain.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : AcceptedChainFFGState cfg ext E anchor}

/-- The two checkpoint maxima maintained on accepted carriers.  `GU` is first
offered to the unrealized maximum; an epoch-boundary tick later offers that
maximum to the realized justified field. -/
structure AcceptedFFGJustifiedLedger
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop where
  gj_epoch_le_justified : ∀ r,
    E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r →
      (S.GJ r).epoch ≤ store.justified_checkpoint.epoch
  gu_epoch_le_unrealized : ∀ r,
    E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r →
      (S.GU r).epoch ≤ store.unrealized_justified_checkpoint.epoch

/-- Every accepted known block selected through the old-block arm has had its
eager `GU` offered to the realized global justified maximum. -/
def AcceptedOldGURealized
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop :=
  ∀ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r →
    get_block_epoch cfg store r < get_current_store_epoch cfg store →
      (S.GU r).epoch ≤ store.justified_checkpoint.epoch

namespace AcceptedFFGJustifiedLedger

private theorem justified_epoch_le_update_checkpoints
    (store : Store Root) (jc fc : Checkpoint Root) :
    store.justified_checkpoint.epoch ≤
      (update_checkpoints store jc fc).justified_checkpoint.epoch := by
  have hfield :
      (update_checkpoints store jc fc).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [update_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with hj
  · exact Nat.le_of_lt hj
  · exact Nat.le_refl _

private theorem candidate_epoch_le_update_checkpoints
    (store : Store Root) (jc fc : Checkpoint Root) :
    jc.epoch ≤
      (update_checkpoints store jc fc).justified_checkpoint.epoch := by
  have hfield :
      (update_checkpoints store jc fc).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [update_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with hj
  · exact Nat.le_refl _
  · exact Nat.le_of_not_gt hj

private theorem unrealized_epoch_le_update_unrealized
    (store : Store Root) (ujc ufc : Checkpoint Root) :
    store.unrealized_justified_checkpoint.epoch ≤
      (update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint.epoch := by
  have hfield :
      (update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint =
        if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
        else store.unrealized_justified_checkpoint := by
    simp only [update_unrealized_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with huj
  · exact Nat.le_of_lt huj
  · exact Nat.le_refl _

private theorem candidate_epoch_le_update_unrealized
    (store : Store Root) (ujc ufc : Checkpoint Root) :
    ujc.epoch ≤
      (update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint.epoch := by
  have hfield :
      (update_unrealized_checkpoints store ujc ufc).unrealized_justified_checkpoint =
        if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
        else store.unrealized_justified_checkpoint := by
    simp only [update_unrealized_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with huj
  · exact Nat.le_refl _
  · exact Nat.le_of_not_gt huj

private theorem update_checkpoints_unrealized_justified_eq
    (store : Store Root) (jc fc : Checkpoint Root) :
    (FastConfirmation.Spec.update_checkpoints store jc fc).unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
  simp only [FastConfirmation.Spec.update_checkpoints]
  split_ifs <;> rfl

private theorem justified_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    store.justified_checkpoint.epoch ≤
      (compute_pulled_up_tip cfg ext store r).justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledJ : pulled.justified_checkpoint = store.justified_checkpoint := by
    simp only [pulled, update_unrealized_checkpoints, recorded]
    split_ifs <;> rfl
  change store.justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      update_checkpoints pulled state.current_justified_checkpoint
        state.finalized_checkpoint
    else pulled).justified_checkpoint.epoch
  split_ifs
  · exact (congrArg Checkpoint.epoch hpulledJ).symm.le.trans
      (justified_epoch_le_update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint)
  · exact (congrArg Checkpoint.epoch hpulledJ).symm.le

private theorem unrealized_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    store.unrealized_justified_checkpoint.epoch ≤
      (compute_pulled_up_tip cfg ext store r).unrealized_justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hbase : store.unrealized_justified_checkpoint.epoch ≤
      pulled.unrealized_justified_checkpoint.epoch :=
    unrealized_epoch_le_update_unrealized recorded
      state.current_justified_checkpoint state.finalized_checkpoint
  change store.unrealized_justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      update_checkpoints pulled state.current_justified_checkpoint
        state.finalized_checkpoint
    else pulled).unrealized_justified_checkpoint.epoch
  split_ifs
  · rw [update_checkpoints_unrealized_justified_eq]
    exact hbase
  · exact hbase

private theorem pulled_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    (ext.process_justification_and_finalization
        (store.block_states r)).current_justified_checkpoint.epoch ≤
      (compute_pulled_up_tip cfg ext store r).unrealized_justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hbase : state.current_justified_checkpoint.epoch ≤
      pulled.unrealized_justified_checkpoint.epoch :=
    candidate_epoch_le_update_unrealized recorded
      state.current_justified_checkpoint state.finalized_checkpoint
  change state.current_justified_checkpoint.epoch ≤
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      update_checkpoints pulled state.current_justified_checkpoint
        state.finalized_checkpoint
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
      (compute_pulled_up_tip cfg ext store r).justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update store.unrealized_justifications
        r state.current_justified_checkpoint }
  let pulled := update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledSame : SameBlocks recorded pulled :=
    update_unrealized_checkpoints_sameBlocks recorded
      state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledBlocks : pulled.blocks = store.blocks :=
    hpulledSame.2.1.symm.trans rfl
  have hpulledTime : pulled.time = store.time := by
    exact (update_unrealized_checkpoints_time recorded
      state.current_justified_checkpoint state.finalized_checkpoint).trans rfl
  have hpulledGenesis : pulled.genesis_time = store.genesis_time := by
    exact (update_unrealized_checkpoints_genesis_time recorded
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
      update_checkpoints pulled state.current_justified_checkpoint
        state.finalized_checkpoint
    else pulled).justified_checkpoint.epoch
  rw [if_pos hpull]
  exact candidate_epoch_le_update_checkpoints pulled
    state.current_justified_checkpoint state.finalized_checkpoint

private theorem compute_pulled_up_tip_current_epoch
    (store : Store Root) (r : Root) :
    get_current_store_epoch cfg (compute_pulled_up_tip cfg ext store r) =
      get_current_store_epoch cfg store := by
  simp only [get_current_store_epoch]
  exact congrArg (compute_epoch_at_slot cfg)
    (get_current_slot_congr cfg
      (compute_pulled_up_tip_time cfg ext store r)
      (compute_pulled_up_tip_storeLE cfg ext store r).2.1.symm)

/-! ## Ledger transport and clock steps -/

theorem of_eq {store store' : Store Root}
    (h : AcceptedFFGJustifiedLedger S store)
    (hroots : store'.block_roots = store.block_roots)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint) :
    AcceptedFFGJustifiedLedger S store' := by
  constructor
  · intro r hr
    have hr' : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
      ⟨by rw [← hroots]; exact hr.known, hr.2⟩
    rw [hj]
    exact h.gj_epoch_le_justified r hr'
  · intro r hr
    have hr' : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
      ⟨by rw [← hroots]; exact hr.known, hr.2⟩
    rw [huj]
    exact h.gu_epoch_le_unrealized r hr'

theorem after_update_checkpoints (store : Store Root) (jc fc : Checkpoint Root)
    (h : AcceptedFFGJustifiedLedger S store) :
    AcceptedFFGJustifiedLedger S (update_checkpoints store jc fc) := by
  have hroots : (update_checkpoints store jc fc).block_roots =
      store.block_roots := by
    simp only [update_checkpoints]
    split_ifs <;> rfl
  have huj : (update_checkpoints store jc fc).unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
    simp only [update_checkpoints]
    split_ifs <;> rfl
  constructor
  · intro r hr
    have hr' : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
      ⟨by rw [← hroots]; exact hr.known, hr.2⟩
    exact (h.gj_epoch_le_justified r hr').trans
      (justified_epoch_le_update_checkpoints store jc fc)
  · intro r hr
    have hr' : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
      ⟨by rw [← hroots]; exact hr.known, hr.2⟩
    rw [huj]
    exact h.gu_epoch_le_unrealized r hr'


theorem after_on_tick_per_slot (store : Store Root) (time : ℕ)
    (h : AcceptedFFGJustifiedLedger S store) :
    AcceptedFFGJustifiedLedger S (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs
  all_goals
    first
    | exact h.of_eq rfl rfl rfl
    | · apply AcceptedFFGJustifiedLedger.after_update_checkpoints
        exact h.of_eq rfl rfl rfl

theorem after_on_tick_aux (tickSlot fuel : ℕ) :
    ∀ store : Store Root, AcceptedFFGJustifiedLedger S store →
      AcceptedFFGJustifiedLedger S
        (FastConfirmation.Spec.on_tick_aux cfg tickSlot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
      intro store h
      rw [FastConfirmation.Spec.on_tick_aux]
      split_ifs
      · exact ih _ (after_on_tick_per_slot _ _ h)
      · exact h

theorem after_on_tick (store : Store Root) (time : ℕ)
    (h : AcceptedFFGJustifiedLedger S store) :
    AcceptedFFGJustifiedLedger S (FastConfirmation.Spec.on_tick cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick]
  exact after_on_tick_per_slot _ _ (after_on_tick_aux _ _ _ h)



theorem after_store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root)
    (h : AcceptedFFGJustifiedLedger S store) :
    AcceptedFFGJustifiedLedger S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> exact h.of_eq rfl rfl rfl

theorem after_update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    (h : AcceptedFFGJustifiedLedger S store) :
    AcceptedFFGJustifiedLedger S (update_latest_messages store indices a) := by
  simp only [update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h.of_eq rfl rfl rfl

theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {isFromBlock : Bool}
    (h : AcceptedFFGJustifiedLedger S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a isFromBlock =
      some store') :
    AcceptedFFGJustifiedLedger S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact after_update_latest_messages _ _ _
    (after_store_target_checkpoint_state _ _ h)

theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root}
    (h : AcceptedFFGJustifiedLedger S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl =
      some store') :
    AcceptedFFGJustifiedLedger S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl

/-! ## Exact successful block transition -/

private theorem on_block_of_selectors
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (haccepted : E.AcceptedRoot cfg ext sb.root)
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgj : post.current_justified_checkpoint = S.GJ sb.root)
    (hgu : (ext.process_justification_and_finalization
      post).current_justified_checkpoint = S.GU sb.root)
    (h : AcceptedFFGJustifiedLedger S store)
    (hh : on_block cfg ext store sb = some store') :
    AcceptedFFGJustifiedLedger S store' := by
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
      let staged := record_block_timeliness cfg notified sb.root
      let boosted := update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      suffices hresult : AcceptedFFGJustifiedLedger S
          (compute_pulled_up_tip cfg ext realized sb.root) by
        exact hresult
      have haddedRoot : sb.root ∈ added.block_roots := by
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hrootCases : ∀ r ∈ added.block_roots,
          r ∈ store.block_roots ∨ r = sb.root := by
        intro r hr
        simpa only [added, List.mem_append, List.mem_singleton] using hr
      have hsame : SameBlocks added realized :=
        hf.sameBlocks.trans
          ((record_block_timeliness_sameBlocks cfg notified sb.root).trans
            ((update_proposer_boost_root_sameBlocks cfg staged
              (get_head cfg store).root sb.root).trans
              (update_checkpoints_sameBlocks boosted
                post.current_justified_checkpoint post.finalized_checkpoint)))
      have hrealizedState : realized.block_states sb.root = post := by
        rw [← hsame.2.2]
        simp only [added, Function.update_self]
      have hboostedJ : boosted.justified_checkpoint =
          store.justified_checkpoint := by
        simp only [boosted, staged, added, update_proposer_boost_root,
          record_block_timeliness]
        split_ifs <;> exact hf.justified_checkpoint
      have hboostedUJ : boosted.unrealized_justified_checkpoint =
          store.unrealized_justified_checkpoint := by
        simp only [boosted, staged, added, update_proposer_boost_root,
          record_block_timeliness]
        split_ifs <;> exact hf.unrealized_justified_checkpoint
      have hrealizedUJ : realized.unrealized_justified_checkpoint =
          boosted.unrealized_justified_checkpoint := by
        simp only [realized, update_checkpoints]
        split_ifs <;> rfl
      have hfinalRoots :
          (compute_pulled_up_tip cfg ext realized sb.root).block_roots =
            added.block_roots := by
        have hp := compute_pulled_up_tip_sameBlocks cfg ext realized sb.root
        exact hp.1.symm.trans hsame.1.symm
      constructor
      · intro r hr
        have hrAdded : r ∈ added.block_roots := by
          rw [← hfinalRoots]
          exact hr.known
        rcases hrootCases r hrAdded with hrold | rfl
        · have hold : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
            ⟨hrold, hr.2⟩
          exact (h.gj_epoch_le_justified r hold).trans
            ((congrArg Checkpoint.epoch hboostedJ.symm).le.trans
              ((justified_epoch_le_update_checkpoints boosted
                post.current_justified_checkpoint post.finalized_checkpoint).trans
                (justified_epoch_le_compute_pulled_up_tip
                  (cfg := cfg) (ext := ext) realized sb.root)))
        · rw [← hgj]
          exact (candidate_epoch_le_update_checkpoints boosted
              post.current_justified_checkpoint post.finalized_checkpoint).trans
            (justified_epoch_le_compute_pulled_up_tip
              (cfg := cfg) (ext := ext) realized sb.root)
      · intro r hr
        have hrAdded : r ∈ added.block_roots := by
          rw [← hfinalRoots]
          exact hr.known
        rcases hrootCases r hrAdded with hrold | rfl
        · have hold : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
            ⟨hrold, hr.2⟩
          exact (h.gu_epoch_le_unrealized r hold).trans
            ((congrArg Checkpoint.epoch hboostedUJ.symm).le.trans
              ((congrArg Checkpoint.epoch hrealizedUJ.symm).le.trans
                (unrealized_epoch_le_compute_pulled_up_tip
                  (cfg := cfg) (ext := ext) realized sb.root)))
        · rw [← hgu, ← hrealizedState]
          exact pulled_epoch_le_compute_pulled_up_tip
            (cfg := cfg) (ext := ext) realized sb.root

/-- Ledger preservation by one exact accepted block transition. -/
theorem acceptedBlockTransition
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedFFGJustifiedLedger S (t.atPrefix.store cfg ext)) :
    AcceptedFFGJustifiedLedger S t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨_hknown, hsame⟩ | ⟨post, hst, hinserted⟩)
  · rw [hsame]
    exact h
  · apply on_block_of_selectors t.root_accepted hst
    · rw [← hinserted]
      exact hcoh.transition_gj t
    · rw [← hinserted]
      exact hcoh.transition_gu t
    · exact h
    · exact t.accepted

end AcceptedFFGJustifiedLedger

/-! ## Realization of old eager sources -/

namespace AcceptedOldGURealized

private theorem of_sameBlocks
    {store store' : Store Root}
    (h : AcceptedOldGURealized S store)
    (hsame : SameBlocks store store')
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (hepoch : get_current_store_epoch cfg store' ≤
      get_current_store_epoch cfg store) :
    AcceptedOldGURealized S store' := by
  intro r hr hrold
  have hr' : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
    ⟨by rw [hsame.1]; exact hr.known, hr.2⟩
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
      (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch :=
    Nat.le_antisymm (Nat.succ_le_of_lt hhi) hlo
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

theorem after_on_tick_per_slot_same
    (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store)
    (h : AcceptedOldGURealized S store) :
    AcceptedOldGURealized S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  apply of_sameBlocks h
    (FastConfirmation.Spec.on_tick_per_slot_sameBlocks cfg store time)
  · simp only [FastConfirmation.Spec.on_tick_per_slot]
    rw [hcurrent]
    simp
  · simp only [get_current_store_epoch]
    rw [on_tick_per_slot_current_slot, hcurrent]

theorem after_on_tick_per_slot_next
    (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store + 1)
    (hledger : AcceptedFFGJustifiedLedger S store)
    (h : AcceptedOldGURealized S store) :
    AcceptedOldGURealized S
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
    have hr' : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
      ⟨by rw [hsame.1]; exact hr.known, hr.2⟩
    have hpull : store.unrealized_justified_checkpoint.epoch ≤
        (FastConfirmation.Spec.on_tick_per_slot cfg store time).justified_checkpoint.epoch := by
      have hstart' : compute_slots_since_epoch_start cfg
          (get_current_slot cfg { store with time := time }) = 0 := by
        rw [hcurrent]
        exact hstart
      simp only [FastConfirmation.Spec.on_tick_per_slot]
      rw [if_pos hadvance, if_pos ⟨hadvance, hstart'⟩]
      exact AcceptedFFGJustifiedLedger.candidate_epoch_le_update_checkpoints _ _ _
    exact (hledger.gu_epoch_le_unrealized r hr').trans hpull
  · apply of_sameBlocks h
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

/-! ## Handler preservation of the old-GU invariant -/

private theorem on_block_of_selector
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgu : (ext.process_justification_and_finalization
      post).current_justified_checkpoint = S.GU sb.root)
    (h : AcceptedOldGURealized S store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    AcceptedOldGURealized S store' := by
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
      let staged := record_block_timeliness cfg notified sb.root
      let boosted := update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      suffices hresult : AcceptedOldGURealized S
          (compute_pulled_up_tip cfg ext realized sb.root) by
        exact hresult
      have hrootCases : ∀ r ∈ added.block_roots,
          r ∈ store.block_roots ∨ r = sb.root := by
        intro r hr
        simpa only [added, List.mem_append, List.mem_singleton] using hr
      have hsame : SameBlocks added realized :=
        hf.sameBlocks.trans
          ((record_block_timeliness_sameBlocks cfg notified sb.root).trans
            ((update_proposer_boost_root_sameBlocks cfg staged
              (get_head cfg store).root sb.root).trans
              (update_checkpoints_sameBlocks boosted
                post.current_justified_checkpoint post.finalized_checkpoint)))
      have hpulled := compute_pulled_up_tip_sameBlocks
        cfg ext realized sb.root
      have hsameFinal : SameBlocks added
          (compute_pulled_up_tip cfg ext realized sb.root) :=
        hsame.trans hpulled
      have hrealizedState : realized.block_states sb.root = post := by
        rw [← hsame.2.2]
        simp only [added, Function.update_self]
      have hboostedJ : boosted.justified_checkpoint =
          store.justified_checkpoint := by
        simp only [boosted, staged, added, update_proposer_boost_root,
          record_block_timeliness]
        split_ifs <;> exact hf.justified_checkpoint
      have hrealizedTime : realized.time = store.time := by
        simp only [realized, boosted, staged, added, update_checkpoints,
          update_proposer_boost_root, record_block_timeliness]
        split_ifs <;> exact hf.time
      have hrealizedGenesis : realized.genesis_time = store.genesis_time := by
        simp only [realized, boosted, staged, added, update_checkpoints,
          update_proposer_boost_root, record_block_timeliness]
        split_ifs <;> exact hf.genesis_time
      have hrealizedCurrent : get_current_store_epoch cfg realized =
          get_current_store_epoch cfg store := by
        simp only [get_current_store_epoch, get_current_slot,
          get_slots_since_genesis, hrealizedTime, hrealizedGenesis]
      intro r hr hrold
      have hrAdded : r ∈ added.block_roots := by
        rw [hsameFinal.1]
        exact hr.known
      by_cases hrNe : r ≠ sb.root
      · have hrOld : r ∈ store.block_roots :=
          (hrootCases r hrAdded).resolve_right hrNe
        have hblock :
            (compute_pulled_up_tip cfg ext realized sb.root).blocks r =
              store.blocks r := by
          rw [← hsameFinal.2.1]
          simp only [added, Function.update_apply, if_neg hrNe]
        have hcurrent : get_current_store_epoch cfg
              (compute_pulled_up_tip cfg ext realized sb.root) =
            get_current_store_epoch cfg store :=
          (AcceptedFFGJustifiedLedger.compute_pulled_up_tip_current_epoch
              (cfg := cfg) (ext := ext) realized sb.root).trans
            hrealizedCurrent
        have hrold' : get_block_epoch cfg store r <
            get_current_store_epoch cfg store := by
          simpa only [get_block_epoch, hblock, hcurrent] using hrold
        have hfinalMono : store.justified_checkpoint.epoch ≤
            (compute_pulled_up_tip cfg ext realized sb.root).justified_checkpoint.epoch :=
          (congrArg Checkpoint.epoch hboostedJ.symm).le.trans
            ((AcceptedFFGJustifiedLedger.justified_epoch_le_update_checkpoints
              boosted post.current_justified_checkpoint post.finalized_checkpoint).trans
              (AcceptedFFGJustifiedLedger.justified_epoch_le_compute_pulled_up_tip
                (cfg := cfg) (ext := ext) realized sb.root))
        exact (h r ⟨hrOld, hr.2⟩ hrold').trans hfinalMono
      · have hre : r = sb.root := Classical.not_not.mp hrNe
        subst r
        have htipOld : get_block_epoch cfg realized sb.root <
            get_current_store_epoch cfg realized := by
          have hblock := congrArg (fun blocks =>
            compute_epoch_at_slot cfg (blocks sb.root).slot) hpulled.2.1
          have hcurrent :=
            AcceptedFFGJustifiedLedger.compute_pulled_up_tip_current_epoch
              (cfg := cfg) (ext := ext) realized sb.root
          simpa only [get_block_epoch, hblock, hcurrent] using hrold
        rw [← hgu, ← hrealizedState]
        exact AcceptedFFGJustifiedLedger.pulled_epoch_le_realized_of_old
          (cfg := cfg) (ext := ext) realized sb.root htipOld

theorem acceptedBlockTransition
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedOldGURealized S (t.atPrefix.store cfg ext)) :
    AcceptedOldGURealized S t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨_hknown, hsame⟩ | ⟨post, hst, hinserted⟩)
  · rw [hsame]
    exact h
  · apply on_block_of_selector hst
    · rw [← hinserted]
      exact hcoh.transition_gu t
    · exact h
    · exact t.accepted

theorem after_store_target_checkpoint_state
    (store : Store Root) (target : Checkpoint Root)
    (h : AcceptedOldGURealized S store) :
    AcceptedOldGURealized S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> exact h

theorem after_update_latest_messages
    (store : Store Root) (indices : List ValidatorIndex)
    (a : Attestation Root) (h : AcceptedOldGURealized S store) :
    AcceptedOldGURealized S
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h

theorem on_attestation
    {store store' : Store Root} {a : Attestation Root}
    {isFromBlock : Bool}
    (h : AcceptedOldGURealized S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a isFromBlock =
      some store') :
    AcceptedOldGURealized S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact after_update_latest_messages _ _ _
    (after_store_target_checkpoint_state _ _ h)

theorem on_attester_slashing
    {store store' : Store Root} {sl : AttesterSlashing Root}
    (h : AcceptedOldGURealized S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl =
      some store') :
    AcceptedOldGURealized S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h

end AcceptedOldGURealized

/-! The complete invariant exposed to causal-store consumers. -/

structure AcceptedFFGJustifiedMaximality
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop where
  ledger : AcceptedFFGJustifiedLedger S store
  oldGU : AcceptedOldGURealized S store

namespace Execution

private theorem accepted_slot_at_succ_le
    (E : Execution Root)
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

private theorem acceptedOldGU_after_execution_tick
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (w : ValidatorIndex) (n : ℕ)
    (hledger : AcceptedFFGJustifiedLedger B.state
      (E.store cfg ext w n))
    (hold : AcceptedOldGURealized B.state (E.store cfg ext w n)) :
    AcceptedOldGURealized B.state
      (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
        (E.time_at (n + 1))) := by
  let store := E.store cfg ext w n
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hs : get_current_slot cfg store = s := by
    simpa only [store, s] using E.store_current_slot cfg ext w n
  have hsnext : s ≤ next := E.slot_at_mono cfg (Nat.le_succ n)
  have hnextLe : next ≤ s + 1 :=
    E.accepted_slot_at_succ_le hdiv hgenTime n
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
      apply AcceptedOldGURealized.on_tick_aux_eq_of_not_lt
      rw [hsame, ← hs]
      exact Nat.lt_irrefl _
    rw [haux]
    apply AcceptedOldGURealized.after_on_tick_per_slot_same store
      (E.time_at (n + 1))
    · rw [htargetCurrent, hsame, ← hs]
    · exact hold
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1) store =
        FastConfirmation.Spec.on_tick_per_slot cfg store
          (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000) := by
      rw [hnext]
      exact AcceptedOldGURealized.on_tick_aux_one_slot store s hs hdiv
    rw [haux]
    let boundaryTime := store.genesis_time +
      (s + 1) * cfg.slot_duration_ms / 1000
    let stepped := FastConfirmation.Spec.on_tick_per_slot cfg store boundaryTime
    have hboundaryCurrent : get_current_slot cfg
        { store with time := boundaryTime } =
          get_current_slot cfg store + 1 := by
      simpa only [boundaryTime, hs] using
        AcceptedOldGURealized.current_slot_at_next_boundary
          (cfg := cfg) hdiv store
    have hsteppedOld : AcceptedOldGURealized B.state stepped :=
      AcceptedOldGURealized.after_on_tick_per_slot_next
        store boundaryTime hboundaryCurrent hledger hold
    have hsteppedCurrent : get_current_slot cfg stepped = next := by
      rw [AcceptedOldGURealized.on_tick_per_slot_current_slot,
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
          exact get_current_slot_congr cfg
            (s := { stepped with time := E.time_at (n + 1) })
            (t := { store with time := E.time_at (n + 1) }) rfl hg
        _ = next := htargetCurrent
        _ = get_current_slot cfg stepped := hsteppedCurrent.symm
    exact AcceptedOldGURealized.after_on_tick_per_slot_same stepped
      (E.time_at (n + 1)) hfinalCurrent hsteppedOld

private theorem genesisAcceptedFFGJustifiedMaximality
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGJustifiedMaximality B.state E.genesis_store := by
  obtain ⟨ast, ablk, hgenEq, hslot⟩ := hgen
  have hanchorEpoch : B.anchor.epoch =
      compute_epoch_at_slot cfg ablk.message.slot := by
    have hepoch := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at hepoch
    simpa only [get_forkchoice_store, get_current_epoch, hslot] using hepoch
  have hrootAt : E.AcceptedBlockAt cfg ext ablk.root ablk.message := by
    refine ⟨E.genesis_store, .genesis, ?_, ?_⟩
    · rw [hgenEq]
      simp only [get_forkchoice_store, List.mem_singleton]
    · rw [hgenEq]
      simp only [get_forkchoice_store, Function.update_self]
  constructor
  · constructor
    · intro r hr
      have hre : r = ablk.root := by
        have := hr.known
        rw [hgenEq] at this
        simpa only [get_forkchoice_store, List.mem_singleton] using this
      subst r
      rcases B.state.gj_anchor_or_before hrootAt with hgj | hbefore
      · rw [hgj, hanchor]
      · rw [← hanchor, hanchorEpoch]
        exact Nat.le_of_lt hbefore
    · intro r hr
      have hre : r = ablk.root := by
        have := hr.known
        rw [hgenEq] at this
        simpa only [get_forkchoice_store, List.mem_singleton] using this
      subst r
      rw [hgenEq]
      change (B.state.GU ablk.root).epoch ≤
        (get_forkchoice_store cfg ast ablk).unrealized_justified_checkpoint.epoch
      simp only [get_forkchoice_store]
      simpa only [get_current_epoch, hslot] using
        B.state.au_epoch_le_block hrootAt
          (B.state.gu_AU cfg ext hrootAt.acceptedRoot)
  · intro r hr hrold
    have hre : r = ablk.root := by
      have := hr.known
      rw [hgenEq] at this
      simpa only [get_forkchoice_store, List.mem_singleton] using this
    subst r
    have hblock :
        (get_forkchoice_store cfg ast ablk).blocks ablk.root = ablk.message := by
      simp only [get_forkchoice_store, Function.update_self]
    have hcurrent := get_current_slot_get_forkchoice_store cfg hdiv ast ablk
    have himpossible : compute_epoch_at_slot cfg ablk.message.slot <
        compute_epoch_at_slot cfg ast.slot := by
      rw [hgenEq] at hrold
      simpa only [get_block_epoch, get_current_store_epoch, hblock,
        hcurrent] using hrold
    rw [hslot] at himpossible
    exact (Nat.lt_irrefl _ himpossible).elim

private theorem acceptedFFGJustifiedMaximality_take
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : AcceptedFFGJustifiedMaximality B.state
      (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
        (E.time_at (n + 1)))) :
    ∀ k : ℕ, k ≤ (E.schedule w (n + 1)).length →
      AcceptedFFGJustifiedMaximality B.state
        (((E.schedule w (n + 1)).take k).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1)))) := by
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
      have hp : AcceptedFFGJustifiedMaximality B.state (p.store cfg ext) :=
        ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedFFGJustifiedMaximality B.state
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
            exact ⟨AcceptedFFGJustifiedLedger.acceptedBlockTransition
                B.coherence.toAcceptedFFGSelectorCoherence t hp.ledger,
              AcceptedOldGURealized.acceptedBlockTransition
                B.coherence.toAcceptedFFGSelectorCoherence t hp.oldGU⟩
        | attestation a fromBlock =>
            exact ⟨AcceptedFFGJustifiedLedger.on_attestation hp.ledger
                (by simpa [apply_event, hevent] using heq),
              AcceptedOldGURealized.on_attestation hp.oldGU
                (by simpa [apply_event, hevent] using heq)⟩
        | attester_slashing sl =>
            exact ⟨AcceptedFFGJustifiedLedger.on_attester_slashing hp.ledger
                (by simpa [apply_event, hevent] using heq),
              AcceptedOldGURealized.on_attester_slashing hp.oldGU
                (by simpa [apply_event, hevent] using heq)⟩
        | execution_payload_envelope envelope observation =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_execution_payload_envelope_frame ext (by simpa [apply_event, hevent] using heq)
            refine ⟨hp.ledger.of_eq hf.block_roots hf.justified_checkpoint
              hf.unrealized_justified_checkpoint, ?_⟩
            exact AcceptedOldGURealized.of_sameBlocks hp.oldGU hf.sameBlocks
              hf.justified_checkpoint (by
                simp only [get_current_store_epoch, get_current_slot,
                  get_slots_since_genesis, hf.time, hf.genesis_time]
                exact le_rfl)
        | payload_attestation_message message isFromBlock =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_payload_attestation_message_frame cfg ext (by simpa [apply_event, hevent] using heq)
            refine ⟨hp.ledger.of_eq hf.block_roots hf.justified_checkpoint
              hf.unrealized_justified_checkpoint, ?_⟩
            exact AcceptedOldGURealized.of_sameBlocks hp.oldGU hf.sameBlocks
              hf.justified_checkpoint (by
                simp only [get_current_store_epoch, get_current_slot,
                  get_slots_since_genesis, hf.time, hf.genesis_time]
                exact le_rfl)

/-- The accepted justified-maximality invariant at every ordinary execution
boundary.  Both block insertion and ticking are executable-handler facts. -/
theorem acceptedFFGJustifiedMaximality
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    AcceptedFFGJustifiedMaximality B.state (E.store cfg ext w n) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _⟩ := hgen
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  induction n with
  | zero =>
      exact genesisAcceptedFFGJustifiedMaximality B hdiv hgen hanchor
  | succ n ih =>
      change AcceptedFFGJustifiedMaximality B.state
        ((E.schedule w (n + 1)).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.acceptedFFGJustifiedMaximality_take B w n
          ⟨AcceptedFFGJustifiedLedger.after_on_tick _ _ ih.ledger,
            E.acceptedOldGU_after_execution_tick B hdiv hgenTime
              w n ih.ledger ih.oldGU⟩
          (E.schedule w (n + 1)).length le_rfl

/-- Exact strict-prefix specialization of accepted justified maximality. -/
theorem ScheduledEventPrefix.acceptedFFGJustifiedMaximality
    (p : E.ScheduledEventPrefix)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGJustifiedMaximality B.state (p.store cfg ext) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _⟩ := hgen
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  apply E.acceptedFFGJustifiedMaximality_take B
    p.node p.previousSecond
  · have hprev := E.acceptedFFGJustifiedMaximality
      B hdiv hgen hanchor p.node p.previousSecond
    exact ⟨AcceptedFFGJustifiedLedger.after_on_tick _ _ hprev.ledger,
      E.acceptedOldGU_after_execution_tick B hdiv hgenTime
        p.node p.previousSecond hprev.ledger hprev.oldGU⟩
  · exact p.count_le

/-- Accepted justified maximality at every store in the exact causal domain. -/
theorem CausalStore.acceptedFFGJustifiedMaximality
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFFGJustifiedMaximality B.state store := by
  cases hstore with
  | genesis =>
      exact genesisAcceptedFFGJustifiedMaximality B hdiv hgen hanchor
  | scheduledPrefix p =>
      exact p.acceptedFFGJustifiedMaximality B hdiv hgen hanchor

end Execution

namespace ExactPrefixAcceptedFFGSemantics

/-- The actual executable voting source of every accepted known root is
bounded by the store's realized justified checkpoint, including the strict
old-block `GU` arm and strict in-second scheduled-event prefixes. -/
theorem causalVotingSource_epoch_le_justified
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {r : Root} (hr : r ∈ store.block_roots) :
    (get_voting_source cfg store r).epoch ≤
      store.justified_checkpoint.epoch := by
  have hmax := hstore.acceptedFFGJustifiedMaximality
    B hdiv hgen hanchor
  have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r :=
    Execution.AcceptedCarrierIn.of_causal_known hstore hr
  have hprojection :=
    Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection B hstore
  simp only [get_voting_source]
  split_ifs with hold
  · rw [hprojection.unrealized_justification r hr]
    exact hmax.oldGU r hcarrier
      (by simpa only [get_block_epoch] using hold)
  · rw [hprojection.block_state_gj r hr]
    exact hmax.ledger.gj_epoch_le_justified r hcarrier

/-- Two-store re-parameterization of `causalVotingSource_epoch_le_justified`.

The voting source a root carries at one accepted causal store is bounded by
the *remote* realized justified epoch of any other accepted causal store which
already knows that root.  Both arms are discharged at the remote store: the
realized arm by its `GJ` maximum, the strict old-block arm by its own
old-`GU` maximum.

The two side conditions are exactly what the old-block arm needs — the remote
store must agree on the root's block slot and must not be behind on the epoch
clock, so that a root which is old at the source store is old at the remote
store as well.  Both are ordinary relay-site facts (`blocks_agree` and slot
monotonicity); neither is a new law. -/
theorem votingSource_epoch_le_remoteJustified_of_known
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {source target : Store Root}
    (hsource : E.CausalStore cfg ext source)
    (htarget : E.CausalStore cfg ext target)
    {r : Root} (hr : r ∈ source.block_roots)
    (hrTarget : r ∈ target.block_roots)
    (hblockSlot : (source.blocks r).slot = (target.blocks r).slot)
    (hepoch : get_current_store_epoch cfg source ≤
      get_current_store_epoch cfg target) :
    (get_voting_source cfg source r).epoch ≤
      target.justified_checkpoint.epoch := by
  have hmax := htarget.acceptedFFGJustifiedMaximality
    B hdiv hgen hanchor
  have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) target r :=
    Execution.AcceptedCarrierIn.of_causal_known htarget hrTarget
  have hprojection :=
    Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection B hsource
  simp only [get_voting_source]
  split_ifs with hold
  · rw [hprojection.unrealized_justification r hr]
    refine hmax.oldGU r hcarrier ?_
    have holdTarget : compute_epoch_at_slot cfg (target.blocks r).slot <
        get_current_store_epoch cfg target := by
      rw [← hblockSlot]
      exact lt_of_lt_of_le hold hepoch
    simpa only [get_block_epoch] using holdTarget
  · rw [hprojection.block_state_gj r hr]
    exact hmax.ledger.gj_epoch_le_justified r hcarrier

end ExactPrefixAcceptedFFGSemantics


end FastConfirmation.Spec

end
