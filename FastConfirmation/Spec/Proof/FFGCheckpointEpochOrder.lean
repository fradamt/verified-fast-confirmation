import FastConfirmation.Spec.Proof.AcceptedFFGGlobalCheckpointTrajectory
import FastConfirmation.Spec.Proof.FFGGlobalCheckpointTrajectory

/-!
# Global FFG checkpoint epoch order

The fork-choice helpers update justified and finalized checkpoints with
independent maximum guards.  Their ordinary order is nevertheless preserved
because each realized pair supplied by a block state satisfies `GF ≤ GJ`, and
each eager pair satisfies `GUF ≤ GU`.  The unrealized order must be tracked
alongside the realized order because an epoch-boundary tick pulls that pair
into the realized fields.

This module proves that handler invariant directly.  It does not assume any
store-level checkpoint order, ancestry, boundary placement, or endpoint FFG
pipeline.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The paired epoch order preserved by the fork-choice checkpoint writers. -/
structure CheckpointEpochOrder (store : Store Root) : Prop where
  finalized_le_justified :
    store.finalized_checkpoint.epoch ≤ store.justified_checkpoint.epoch
  unrealized_finalized_le_unrealized_justified :
    store.unrealized_finalized_checkpoint.epoch ≤
      store.unrealized_justified_checkpoint.epoch

namespace CheckpointEpochOrder

omit [LinearOrder Root] [Inhabited Root] in
/-- Transport across a helper which leaves the four checkpoint fields fixed. -/
theorem of_eq {store store' : Store Root}
    (h : CheckpointEpochOrder store)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (hf : store'.finalized_checkpoint = store.finalized_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint)
    (huf : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    CheckpointEpochOrder store' := by
  constructor
  · rw [hf, hj]
    exact h.finalized_le_justified
  · rw [huf, huj]
    exact h.unrealized_finalized_le_unrealized_justified

omit [LinearOrder Root] [Inhabited Root] in
/-- Independent maximum guards preserve the realized order when their input
pair is ordered. -/
theorem update_checkpoints (store : Store Root)
    (justified finalized : Checkpoint Root)
    (h : CheckpointEpochOrder store)
    (hpair : finalized.epoch ≤ justified.epoch) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.update_checkpoints store justified finalized) := by
  have hold := h.finalized_le_justified
  have hjField :
      (FastConfirmation.Spec.update_checkpoints store justified finalized).justified_checkpoint =
        if justified.epoch > store.justified_checkpoint.epoch then justified
        else store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hfField :
      (FastConfirmation.Spec.update_checkpoints store justified finalized).finalized_checkpoint =
        if finalized.epoch > store.finalized_checkpoint.epoch then finalized
        else store.finalized_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  constructor
  · rw [hfField, hjField]
    by_cases hj : justified.epoch > store.justified_checkpoint.epoch
    · rw [if_pos hj]
      by_cases hf : finalized.epoch > store.finalized_checkpoint.epoch
      · rw [if_pos hf]
        exact hpair
      · rw [if_neg hf]
        exact hold.trans (Nat.le_of_lt hj)
    · rw [if_neg hj]
      by_cases hf : finalized.epoch > store.finalized_checkpoint.epoch
      · rw [if_pos hf]
        exact hpair.trans (Nat.le_of_not_gt hj)
      · rw [if_neg hf]
        exact hold
  · simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs
    all_goals exact h.unrealized_finalized_le_unrealized_justified

omit [LinearOrder Root] [Inhabited Root] in
/-- The unrealized maximum writers preserve their paired order. -/
theorem update_unrealized_checkpoints (store : Store Root)
    (justified finalized : Checkpoint Root)
    (h : CheckpointEpochOrder store)
    (hpair : finalized.epoch ≤ justified.epoch) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.update_unrealized_checkpoints
        store justified finalized) := by
  have hold := h.unrealized_finalized_le_unrealized_justified
  have hjField :
      (FastConfirmation.Spec.update_unrealized_checkpoints
        store justified finalized).unrealized_justified_checkpoint =
        if justified.epoch > store.unrealized_justified_checkpoint.epoch then justified
        else store.unrealized_justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hfField :
      (FastConfirmation.Spec.update_unrealized_checkpoints
        store justified finalized).unrealized_finalized_checkpoint =
        if finalized.epoch > store.unrealized_finalized_checkpoint.epoch then finalized
        else store.unrealized_finalized_checkpoint := by
    simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  constructor
  · simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs
    all_goals exact h.finalized_le_justified
  · rw [hfField, hjField]
    by_cases hj : justified.epoch >
        store.unrealized_justified_checkpoint.epoch
    · rw [if_pos hj]
      by_cases hf : finalized.epoch >
          store.unrealized_finalized_checkpoint.epoch
      · rw [if_pos hf]
        exact hpair
      · rw [if_neg hf]
        exact hold.trans (Nat.le_of_lt hj)
    · rw [if_neg hj]
      by_cases hf : finalized.epoch >
          store.unrealized_finalized_checkpoint.epoch
      · rw [if_pos hf]
        exact hpair.trans (Nat.le_of_not_gt hj)
      · rw [if_neg hf]
        exact hold

omit [Inhabited Root] in
/-- Eager pull-up preserves both orders when the pulled state itself has
ordered finalized and justified checkpoints. -/
theorem compute_pulled_up_tip (store : Store Root) (r : Root)
    (h : CheckpointEpochOrder store)
    (hpair :
      (ext.process_justification_and_finalization
          (store.block_states r)).finalized_checkpoint.epoch ≤
        (ext.process_justification_and_finalization
          (store.block_states r)).current_justified_checkpoint.epoch) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) := by
  let state :=
    ext.process_justification_and_finalization (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications :=
        Function.update store.unrealized_justifications r
          state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hrecorded : CheckpointEpochOrder recorded := by
    apply h.of_eq <;> rfl
  have hpulled : CheckpointEpochOrder pulled :=
    CheckpointEpochOrder.update_unrealized_checkpoints recorded
      state.current_justified_checkpoint state.finalized_checkpoint hrecorded
        (show state.finalized_checkpoint.epoch ≤
          state.current_justified_checkpoint.epoch from hpair)
  simp only [FastConfirmation.Spec.compute_pulled_up_tip]
  change CheckpointEpochOrder
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled)
  split_ifs
  · exact CheckpointEpochOrder.update_checkpoints pulled
      state.current_justified_checkpoint state.finalized_checkpoint hpulled
        (show state.finalized_checkpoint.epoch ≤
          state.current_justified_checkpoint.epoch from hpair)
  · exact hpulled

omit [LinearOrder Root] in
/-- A single tick step either preserves the checkpoint fields or pulls the
already-ordered unrealized pair into the realized pair. -/
theorem on_tick_per_slot (store : Store Root) (time : Nat)
    (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  split_ifs
  all_goals
    first
    | exact h.of_eq rfl rfl rfl rfl
    | exact CheckpointEpochOrder.update_checkpoints _
        store.unrealized_justified_checkpoint
        store.unrealized_finalized_checkpoint
        (h.of_eq rfl rfl rfl rfl)
        h.unrealized_finalized_le_unrealized_justified

omit [LinearOrder Root] in
theorem on_tick_aux (tickSlot fuel : Nat) :
    ∀ store : Store Root, CheckpointEpochOrder store →
      CheckpointEpochOrder
        (FastConfirmation.Spec.on_tick_aux cfg tickSlot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
      intro store h
      rw [FastConfirmation.Spec.on_tick_aux]
      split_ifs
      · exact ih _ (CheckpointEpochOrder.on_tick_per_slot cfg _ _ h)
      · exact h

omit [LinearOrder Root] in
theorem on_tick (store : Store Root) (time : Nat)
    (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder (FastConfirmation.Spec.on_tick cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick]
  exact CheckpointEpochOrder.on_tick_per_slot cfg _ _
    (CheckpointEpochOrder.on_tick_aux cfg _ _ store h)

omit [Inhabited Root] in
theorem record_block_timeliness (store : Store Root) (r : Root)
    (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.record_block_timeliness cfg store r) := by
  simp only [FastConfirmation.Spec.record_block_timeliness]
  exact h.of_eq rfl rfl rfl rfl

theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;> exact h.of_eq rfl rfl rfl rfl

omit [Inhabited Root] in
theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root) (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> exact h.of_eq rfl rfl rfl rfl

omit [LinearOrder Root] [Inhabited Root] in
theorem update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h.of_eq rfl rfl rfl rfl

omit [Inhabited Root] in
theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {isFromBlock : Bool}
    (h : CheckpointEpochOrder store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a isFromBlock =
      some store') :
    CheckpointEpochOrder store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact update_latest_messages _ _ _
    (store_target_checkpoint_state cfg ext _ _ h)

omit [Inhabited Root] in
theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root}
    (h : CheckpointEpochOrder store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl =
      some store') :
    CheckpointEpochOrder store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl rfl rfl

/-- Handler-mechanical block preservation once the concrete transition's
realized and eager checkpoint pairs are known to be epoch-ordered.  This core
mentions no FFG semantic state or execution-root domain. -/
private theorem on_block_of_ordered_transition
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hstatePair : post.finalized_checkpoint.epoch ≤
      post.current_justified_checkpoint.epoch)
    (hpulledPair :
      (ext.process_justification_and_finalization
        post).finalized_checkpoint.epoch ≤
      (ext.process_justification_and_finalization
        post).current_justified_checkpoint.epoch)
    (h : CheckpointEpochOrder store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    CheckpointEpochOrder store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [FastConfirmation.Spec.on_block, hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    rw [hst] at hh
    cases hh
    let added : Store Root :=
      { store with
        block_roots := if sb.root ∈ store.block_roots then
            store.block_roots else store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post }
    let staged := FastConfirmation.Spec.record_block_timeliness cfg added sb.root
    let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
      (get_head cfg store).root sb.root
    let realized := FastConfirmation.Spec.update_checkpoints boosted
      post.current_justified_checkpoint post.finalized_checkpoint
    have hadded : CheckpointEpochOrder added := by
      apply h.of_eq <;> rfl
    have hstaged : CheckpointEpochOrder staged :=
      CheckpointEpochOrder.record_block_timeliness cfg added sb.root hadded
    have hboosted : CheckpointEpochOrder boosted :=
      CheckpointEpochOrder.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root hstaged
    have hrealized : CheckpointEpochOrder realized :=
      CheckpointEpochOrder.update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
        hboosted hstatePair
    have hrealizedState : realized.block_states sb.root = post := by
      simp only [realized, boosted, staged, added,
        FastConfirmation.Spec.update_checkpoints,
        FastConfirmation.Spec.update_proposer_boost_root,
        FastConfirmation.Spec.record_block_timeliness]
      split_ifs <;> simp only [Function.update_self]
    have hresult : CheckpointEpochOrder
        (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) :=
      CheckpointEpochOrder.compute_pulled_up_tip cfg ext realized sb.root
        hrealized (by rw [hrealizedState]; exact hpulledPair)
    dsimp only [realized, boosted, staged, added] at hresult ⊢
    split_ifs at hresult
    all_goals exact hresult

/-- A concrete exact accepted block transition preserves checkpoint epoch
order.  Both pair inequalities are semantic consequences at the transition's
derived accepted root. -/
theorem acceptedBlockTransition
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : CheckpointEpochOrder (t.atPrefix.store cfg ext)) :
    CheckpointEpochOrder t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨_hknown, hpost⟩ | ⟨post, hst, hinserted⟩)
  · rw [hpost]
    exact h
  · have hstatePair : post.finalized_checkpoint.epoch ≤
        post.current_justified_checkpoint.epoch := by
      rw [← hinserted, hcoh.transition_gf t, hcoh.transition_gj t]
      exact S.gf_epoch_le_gj t.signedBlock.root t.root_accepted
    have hpulledPair :
        (ext.process_justification_and_finalization
          post).finalized_checkpoint.epoch ≤
        (ext.process_justification_and_finalization
          post).current_justified_checkpoint.epoch := by
      rw [← hinserted, hcoh.transition_guf t, hcoh.transition_gu t]
      exact S.guf_epoch_le_gu t.signedBlock.root t.root_accepted
    exact on_block_of_ordered_transition cfg ext hst hstatePair hpulledPair
      h t.accepted

/-- A successful scheduled block insertion first offers the ordered `GF/GJ`
pair and then the ordered eager `GUF/GU` pair. -/
theorem on_block
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hscheduled : ∃ (w : ValidatorIndex) (n : Nat),
      Event.block sb ∈ E.schedule w n)
    (h : CheckpointEpochOrder store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    CheckpointEpochOrder store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [FastConfirmation.Spec.on_block, hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
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
      have hrootAt : E.BlockAt sb.root sb.message := by
        rcases hscheduled with ⟨w, n, hs⟩
        exact Or.inr ⟨w, n, sb, hs, rfl, rfl⟩
      have hroot : E.ExecutionRoot sb.root := ⟨sb.message, hrootAt⟩
      have hstatePair : state.finalized_checkpoint.epoch ≤
          state.current_justified_checkpoint.epoch := by
        rw [hcoh.transition_gf _ _ _ hscheduled hst,
          hcoh.transition_gj _ _ _ hscheduled hst]
        exact S.gf_epoch_le_gj sb.root hroot
      have hpulledPair :
          (ext.process_justification_and_finalization
            state).finalized_checkpoint.epoch ≤
            (ext.process_justification_and_finalization
              state).current_justified_checkpoint.epoch := by
        rw [hcoh.transition_guf _ _ _ hscheduled hst,
          hcoh.transition_gu _ _ _ hscheduled hst]
        exact S.guf_epoch_le_gu sb.root hroot
      have hadded : CheckpointEpochOrder added := by
        apply h.of_eq <;> rfl
      have hstaged : CheckpointEpochOrder staged :=
        CheckpointEpochOrder.record_block_timeliness cfg added sb.root hadded
      have hboosted : CheckpointEpochOrder boosted :=
        CheckpointEpochOrder.update_proposer_boost_root cfg staged
          (get_head cfg store).root sb.root hstaged
      have hrealized : CheckpointEpochOrder realized :=
        CheckpointEpochOrder.update_checkpoints boosted
          state.current_justified_checkpoint state.finalized_checkpoint
          hboosted hstatePair
      have hrealizedState : realized.block_states sb.root = state := by
        simp only [realized, boosted, staged, added,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> simp only [Function.update_self]
      have hresult : CheckpointEpochOrder
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) :=
        CheckpointEpochOrder.compute_pulled_up_tip cfg ext realized sb.root hrealized (by
          rw [hrealizedState]
          exact hpulledPair)
      dsimp only [realized, boosted, staged, added] at hresult ⊢
      split_ifs at hresult
      all_goals exact hresult

theorem apply_event_getD
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} {n : Nat}
    (store : Store Root) (event : Event Root)
    (hscheduled : event ∈ E.schedule w n)
    (h : CheckpointEpochOrder store) :
    CheckpointEpochOrder
      ((FastConfirmation.Spec.apply_event cfg ext store event).getD store) := by
  cases heq : FastConfirmation.Spec.apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
    simp only [Option.getD_some]
    cases event with
    | block sb => exact on_block cfg ext hcoh ⟨w, n, hscheduled⟩ h heq
    | attestation a isFromBlock => exact on_attestation cfg ext h heq
    | attester_slashing sl => exact on_attester_slashing ext h heq

end CheckpointEpochOrder

namespace Execution

variable (E : Execution Root)

private theorem checkpointEpochOrder_foldl
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (n : Nat) :
    ∀ events : List (Event Root), events ⊆ E.schedule w n →
      ∀ store : Store Root, CheckpointEpochOrder store →
        CheckpointEpochOrder
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
    · exact CheckpointEpochOrder.apply_event_getD cfg ext hcoh store event
        (hevents List.mem_cons_self) h

/-- Both checkpoint pairs are epoch-ordered at every reachable store. -/
theorem checkpointEpochOrder_of_globalTrajectory
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (n : Nat) :
    CheckpointEpochOrder (E.store cfg ext w n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq⟩ := hgen
      change CheckpointEpochOrder E.genesis_store
      rw [hgenEq]
      constructor <;> exact Nat.le_refl _
  | succ n ih =>
      change CheckpointEpochOrder
        ((E.schedule w (n + 1)).foldl
          (fun store event =>
            (FastConfirmation.Spec.apply_event cfg ext store event).getD store)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      apply E.checkpointEpochOrder_foldl cfg ext hcoh w (n + 1)
        (E.schedule w (n + 1)) (List.Subset.refl _)
      exact CheckpointEpochOrder.on_tick cfg _ _ ih

/-- Direct producer for `EndpointFFGPipeline.finalized_epoch_le_justified`. -/
theorem finalizedEpoch_le_justified_of_globalTrajectory
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (n : Nat) :
    (E.store cfg ext w n).finalized_checkpoint.epoch ≤
      (E.store cfg ext w n).justified_checkpoint.epoch := by
  have horder :=
    E.checkpointEpochOrder_of_globalTrajectory cfg ext hcoh hgen w n
  exact horder.finalized_le_justified

/-! ## Accepted exact-prefix trajectory -/

private theorem acceptedCheckpointEpochOrder_take
    {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : CheckpointEpochOrder
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      CheckpointEpochOrder
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
      have hp : CheckpointEpochOrder (p.store cfg ext) := ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change CheckpointEpochOrder ((p.successor hklt).store cfg ext)
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
            exact CheckpointEpochOrder.acceptedBlockTransition cfg ext hcoh t hp
        | attestation a fromBlock =>
            exact CheckpointEpochOrder.on_attestation cfg ext hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact CheckpointEpochOrder.on_attester_slashing ext hp
              (by simpa [apply_event, hevent] using heq)

/-- Checkpoint epoch order at every ordinary execution boundary, derived only
from exact accepted block transitions. -/
theorem acceptedCheckpointEpochOrder
    {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (n : ℕ) :
    CheckpointEpochOrder (E.store cfg ext w n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq⟩ := hgen
      change CheckpointEpochOrder E.genesis_store
      rw [hgenEq]
      constructor <;> exact Nat.le_refl _
  | succ n ih =>
      change CheckpointEpochOrder
        ((E.schedule w (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.acceptedCheckpointEpochOrder_take cfg ext hcoh w n
          (CheckpointEpochOrder.on_tick cfg _ _ ih)
          (E.schedule w (n + 1)).length le_rfl

/-- Checkpoint epoch order at every exact in-second schedule prefix. -/
theorem ScheduledEventPrefix.acceptedCheckpointEpochOrder
    {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (p : E.ScheduledEventPrefix)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    CheckpointEpochOrder (p.store cfg ext) := by
  apply E.acceptedCheckpointEpochOrder_take cfg ext hcoh
    p.node p.previousSecond
  · exact CheckpointEpochOrder.on_tick cfg _ _
      (E.acceptedCheckpointEpochOrder cfg ext hcoh hgen
        p.node p.previousSecond)
  · exact p.count_le

/-- Checkpoint epoch order throughout the exact causal-store domain. -/
theorem CausalStore.acceptedCheckpointEpochOrder
    {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    CheckpointEpochOrder store := by
  cases hstore with
  | genesis => exact E.acceptedCheckpointEpochOrder cfg ext hcoh hgen 0 0
  | scheduledPrefix p =>
      exact p.acceptedCheckpointEpochOrder cfg ext E hcoh hgen

end Execution

/-- Accepted global selector/carrier provenance paired with the handler-derived
checkpoint epoch order at one exact causal store. -/
structure AcceptedFFGOrderedGlobalStoreProjection
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop where
  globalProjection : AcceptedFFGGlobalStoreProjection S store
  checkpointOrder : CheckpointEpochOrder store

namespace ExactPrefixAcceptedFFGSemantics

/-- One preselected accepted semantic state supplies block-local projection,
named global carriers, and checkpoint epoch order at the same causal store. -/
theorem causalStoreOrderedGlobalProjection
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    AcceptedFFGOrderedGlobalStoreProjection cfg ext B.state store := by
  obtain ⟨ast, ablk, hgenEq, hslot⟩ := hgen
  exact
    ⟨B.causalStoreGlobalProjection ⟨ast, ablk, hgenEq, hslot⟩
        hanchor hstore,
      hstore.acceptedCheckpointEpochOrder cfg ext E
        B.coherence.toAcceptedFFGSelectorCoherence
        ⟨ast, ablk, hgenEq⟩⟩

/-- Real accepted global consumer: finalized never exceeds justified at any
exact causal store, while the paired projection retains its named global
carrier evidence for downstream use. -/
theorem globalFinalizedEpoch_le_justified
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.finalized_checkpoint.epoch ≤
      store.justified_checkpoint.epoch :=
  (causalStoreOrderedGlobalProjection cfg ext B hgen hanchor hstore)
    |>.checkpointOrder
    |>.finalized_le_justified

/-- The eager pair has the analogous order at every exact causal store. -/
theorem globalUnrealizedFinalizedEpoch_le_unrealizedJustified
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.unrealized_finalized_checkpoint.epoch ≤
      store.unrealized_justified_checkpoint.epoch :=
  (causalStoreOrderedGlobalProjection cfg ext B hgen hanchor hstore)
    |>.checkpointOrder
    |>.unrealized_finalized_le_unrealized_justified

end ExactPrefixAcceptedFFGSemantics

end FastConfirmation.Spec
