module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.State.ProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.SourceHistory.FFGJustifiedMaximality
public import FastConfirmationProofs.Handlers.BlockTransitionProvenance
public import FastConfirmationProofs.Execution.History.CausalQueryTraceAdapter

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted realized-justified executable origins

The generic accepted global-checkpoint origin records that a realized
justified field came from either `GJ r` or `GU r`, but deliberately forgets
the executable guard under which `GU r` can be copied into the realized
field.  This module retains that guard:

* a `GJ` origin may be carried by any accepted known block; and
* a `GU` origin is carried only by a block which is already old in that
  concrete store.

This is an operational handler invariant.  It is not cross-store justified
checkpoint monotonicity.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Exact executable origin of one realized justified checkpoint. -/
def AcceptedRealizedJustifiedOrigin
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨
    ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧
      (c = S.GJ r ∨
        (c = S.GU r ∧
          get_block_epoch cfg store r <
            get_current_store_epoch cfg store))

/-- The realized origin is paired with the ordinary unrealized origin because
an epoch-boundary tick copies the latter into the former. -/
structure AcceptedRealizedJustifiedOrigins
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop where
  realized : AcceptedRealizedJustifiedOrigin cfg ext S store
    store.justified_checkpoint
  unrealized : AcceptedGlobalUnrealizedJustifiedOrigin S store
    store.unrealized_justified_checkpoint

namespace AcceptedRealizedJustifiedOrigin

/-- Transport an origin across identical block identity and clock, while
allowing the named checkpoint itself to be rewritten. -/
theorem of_sameBlocks_currentEpoch
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root} {c c' : Checkpoint Root}
    (h : AcceptedRealizedJustifiedOrigin cfg ext S store c)
    (hsame : SameBlocks store store')
    (hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store)
    (hc : c' = c) :
    AcceptedRealizedJustifiedOrigin cfg ext S store' c' := by
  rcases h with hanchor | ⟨r, hr, hgj | ⟨hgu, hold⟩⟩
  · exact Or.inl (hc.trans hanchor)
  · exact Or.inr ⟨r, ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩,
      Or.inl (hc.trans hgj)⟩
  · right
    refine ⟨r, ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩,
      Or.inr ⟨hc.trans hgu, ?_⟩⟩
    have hblock : get_block_epoch cfg store' r =
        get_block_epoch cfg store r := by
      simp only [get_block_epoch]
      rw [← hsame.2.1]
    rw [hblock, hcurrent]
    exact hold

/-- Forward clock transport: an already-old `GU` carrier remains old. -/
theorem of_sameBlocks_currentEpoch_mono
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root} {c c' : Checkpoint Root}
    (h : AcceptedRealizedJustifiedOrigin cfg ext S store c)
    (hsame : SameBlocks store store')
    (hcurrent : get_current_store_epoch cfg store ≤
      get_current_store_epoch cfg store')
    (hc : c' = c) :
    AcceptedRealizedJustifiedOrigin cfg ext S store' c' := by
  rcases h with hanchor | ⟨r, hr, hgj | ⟨hgu, hold⟩⟩
  · exact Or.inl (hc.trans hanchor)
  · exact Or.inr ⟨r, ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩,
      Or.inl (hc.trans hgj)⟩
  · right
    refine ⟨r, ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩,
      Or.inr ⟨hc.trans hgu, ?_⟩⟩
    have hblock : get_block_epoch cfg store' r =
        get_block_epoch cfg store r := by
      simp only [get_block_epoch]
      rw [← hsame.2.1]
    rw [hblock]
    exact hold.trans_le hcurrent

end AcceptedRealizedJustifiedOrigin

namespace AcceptedRealizedJustifiedOrigins

/-- Transport the paired invariant across a checkpoint-identical helper with
the same block identity and current epoch. -/
theorem of_sameBlocks_currentEpoch
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root}
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hsame : SameBlocks store store')
    (hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint) :
    AcceptedRealizedJustifiedOrigins cfg ext S store' := by
  constructor
  · exact h.realized.of_sameBlocks_currentEpoch cfg ext hsame hcurrent hj
  · rcases h.unrealized with hanchor | ⟨r, hr, hgu⟩
    · exact Or.inl (huj.trans hanchor)
    · exact Or.inr ⟨r,
        ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩, huj.trans hgu⟩

/-- Convenient transport when the concrete time/genesis fields and both
justified fields are unchanged. -/
theorem of_eq
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root}
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hsame : SameBlocks store store')
    (htime : store'.time = store.time)
    (hgenesis : store'.genesis_time = store.genesis_time)
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint) :
    AcceptedRealizedJustifiedOrigins cfg ext S store' := by
  have hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store := by
    simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg htime hgenesis)
  exact h.of_sameBlocks_currentEpoch cfg ext hsame hcurrent hj huj

/-- Payload writes preserve every field used by the paired origin invariant. -/
theorem of_payloadFrame
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root}
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hf : PayloadFrame store store') :
    AcceptedRealizedJustifiedOrigins cfg ext S store' :=
  h.of_eq cfg ext hf.sameBlocks hf.time hf.genesis_time
    hf.justified_checkpoint hf.unrealized_justified_checkpoint

/-- Pair-level forward clock transport. -/
theorem of_sameBlocks_currentEpoch_mono
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root}
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hsame : SameBlocks store store')
    (hcurrent : get_current_store_epoch cfg store ≤
      get_current_store_epoch cfg store')
    (hj : store'.justified_checkpoint = store.justified_checkpoint)
    (huj : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint) :
    AcceptedRealizedJustifiedOrigins cfg ext S store' := by
  constructor
  · exact h.realized.of_sameBlocks_currentEpoch_mono cfg ext
      hsame hcurrent hj
  · rcases h.unrealized with hanchor | ⟨r, hr, hgu⟩
    · exact Or.inl (huj.trans hanchor)
    · exact Or.inr ⟨r,
        ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩, huj.trans hgu⟩

/-- A realized checkpoint update chooses between two already-classified
realized origins; the unrealized field is untouched. -/
theorem update_checkpoints
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (jc fc : Checkpoint Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hjc : AcceptedRealizedJustifiedOrigin cfg ext S store jc) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.update_checkpoints store jc fc) := by
  let store' := FastConfirmation.Spec.update_checkpoints store jc fc
  have hsame : SameBlocks store store' :=
    FastConfirmation.Spec.update_checkpoints_sameBlocks store jc fc
  have hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store := by
    simp only [store', get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg
        (FastConfirmation.Spec.update_checkpoints_time store jc fc)
        (FastConfirmation.Spec.update_checkpoints_genesis_time store jc fc))
  have hjField : store'.justified_checkpoint =
      if jc.epoch > store.justified_checkpoint.epoch then jc
      else store.justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  have hujField : store'.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  change AcceptedRealizedJustifiedOrigins cfg ext S store'
  constructor
  · rw [hjField]
    split_ifs with htake
    · apply hjc.of_sameBlocks_currentEpoch cfg ext hsame hcurrent
      rfl
    · apply h.realized.of_sameBlocks_currentEpoch cfg ext hsame hcurrent
      rfl
  · rcases h.unrealized with hanchor | ⟨r, hr, hgu⟩
    · exact Or.inl (hujField.trans hanchor)
    · exact Or.inr ⟨r,
        ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩, hujField.trans hgu⟩

/-- An unrealized checkpoint update chooses between ordinary `GU` origins;
the refined realized field is untouched. -/
theorem update_unrealized_checkpoints
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (ujc ufc : Checkpoint Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hujc : AcceptedGlobalUnrealizedJustifiedOrigin S store ujc) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc) := by
  let store' := FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc
  have hsame : SameBlocks store store' :=
    FastConfirmation.Spec.update_unrealized_checkpoints_sameBlocks store ujc ufc
  have hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store := by
    simp only [store', get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg
        (FastConfirmation.Spec.update_unrealized_checkpoints_time store ujc ufc)
        (FastConfirmation.Spec.update_unrealized_checkpoints_genesis_time
          store ujc ufc))
  have hjField : store'.justified_checkpoint = store.justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  have hujField : store'.unrealized_justified_checkpoint =
      if ujc.epoch > store.unrealized_justified_checkpoint.epoch then ujc
      else store.unrealized_justified_checkpoint := by
    simp only [store', FastConfirmation.Spec.update_unrealized_checkpoints]
    split_ifs <;> rfl
  change AcceptedRealizedJustifiedOrigins cfg ext S store'
  constructor
  · exact h.realized.of_sameBlocks_currentEpoch cfg ext hsame hcurrent hjField
  · rw [hujField]
    split_ifs with htake
    · rcases hujc with hanchor | ⟨r, hr, hgu⟩
      · exact Or.inl hanchor
      · exact Or.inr ⟨r,
          ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩,
          hgu⟩
    · rcases h.unrealized with hanchor | ⟨r, hr, hgu⟩
      · exact Or.inl hanchor
      · exact Or.inr ⟨r,
          ⟨by rw [← hsame.1]; exact hr.known, hr.2⟩,
          hgu⟩

theorem record_block_timeliness
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (r : Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.record_block_timeliness cfg store r) := by
  apply h.of_eq cfg ext
    (FastConfirmation.Spec.record_block_timeliness_sameBlocks cfg store r)
  all_goals rfl

theorem update_proposer_boost_root
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (head r : Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;> apply h.of_eq cfg ext <;> first | exact ⟨rfl, rfl, rfl⟩ | rfl

theorem store_target_checkpoint_state
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (target : Checkpoint Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> apply h.of_eq cfg ext <;> first | exact ⟨rfl, rfl, rfl⟩ | rfl

theorem update_latest_messages
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (indices : List ValidatorIndex)
    (a : Attestation Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> apply h.of_eq cfg ext <;>
        first | exact ⟨rfl, rfl, rfl⟩ | rfl

theorem on_attestation
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root} {a : Attestation Root}
    {is_from_block : Bool}
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    AcceptedRealizedJustifiedOrigins cfg ext S store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact update_latest_messages cfg ext _ _ _
    (store_target_checkpoint_state cfg ext _ _ h)

theorem on_attester_slashing
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store store' : Store Root} {sl : AttesterSlashing Root}
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl =
      some store') :
    AcceptedRealizedJustifiedOrigins cfg ext S store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  apply h.of_eq cfg ext
  · exact ⟨rfl, rfl, rfl⟩
  all_goals rfl

/-! ## One-slot tick preservation -/

private theorem epoch_lt_of_slots_since_succ_eq_zero (s : Slot)
    (hzero : compute_slots_since_epoch_start cfg (s + 1) = 0) :
    compute_epoch_at_slot cfg s < compute_epoch_at_slot cfg (s + 1) := by
  by_contra hnot
  have hmono : compute_epoch_at_slot cfg s ≤
      compute_epoch_at_slot cfg (s + 1) :=
    ce_mono (cfg := cfg) (Nat.le_succ s)
  have heq : compute_epoch_at_slot cfg (s + 1) =
      compute_epoch_at_slot cfg s :=
    Nat.le_antisymm (Nat.le_of_not_gt hnot) hmono
  have hboundaryLe : s + 1 ≤
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (s + 1)) :=
    Nat.sub_eq_zero_iff_le.mp hzero
  rw [heq] at hboundaryLe
  have hfloor := Nat.div_mul_le_self s cfg.slots_per_epoch
  have himpossible : s + 1 ≤ s :=
    hboundaryLe.trans (by
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot]
        using hfloor)
  exact (Nat.not_succ_le_self s) himpossible

theorem after_on_tick_per_slot_same
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  rw [hcurrent]
  simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte, false_and]
  apply h.of_sameBlocks_currentEpoch cfg ext
  · exact ⟨rfl, rfl, rfl⟩
  · simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg) hcurrent
  all_goals rfl

/-- A one-slot advance preserves old realized origins.  At an epoch boundary,
the unrealized `GU` origin becomes a realized origin and nonfuturity makes its
carrier strictly old in the new epoch. -/
theorem after_on_tick_per_slot_next
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store + 1)
    (hnonfuture : BlocksSlotLe (get_current_slot cfg store) store)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  let timed : Store Root := { store with time := time }
  let reset : Store Root :=
    if get_current_slot cfg timed > get_current_slot cfg store then
      { timed with proposer_boost_root := (default : Root) }
    else timed
  have hresetSame : SameBlocks store reset := by
    simp only [reset, timed]
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  have hresetSlot : get_current_slot cfg reset =
      get_current_slot cfg timed := by
    simp only [reset]
    split_ifs <;> rfl
  have hresetJ : reset.justified_checkpoint =
      store.justified_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  have hresetUJ : reset.unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  have hcurrentLe : get_current_store_epoch cfg store ≤
      get_current_store_epoch cfg reset := by
    apply ce_mono (cfg := cfg)
    rw [hresetSlot]
    rw [show get_current_slot cfg timed = get_current_slot cfg store + 1 by
      simpa only [timed] using hcurrent]
    exact Nat.le_succ _
  have hbase : AcceptedRealizedJustifiedOrigins cfg ext S reset :=
    h.of_sameBlocks_currentEpoch_mono cfg ext hresetSame hcurrentLe
      hresetJ hresetUJ
  change AcceptedRealizedJustifiedOrigins cfg ext S
    (if get_current_slot cfg timed > get_current_slot cfg store ∧
        compute_slots_since_epoch_start cfg
          (get_current_slot cfg timed) = 0 then
      FastConfirmation.Spec.update_checkpoints reset
        reset.unrealized_justified_checkpoint
        reset.unrealized_finalized_checkpoint
    else reset)
  split_ifs with hpull
  · apply update_checkpoints cfg ext reset
      reset.unrealized_justified_checkpoint
      reset.unrealized_finalized_checkpoint hbase
    have hzero : compute_slots_since_epoch_start cfg
        (get_current_slot cfg store + 1) = 0 := by
      rw [← hcurrent]
      simpa only [timed] using hpull.2
    have hstrict : get_current_store_epoch cfg store <
        get_current_store_epoch cfg reset := by
      simp only [get_current_store_epoch]
      rw [hresetSlot]
      have htimed : get_current_slot cfg timed =
          get_current_slot cfg store + 1 := by
        simpa only [timed] using hcurrent
      rw [htimed]
      exact epoch_lt_of_slots_since_succ_eq_zero
        (cfg := cfg) (get_current_slot cfg store) hzero
    rcases h.unrealized with hanchor | ⟨r, hr, hgu⟩
    · exact Or.inl (hresetUJ.trans hanchor)
    · right
      refine ⟨r, ⟨by rw [← hresetSame.1]; exact hr.known, hr.2⟩,
        Or.inr ⟨hresetUJ.trans hgu, ?_⟩⟩
      have hblockEq : get_block_epoch cfg reset r =
          get_block_epoch cfg store r := by
        simp only [get_block_epoch]
        rw [← hresetSame.2.1]
      rw [hblockEq]
      exact (ce_mono (cfg := cfg)
        (hnonfuture r hr.known)).trans_lt hstrict
  · exact hbase

/-- Eager pull-up records a `GU` origin in the unrealized field.  It copies
that value into the realized field only under the literal old-block guard,
which is exactly the refined origin's age witness. -/
theorem compute_pulled_up_tip
    {S : AcceptedChainFFGState cfg ext E anchor}
    (store : Store Root) (r : Root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hr : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r)
    (hgu : (ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint = S.GU r) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) := by
  let state := ext.process_justification_and_finalization
    (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update
        store.unrealized_justifications r
          state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hrecorded : AcceptedRealizedJustifiedOrigins cfg ext S recorded := by
    apply h.of_eq cfg ext
    · exact ⟨rfl, rfl, rfl⟩
    all_goals rfl
  have hrRecorded : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
      recorded r := by
    exact ⟨by simpa only [recorded] using hr.known, hr.2⟩
  have hujOrigin : AcceptedGlobalUnrealizedJustifiedOrigin S recorded
      state.current_justified_checkpoint := by
    right
    refine ⟨r, hrRecorded, ?_⟩
    simpa only [state] using hgu
  have hpulled : AcceptedRealizedJustifiedOrigins cfg ext S pulled :=
    update_unrealized_checkpoints cfg ext recorded
      state.current_justified_checkpoint state.finalized_checkpoint
      hrecorded hujOrigin
  have hsame : SameBlocks recorded pulled :=
    FastConfirmation.Spec.update_unrealized_checkpoints_sameBlocks
      recorded state.current_justified_checkpoint state.finalized_checkpoint
  have hrPulled : E.AcceptedCarrierIn (cfg := cfg) (ext := ext) pulled r :=
    ⟨by rw [← hsame.1]; exact hrRecorded.known, hr.2⟩
  change AcceptedRealizedJustifiedOrigins cfg ext S
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled)
  split_ifs with hold
  · apply update_checkpoints cfg ext pulled
      state.current_justified_checkpoint state.finalized_checkpoint hpulled
    right
    exact ⟨r, hrPulled, Or.inr ⟨by simpa only [state] using hgu,
      by simpa only [get_block_epoch] using hold⟩⟩
  · exact hpulled

/-! ## Successful accepted block steps -/

private theorem on_block_of_selectors
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hwf : WellFormedExecution E)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (hstore : E.CausalStore cfg ext store)
    (hnewAt : E.AcceptedBlockAt cfg ext sb.root sb.message)
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgj : post.current_justified_checkpoint = S.GJ sb.root)
    (hgu : (ext.process_justification_and_finalization
      post).current_justified_checkpoint = S.GU sb.root)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    AcceptedRealizedJustifiedOrigins cfg ext S store' := by
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
      let staged := FastConfirmation.Spec.record_block_timeliness cfg notified sb.root
      let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := FastConfirmation.Spec.update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      suffices hresult : AcceptedRealizedJustifiedOrigins cfg ext S
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized sb.root) by
        exact hresult
      have hsub : store.block_roots ⊆ added.block_roots := by
        intro r hr
        exact List.mem_append_left _ hr
      have holdBlock : ∀ r, r ∈ store.block_roots →
          added.blocks r = store.blocks r := by
        intro r hr
        by_cases hre : r = sb.root
        · subst r
          have holdAt : E.AcceptedBlockAt cfg ext sb.root
              (store.blocks sb.root) :=
            E.acceptedBlockAt_of_causal_known cfg ext hstore hr
          have heq : store.blocks sb.root = sb.message :=
            holdAt.unique cfg ext E hwf hnewAt
          simp only [added, Function.update_self, heq]
        · simp [added, Function.update, hre]
      have haddedCurrent : get_current_store_epoch cfg added =
          get_current_store_epoch cfg store := rfl
      have hadded : AcceptedRealizedJustifiedOrigins cfg ext S added := by
        constructor
        · rcases h.realized with hanchor | ⟨r, hr, hgj' | ⟨hgu', hold⟩⟩
          · exact Or.inl hanchor
          · exact Or.inr ⟨r, ⟨hsub hr.known, hr.2⟩, Or.inl hgj'⟩
          · right
            refine ⟨r, ⟨hsub hr.known, hr.2⟩, Or.inr ⟨hgu', ?_⟩⟩
            have hblock : get_block_epoch cfg added r =
                get_block_epoch cfg store r := by
              simp only [get_block_epoch, holdBlock r hr.known]
            rw [hblock, haddedCurrent]
            exact hold
        · rcases h.unrealized with hanchor | ⟨r, hr, hgu'⟩
          · exact Or.inl hanchor
          · exact Or.inr ⟨r, ⟨hsub hr.known, hr.2⟩, hgu'⟩
      have hstaged : AcceptedRealizedJustifiedOrigins cfg ext S staged :=
        record_block_timeliness cfg ext notified sb.root (hadded.of_payloadFrame cfg ext hf)
      have hboosted : AcceptedRealizedJustifiedOrigins cfg ext S boosted :=
        update_proposer_boost_root cfg ext staged (get_head cfg store).root
          sb.root hstaged
      have haddedRoot : sb.root ∈ added.block_roots := by
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hboostedRoot : sb.root ∈ boosted.block_roots := by
        simp only [boosted, staged,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs
        all_goals rw [hf.block_roots]; exact haddedRoot
      have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
          boosted sb.root := ⟨hboostedRoot, sb.message, hnewAt⟩
      have hrealized : AcceptedRealizedJustifiedOrigins cfg ext S realized := by
        apply update_checkpoints cfg ext boosted post.current_justified_checkpoint
          post.finalized_checkpoint hboosted
        exact Or.inr ⟨sb.root, hcarrier, Or.inl hgj⟩
      have hsameRoots : realized.block_roots = added.block_roots := by
        simp only [realized, boosted, staged,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> exact hf.block_roots
      have hsameStates : realized.block_states = added.block_states := by
        simp only [realized, boosted, staged,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> exact hf.block_states
      have hrealizedCarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
          realized sb.root :=
        ⟨by rw [hsameRoots]; exact haddedRoot, sb.message, hnewAt⟩
      apply compute_pulled_up_tip cfg ext realized sb.root hrealized
        hrealizedCarrier
      rw [hsameStates]
      simp only [added, Function.update_self]
      exact hgu

/-- One exact accepted block transition preserves the refined origin. -/
theorem acceptedBlockTransition
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (hwf : WellFormedExecution E)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S
      (t.atPrefix.store cfg ext)) :
    AcceptedRealizedJustifiedOrigins cfg ext S t.postStore := by
  by_cases hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots
  · obtain ⟨post, hst, hinserted⟩ :=
      Execution.AcceptedBlockTransition.on_block_inserted_state_fresh
        cfg ext hfresh t.accepted
    have hnewAt : E.AcceptedBlockAt cfg ext t.signedBlock.root
        t.signedBlock.message :=
      ⟨t.postStore, t.post_causal, t.root_known,
        Execution.AcceptedBlockTransition.inserted_message_fresh t hfresh⟩
    apply on_block_of_selectors cfg ext hwf (.scheduledPrefix t.atPrefix)
      hnewAt hst
    · rw [← hinserted]
      exact hcoh.transition_gj t
    · rw [← hinserted]
      exact hcoh.transition_gu t
    · exact h
    · exact t.accepted
  · have hknown : t.signedBlock.root ∈
        (t.atPrefix.store cfg ext).block_roots :=
      Classical.byContradiction hfresh
    have hsame : t.postStore = t.atPrefix.store cfg ext := by
      exact (Option.some.inj (by
        simpa only [on_block, if_pos hknown] using t.accepted)).symm
    rw [hsame]
    exact h

end AcceptedRealizedJustifiedOrigins

/-! ## Exact execution trajectory -/

private theorem realizedJustifiedOrigin_slot_at_succ_le
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (n : ℕ) : E.slot_at cfg (n + 1) ≤ E.slot_at cfg n + 1 := by
  obtain ⟨secondsPerSlot, hduration⟩ := hdiv
  have hsecondsPos : 0 < secondsPerSlot := by
    have hdurationPos := cfg.slot_duration_ms_pos
    rw [hduration] at hdurationPos
    omega
  have hdenPos : 0 < cfg.slot_duration_ms / 1000 := by
    rw [hduration, Nat.mul_div_cancel_left secondsPerSlot
      (by omega : (0 : ℕ) < 1000)]
    exact hsecondsPos
  have hdiv' : 1000 ∣ cfg.slot_duration_ms := ⟨secondsPerSlot, hduration⟩
  rw [E.slot_at_eq cfg hdiv', E.slot_at_eq cfg hdiv']
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

private theorem realizedJustifiedOrigins_after_execution_tick
    {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (w : ValidatorIndex) (n : ℕ)
    (h : AcceptedRealizedJustifiedOrigins cfg ext S
      (E.store cfg ext w n)) :
    AcceptedRealizedJustifiedOrigins cfg ext S
      (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
        (E.time_at (n + 1))) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤
      E.genesis_store.time := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).time_ge_genesis
  let store := E.store cfg ext w n
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hs : get_current_slot cfg store = s := by
    simpa only [store, s] using E.store_current_slot cfg ext w n
  have hsnext : s ≤ next := E.slot_at_mono cfg (Nat.le_succ n)
  have hnextLe : next ≤ s + 1 :=
    E.realizedJustifiedOrigin_slot_at_succ_le cfg hT.whole_seconds
      hgenTime n
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
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1)
        store = store := by
      apply AcceptedOldGURealized.on_tick_aux_eq_of_not_lt
      rw [hsame, ← hs]
      exact Nat.lt_irrefl _
    rw [haux]
    apply AcceptedRealizedJustifiedOrigins.after_on_tick_per_slot_same
      cfg ext store (E.time_at (n + 1))
    · rw [htargetCurrent, hsame, ← hs]
    · exact h
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1)
        store = FastConfirmation.Spec.on_tick_per_slot cfg store
          (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000) := by
      rw [hnext]
      exact AcceptedOldGURealized.on_tick_aux_one_slot store s hs
        hT.whole_seconds
    rw [haux]
    let boundaryTime := store.genesis_time +
      (s + 1) * cfg.slot_duration_ms / 1000
    let stepped := FastConfirmation.Spec.on_tick_per_slot cfg store boundaryTime
    have hboundaryCurrent : get_current_slot cfg
        { store with time := boundaryTime } =
          get_current_slot cfg store + 1 := by
      simpa only [boundaryTime, hs] using
        AcceptedOldGURealized.current_slot_at_next_boundary
          (cfg := cfg) hT.whole_seconds store
    have hnonfuture : BlocksSlotLe (get_current_slot cfg store) store := by
      simpa only [store] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds
          ⟨ast, ablk, hgen, hgenSlot⟩ w n
    have hstepped : AcceptedRealizedJustifiedOrigins cfg ext S stepped :=
      AcceptedRealizedJustifiedOrigins.after_on_tick_per_slot_next
        cfg ext store boundaryTime hboundaryCurrent hnonfuture h
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
    exact AcceptedRealizedJustifiedOrigins.after_on_tick_per_slot_same
      cfg ext stepped (E.time_at (n + 1)) hfinalCurrent hstepped

private theorem genesisAcceptedRealizedJustifiedOrigins
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    AcceptedRealizedJustifiedOrigins cfg ext B.state E.genesis_store := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  rw [hgen] at hanchor ⊢
  constructor <;> apply Or.inl <;>
    simpa only [get_forkchoice_store] using hanchor.symm

private theorem acceptedRealizedJustifiedOrigins_take
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : AcceptedRealizedJustifiedOrigins cfg ext B.state
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      AcceptedRealizedJustifiedOrigins cfg ext B.state
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
      have hp : AcceptedRealizedJustifiedOrigins cfg ext B.state
          (p.store cfg ext) := ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedRealizedJustifiedOrigins cfg ext B.state
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
            exact AcceptedRealizedJustifiedOrigins.acceptedBlockTransition
              cfg ext B.coherence.toAcceptedFFGSelectorCoherence
                hT.wellFormed t hp
        | attestation a fromBlock =>
            exact AcceptedRealizedJustifiedOrigins.on_attestation
              cfg ext hp (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact AcceptedRealizedJustifiedOrigins.on_attester_slashing
              cfg ext hp (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope envelope observation =>
            exact hp.of_payloadFrame cfg ext (on_execution_payload_envelope_frame ext
              (by simpa [apply_event, hevent] using heq))
        | payload_attestation_message message fromBlock =>
            exact hp.of_payloadFrame cfg ext (on_payload_attestation_message_frame cfg ext
              (by simpa [apply_event, hevent] using heq))

/-- Every ordinary execution boundary retains the executable `GJ`/old-`GU`
origin of its realized justified checkpoint. -/
theorem acceptedRealizedJustifiedOrigins
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (n : ℕ) :
    AcceptedRealizedJustifiedOrigins cfg ext B.state
      (E.store cfg ext w n) := by
  induction n with
  | zero =>
      exact E.genesisAcceptedRealizedJustifiedOrigins cfg ext B hT hanchor
  | succ n ih =>
      change AcceptedRealizedJustifiedOrigins cfg ext B.state
        ((E.schedule w (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.acceptedRealizedJustifiedOrigins_take cfg ext B hT w n
          (E.realizedJustifiedOrigins_after_execution_tick cfg ext B.state
            hT w n ih)
          (E.schedule w (n + 1)).length le_rfl



end Execution

end FastConfirmation.Spec

end
