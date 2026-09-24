module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGFacts

/-! Two-epoch realized finalization lag from the observer's own accepted calls. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace ObserverFFG
namespace Execution
open FastConfirmation.Spec.Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable (E : FastConfirmation.Spec.Execution Root) {obs : ValidatorIndex}

private theorem ce_mono (cfg : Config) {s t : Slot} (h : s ≤ t) :
    compute_epoch_at_slot cfg s ≤ compute_epoch_at_slot cfg t :=
  Nat.div_le_div_right h

structure AcceptedFinalizationLagAt (anchor : Checkpoint Root)
    (store : Store Root) : Prop where
  realized : store.finalized_checkpoint = anchor ∨
    store.finalized_checkpoint.epoch + 2 ≤
      get_current_store_epoch cfg store
  unrealized : store.unrealized_finalized_checkpoint = anchor ∨
    store.unrealized_finalized_checkpoint.epoch + 1 ≤
      get_current_store_epoch cfg store

namespace AcceptedFinalizationLagAt

private theorem oneEpochLag_becomes_two_of_strict
    {a b c : ℕ} (hab : a + 1 ≤ b) (hbc : b < c) : a + 2 ≤ c := by
  omega

/-- Transport when only the current epoch (rather than the underlying clock
fields) is already known equal. -/
private theorem of_current_eq {anchor : Checkpoint Root} {store store' : Store Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store)
    (hfinalized : store'.finalized_checkpoint = store.finalized_checkpoint)
    (hunrealized : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    AcceptedFinalizationLagAt cfg anchor store' := by
  constructor
  · rw [hfinalized, hcurrent]
    exact h.realized
  · rw [hunrealized, hcurrent]
    exact h.unrealized

/-- Transport across a helper which preserves the clock and both finalized
fields. -/
private theorem of_eq {anchor : Checkpoint Root} {store store' : Store Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (htime : store'.time = store.time)
    (hgenesis : store'.genesis_time = store.genesis_time)
    (hfinalized : store'.finalized_checkpoint = store.finalized_checkpoint)
    (hunrealized : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    AcceptedFinalizationLagAt cfg anchor store' := by
  have hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store := by
    simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg htime hgenesis)
  exact AcceptedFinalizationLagAt.of_current_eq
    (cfg := cfg) h hcurrent hfinalized hunrealized

private theorem update_checkpoints (store : Store Root)
    (jc fc : Checkpoint Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hfc : fc = anchor ∨
      fc.epoch + 2 ≤ get_current_store_epoch cfg store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_checkpoints store jc fc) := by
  simp only [FastConfirmation.Spec.update_checkpoints]
  split_ifs
  all_goals
    constructor
    · first | exact hfc | exact h.realized
    · exact h.unrealized

private theorem update_unrealized_checkpoints (store : Store Root)
    (ujc ufc : Checkpoint Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hufc : ufc = anchor ∨
      ufc.epoch + 1 ≤ get_current_store_epoch cfg store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc) := by
  simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
  split_ifs
  all_goals
    constructor
    · exact h.realized
    · first | exact hufc | exact h.unrealized

private theorem record_block_timeliness (store : Store Root) (r : Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.record_block_timeliness cfg store r) :=
  AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

private theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;>
    exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

private theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root) {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;>
    exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

private theorem update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;>
        exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

private theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {is_from_block : Bool}
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    AcceptedFinalizationLagAt cfg anchor store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact AcceptedFinalizationLagAt.update_latest_messages
    (cfg := cfg) _ _ _
    (AcceptedFinalizationLagAt.store_target_checkpoint_state
      (cfg := cfg) (ext := ext) _ _ h)

private theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root} {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl = some store') :
    AcceptedFinalizationLagAt cfg anchor store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

/-- Pull-up preservation from the already-derived one-epoch GUF timing. -/
private theorem compute_pulled_up_tip (store : Store Root) (r : Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (huf : let ufc := (ext.process_justification_and_finalization
        (store.block_states r)).finalized_checkpoint
      ufc = anchor ∨ ufc.epoch + 1 ≤ get_block_epoch cfg store r)
    (hblock : get_block_epoch cfg store r ≤
      get_current_store_epoch cfg store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) := by
  let state := ext.process_justification_and_finalization
    (store.block_states r)
  set ufc : Checkpoint Root := state.finalized_checkpoint with hufcEq
  have huf' : ufc = anchor ∨
      ufc.epoch + 1 ≤
        get_block_epoch cfg store r := by
    rw [hufcEq]
    simpa only [state] using huf
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update
        store.unrealized_justifications r
          state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hrecorded : AcceptedFinalizationLagAt cfg anchor recorded :=
    AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl
  have hufCurrent : state.finalized_checkpoint = anchor ∨
      state.finalized_checkpoint.epoch + 1 ≤
        get_current_store_epoch cfg recorded := by
    rcases huf' with hanchor | hlag
    · exact Or.inl (hufcEq.symm.trans hanchor)
    · rw [← hufcEq]
      exact Or.inr (hlag.trans hblock)
  have hpulled : AcceptedFinalizationLagAt cfg anchor pulled :=
    AcceptedFinalizationLagAt.update_unrealized_checkpoints
      (cfg := cfg) recorded state.current_justified_checkpoint
        state.finalized_checkpoint hrecorded hufCurrent
  have hpulledBlocks : pulled.blocks = store.blocks := by
    exact (FastConfirmation.Spec.update_unrealized_checkpoints_sameBlocks
      recorded state.current_justified_checkpoint
        state.finalized_checkpoint).2.1.symm.trans rfl
  have hpulledCurrent : get_current_store_epoch cfg pulled =
      get_current_store_epoch cfg store := by
    simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg
        (FastConfirmation.Spec.update_unrealized_checkpoints_time recorded
          state.current_justified_checkpoint state.finalized_checkpoint)
        (FastConfirmation.Spec.update_unrealized_checkpoints_genesis_time recorded
          state.current_justified_checkpoint state.finalized_checkpoint))
  change AcceptedFinalizationLagAt cfg anchor
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled)
  split_ifs with hold
  · apply AcceptedFinalizationLagAt.update_checkpoints (cfg := cfg)
    · exact hpulled
    · rcases huf' with hanchor | hlag
      · exact Or.inl (hufcEq.symm.trans hanchor)
      · right
        have hold' : get_block_epoch cfg store r <
            get_current_store_epoch cfg store := by
          simpa only [get_block_epoch, hpulledBlocks, hpulledCurrent] using hold
        have htwo := oneEpochLag_becomes_two_of_strict
          (a := ufc.epoch)
          (b := get_block_epoch cfg store r)
          (c := get_current_store_epoch cfg store) hlag hold'
        have hepoch : ufc.epoch = state.finalized_checkpoint.epoch :=
          congrArg Checkpoint.epoch hufcEq
        rw [hpulledCurrent, ← hepoch]
        exact htwo
  · exact hpulled

end AcceptedFinalizationLagAt

/- Successful `on_block` exposes the handler's not-in-the-future gate. -/

namespace FFGGlobalCheckpointLedger
private theorem on_tick_per_slot_current_slot
    (store : Store Root) (time : ℕ) :
    get_current_slot cfg (FastConfirmation.Spec.on_tick_per_slot cfg store time) =
      get_current_slot cfg { store with time := time } := by
  simp only [get_current_slot, get_slots_since_genesis,
    FastConfirmation.Spec.on_tick_per_slot_time]
  rw [← (FastConfirmation.Spec.on_tick_per_slot_storeLE cfg store time).2.1]



private theorem current_slot_at_next_boundary
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

private theorem on_tick_aux_eq_of_not_lt
    (tickSlot fuel : ℕ) (store : Store Root)
    (h : ¬ get_current_slot cfg store < tickSlot) :
    FastConfirmation.Spec.on_tick_aux cfg tickSlot fuel store = store := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [FastConfirmation.Spec.on_tick_aux, if_neg h]

private theorem on_tick_aux_one_slot
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


end FFGGlobalCheckpointLedger

private theorem AcceptedBlockTransition.blockEpoch_le_current
    (t : E.AcceptedBlockTransition cfg ext)
    (hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots) :
    compute_epoch_at_slot cfg t.signedBlock.message.slot ≤
      get_current_store_epoch cfg (t.atPrefix.store cfg ext) := by
  have hh := t.accepted
  simp only [FastConfirmation.Spec.on_block, if_neg hfresh] at hh
  split_ifs at hh <;> try cases hh
  apply ce_mono cfg
  simp_all

/-- Handler-local block preservation once the realized and pulled-up timing
facts have been supplied for this concrete transition output. -/
private theorem AcceptedFinalizationLagAt.on_block_of_delays
    {anchor : Checkpoint Root} {store store' : Store Root}
    {sb : SignedBeaconBlock Root} {post : BeaconState Root}
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgf : post.finalized_checkpoint = anchor ∨
      post.finalized_checkpoint.epoch + 2 ≤
        compute_epoch_at_slot cfg sb.message.slot)
    (hguf :
      (ext.process_justification_and_finalization post).finalized_checkpoint =
          anchor ∨
        (ext.process_justification_and_finalization post
          ).finalized_checkpoint.epoch + 1 ≤
          compute_epoch_at_slot cfg sb.message.slot)
    (hblock : compute_epoch_at_slot cfg sb.message.slot ≤
      get_current_store_epoch cfg store)
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    AcceptedFinalizationLagAt cfg anchor store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [FastConfirmation.Spec.on_block, if_pos hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
    rw [hst] at hh
    let inserted : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote := Function.update store.payload_data_availability_vote
          sb.root (some (List.replicate cfg.ptc_size none)) }
    change (match notify_ptc_messages cfg ext inserted post sb.message.payload_attestations with
      | none => none
      | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
          (FastConfirmation.Spec.update_checkpoints
            (FastConfirmation.Spec.update_proposer_boost_root cfg
              (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
              (get_head cfg store).root sb.root)
            post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
      some store' at hh
    cases hn : notify_ptc_messages cfg ext inserted post sb.message.payload_attestations with
    | none => rw [hn] at hh; cases hh
    | some notified =>
      rw [hn] at hh
      cases hh
      have hf : PayloadFrame inserted notified := notify_ptc_messages_frame cfg ext hn
      let added := notified
      let staged := FastConfirmation.Spec.record_block_timeliness cfg added
        sb.root
      let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := FastConfirmation.Spec.update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      suffices hresult : AcceptedFinalizationLagAt cfg anchor
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized
            sb.root) by
        exact hresult
      have hadded : AcceptedFinalizationLagAt cfg anchor added :=
        AcceptedFinalizationLagAt.of_eq (cfg := cfg) h hf.time hf.genesis_time
          hf.finalized_checkpoint hf.unrealized_finalized_checkpoint
      have hstaged : AcceptedFinalizationLagAt cfg anchor staged :=
        AcceptedFinalizationLagAt.record_block_timeliness (cfg := cfg) added
          sb.root hadded
      have hboosted : AcceptedFinalizationLagAt cfg anchor boosted :=
        AcceptedFinalizationLagAt.update_proposer_boost_root (cfg := cfg) staged
          (get_head cfg store).root sb.root hstaged
      have hgfCurrent : post.finalized_checkpoint = anchor ∨
          post.finalized_checkpoint.epoch + 2 ≤
            get_current_store_epoch cfg boosted := by
        rcases hgf with hanchor | hlag
        · exact Or.inl hanchor
        · right
          have hcurrent : get_current_store_epoch cfg boosted =
              get_current_store_epoch cfg store := by
            simp only [boosted, staged, added, hf.time, hf.genesis_time, inserted,
              FastConfirmation.Spec.update_proposer_boost_root,
              FastConfirmation.Spec.record_block_timeliness,
              get_current_store_epoch, get_current_slot, get_slots_since_genesis]
            split_ifs <;> simp only [hf.time, hf.genesis_time, inserted]
          rw [hcurrent]
          exact hlag.trans hblock
      have hrealized : AcceptedFinalizationLagAt cfg anchor realized :=
        AcceptedFinalizationLagAt.update_checkpoints (cfg := cfg) boosted
          post.current_justified_checkpoint post.finalized_checkpoint
          hboosted hgfCurrent
      have hrealizedBlock : get_block_epoch cfg realized sb.root =
          compute_epoch_at_slot cfg sb.message.slot := by
        simp only [get_block_epoch, realized, boosted, staged, added, hf.blocks, inserted,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> simp only [hf.blocks, inserted, Function.update_self]
      have hrealizedState : realized.block_states sb.root = post := by
        simp only [realized, boosted, staged, added, hf.block_states, inserted,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> simp only [hf.block_states, inserted, Function.update_self]
      have hrealizedCurrent : get_current_store_epoch cfg realized =
          get_current_store_epoch cfg store := by
        simp only [realized, boosted, staged, added, hf.time, hf.genesis_time, inserted,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness,
          get_current_store_epoch, get_current_slot, get_slots_since_genesis]
        split_ifs <;> simp only [hf.time, hf.genesis_time, inserted]
      apply AcceptedFinalizationLagAt.compute_pulled_up_tip
        (cfg := cfg) (ext := ext) realized
        sb.root hrealized
      · rw [hrealizedState, hrealizedBlock]
        exact hguf
      · rw [hrealizedBlock, hrealizedCurrent]
        exact hblock

private theorem AcceptedFinalizationLagAt.acceptedBlockTransition
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (t : E.AcceptedBlockTransition cfg ext) (ht : t.atPrefix.node = obs)
    (h : AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint
      (t.atPrefix.store cfg ext)) :
    AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint t.postStore := by
  by_cases hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots
  · obtain ⟨post, hst, hinserted⟩ :=
      Execution.AcceptedBlockTransition.on_block_inserted_state_fresh
        cfg ext hfresh t.accepted
    apply AcceptedFinalizationLagAt.on_block_of_delays
      (cfg := cfg) (ext := ext) hst
    · simpa only [hinserted] using B.finalization_delay t ht
    · simpa only [hinserted] using
        B.pulled_finalized_lag core localInputs t ht
    · exact AcceptedBlockTransition.blockEpoch_le_current
        cfg ext E t hfresh
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

private theorem epoch_lt_of_slots_since_succ_eq_zero (s : Slot)
    (hzero : compute_slots_since_epoch_start cfg (s + 1) = 0) :
    compute_epoch_at_slot cfg s < compute_epoch_at_slot cfg (s + 1) := by
  by_contra hnot
  have hmono : compute_epoch_at_slot cfg s ≤
      compute_epoch_at_slot cfg (s + 1) :=
    ce_mono cfg (Nat.le_succ s)
  have heq : compute_epoch_at_slot cfg (s + 1) =
      compute_epoch_at_slot cfg s :=
    Nat.le_antisymm (Nat.le_of_not_gt hnot) hmono
  have hboundaryLe : s + 1 ≤
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (s + 1)) :=
    Nat.sub_eq_zero_iff_le.mp hzero
  rw [heq] at hboundaryLe
  have hfloor := Nat.div_mul_le_self s cfg.slots_per_epoch
  have himpossible : s + 1 ≤ s := by
    exact hboundaryLe.trans (by
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hfloor)
  exact (Nat.not_succ_le_self s) himpossible

/-- If the final clock write remains in the same slot, `on_tick_per_slot`
does not pull up checkpoints. -/
private theorem AcceptedFinalizationLagAt.after_on_tick_per_slot_same
    {anchor : Checkpoint Root} (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store)
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  rw [hcurrent]
  simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte, false_and]
  apply AcceptedFinalizationLagAt.of_current_eq (cfg := cfg) h
  · simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg) hcurrent
  · rfl
  · rfl

/-- Crossing one slot preserves the pair.  At an epoch boundary the old
unrealized finalized checkpoint is offered to the realized maximum; its
one-epoch lag becomes a two-epoch lag because the epoch strictly advanced. -/
private theorem AcceptedFinalizationLagAt.after_on_tick_per_slot_next
    {anchor : Checkpoint Root} (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store + 1)
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  let timed : Store Root := { store with time := time }
  let reset : Store Root :=
    if get_current_slot cfg timed > get_current_slot cfg store then
      { timed with proposer_boost_root := (default : Root) }
    else timed
  have hresetSlot : get_current_slot cfg reset = get_current_slot cfg timed := by
    simp only [reset]
    split_ifs <;> rfl
  have hresetFinalized : reset.finalized_checkpoint =
      store.finalized_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  have hresetUnrealized : reset.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  have hcurrentLe : get_current_store_epoch cfg store ≤
      get_current_store_epoch cfg reset := by
    apply ce_mono cfg
    rw [hresetSlot, hcurrent]
    exact Nat.le_succ _
  have hbase : AcceptedFinalizationLagAt cfg anchor reset := by
    constructor
    · rw [hresetFinalized]
      rcases h.realized with hanchor | hlag
      · exact Or.inl hanchor
      · exact Or.inr (hlag.trans hcurrentLe)
    · rw [hresetUnrealized]
      rcases h.unrealized with hanchor | hlag
      · exact Or.inl hanchor
      · exact Or.inr (hlag.trans hcurrentLe)
  change AcceptedFinalizationLagAt cfg anchor
    (if get_current_slot cfg timed > get_current_slot cfg store ∧
        compute_slots_since_epoch_start cfg (get_current_slot cfg timed) = 0 then
      FastConfirmation.Spec.update_checkpoints reset
        reset.unrealized_justified_checkpoint
        reset.unrealized_finalized_checkpoint
    else reset)
  split_ifs with hpull
  · apply AcceptedFinalizationLagAt.update_checkpoints (cfg := cfg)
    · exact hbase
    · have hzero : compute_slots_since_epoch_start cfg
          (get_current_slot cfg store + 1) = 0 := by
        rw [← hcurrent]
        exact hpull.2
      have hepochStrict : get_current_store_epoch cfg store <
          get_current_store_epoch cfg reset := by
        have htimedSlot : get_current_slot cfg timed =
            get_current_slot cfg store + 1 := by
          simpa only [timed] using hcurrent
        simp only [get_current_store_epoch]
        rw [hresetSlot, htimedSlot]
        exact epoch_lt_of_slots_since_succ_eq_zero
          (cfg := cfg) (get_current_slot cfg store) hzero
      rw [hresetUnrealized]
      rcases h.unrealized with hanchor | hlag
      · exact Or.inl hanchor
      · exact Or.inr
          (oneEpochLag_becomes_two_of_strict hlag hepochStrict)
  · exact hbase

/-- The execution clock advances by at most one slot per relative second. -/
private theorem finalizationLag_slot_at_succ_le
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

/-- The exact execution tick preserves the paired invariant. -/
private theorem finalizationLag_after_execution_tick
    {anchor : Checkpoint Root}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (w : ValidatorIndex) (n : ℕ)
    (h : AcceptedFinalizationLagAt cfg anchor (E.store cfg ext w n)) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
        (E.time_at (n + 1))) := by
  let store := E.store cfg ext w n
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hs : get_current_slot cfg store = s := by
    simpa only [store, s] using E.store_current_slot cfg ext w n
  have hsnext : s ≤ next := E.slot_at_mono cfg (Nat.le_succ n)
  have hnextLe : next ≤ s + 1 :=
    FastConfirmation.Spec.ObserverFFG.Execution.finalizationLag_slot_at_succ_le cfg E hdiv hgenTime n
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
    apply AcceptedFinalizationLagAt.after_on_tick_per_slot_same
      (cfg := cfg) store (E.time_at (n + 1))
    · rw [htargetCurrent, hsame, ← hs]
    · exact h
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1) store =
        FastConfirmation.Spec.on_tick_per_slot cfg store
          (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000) := by
      rw [hnext]
      exact FFGGlobalCheckpointLedger.on_tick_aux_one_slot cfg store s hs hdiv
    rw [haux]
    let boundaryTime := store.genesis_time +
      (s + 1) * cfg.slot_duration_ms / 1000
    let stepped := FastConfirmation.Spec.on_tick_per_slot cfg store boundaryTime
    have hboundaryCurrent : get_current_slot cfg
        { store with time := boundaryTime } =
          get_current_slot cfg store + 1 := by
      simpa only [boundaryTime, hs] using
        FFGGlobalCheckpointLedger.current_slot_at_next_boundary
          (cfg := cfg) hdiv store
    have hstepped : AcceptedFinalizationLagAt cfg anchor stepped :=
      AcceptedFinalizationLagAt.after_on_tick_per_slot_next
        (cfg := cfg) store boundaryTime hboundaryCurrent h
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
          exact get_current_slot_congr cfg
            (s := { stepped with time := E.time_at (n + 1) })
            (t := { store with time := E.time_at (n + 1) }) rfl hg
        _ = next := htargetCurrent
        _ = get_current_slot cfg stepped := hsteppedCurrent.symm
    exact AcceptedFinalizationLagAt.after_on_tick_per_slot_same
      (cfg := cfg) stepped (E.time_at (n + 1)) hfinalCurrent hstepped

private theorem genesisAcceptedFinalizationLagAt
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    :
    AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint E.genesis_store := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hcommit, _hparent⟩ := core.genesis
  change AcceptedFinalizationLagAt cfg
    E.genesis_store.justified_checkpoint E.genesis_store
  rw [show E.genesis_store = _ from hgenEq]
  constructor <;> exact Or.inl rfl

private theorem acceptedFinalizationLagAt_take
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (w : ValidatorIndex) (n : ℕ) (hw : w = obs)
    (hbase : AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint
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
      have hp : AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint (p.store cfg ext) :=
        ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint
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
            exact AcceptedFinalizationLagAt.acceptedBlockTransition
              (cfg := cfg) (ext := ext) (E := E) B core localInputs t hw hp
        | attestation a fromBlock =>
            exact AcceptedFinalizationLagAt.on_attestation
              (cfg := cfg) (ext := ext) hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact AcceptedFinalizationLagAt.on_attester_slashing
              (cfg := cfg) (ext := ext) hp
              (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope envelope observation =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_execution_payload_envelope_frame ext (by simpa [apply_event, hevent] using heq)
            exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) hp hf.time hf.genesis_time
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint
        | payload_attestation_message message isFromBlock =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_payload_attestation_message_frame cfg ext (by simpa [apply_event, hevent] using heq)
            exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) hp hf.time hf.genesis_time
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint

/-- The paired finalization-lag invariant at every ordinary execution
boundary. -/
theorem acceptedFinalizationLagAt
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (w : ValidatorIndex) (n : ℕ) (hw : w = obs) :
    AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint (E.store cfg ext w n) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hcommit, _hparent⟩ := core.genesis
    rw [show E.genesis_store = _ from hgenEq]
    simp only [get_forkchoice_store]
    omega
  induction n with
  | zero =>
      exact FastConfirmation.Spec.ObserverFFG.Execution.genesisAcceptedFinalizationLagAt cfg ext E B core localInputs
  | succ n ih =>
      change AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint
        ((E.schedule w (n + 1)).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      simpa only [List.take_length] using
        FastConfirmation.Spec.ObserverFFG.Execution.acceptedFinalizationLagAt_take cfg ext E B core localInputs w n hw
          (FastConfirmation.Spec.ObserverFFG.Execution.finalizationLag_after_execution_tick cfg ext E
            core.base.whole_seconds hgenTime w n ih)
          (E.schedule w (n + 1)).length le_rfl

/-- The same invariant at an arbitrary exact in-second scheduled prefix. -/
theorem ScheduledEventPrefix.acceptedFinalizationLagAt
    (p : E.ScheduledEventPrefix) (hp : p.node = obs)
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    :
    AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint (p.store cfg ext) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hcommit, _hparent⟩ := core.genesis
    rw [show E.genesis_store = _ from hgenEq]
    simp only [get_forkchoice_store]
    omega
  apply FastConfirmation.Spec.ObserverFFG.Execution.acceptedFinalizationLagAt_take cfg ext E B core localInputs
    p.node p.previousSecond hp
  · exact FastConfirmation.Spec.ObserverFFG.Execution.finalizationLag_after_execution_tick cfg ext E
      core.base.whole_seconds hgenTime p.node p.previousSecond
      (FastConfirmation.Spec.ObserverFFG.Execution.acceptedFinalizationLagAt cfg ext E B core localInputs p.node p.previousSecond hp)
  · exact p.count_le

/-- Paired lag at every exact causal store. -/
theorem observerCausalStore_finalizationLag
    {store : Store Root} (hstore : E.ObserverCausalStore cfg ext obs store)
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    :
    AcceptedFinalizationLagAt cfg E.genesis_store.justified_checkpoint store := by
  cases hstore with
  | genesis =>
      exact FastConfirmation.Spec.ObserverFFG.Execution.genesisAcceptedFinalizationLagAt cfg ext E B core localInputs
  | scheduledPrefix p hp =>
      exact ScheduledEventPrefix.acceptedFinalizationLagAt p hp
        (cfg := cfg) (ext := ext) (E := E) B core localInputs


end Execution
end ObserverFFG
end FastConfirmation.Spec
end
