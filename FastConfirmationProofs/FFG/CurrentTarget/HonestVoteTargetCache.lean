module
public import FastConfirmationProofs.Execution.Delivery.Delivery

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Honest vote target cache

Checkpoint-state keys persist through every handler and each execution step.
An honest vote delivered at the next slot passes validation and caches its
exact FFG target. Payload-envelope relay supplies receiver verification for
index-one votes before validation.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Monotonicity of the checkpoint-state key domain -/

/-- The checkpoint-state cache domain only grows. -/
def CheckpointKeysLE (old new : Store Root) : Prop :=
  old.checkpoint_state_keys ⊆ new.checkpoint_state_keys

namespace CheckpointKeysLE

theorem refl (store : Store Root) : CheckpointKeysLE store store :=
  Finset.Subset.refl _

theorem trans {a b c : Store Root}
    (hab : CheckpointKeysLE a b) (hbc : CheckpointKeysLE b c) :
    CheckpointKeysLE a c := by
  intro checkpoint hcheckpoint
  exact hbc (hab hcheckpoint)

theorem of_eq {old new : Store Root}
    (h : new.checkpoint_state_keys = old.checkpoint_state_keys) :
    CheckpointKeysLE old new := by
  unfold CheckpointKeysLE
  rw [h]

end CheckpointKeysLE

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

omit [LinearOrder Root] [Inhabited Root] in
@[simp] theorem update_latest_messages_checkpoint_state_keys
    (store : Store Root) (indices : List ValidatorIndex)
    (a : Attestation Root) :
    (update_latest_messages store indices a).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [update_latest_messages]
  induction indices.filter
      (fun i => decide (i ∉ store.equivocating_indices)) generalizing store with
  | nil => rfl
  | cons i rest ih =>
      rw [List.foldl_cons, ih]
      split_ifs <;> rfl

omit [Inhabited Root] in
@[simp] theorem store_target_checkpoint_state_checkpointKeysLE
    (store : Store Root) (target : Checkpoint Root) :
    CheckpointKeysLE store
      (store_target_checkpoint_state cfg ext store target) := by
  simp only [CheckpointKeysLE, store_target_checkpoint_state]
  split_ifs <;>
    first
    | exact Finset.Subset.refl _
    | exact Finset.subset_insert _ _

omit [Inhabited Root] in
@[simp] theorem store_target_checkpoint_state_target_mem
    (store : Store Root) (target : Checkpoint Root) :
    target ∈
      (store_target_checkpoint_state cfg ext store target).checkpoint_state_keys := by
  simp only [store_target_checkpoint_state]
  split_ifs with hnew <;> simp_all

omit [Inhabited Root] in
@[simp] theorem compute_pulled_up_tip_checkpoint_state_keys
    (store : Store Root) (root : Root) :
    (compute_pulled_up_tip cfg ext store root).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [compute_pulled_up_tip]
  split_ifs <;> simp

omit [LinearOrder Root] in
@[simp] theorem on_tick_per_slot_checkpoint_state_keys
    (store : Store Root) (time : Nat) :
    (on_tick_per_slot cfg store time).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [on_tick_per_slot]
  split_ifs <;> simp

omit [Inhabited Root] in
@[simp] theorem record_block_timeliness_checkpoint_state_keys
    (store : Store Root) (root : Root) :
    (record_block_timeliness cfg store root).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  rfl

@[simp] theorem update_proposer_boost_root_checkpoint_state_keys
    (store : Store Root) (head root : Root) :
    (update_proposer_boost_root cfg store head root).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [update_proposer_boost_root]
  split_ifs <;> rfl

omit [LinearOrder Root] in
@[simp] theorem on_tick_aux_checkpoint_state_keys
    (tickSlot fuel : Nat) (store : Store Root) :
    (on_tick_aux cfg tickSlot fuel store).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  induction fuel generalizing store with
  | zero => rfl
  | succ fuel ih =>
      rw [on_tick_aux]
      split_ifs
      · rw [ih, on_tick_per_slot_checkpoint_state_keys]
      · rfl

omit [LinearOrder Root] in
@[simp] theorem on_tick_checkpoint_state_keys
    (store : Store Root) (time : Nat) :
    (on_tick cfg store time).checkpoint_state_keys =
      store.checkpoint_state_keys := by
  simp only [on_tick, on_tick_per_slot_checkpoint_state_keys,
    on_tick_aux_checkpoint_state_keys]

omit [Inhabited Root] in
theorem on_attestation_checkpointKeysLE {store store' : Store Root}
    {a : Attestation Root} {fromBlock : Bool}
    (h : on_attestation cfg ext store a fromBlock = some store') :
    CheckpointKeysLE store store' := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  unfold CheckpointKeysLE
  rw [update_latest_messages_checkpoint_state_keys]
  exact store_target_checkpoint_state_checkpointKeysLE cfg ext store a.data.target

omit [Inhabited Root] in
theorem on_attestation_target_cached {store store' : Store Root}
    {a : Attestation Root} {fromBlock : Bool}
    (h : on_attestation cfg ext store a fromBlock = some store') :
    a.data.target ∈ store'.checkpoint_state_keys := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  rw [update_latest_messages_checkpoint_state_keys]
  exact store_target_checkpoint_state_target_mem cfg ext store a.data.target

omit [Inhabited Root] in
theorem on_attester_slashing_checkpointKeysLE {store store' : Store Root}
    {slashing : AttesterSlashing Root}
    (h : on_attester_slashing ext store slashing = some store') :
    CheckpointKeysLE store store' := by
  simp only [on_attester_slashing] at h
  split_ifs at h
  cases h
  exact CheckpointKeysLE.refl _

theorem on_block_checkpointKeysLE {store store' : Store Root}
    {block : SignedBeaconBlock Root}
    (h : on_block cfg ext store block = some store') :
    CheckpointKeysLE store store' := by
  by_cases hknown : block.root ∈ store.block_roots
  · simp only [on_block, if_pos hknown] at h
    cases h
    exact CheckpointKeysLE.refl _
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h <;> try cases h
    cases htransition :
        ext.state_transition (store.block_states block.message.parent_root) block with
    | none => rw [htransition] at h; cases h
    | some state =>
        rw [htransition] at h
        let added : Store Root :=
          { store with
            block_roots := store.block_roots ++ [block.root]
            blocks := Function.update store.blocks block.root block.message
            block_states := Function.update store.block_states block.root state
            payload_timeliness_vote := Function.update store.payload_timeliness_vote
              block.root (some (List.replicate cfg.ptc_size none))
            payload_data_availability_vote := Function.update store.payload_data_availability_vote
              block.root (some (List.replicate cfg.ptc_size none)) }
        change (match notify_ptc_messages cfg ext added state block.message.payload_attestations with
          | none => none
          | some notified => some (compute_pulled_up_tip cfg ext
              (update_checkpoints
                (update_proposer_boost_root cfg
                  (record_block_timeliness cfg notified block.root)
                  (get_head cfg store).root block.root)
                state.current_justified_checkpoint state.finalized_checkpoint) block.root)) =
            some store' at h
        cases hn : notify_ptc_messages cfg ext added state block.message.payload_attestations with
        | none => rw [hn] at h; cases h
        | some notified =>
          rw [hn] at h
          cases h
          apply CheckpointKeysLE.of_eq
          simp only [compute_pulled_up_tip_checkpoint_state_keys,
            update_checkpoints_checkpoint_state_keys,
            update_proposer_boost_root_checkpoint_state_keys,
            record_block_timeliness_checkpoint_state_keys]
          exact (notify_ptc_messages_frame cfg ext hn).checkpoint_state_keys

theorem apply_event_checkpointKeysLE {store store' : Store Root}
    {event : Event Root}
    (h : apply_event cfg ext store event = some store') :
    CheckpointKeysLE store store' := by
  cases event with
  | block b => exact on_block_checkpointKeysLE cfg ext h
  | attestation a fromBlock => exact on_attestation_checkpointKeysLE cfg ext h
  | attester_slashing slashing =>
      exact on_attester_slashing_checkpointKeysLE ext h
  | execution_payload_envelope envelope observation =>
      exact CheckpointKeysLE.of_eq (on_execution_payload_envelope_frame ext h).checkpoint_state_keys
  | payload_attestation_message message ifb =>
      exact CheckpointKeysLE.of_eq (on_payload_attestation_message_frame cfg ext h).checkpoint_state_keys

theorem apply_event_getD_checkpointKeysLE
    (store : Store Root) (event : Event Root) :
    CheckpointKeysLE store ((apply_event cfg ext store event).getD store) := by
  cases h : apply_event cfg ext store event with
  | none => exact CheckpointKeysLE.refl _
  | some store' => exact apply_event_checkpointKeysLE cfg ext h

theorem foldl_checkpointKeysLE (events : List (Event Root))
    (store : Store Root) :
    CheckpointKeysLE store
      (events.foldl
        (fun acc event => (apply_event cfg ext acc event).getD acc) store) := by
  induction events generalizing store with
  | nil => exact CheckpointKeysLE.refl _
  | cons event rest ih =>
      exact (apply_event_getD_checkpointKeysLE cfg ext store event).trans (ih _)

namespace Execution

variable (E : Execution Root)

theorem store_checkpointKeysLE_succ (v : ValidatorIndex) (n : Nat) :
    CheckpointKeysLE (E.store cfg ext v n) (E.store cfg ext v (n + 1)) := by
  change CheckpointKeysLE (E.store cfg ext v n)
    ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
  exact (CheckpointKeysLE.of_eq
      (on_tick_checkpoint_state_keys cfg (E.store cfg ext v n)
        (E.time_at (n + 1)))).trans
    (foldl_checkpointKeysLE cfg ext _ _)

theorem store_checkpointKeysLE (v : ValidatorIndex)
    {n m : Nat} (hnm : n ≤ m) :
    CheckpointKeysLE (E.store cfg ext v n) (E.store cfg ext v m) := by
  induction m with
  | zero =>
      cases Nat.le_zero.mp hnm
      exact CheckpointKeysLE.refl _
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans
          (E.store_checkpointKeysLE_succ cfg ext v m)
      · cases Nat.le_antisymm hnm hge
        exact CheckpointKeysLE.refl _

/-! ## Honest target caching at and after delivery -/

/-- At the first second of the next slot, every honest recipient has cached
the exact target of the delivered honest vote.  This is the target-key
postcondition hidden inside `vote_lands`: validation succeeds, then
`store_target_checkpoint_state` inserts the target before latest messages are
updated, and the remaining events preserve the key. -/
theorem honestVoteTarget_cached_at_delivery
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : NextSlotSynchronyPremises cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : Nat} {index : CommitteeIndex}
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHdeliver : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hheadKnown :
      (honest_attestation cfg ext
        (E.store cfg ext v n) s index v).data.beacon_block_root ∈
          (E.store cfg ext v n).block_roots)
    (hheadWalk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext v n) s index v).data.target.epoch)
      (honest_attestation cfg ext
        (E.store cfg ext v n) s index v).data.beacon_block_root) :
    (honest_attestation cfg ext
      (E.store cfg ext v n) s index v).data.target ∈
        (E.store cfg ext w
          (E.slot_start cfg (s + 1))).checkpoint_state_keys := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  set a := honest_attestation cfg ext
    (E.store cfg ext v n) s index v with ha
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hgenTime :
      E.genesis_store.genesis_time ≤ E.genesis_store.time :=
    hgws.time_ge_genesis
  have hparentSlots : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled v n
  have hsingle : a.attesting_indices = [v] := by rw [ha]; rfl
  have haSlot : a.data.slot = s := by rw [ha]; rfl
  have hheadStateSlot :
      ((E.store cfg ext v n).block_states
        (get_head cfg (E.store cfg ext v n)).root).slot ≤ s := by
    have hheadRoot : (get_head cfg
        (E.store cfg ext v n)).root ∈
          (E.store cfg ext v n).block_roots := hheadKnown
    have hcore := E.store_wellFormedStoreCore cfg ext
      hec.state_transition_slot hgws.core v n
    rw [hcore.2 _ hheadRoot]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext hdiv
      ⟨ast, ablk, hgenEq, hslot⟩ v n _ hheadRoot
    rwa [E.store_current_slot cfg ext v n, hn] at hblockSlot
  have htargetEpoch :
      a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot := by
    rw [haSlot, ha]
    exact honest_attestation_data_target_epoch cfg ext
      (E.store cfg ext v n) s index hec.process_slots_slot hheadStateSlot
  have htargetCheckpoint :
      a.data.target.root = get_checkpoint_block cfg
        (E.store cfg ext v n) a.data.beacon_block_root
          a.data.target.epoch := by
    rw [ha]
    exact honest_attestation_data_target_root cfg ext
      (E.store cfg ext v n) s index
  have htargetRoot :
      a.data.target.root ∈ (E.store cfg ext v n).block_roots := by
    rw [htargetCheckpoint]
    simp only [get_checkpoint_block]
    exact (get_ancestor_spec hparentSlots hheadWalk).1
  have hbeaconSlot :
      ((E.store cfg ext v n).blocks a.data.beacon_block_root).slot ≤
        a.data.slot := by
    rw [haSlot]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext hdiv
      ⟨ast, ablk, hgenEq, hslot⟩ v n
      a.data.beacon_block_root hheadKnown
    rwa [E.store_current_slot cfg ext v n, hn] at hblockSlot
  have hcommittee : v ∈ E.committee s :=
    hhb.votes_assigned v hv s
      (by rw [hvote]; exact Option.some_ne_none _)
  have hcommitteeAtVote : v ∈ E.committee a.data.slot := by
    rw [haSlot]
    exact hcommittee
  have hvoteExists :
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data :=
    ⟨n, a, by rw [haSlot]; exact hvote, rfl⟩
  have hs0 : E.slot_at cfg 0 ≤ s :=
    hn ▸ E.slot_at_mono cfg (Nat.zero_le n)
  have hdeliverySlot :
      E.slot_at cfg (E.slot_start cfg (s + 1)) = s + 1 :=
    E.slot_at_slot_start cfg hdiv
      (le_trans hs0 (Nat.le_succ s)) hgenTime
  have hdeliveryPos : 0 < E.slot_start cfg (s + 1) := by
    rcases Nat.eq_zero_or_pos (E.slot_start cfg (s + 1)) with hzero | hpos
    · exfalso
      rw [hzero] at hdeliverySlot
      rw [hdeliverySlot] at hs0
      exact absurd hs0 (Nat.not_succ_le_self s)
    · exact hpos
  obtain ⟨deliveryPred, hdeliveryEq⟩ :
      ∃ k, E.slot_start cfg (s + 1) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hdeliveryPos).symm⟩
  have hslotPred : E.slot_at cfg (deliveryPred + 1) = s + 1 := by
    rw [← hdeliveryEq]
    exact hdeliverySlot
  have hrelayTiming :
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (deliveryPred + 1) :=
    le_of_eq (by rw [hn, hslotPred])
  set ticked := on_tick cfg (E.store cfg ext w deliveryPred)
    (E.time_at (deliveryPred + 1)) with hticked
  have htickedGenesis :
      ticked.genesis_time = E.genesis_store.genesis_time := by
    rw [hticked,
      ← (on_tick_storeLE cfg (E.store cfg ext w deliveryPred)
        (E.time_at (deliveryPred + 1))).2.1,
      E.store_genesis_time cfg ext w deliveryPred]
  have htickedSlot :
      get_current_slot cfg ticked = E.slot_at cfg (deliveryPred + 1) := by
    rw [hticked, get_current_slot, get_slots_since_genesis,
      on_tick_time, htickedGenesis, Execution.slot_at]
  have hscheduled :
      Event.attestation a false ∈ E.schedule w (deliveryPred + 1) := by
    rw [← hdeliveryEq]
    exact hsyn.attestation_delivery v hv s n a
      (E.slotWithinHorizon_of_le cfg (by rw [hn]) hHn)
      hHn hvote hHdeliver w hw
  obtain ⟨pre, suf, hscheduleEq⟩ := List.append_of_mem hscheduled
  have htickedRoots :
      ticked.block_roots = (E.store cfg ext w deliveryPred).block_roots := by
    rw [hticked]
    exact ((on_tick_sameBlocks cfg (E.store cfg ext w deliveryPred)
      (E.time_at (deliveryPred + 1))).1).symm
  have hroots :
      (E.store cfg ext v n).block_roots ⊆
        (pre.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ticked).block_roots := by
    intro root hroot
    have hHdelivery : E.WithinHorizon cfg (deliveryPred + 1) := by
      rwa [← hdeliveryEq]
    have hHpred : E.WithinHorizon cfg deliveryPred :=
      E.withinHorizon_mono cfg (Nat.le_succ deliveryPred) hHdelivery
    have hrootPred : root ∈
        (E.store cfg ext w deliveryPred).block_roots :=
      hsyn.block_relay v hv n root hHn hroot w hw deliveryPred hHpred
        hrelayTiming
    have hrootTicked : root ∈ ticked.block_roots := by
      rw [htickedRoots]
      exact hrootPred
    exact (foldl_storeLE cfg ext pre ticked).1 hrootTicked
  have htickedProvenance : BlockProvenance E ticked := by
    rw [hticked]
    exact on_tick_blockProvenance cfg
      (E.store cfg ext w deliveryPred) (E.time_at (deliveryPred + 1))
      (E.blockProvenance cfg ext w deliveryPred)
  have hprefixBlocks :
      ∀ b, Event.block b ∈ pre → IsScheduledBlock E b :=
    fun b hb =>
      ⟨w, deliveryPred + 1,
        by rw [hscheduleEq]; exact List.mem_append_left _ hb⟩
  have hprefixProvenance : BlockProvenance E
      (pre.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) :=
    blockProvenance_foldl cfg ext pre ticked
      hprefixBlocks htickedProvenance
  have hagree :
      ∀ root ∈ (E.store cfg ext v n).block_roots,
        (E.store cfg ext v n).blocks root =
          (pre.foldl
            (fun store event => (apply_event cfg ext store event).getD store)
            ticked).blocks root :=
    fun root hroot => hwf.blocks_agree
      (E.blockProvenance cfg ext v n) hprefixProvenance
      hroot (hroots hroot)
  have hprefixSlot : get_current_slot cfg
      (pre.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) = a.data.slot + 1 := by
    rw [foldl_get_current_slot cfg ext pre ticked,
      htickedSlot, hslotPred, haSlot]
  have hindex : a.data.index = 0 ∨ a.data.index = 1 := by
    rw [ha]
    exact honest_attestation_data_index_shape cfg ext (E.store cfg ext v n) s index
  have hsame : ((E.store cfg ext v n).blocks a.data.beacon_block_root).slot =
      a.data.slot → a.data.index = 0 := by
    intro hs
    rw [ha] at hs ⊢
    exact honest_attestation_data_same_slot_index cfg ext (E.store cfg ext v n) s index hs
  have hpayload : a.data.index = 1 → is_payload_verified
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        ticked) a.data.beacon_block_root = true := by
    intro hi
    rw [ha, hticked]
    exact E.honest_payload_verified_at_delivery_prefix cfg ext hwf hsyn hec hv hw hHn
      (E.withinHorizon_mono cfg (Nat.le_succ deliveryPred)
        (by simpa only [Nat.succ_eq_add_one, ← hdeliveryEq] using hHdeliver))
      hrelayTiming pre s index hi
  have hvalidates : validate_on_attestation cfg
      (pre.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) a false = true :=
    validate_at_extension cfg (E.store cfg ext v n)
      (pre.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) a hagree hroots hprefixSlot htargetEpoch hheadKnown
      htargetRoot hbeaconSlot htargetCheckpoint hheadWalk hindex hsame hpayload
  have hindexedValid : ext.is_valid_indexed_attestation
      ((store_target_checkpoint_state cfg ext
        (pre.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ticked) a.data.target).checkpoint_states a.data.target) a = true :=
    honest_attestation_valid_prepared cfg ext hec
      (E.honestCausalStore_prefix cfg ext w hw deliveryPred
        (by simpa only [← hdeliveryEq] using hHdeliver)
        pre (Event.attestation a false :: suf) hscheduleEq)
      a (hroots htargetRoot) v hv hsingle hcommitteeAtVote hvoteExists
  let applied := update_latest_messages
    (store_target_checkpoint_state cfg ext
      (pre.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) a.data.target) a.attesting_indices a
  have happlied : on_attestation cfg ext
      (pre.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) a false = some applied := by
    simp only [on_attestation]
    rw [if_neg (not_not_intro hvalidates),
      if_neg (not_not_intro hindexedValid)]
  have htargetApplied : a.data.target ∈ applied.checkpoint_state_keys :=
    on_attestation_target_cached cfg ext happlied
  have htargetEnd : a.data.target ∈
      (suf.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        applied).checkpoint_state_keys :=
    (foldl_checkpointKeysLE cfg ext suf applied) htargetApplied
  rw [show E.slot_start cfg (s + 1) = deliveryPred + 1 from hdeliveryEq]
  change a.data.target ∈
    ((E.schedule w (deliveryPred + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      ticked).checkpoint_state_keys
  rw [hscheduleEq, List.foldl_append,
    foldl_cons_attestation cfg ext _ a suf happlied]
  exact htargetEnd

/-- The exact target key persists at every later endpoint. -/
theorem honestVoteTarget_cached
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : NextSlotSynchronyPremises cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : Nat} {index : CommitteeIndex}
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hheadKnown :
      (honest_attestation cfg ext
        (E.store cfg ext v n) s index v).data.beacon_block_root ∈
          (E.store cfg ext v n).block_roots)
    (hheadWalk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext v n) s index v).data.target.epoch)
      (honest_attestation cfg ext
        (E.store cfg ext v n) s index v).data.beacon_block_root)
    {m : Nat} (hdeliveryLe : E.slot_start cfg (s + 1) ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    (honest_attestation cfg ext
      (E.store cfg ext v n) s index v).data.target ∈
        (E.store cfg ext w m).checkpoint_state_keys := by
  have hcached := E.honestVoteTarget_cached_at_delivery cfg ext
    hwf hhb hsyn hec hdiv hgen hv hw hn hHn
    (E.withinHorizon_mono cfg hdeliveryLe hHm)
    hvote hheadKnown hheadWalk
  exact (E.store_checkpointKeysLE cfg ext w hdeliveryLe) hcached

end Execution

end FastConfirmation.Spec

end
