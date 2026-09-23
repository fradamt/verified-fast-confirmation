module
public import FastConfirmationProofs.Handlers.ResetAdoption
public import FastConfirmationProofs.Discount.SelectedCoveredMarginConstruction
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Shared mechanics for actual FCR calls

This module proves two execution facts used by the accepted next-slot proof:

1. a node's realized justified epoch never decreases along its executable
   trajectory; and
2. the descendant selector preserves a carried input's `SafeFrom` property,
   with the strict-edge filter supplier kept as an explicit parameter.

Neither result assumes a reset-safety or head-ancestry conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Realized-justified epoch monotonicity

`StoreLE` deliberately omits the checkpoint fields. The executable handlers
nevertheless make epoch monotonicity true directly: the only
writes to `justified_checkpoint` pass through `update_checkpoints`, which
keeps the larger epoch.  The following private handler facts expose that
small piece of execution semantics and the public trajectory theorem folds
them through one node's schedule.

This argument needs no FFG certificate, synchrony, or accepted-state
assumption. -/

private theorem justified_epoch_le_update_checkpoints
    (store : Store Root) (jc fc : Checkpoint Root) :
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.update_checkpoints store jc fc
        ).justified_checkpoint.epoch := by
  have hfield :
      (FastConfirmation.Spec.update_checkpoints store jc fc
        ).justified_checkpoint =
        if jc.epoch > store.justified_checkpoint.epoch then jc
        else store.justified_checkpoint := by
    simp only [FastConfirmation.Spec.update_checkpoints]
    split_ifs <;> rfl
  rw [hfield]
  split_ifs with hj
  · exact Nat.le_of_lt hj
  · exact Nat.le_refl _

private theorem justified_epoch_le_compute_pulled_up_tip
    (store : Store Root) (r : Root) :
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r
        ).justified_checkpoint.epoch := by
  let state := ext.process_justification_and_finalization
    (store.block_states r)
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update
        store.unrealized_justifications r
          state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hpulledJ : pulled.justified_checkpoint =
      store.justified_checkpoint := by
    simp only [pulled, FastConfirmation.Spec.update_unrealized_checkpoints,
      recorded]
    split_ifs <;> rfl
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

private theorem justified_epoch_le_on_tick_per_slot
    (store : Store Root) (time : ℕ) :
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.on_tick_per_slot cfg store time
        ).justified_checkpoint.epoch := by
  let previousSlot := get_current_slot cfg store
  let timed : Store Root := { store with time := time }
  let currentSlot := get_current_slot cfg timed
  let reset : Store Root :=
    if currentSlot > previousSlot then
      { timed with proposer_boost_root := (default : Root) }
    else timed
  have hresetJ : reset.justified_checkpoint =
      store.justified_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  change store.justified_checkpoint.epoch ≤
    (if currentSlot > previousSlot ∧
        compute_slots_since_epoch_start cfg currentSlot = 0 then
      FastConfirmation.Spec.update_checkpoints reset
        reset.unrealized_justified_checkpoint
          reset.unrealized_finalized_checkpoint
    else reset).justified_checkpoint.epoch
  split_ifs
  · exact (congrArg Checkpoint.epoch hresetJ).symm.le.trans
      (justified_epoch_le_update_checkpoints reset
        reset.unrealized_justified_checkpoint
          reset.unrealized_finalized_checkpoint)
  · exact (congrArg Checkpoint.epoch hresetJ).symm.le

private theorem justified_epoch_le_on_tick_aux
    (tickSlot fuel : ℕ) : ∀ store : Store Root,
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.on_tick_aux cfg tickSlot fuel store
        ).justified_checkpoint.epoch := by
  induction fuel with
  | zero =>
      intro store
      exact Nat.le_refl _
  | succ fuel ih =>
      intro store
      rw [FastConfirmation.Spec.on_tick_aux]
      split_ifs
      · exact (justified_epoch_le_on_tick_per_slot
          (cfg := cfg) store _).trans (ih _)
      · exact Nat.le_refl _

private theorem justified_epoch_le_on_tick
    (store : Store Root) (time : ℕ) :
    store.justified_checkpoint.epoch ≤
      (FastConfirmation.Spec.on_tick cfg store time
        ).justified_checkpoint.epoch := by
  simp only [FastConfirmation.Spec.on_tick]
  exact (justified_epoch_le_on_tick_aux (cfg := cfg) _ _ store).trans
    (justified_epoch_le_on_tick_per_slot (cfg := cfg) _ _)

private theorem update_latest_messages_justified_checkpoint
    (store : Store Root) (indices : List ValidatorIndex)
    (a : Attestation Root) :
    (FastConfirmation.Spec.update_latest_messages store indices a
      ).justified_checkpoint = store.justified_checkpoint := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter
      (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => rfl
  | cons i rest ih =>
      rw [List.foldl_cons]
      exact (ih _).trans (by
        split_ifs <;> rfl)

private theorem store_target_checkpoint_state_justified_checkpoint
    (store : Store Root) (target : Checkpoint Root) :
    (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target
      ).justified_checkpoint = store.justified_checkpoint := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;> rfl

private theorem on_attestation_justified_checkpoint
    {store store' : Store Root} {a : Attestation Root} {fromBlock : Bool}
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a fromBlock =
      some store') :
    store'.justified_checkpoint = store.justified_checkpoint := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact (update_latest_messages_justified_checkpoint _ _ _).trans
    (store_target_checkpoint_state_justified_checkpoint
      (cfg := cfg) (ext := ext) _ _)

private theorem on_attester_slashing_justified_checkpoint
    {store store' : Store Root} {sl : AttesterSlashing Root}
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl =
      some store') :
    store'.justified_checkpoint = store.justified_checkpoint := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  rfl

private theorem justified_epoch_le_on_block
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    store.justified_checkpoint.epoch ≤
      store'.justified_checkpoint.epoch := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [FastConfirmation.Spec.on_block, if_pos hknown] at hh
    cases hh
    exact Nat.le_refl _
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
    cases hst : ext.state_transition
        (store.block_states sb.message.parent_root) sb with
    | none =>
        rw [hst] at hh
        cases hh
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
          have hf := notify_ptc_messages_frame cfg ext hn
          let staged := FastConfirmation.Spec.record_block_timeliness cfg
            notified sb.root
          let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg
            staged (get_head cfg store).root sb.root
          let realized := FastConfirmation.Spec.update_checkpoints boosted
            state.current_justified_checkpoint state.finalized_checkpoint
          have hboostedJ : boosted.justified_checkpoint =
              store.justified_checkpoint := by
            simp only [boosted, staged,
              FastConfirmation.Spec.update_proposer_boost_root,
              FastConfirmation.Spec.record_block_timeliness]
            split_ifs <;> exact hf.justified_checkpoint
          exact (congrArg Checkpoint.epoch hboostedJ.symm).le.trans
            ((justified_epoch_le_update_checkpoints boosted
                state.current_justified_checkpoint
                state.finalized_checkpoint).trans
              (justified_epoch_le_compute_pulled_up_tip
                (cfg := cfg) (ext := ext) realized sb.root))

private theorem justified_epoch_le_apply_event_getD
    (store : Store Root) (event : Event Root) :
    store.justified_checkpoint.epoch ≤
      ((FastConfirmation.Spec.apply_event cfg ext store event).getD store
        ).justified_checkpoint.epoch := by
  cases hevent : FastConfirmation.Spec.apply_event cfg ext store event with
  | none =>
      exact Nat.le_refl _
  | some store' =>
      simp only [hevent, Option.getD_some]
      cases event with
      | block sb =>
          exact justified_epoch_le_on_block (cfg := cfg) (ext := ext)
            (by simpa only [FastConfirmation.Spec.apply_event] using hevent)
      | attestation a fromBlock =>
          exact (congrArg Checkpoint.epoch
            (on_attestation_justified_checkpoint (cfg := cfg) (ext := ext)
              (by simpa only [FastConfirmation.Spec.apply_event]
                using hevent))).symm.le
      | attester_slashing sl =>
          exact (congrArg Checkpoint.epoch
            (on_attester_slashing_justified_checkpoint (ext := ext)
              (by simpa only [FastConfirmation.Spec.apply_event]
                using hevent))).symm.le
      | execution_payload_envelope envelope observation =>
          exact (congrArg Checkpoint.epoch
            (on_execution_payload_envelope_frame ext hevent).justified_checkpoint).symm.le
      | payload_attestation_message message fromBlock =>
          exact (congrArg Checkpoint.epoch
            (on_payload_attestation_message_frame cfg ext hevent).justified_checkpoint).symm.le

private theorem justified_epoch_le_event_fold
    (events : List (Event Root)) (store : Store Root) :
    store.justified_checkpoint.epoch ≤
      (events.foldl (fun st event =>
        (FastConfirmation.Spec.apply_event cfg ext st event).getD st) store
      ).justified_checkpoint.epoch := by
  induction events generalizing store with
  | nil => exact Nat.le_refl _
  | cons event rest ih =>
      rw [List.foldl_cons]
      exact (justified_epoch_le_apply_event_getD
        (cfg := cfg) (ext := ext) store event).trans (ih _)

/-- Within one node's executable trajectory, the realized justified epoch
never decreases. -/
theorem store_justified_epoch_mono
    (w : ValidatorIndex) {q m : ℕ} (hqm : q ≤ m) :
    (E.store cfg ext w q).justified_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  induction m generalizing q with
  | zero =>
      have hq : q = 0 := by omega
      subst q
      exact Nat.le_refl _
  | succ m ih =>
      by_cases hq : q = m + 1
      · subst q
        exact Nat.le_refl _
      · have hqm' : q ≤ m := by omega
        apply (ih hqm').trans
        change (E.store cfg ext w m).justified_checkpoint.epoch ≤
          ((E.schedule w (m + 1)).foldl
            (fun st event =>
              (FastConfirmation.Spec.apply_event cfg ext st event).getD st)
            (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w m)
              (E.time_at (m + 1)))).justified_checkpoint.epoch
        exact (justified_epoch_le_on_tick
            (cfg := cfg) (E.store cfg ext w m)
              (E.time_at (m + 1))).trans
          (justified_epoch_le_event_fold (cfg := cfg) (ext := ext) _ _)

/-! ## The one open strict-helper supplier -/

/-- The only strict selected-result producer left abstract by this facade.

It is demanded only when the actual descendant selector changes its carried
input.  The proposition is the low-level filter-membership interface consumed
by `selectedCoveredMarginSupplyAt_of_filterSupply_minimal`; it does not bundle
a trace pipeline, justification interface, safety conclusion, or helper
proviso under another name. -/
def ActualFCRStrictSelectedFilterSupplierAt
    (v : ValidatorIndex) (n : ℕ)
    (trace : GetLatestConfirmedTrace cfg ext
      (E.fcrStep cfg ext v n)) : Prop :=
  trace.result ≠ trace.afterObserved →
    E.SelectedStrictEdgeFilterSupplyAt cfg ext trace.result
      trace.afterObserved v (n + 1) (E.fcrStep cfg ext v n)

/-! ## Strict helper preservation -/

/-- At a genuine actual FCR call, the exact selector result is safe whenever
its carried input is safe and known.  Only a strict result consumes
`ActualFCRStrictSelectedFilterSupplierAt`; an unchanged result inherits the
input property directly.

The input is stated at `n+1`, which equals the start of the newly entered slot
for an actual advancing call. -/
theorem GetLatestConfirmedTrace.result_safeFrom_of_actualCall_strictSupplier
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (trace : GetLatestConfirmedTrace cfg ext
      (E.fcrStep cfg ext v n))
    (hinputKnown : trace.afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hinputSafe : E.SafeFrom cfg ext trace.afterObserved (n + 1))
    (hsupplier : E.ActualFCRStrictSelectedFilterSupplierAt cfg ext
      v n trace) :
    E.SafeFrom cfg ext trace.result (n + 1) := by
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hHn1 hcall
  have hquery : (E.fcrStep cfg ext v n).store =
      E.store cfg ext v (n + 1) := E.fcrStep_store cfg ext v n
  have hbase : E.SafeFrom cfg ext trace.afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))) := by
    simpa only [hstartEq] using hinputSafe
  rcases trace.selector_cases with ⟨hresult, _hguard⟩ |
      ⟨hresult, _hguard⟩
  · rw [hresult]
    exact hinputSafe
  · rw [hresult]
    apply E.safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal
      cfg ext hA v hv (n + 1) hHn1 (E.fcrStep cfg ext v n)
        hquery trace.afterObserved hinputKnown hbase
    intro hstrict
    have hresultStrict : trace.result ≠ trace.afterObserved := by
      rw [hresult]
      exact hstrict
    have hsupply : E.SelectedStrictEdgeFilterSupplyAt cfg ext trace.result
        trace.afterObserved v (n + 1) (E.fcrStep cfg ext v n) :=
      hsupplier hresultStrict
    rw [hresult] at hsupply
    exact E.selectedCoveredMarginSupplyAt_of_filterSupply_minimal
      cfg ext hA hwalkDomain v hv (n + 1) hHn1
        (E.fcrStep cfg ext v n) hquery trace.afterObserved hinputKnown
        (find_latest_confirmed_descendant cfg ext
          (E.fcrStep cfg ext v n) trace.afterObserved)
        rfl hstrict hsupply

end Execution

end FastConfirmation.Spec

end
