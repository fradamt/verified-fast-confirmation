module
public import FastConfirmationProofs.Safety.ConfirmedCacheSafety
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationInternal.Legacy.Vocabulary

public import FastConfirmationStatements.Claims
@[expose] public section

/-!
# Accepted actual-FCR next-slot safety facade

This module proves following-slot safety for stored FCR outputs without
placing a reset law in the accepted assumption bundle.  Finalized and
active-observed restart safety are both derived from the accepted execution
dynamics.

The property says directly that a stored output at second `n` is canonical at
every in-horizon honest
endpoint whose slot is at least `slot_at n + 1`.

The theorem covers stored outputs at completed execution boundaries. It does
not cover optional calls at arbitrary in-slot action prefixes.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-! The totalized block map has its initial value outside its key list. -/

private def UnknownBlocksDefault (store : Store Root) : Prop :=
  ∀ r, r ∉ store.block_roots → store.blocks r = default

omit [LinearOrder Root] in
private theorem UnknownBlocksDefault.of_eq {s t : Store Root}
    (h : UnknownBlocksDefault s) (hr : t.block_roots = s.block_roots)
    (hb : t.blocks = s.blocks) : UnknownBlocksDefault t := by
  intro r hnot
  rw [hr] at hnot
  rw [hb]
  exact h r hnot

omit [LinearOrder Root] in
private theorem SameBlocks.unknownBlocksDefault {s t : Store Root}
    (hs : SameBlocks s t) (h : UnknownBlocksDefault s) :
    UnknownBlocksDefault t :=
  h.of_eq hs.1.symm hs.2.1.symm

omit [LinearOrder Root] in
private theorem unknownBlocksDefault_foldl {α : Type*}
    {f : Store Root → α → Store Root}
    (hf : ∀ s a, UnknownBlocksDefault s → UnknownBlocksDefault (f s a))
    (l : List α) (s : Store Root) (h : UnknownBlocksDefault s) :
    UnknownBlocksDefault (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact h
  | cons a l ih => exact ih _ (hf s a h)

private theorem on_block_unknownBlocksDefault {s t : Store Root}
    {b : SignedBeaconBlock Root} (h : UnknownBlocksDefault s)
    (hs : on_block cfg ext s b = some t) : UnknownBlocksDefault t := by
  by_cases hknown : b.root ∈ s.block_roots
  · simp [on_block, hknown] at hs
    cases hs
    exact h
  · simp only [on_block, if_neg hknown] at hs
    split_ifs at hs with hp hpayload hslot hfin hfc
    cases hst : ext.state_transition (s.block_states b.message.parent_root) b with
    | none => rw [hst] at hs; cases hs
    | some state =>
      rw [hst] at hs
      let added : Store Root :=
        { s with
          block_roots := s.block_roots ++ [b.root]
          blocks := Function.update s.blocks b.root b.message
          block_states := Function.update s.block_states b.root state
          payload_timeliness_vote := Function.update s.payload_timeliness_vote
            b.root (some (List.replicate cfg.ptc_size none))
          payload_data_availability_vote := Function.update s.payload_data_availability_vote
            b.root (some (List.replicate cfg.ptc_size none)) }
      change (match notify_ptc_messages cfg ext added state b.message.payload_attestations with
        | none => none
        | some notified => some (compute_pulled_up_tip cfg ext
            (update_checkpoints
              (update_proposer_boost_root cfg
                (record_block_timeliness cfg notified b.root)
                (get_head cfg s).root b.root)
              state.current_justified_checkpoint state.finalized_checkpoint) b.root)) =
          some t at hs
      have hadded : UnknownBlocksDefault added := by
        intro r hr
        simp only [added, List.mem_append, List.mem_singleton, not_or] at hr ⊢
        rw [Function.update_of_ne hr.2]
        exact h r hr.1
      cases hn : notify_ptc_messages cfg ext added state b.message.payload_attestations with
      | none => rw [hn] at hs; cases hs
      | some notified =>
        rw [hn] at hs
        cases hs
        refine (compute_pulled_up_tip_sameBlocks cfg ext _ _).unknownBlocksDefault ?_
        refine (update_checkpoints_sameBlocks _ _ _).unknownBlocksDefault ?_
        refine (update_proposer_boost_root_sameBlocks cfg _ _ _).unknownBlocksDefault ?_
        refine (record_block_timeliness_sameBlocks cfg _ _).unknownBlocksDefault ?_
        exact (notify_ptc_messages_sameBlocks cfg ext hn).unknownBlocksDefault hadded

private theorem on_tick_unknownBlocksDefault (s : Store Root) (time : ℕ)
    (h : UnknownBlocksDefault s) :
    UnknownBlocksDefault (on_tick cfg s time) :=
  (on_tick_sameBlocks cfg s time).unknownBlocksDefault h

private theorem apply_event_unknownBlocksDefault (s : Store Root) (event : Event Root)
    (h : UnknownBlocksDefault s) :
    UnknownBlocksDefault ((apply_event cfg ext s event).getD s) := by
  cases event with
  | block b =>
    simp only [apply_event]
    cases he : on_block cfg ext s b with
    | none => exact h
    | some t => exact on_block_unknownBlocksDefault cfg ext h he
  | attestation a fromBlock =>
    simp only [apply_event]
    cases he : on_attestation cfg ext s a fromBlock with
    | none => exact h
    | some t => exact (on_attestation_sameBlocks cfg ext he).unknownBlocksDefault h
  | attester_slashing sl =>
    simp only [apply_event]
    cases he : on_attester_slashing ext s sl with
    | none => exact h
    | some t => exact (on_attester_slashing_sameBlocks ext he).unknownBlocksDefault h
  | execution_payload_envelope envelope observation =>
    simp only [apply_event]
    cases he : on_execution_payload_envelope ext s envelope observation with
    | none => exact h
    | some t => exact (on_execution_payload_envelope_frame ext he).sameBlocks.unknownBlocksDefault h
  | payload_attestation_message message fromBlock =>
    simp only [apply_event]
    cases he : on_payload_attestation_message cfg ext s message fromBlock with
    | none => exact h
    | some t =>
      exact (on_payload_attestation_message_frame cfg ext he).sameBlocks.unknownBlocksDefault h

private theorem get_forkchoice_store_unknownBlocksDefault
    (state : BeaconState Root) (block : SignedBeaconBlock Root) :
    UnknownBlocksDefault (get_forkchoice_store cfg state block) := by
  intro r hr
  simp only [get_forkchoice_store, List.mem_singleton] at hr ⊢
  simp [hr]

private theorem Execution.unknownBlocksDefault_store (E : Execution Root)
    (hgen : ∃ state block, E.genesis_store = get_forkchoice_store cfg state block)
    (v : ValidatorIndex) (n : ℕ) :
    UnknownBlocksDefault (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨state, block, hgen⟩ := hgen
    change UnknownBlocksDefault E.genesis_store
    rw [hgen]
    exact get_forkchoice_store_unknownBlocksDefault cfg state block
  | succ n ih =>
    exact unknownBlocksDefault_foldl (apply_event_unknownBlocksDefault cfg ext) _ _
      (on_tick_unknownBlocksDefault cfg _ _ ih)

private theorem get_ancestor_aux_default_root
    (s : Store Root) (p : Root) (hp : s.blocks p = default)
    (slot fuel : ℕ) (status : PayloadStatus) :
    (get_ancestor_aux s slot fuel (ForkChoiceNode.mk p status)).root = p := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hzero : (default : BeaconBlock Root).slot = 0 := rfl
    simp [get_ancestor_aux, hp, hzero]

/-- A walk from a known root can leave the key list only at the anchor's
dangling parent. The default block stops the walk there. -/
theorem ancestor_root_known_or_anchor_parent
    (s : Store Root) (anchor parent : Root)
    (hparents : NonAnchorParentKnown anchor s)
    (hanchor : (s.blocks anchor).parent_root = parent)
    (hdefault : s.blocks parent = default)
    {node : ForkChoiceNode Root} (hnode : node.root ∈ s.block_roots)
    (slot : Slot) :
    (get_ancestor s node slot).root ∈ s.block_roots ∨
      (get_ancestor s node slot).root = parent := by
  have aux : ∀ fuel (node : ForkChoiceNode Root), node.root ∈ s.block_roots →
      (get_ancestor_aux s slot fuel node).root ∈ s.block_roots ∨
        (get_ancestor_aux s slot fuel node).root = parent := by
    intro fuel
    induction fuel with
    | zero =>
      intro node hn
      exact Or.inl hn
    | succ fuel ih =>
      intro node hn
      by_cases hstep : slot < (s.blocks node.root).slot
      · simp only [get_ancestor_aux, if_pos hstep]
        by_cases ha : node.root = anchor
        · have hp : (s.blocks node.root).parent_root = parent := by
            rw [ha, hanchor]
          rw [hp, get_ancestor_aux_default_root s parent hdefault slot fuel]
          exact Or.inr rfl
        · exact ih _ ((hparents node.root hn).resolve_left ha)
      · simp only [get_ancestor_aux, if_neg hstep]
        exact Or.inl hn
  exact aux _ node hnode


namespace Execution

variable (E : Execution Root)

namespace NextSlotSafetyPremises

/-- Bundle-facing following-slot invariant. -/
theorem confirmed_safeFromFollowingSlot
    (h : E.NextSlotSafetyPremises cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    E.ConfirmedSafeFromFollowingSlot cfg ext v n := by
  exact E.confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold
    cfg ext h.ffg_interpretation h.trajectory h.completed_calls h.epoch_ends_fit
      h.anchor_eq h.anchor_boundary h.finalization_delay
      h.slots_per_epoch_gt_one h.checkpoint_inclusion h.checkpoint_projection
      h.exact_link_validity hv n hHn

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1400000 in
-- The dependent dispatcher elaborates all executable input/reset origins here.
/-- Reset-free form of the mandatory descendant-helper guarantee.

At an actual boundary call, the preceding cached root is already safe at the
call boundary by the following-slot invariant.  A selector-eligible finalized
reset is forced to the trusted anchor by causal finalization lag, and an
observed reset is safe by the accepted dynamic checkpoint theorem.  The
accepted dispatcher then proves the literal helper return safe, including the
case where the helper runs but returns its input unchanged. -/
theorem selected_result_safe_from_next_slot_of_scheduled_call
    (h : E.NextSlotSafetyPremises cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hselector : getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext (E.fcrStoreAtCall cfg ext v n)
        (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
      (n + 1) := by
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hselectorTrace : getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
      trace.afterObserved := by
    simpa only [trace] using hselector
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hpaths := E.honestHeadPathAdmissibility_of_accepted cfg ext
    h.ffg_interpretation h.trajectory h.completed_calls h.anchor_eq h.anchor_boundary
    h.slots_per_epoch_gt_one h.finalization_delay h.checkpoint_projection h.exact_link_validity
  have hdomain : SelectedMarginDomain cfg ext E :=
    E.selectedMarginDomain_of_acceptedGlobalTrajectory
      cfg ext h.ffg_interpretation h.trajectory h.completed_calls.synchrony hpaths
        h.anchor_eq h.anchor_boundary
  have hanchorExact : h.ffg_interpretation.anchor =
      h.ffg_interpretation.state.checkpoint_at_epoch h.ffg_interpretation.anchor.root h.ffg_interpretation.anchor.epoch :=
    acceptedAnchorExact_of_trajectory cfg ext E h.ffg_interpretation h.trajectory
      h.anchor_eq h.anchor_boundary
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := h.trajectory.genesis_structure
      wellFormed := h.trajectory.wellFormed
      whole_seconds := h.trajectory.whole_seconds
      honest_behavior := h.trajectory.honest_behavior
      synchrony := h.completed_calls.synchrony
      externals_coherence := h.trajectory.externals_coherence
      static_validators := h.completed_calls.static_validators
      byzantine_bound := h.completed_calls.byzantine_bound
      domain := hdomain }
  have hpreviousDeadline : E.followingSlotStart cfg n = n + 1 :=
    E.followingSlotStart_eq_succ_of_call
      cfg ext h.trajectory hMargin hHn1 hcall
  have hsafePreviousAtCall : E.SafeFrom cfg ext
      (E.confirmed cfg ext v n) (n + 1) := by
    have hsafePrevious :=
      h.confirmed_safeFromFollowingSlot cfg ext E hv hHn
    simpa only [ConfirmedSafeFromFollowingSlot, hpreviousDeadline] using
      hsafePrevious
  have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
  have hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots :=
    E.confirmed_known_of_acceptedGlobalTrajectory
      cfg ext h.ffg_interpretation h.trajectory h.anchor_eq h.anchor_boundary hv n hHn
  have hinputKnown : trace.afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
    simpa only [trace] using
      E.getLatestConfirmedTraceAt_input_known
        cfg ext h.ffg_interpretation h.trajectory h.anchor_eq h.anchor_boundary hknownN
  have hbranch : CandidateHistoryCallBranch cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace := by
    simpa only [trace] using hrec.branch
  have hinputSafe : E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
    cases hbranch with
    | carriedUnchanged hinput _ =>
        rw [hinput.input_eq, E.fcrStep_confirmed_root]
        exact hsafePreviousAtCall
    | finalizedResetUnchanged hinput _ =>
        exact E.finalizedResetCandidateInput_safeFrom_anchor_of_recent
          cfg ext h.ffg_interpretation h.trajectory h.anchor_eq h.anchor_boundary
            h.finalization_delay hinput hselectorTrace
    | observedResetUnchanged hinput _ =>
        exact
          Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
            (E := E) cfg ext h.ffg_interpretation h.trajectory
              h.completed_calls.synchrony hpaths h.completed_calls.static_validators
                h.completed_calls.byzantine_bound h.anchor_eq h.anchor_boundary
                  h.slots_per_epoch_gt_one h.finalization_delay
                    h.checkpoint_projection h.exact_link_validity hv hHn1 hcall hinput
    | strictSelected horigin _ =>
        cases horigin with
        | carried hinput =>
            rw [hinput.input_eq, E.fcrStep_confirmed_root]
            exact hsafePreviousAtCall
        | finalizedReset hinput =>
            exact E.finalizedResetCandidateInput_safeFrom_anchor_of_recent
              cfg ext h.ffg_interpretation h.trajectory h.anchor_eq h.anchor_boundary
                h.finalization_delay hinput hselectorTrace
        | observedReset hinput =>
            exact
              Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics
                (E := E) cfg ext h.ffg_interpretation h.trajectory
                  h.completed_calls.synchrony hpaths
                    h.completed_calls.static_validators
                      h.completed_calls.byzantine_bound h.anchor_eq
                        h.anchor_boundary h.slots_per_epoch_gt_one
                          h.finalization_delay h.checkpoint_projection
                            h.exact_link_validity hv hHn1
                          hcall hinput
  have hresultSafe : E.SafeFrom cfg ext trace.result (n + 1) := by
    simpa only [trace] using
      E.getLatestConfirmedTraceAt_result_safeFrom_of_acceptedDispatcher
        cfg ext h.ffg_interpretation h.trajectory h.completed_calls h.epoch_ends_fit
          hdomain h.anchor_eq h.anchor_boundary h.finalization_delay
            h.slots_per_epoch_gt_one h.checkpoint_inclusion h.checkpoint_projection
              h.exact_link_validity hanchorExact hv hHn1 hcall
              ((E.confirmed_safety_and_lineage_of_acceptedActualFCRFold
                cfg ext h.ffg_interpretation h.trajectory h.completed_calls h.epoch_ends_fit
                h.anchor_eq h.anchor_boundary h.finalization_delay h.slots_per_epoch_gt_one
                h.checkpoint_inclusion h.checkpoint_projection h.exact_link_validity hv n hHn).2)
              hinputKnown hinputSafe
  have hselected : trace.result =
      find_latest_confirmed_descendant cfg ext (E.fcrStoreAtCall cfg ext v n)
        trace.afterObserved :=
    trace.selected_facts cfg ext hselectorTrace
  rw [hselected] at hresultSafe
  simpa only [trace] using hresultSafe

/-- Bundle-facing endpoint form with the literal next-slot timing premise. -/
theorem confirmed_head_nextSlot
    (h : E.NextSlotSafetyPremises cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.confirmed cfg ext v n)) = true := by
  exact E.confirmed_head_of_acceptedActualFCRFold_nextSlot
    cfg ext h.ffg_interpretation h.trajectory h.completed_calls h.epoch_ends_fit
      h.anchor_eq h.anchor_boundary h.finalization_delay
      h.slots_per_epoch_gt_one h.checkpoint_inclusion h.checkpoint_projection
      h.exact_link_validity hv hw hnm hnext hHm

end NextSlotSafetyPremises

end Execution

/-- Stored-output safety theorem at the following-slot deadline. The observer
has the root in its block store, and its head descends from that root. -/
theorem confirmed_root_safe_from_next_slot :
    ConfirmedRootSafeFromNextSlot cfg ext := by
  intro E h v hv n w hw m hnm hnext hHm
  have hanc := h.confirmed_head_nextSlot cfg ext E hv hw hnm hnext hHm
  have hHn : E.WithinHorizon cfg n := E.withinHorizon_mono cfg hnm hHm
  have hknownV := E.confirmed_known_of_acceptedGlobalTrajectory
    cfg ext h.ffg_interpretation h.trajectory h.anchor_eq h.anchor_boundary hv n hHn
  have hconfirmedRoot : E.ExecutionRoot (E.confirmed cfg ext v n) :=
    ⟨(E.store cfg ext v n).blocks (E.confirmed cfg ext v n),
      E.blockAt_of_store_known cfg ext hknownV⟩
  obtain ⟨ast, ablk, hgen, _hslot, hparent⟩ := h.trajectory.genesis_structure
  have hpaths := E.honestHeadPathAdmissibility_of_accepted cfg ext
    h.ffg_interpretation h.trajectory h.completed_calls h.anchor_eq h.anchor_boundary
    h.slots_per_epoch_gt_one h.finalization_delay h.checkpoint_projection h.exact_link_validity
  have hdomain : SelectedMarginDomain cfg ext E :=
    E.selectedMarginDomain_of_acceptedGlobalTrajectory
      cfg ext h.ffg_interpretation h.trajectory h.completed_calls.synchrony hpaths
        h.anchor_eq h.anchor_boundary
  have hhead : (get_head cfg (E.store cfg ext w m)).root ∈
      (E.store cfg ext w m).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hdomain hw m hHm
  have hanchor0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgen]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorM : ablk.root ∈ (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchor0
  have hanchorBlock := E.store_anchor_block cfg ext h.trajectory.wellFormed
    hgen w m hanchorM
  have hanchorParent :
      ((E.store cfg ext w m).blocks ablk.root).parent_root =
        ablk.message.parent_root := by rw [hanchorBlock]
  have hPnot := E.store_dangling_parent_unknown cfg ext
    h.trajectory.wellFormed hgen hparent w m
  have hdefaultP : (E.store cfg ext w m).blocks ablk.message.parent_root = default :=
    (E.unknownBlocksDefault_store cfg ext ⟨ast, ablk, hgen⟩ w m)
      ablk.message.parent_root hPnot
  have hwalk := ancestor_root_known_or_anchor_parent
    (E.store cfg ext w m) ablk.root ablk.message.parent_root
    (E.store_nonAnchorParentKnown cfg ext hgen w m)
    hanchorParent hdefaultP hhead
    ((E.store cfg ext w m).blocks (E.confirmed cfg ext v n)).slot
  have heq : (get_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      ((E.store cfg ext w m).blocks (E.confirmed cfg ext v n)).slot).root =
      E.confirmed cfg ext v n := by
    simpa only [is_ancestor_get_node_for_root, decide_eq_true_eq] using hanc
  rw [heq] at hwalk
  rcases hwalk with hmember | hparentEq
  · exact ⟨hmember, hanc⟩
  · have hparentRoot : E.ExecutionRoot ablk.message.parent_root := by
      rw [← hparentEq]
      exact hconfirmedRoot
    exact False.elim ((E.anchorParent_not_executionRoot_for_storeReflection
      cfg h.trajectory.wellFormed hgen hparent) hparentRoot)

end FastConfirmation.Spec

end
