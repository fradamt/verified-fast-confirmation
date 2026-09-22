import FastConfirmation.Spec.Proof.CurrentTargetPrefixAccounting

/-!
# Current-target vote realization at an exact scheduled prefix

The completed-boundary current-target bridge cannot be applied directly to a
strict in-second query store.  This module supplies the two exact-prefix facts
needed by the accepted gate path:

* strengthened schedule provenance retains the target epoch of the actual
  attestation which installed each latest message; and
* an observed honest current-target supporter in any exact scheduled prefix
  realizes a canonical ground vote for that prefix store's exact target before
  the next epoch boundary.

The target root is compared between the voter's boundary store and the query
prefix through one preselected `ExactPrefixAcceptedFFGSemantics`.  No block-set
inclusion between those stores, target agreement across validators, quorum,
source agreement, ancestry segment, or safety conclusion is assumed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Strengthened latest-message provenance at exact prefixes -/

omit [LinearOrder Root] [Inhabited Root] in
private theorem prefixCurrentTargetProvenance_of_latest_eq
    {E : Execution Root} {store store' : Store Root}
    (h : CurrentTargetScheduledLatestMessageProvenance cfg E store)
    (hlm : store'.latest_messages = store.latest_messages) :
    CurrentTargetScheduledLatestMessageProvenance cfg E store' := by
  intro i m hm
  rw [hlm] at hm
  exact h i m hm

omit [Inhabited Root] in
private theorem prefixCurrentTargetProvenance_on_attestation
    {E : Execution Root} {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool}
    (hsched : ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : CurrentTargetScheduledLatestMessageProvenance cfg E store)
    (hh : on_attestation cfg ext store a ifb = some store') :
    CurrentTargetScheduledLatestMessageProvenance cfg E store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  simp only [validate_on_attestation, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨_, hEpoch⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hv
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with
    hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact h i m hold
  · obtain ⟨u, t, hmem⟩ := hsched
    refine ⟨a, u, t, ifb, hmem, hi, ?_, ?_, ?_⟩
    · rw [hmeq]
    · rw [hmeq]
    · rw [hmeq]
      exact hEpoch.symm

private theorem prefixCurrentTargetProvenance_apply_event
    {E : Execution Root} {store store' : Store Root} {e : Event Root}
    (hsched : ∀ a ifb, e = Event.attestation a ifb →
      ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : CurrentTargetScheduledLatestMessageProvenance cfg E store)
    (he : apply_event cfg ext store e = some store') :
    CurrentTargetScheduledLatestMessageProvenance cfg E store' := by
  cases e with
  | block b =>
      simp only [apply_event] at he
      exact prefixCurrentTargetProvenance_of_latest_eq cfg h
        (on_block_latest cfg ext he)
  | attestation a ifb =>
      simp only [apply_event] at he
      exact prefixCurrentTargetProvenance_on_attestation cfg ext
        (hsched a ifb rfl) h he
  | attester_slashing asl =>
      simp only [apply_event] at he
      exact prefixCurrentTargetProvenance_of_latest_eq cfg h
        (on_attester_slashing_latest ext he)

private theorem prefixCurrentTargetProvenance_foldl
    {E : Execution Root} :
    ∀ (l : List (Event Root)) (store : Store Root),
      (∀ a ifb, Event.attestation a ifb ∈ l →
        ∃ u t, Event.attestation a ifb ∈ E.schedule u t) →
      CurrentTargetScheduledLatestMessageProvenance cfg E store →
      CurrentTargetScheduledLatestMessageProvenance cfg E
        (l.foldl
          (fun st event => (apply_event cfg ext st event).getD st) store) := by
  intro l
  induction l with
  | nil => intro store _ h; exact h
  | cons e rest ih =>
      intro store hl h
      rw [List.foldl_cons]
      have hesched : ∀ a ifb, e = Event.attestation a ifb →
          ∃ u t, Event.attestation a ifb ∈ E.schedule u t :=
        fun a ifb he => hl a ifb (by rw [← he]; exact List.mem_cons_self)
      cases he : apply_event cfg ext store e with
      | none =>
          simp only [Option.getD_none]
          exact ih store
            (fun a ifb ha => hl a ifb (List.mem_cons_of_mem e ha)) h
      | some store' =>
          simp only [Option.getD_some]
          exact ih store'
            (fun a ifb ha => hl a ifb (List.mem_cons_of_mem e ha))
            (prefixCurrentTargetProvenance_apply_event cfg ext hesched h he)

namespace Execution

variable (E : Execution Root)

/-- The exact lower facts used to turn one observed prefix supporter into a
ground vote.  The trajectory component contains only genesis, handler
well-formedness, whole-second timing, honest behavior, and external
coherence.  The separate root-knownness field is used solely for the
totalized `get_head` justified-root fallback in the voter's own boundary
store.  There is no synchrony, economic bound, selected-margin domain,
target agreement, or safety field. -/
structure CurrentTargetPrefixVoteAssumptions : Prop where
  trajectory : E.ScheduledPrefixTrajectoryAssumptions cfg ext
  justified_root_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
      (E.store cfg ext w m).justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots

/-- Project the narrow vote-realization interface from the existing selected
bundle and explicit committed-anchor evidence. Final action producers may
instead construct the narrow interface
directly from accepted trajectory facts; no legacy justification-interface
field is built into its definition. -/
def CurrentTargetPrefixVoteAssumptions.of_selectedMarginAssumptions
    (hA : SelectedMarginAssumptions cfg ext E)
    (hgen : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root) :
    E.CurrentTargetPrefixVoteAssumptions cfg ext where
  trajectory :=
    ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions
      cfg ext E hA hgen
  justified_root_known := hA.domain.justified_root_known

/-- Every exact scheduled-event prefix retains the target epoch of the actual
scheduled attestation which installed each current latest message. -/
theorem ScheduledEventPrefix.currentTargetScheduledLatestMessageProvenance
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (p : E.ScheduledEventPrefix) :
    CurrentTargetScheduledLatestMessageProvenance cfg E
      (p.store cfg ext) := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  rw [ScheduledEventPrefix.store]
  refine prefixCurrentTargetProvenance_foldl cfg ext _ _ ?_ ?_
  · intro a ifb hmem
    exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hmem⟩
  · exact prefixCurrentTargetProvenance_of_latest_eq cfg
      (E.currentTargetScheduledLatestMessageProvenance cfg ext
        ⟨anchorState, anchorBlock, hgen⟩ p.node p.previousSecond)
      (on_tick_latest cfg (E.store cfg ext p.node p.previousSecond)
        (E.time_at (p.previousSecond + 1)))

omit [LinearOrder Root] [Inhabited Root] in
private theorem slot_lt_prefix_next_epoch_start {s : Slot} {e : Epoch}
    (hepoch : compute_epoch_at_slot cfg s = e) :
    s < compute_start_slot_at_epoch cfg (e + 1) := by
  rw [← hepoch]
  simp only [compute_start_slot_at_epoch, compute_epoch_at_slot]
  simpa only [Nat.mul_comm] using
    (Nat.lt_mul_div_succ (b := cfg.slots_per_epoch) s
      cfg.slots_per_epoch_pos)

/-! ## Observed supporter realization in the exact query store -/

/-- An observed honest contributor at any exact scheduled prefix is an actual
canonical ground vote for that prefix store's exact current target before the
next epoch boundary.

The prefix node itself need not be honest.  `hqH` bounds the exact query
second, while `B.coherence.checkpoint_of_known` identifies the checkpoint
projection of the same accepted LMD/head root in the voter's causal boundary
store and the query prefix. -/
theorem currentTargetObservedHonestSupporter_vote_of_prefix
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hV : E.CurrentTargetPrefixVoteAssumptions cfg ext)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    (p : E.ScheduledEventPrefix)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    {state : BeaconState Root} {i : ValidatorIndex}
    (hiObserved : i ∈ E.currentTargetObservedHonestSupporters cfg
      (p.store cfg ext) state) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (p.store cfg ext)).epoch + 1))
      (get_current_target cfg (p.store cfg ext))) := by
  obtain ⟨hdiv, hwf, hec, hhb, hgen⟩ := hV.trajectory
  obtain ⟨ast, ablk, hgeq, hgenSlot, _hcommit, _hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  simp only [Execution.currentTargetObservedHonestSupporters,
    List.mem_toFinset, List.mem_filter] at hiObserved
  have hi : i ∈ E.honest := (decide_eq_true_eq).mp hiObserved.2
  obtain ⟨_active, _unslashed, lm, hlm, _hnequiv, htarget⟩ :=
    mem_CurrentTargetSupporters cfg hiObserved.1
  have htargetEpoch :
      (get_current_target cfg (p.store cfg ext)).epoch = lm.epoch := by
    have h := congrArg Checkpoint.epoch htarget
    simpa only [get_checkpoint_for_block] using h
  obtain ⟨a, u, t, ifb, hsched, hiAttests, haTargetEpoch,
      haRoot, haSlotEpoch⟩ :=
    p.currentTargetScheduledLatestMessageProvenance cfg ext E
      hV.trajectory i lm hlm
  obtain ⟨kGround, aGround, hvoteGround, hdataGround⟩ :=
    hhb.no_forgery u t a ifb hsched i hi hiAttests
  have hiCommittee : i ∈ E.committee a.data.slot :=
    hhb.votes_assigned i hi a.data.slot
      (by rw [hvoteGround]; exact Option.some_ne_none _)
  have hprov := p.latestMessageProvenance cfg ext E hV.trajectory
  obtain ⟨ap, _hapAttests, _hapTargetEpoch, _hapRoot, hapSlotEpoch,
      hapApplied, hapCommittee, hlmKnown, _hlmSlot⟩ :=
    hprov i lm hlm
  have haSlotEq : a.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a.data.slot ap.data.slot
      hiCommittee hapCommittee (haSlotEpoch.trans hapSlotEpoch.symm)
  have haApplied : a.data.slot + 1 ≤
      E.slot_at cfg (p.previousSecond + 1) := by
    rw [haSlotEq, ← p.current_slot cfg ext]
    exact hapApplied
  have haSlotH : E.SlotWithinHorizon cfg a.data.slot :=
    E.slotWithinHorizon_of_le cfg
      (le_trans (Nat.le_succ _) haApplied) hqH
  have hslot0 : E.slot_at cfg 0 = ast.slot := by
    have hcur := E.store_current_slot cfg ext p.node 0
    rw [show E.store cfg ext p.node 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at hcur
    exact hcur.symm
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg (get_current_epoch cfg ast) := by
    simpa only [TrustedAnchorBoundaryAligned, hgeq,
      get_forkchoice_store, Function.update_self] using hboundary
  have hqueryEpoch : compute_epoch_at_slot cfg
      (E.slot_at cfg (p.previousSecond + 1)) = lm.epoch := by
    calc
      compute_epoch_at_slot cfg (E.slot_at cfg (p.previousSecond + 1)) =
          get_current_store_epoch cfg (p.store cfg ext) := by
        simp only [get_current_store_epoch]
        rw [p.current_slot cfg ext]
      _ = (get_current_target cfg (p.store cfg ext)).epoch := rfl
      _ = lm.epoch := htargetEpoch
  have hanchorEpochLe : get_current_epoch cfg ast ≤ lm.epoch := by
    calc
      get_current_epoch cfg ast =
          compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
        simp only [get_current_epoch, hslot0]
      _ ≤ compute_epoch_at_slot cfg
          (E.slot_at cfg (p.previousSecond + 1)) :=
        Nat.div_le_div_right
          (E.slot_at_mono cfg (Nat.zero_le (p.previousSecond + 1)))
      _ = lm.epoch := hqueryEpoch
  have hstartMono : compute_start_slot_at_epoch cfg
      (get_current_epoch cfg ast) ≤
      compute_start_slot_at_epoch cfg lm.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hstartVote : compute_start_slot_at_epoch cfg lm.epoch ≤
      a.data.slot := by
    have h := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
    have hdivEpoch : a.data.slot / cfg.slots_per_epoch = lm.epoch := by
      simpa only [compute_epoch_at_slot] using haSlotEpoch
    rw [hdivEpoch] at h
    exact h
  have hfrom0 : E.slot_at cfg 0 ≤ a.data.slot := by
    calc
      E.slot_at cfg 0 = ast.slot := hslot0
      _ = ablk.message.slot := hgenSlot
      _ ≤ compute_start_slot_at_epoch cfg (get_current_epoch cfg ast) :=
        hboundary'
      _ ≤ compute_start_slot_at_epoch cfg lm.epoch := hstartMono
      _ ≤ a.data.slot := hstartVote
  obtain ⟨k, index, hkH, hkSlot, hvote⟩ :=
    hhb.votes_head i hi a.data.slot hiCommittee haSlotH hfrom0
  rw [hvote] at hvoteGround
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteGround
  obtain ⟨_, hcanonical⟩ := hvoteGround
  have hdata : a.data =
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data :=
    hdataGround.trans
      (congrArg (fun x : Attestation Root => x.data) hcanonical.symm)
  have hheadKnown : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext i k).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i k) with h | h
    · exact h
    · rw [h]
      exact hV.justified_root_known i hi k hkH
  have hheadRoot :
      (get_head cfg (E.store cfg ext i k)).root = lm.root := by
    calc
      (get_head cfg (E.store cfg ext i k)).root =
          (honest_attestation cfg ext (E.store cfg ext i k)
            a.data.slot index i).data.beacon_block_root := by
        symm
        exact honest_attestation_data_beacon_block_root cfg ext
          (E.store cfg ext i k) a.data.slot index
      _ = a.data.beacon_block_root :=
        (congrArg (fun d : AttestationData Root => d.beacon_block_root)
          hdata).symm
      _ = lm.root := haRoot
  have hcanonicalEpoch :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target.epoch = lm.epoch :=
    (congrArg (fun d : AttestationData Root => d.target.epoch) hdata).symm.trans
      haTargetEpoch
  have hgroundProjection := B.coherence.checkpoint_of_known
    (E.store_causal cfg ext i k)
    (get_head cfg (E.store cfg ext i k)).root hheadKnown
    (honest_attestation cfg ext (E.store cfg ext i k)
      a.data.slot index i).data.target.epoch
  have hqueryProjection := B.coherence.checkpoint_of_known
    (Execution.CausalStore.scheduledPrefix p) lm.root hlmKnown lm.epoch
  have hcanonicalRoot :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target.root =
        (get_current_target cfg (p.store cfg ext)).root := by
    calc
      (honest_attestation cfg ext (E.store cfg ext i k)
          a.data.slot index i).data.target.root =
          get_checkpoint_block cfg (E.store cfg ext i k)
            (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch :=
        honest_attestation_data_target_root cfg ext
          (E.store cfg ext i k) a.data.slot index
      _ = (get_checkpoint_for_block cfg (E.store cfg ext i k)
            (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch).root := rfl
      _ = (B.state.C (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch).root :=
        (congrArg Checkpoint.root hgroundProjection).symm
      _ = (B.state.C lm.root lm.epoch).root := by
        rw [hheadRoot, hcanonicalEpoch]
      _ = (get_checkpoint_for_block cfg (p.store cfg ext)
            lm.root lm.epoch).root :=
        congrArg Checkpoint.root hqueryProjection
      _ = (get_current_target cfg (p.store cfg ext)).root :=
        congrArg Checkpoint.root htarget.symm
  have htargetExact :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target =
        get_current_target cfg (p.store cfg ext) := by
    have hepoch := hcanonicalEpoch.trans htargetEpoch.symm
    generalize hc : (honest_attestation cfg ext (E.store cfg ext i k)
      a.data.slot index i).data.target = c at hepoch hcanonicalRoot ⊢
    generalize ht : get_current_target cfg (p.store cfg ext) = target
      at hepoch hcanonicalRoot ⊢
    cases c
    cases target
    simp only at hepoch hcanonicalRoot ⊢
    subst_vars
    rfl
  refine ⟨⟨a.data.slot, k, index, hi, hkH, hkSlot, haSlotH,
    hiCommittee, hvote, haSlotEpoch.trans htargetEpoch.symm, ?_,
    htargetExact⟩⟩
  exact slot_lt_prefix_next_epoch_start cfg
    (haSlotEpoch.trans htargetEpoch.symm)

/-- Convenience specialization for callers which already carry the selected
lower-assumption bundle and committed-anchor evidence. The proof uses the
fields documented by `CurrentTargetPrefixVoteAssumptions`. -/
theorem currentTargetObservedHonestSupporter_vote_of_prefix_of_selected
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hgen : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    (p : E.ScheduledEventPrefix)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    {state : BeaconState Root} {i : ValidatorIndex}
    (hiObserved : i ∈ E.currentTargetObservedHonestSupporters cfg
      (p.store cfg ext) state) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (p.store cfg ext)).epoch + 1))
      (get_current_target cfg (p.store cfg ext))) :=
  E.currentTargetObservedHonestSupporter_vote_of_prefix cfg ext B
    (CurrentTargetPrefixVoteAssumptions.of_selectedMarginAssumptions
      cfg ext E hA hgen) hboundary p hqH hiObserved

end Execution

end FastConfirmation.Spec
