module
public import FastConfirmationProofs.Execution.Calls.CurrentTargetPrefixVoteRealization
public import FastConfirmationProofs.Execution.Calls.TrustedScheduledPrefixGeometry
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

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

The prefix node is honest. `hqH` bounds the exact query
second, while `B.coherence.checkpoint_of_known` identifies the checkpoint
projection of the same accepted LMD/head root in the voter's causal boundary
store and the query prefix. -/
theorem trusted_currentTargetObservedHonestSupporter_vote_of_prefix_of_provenance
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hV : E.CurrentTargetPrefixVoteAssumptions cfg ext)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    (p : E.ScheduledEventPrefix)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (p.store cfg ext)) (p.store cfg ext))
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
      (get_current_target cfg (p.store cfg ext)).epoch = (get_latest_message_epoch cfg lm) := by
    have h := congrArg Checkpoint.epoch htarget
    simpa only [get_checkpoint_for_block] using h
  obtain ⟨a, u, t, ifb, hsched, hiAttests, haTargetEpoch,
      haRoot, haSlotEpoch⟩ :=
    p.currentTargetScheduledLatestMessageProvenance cfg ext E
      hV.trajectory i lm hlm
  obtain ⟨kGround, aGround, _hcausal, hvoteGround, hdataGround⟩ :=
    hhb.no_forgery u t a ifb hsched i hi hiAttests
  have hiCommittee : i ∈ E.committee a.data.slot :=
    hhb.votes_assigned i hi a.data.slot
      (by rw [hvoteGround]; exact Option.some_ne_none _)
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
      (E.slot_at cfg (p.previousSecond + 1)) = (get_latest_message_epoch cfg lm) := by
    calc
      compute_epoch_at_slot cfg (E.slot_at cfg (p.previousSecond + 1)) =
          get_current_store_epoch cfg (p.store cfg ext) := by
        simp only [get_current_store_epoch]
        rw [p.current_slot cfg ext]
      _ = (get_current_target cfg (p.store cfg ext)).epoch := rfl
      _ = (get_latest_message_epoch cfg lm) := htargetEpoch
  have hanchorEpochLe : get_current_epoch cfg ast ≤ (get_latest_message_epoch cfg lm) := by
    calc
      get_current_epoch cfg ast =
          compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
        simp only [get_current_epoch, hslot0]
      _ ≤ compute_epoch_at_slot cfg
          (E.slot_at cfg (p.previousSecond + 1)) :=
        Nat.div_le_div_right
          (E.slot_at_mono cfg (Nat.zero_le (p.previousSecond + 1)))
      _ = (get_latest_message_epoch cfg lm) := hqueryEpoch
  have hstartMono : compute_start_slot_at_epoch cfg
      (get_current_epoch cfg ast) ≤
      compute_start_slot_at_epoch cfg (get_latest_message_epoch cfg lm) :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hstartVote : compute_start_slot_at_epoch cfg (get_latest_message_epoch cfg lm) ≤
      a.data.slot := by
    have h := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
    have hdivEpoch : a.data.slot / cfg.slots_per_epoch = (get_latest_message_epoch cfg lm) := by
      simpa only [compute_epoch_at_slot] using haSlotEpoch
    rw [hdivEpoch] at h
    exact h
  have hfrom0 : E.slot_at cfg 0 ≤ a.data.slot := by
    calc
      E.slot_at cfg 0 = ast.slot := hslot0
      _ = ablk.message.slot := hgenSlot
      _ ≤ compute_start_slot_at_epoch cfg (get_current_epoch cfg ast) :=
        hboundary'
      _ ≤ compute_start_slot_at_epoch cfg (get_latest_message_epoch cfg lm) := hstartMono
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
        a.data.slot index i).data.target.epoch = (get_latest_message_epoch cfg lm) :=
    (congrArg (fun d : AttestationData Root => d.target.epoch) hdata).symm.trans
      haTargetEpoch
  have hgroundProjection := B.coherence.checkpoint_of_known
    (E.store_causal cfg ext i k)
    (get_head cfg (E.store cfg ext i k)).root hheadKnown
    (honest_attestation cfg ext (E.store cfg ext i k)
      a.data.slot index i).data.target.epoch
  have hqueryProjection := B.coherence.checkpoint_of_known
    (Execution.CausalStore.scheduledPrefix p) lm.root hlmKnown (get_latest_message_epoch cfg lm)
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
      _ = (B.state.C lm.root (get_latest_message_epoch cfg lm)).root := by
        rw [hheadRoot, hcanonicalEpoch]
      _ = (get_checkpoint_for_block cfg (p.store cfg ext)
            lm.root (get_latest_message_epoch cfg lm)).root :=
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
    hiCommittee, hvote, (hhb.vote_deadline i hi a.data.slot k _ hvote).2,
    haSlotEpoch.trans htargetEpoch.symm, ?_,
    htargetExact⟩⟩
  exact slot_lt_prefix_next_epoch_start cfg
    (haSlotEpoch.trans htargetEpoch.symm)


theorem trusted_currentTargetObservedHonestSupporter_vote_of_prefix
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hV : E.CurrentTargetPrefixVoteAssumptions cfg ext)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    (p : E.ScheduledEventPrefix)
    (hp : p.node ∈ E.honest)
    (hqH : E.WithinHorizon cfg (p.previousSecond + 1))
    {state : BeaconState Root} {i : ValidatorIndex}
    (hiObserved : i ∈ E.currentTargetObservedHonestSupporters cfg
      (p.store cfg ext) state) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (p.store cfg ext)).epoch + 1))
      (get_current_target cfg (p.store cfg ext))) := by
  exact E.trusted_currentTargetObservedHonestSupporter_vote_of_prefix_of_provenance
    cfg ext B hV hboundary p
    (p.latestMessageProvenance cfg ext E hV.trajectory hp hqH) hqH hiObserved


end Execution
end FastConfirmation.Spec
end
