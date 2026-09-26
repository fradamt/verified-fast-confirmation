module
public import FastConfirmationProofs.Checkpoints.DeadlineCarrierAdoption
public import FastConfirmationProofs.FFG.Certificates.EarlyFinalizingSigner
public import FastConfirmationProofs.FFG.State.FinalizationTiming
public import FastConfirmationProofs.FFG.SourceHistory.FFGSourceCoherence

@[expose] public section

/-! A next-slot finalized checkpoint is no newer than the voter's justification. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

private theorem finalization_last_slot_le {f S s : ℕ}
    (hS : 1 < S) (hbound : (f + 2) * S ≤ s + 1) :
    (f + 1) * S + (S - 1) ≤ s := by
  simp only [Nat.add_mul, one_mul] at hbound ⊢
  omega

/-- Slot processing from a known block state of an honest store, to a slot
at or before the store slot, keeps the anchor's total active balance.  Slot
processing reaches a state covered by the in-horizon registry condition,
and activity is constant in the horizon. -/
theorem process_slots_block_state_total_active
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn : E.WithinHorizon cfg n)
    {r : Root} (hr : r ∈ (E.store cfg ext v n).block_roots)
    {s : Slot} (hlt : ((E.store cfg ext v n).block_states r).slot < s)
    (hle : s ≤ E.slot_at cfg n) :
    get_total_active_balance cfg
        (ext.process_slots ((E.store cfg ext v n).block_states r) s) =
      E.total_active cfg := by
  obtain ⟨ast, ablk, hgen, _, _⟩ := hT.genesis_structure
  have hval : (ext.process_slots
      ((E.store cfg ext v n).block_states r) s).validators = E.registry :=
    hT.externals_coherence.registry_static_in_horizon _
      (Or.inr ⟨_, _,
        ⟨_, E.honest_store_prefix cfg ext v hv n hHn,
          Or.inl ⟨r, hr, rfl⟩⟩,
        E.slotWithinHorizon_of_le cfg hle hHn, rfl⟩)
  have hanchorN : E.anchor_state.slot ≤ E.slot_at cfg n :=
    le_trans (E.anchor_state_slot_le cfg hT.whole_seconds ⟨ast, ablk, hgen⟩)
      (E.slot_at_mono cfg (Nat.zero_le n))
  change _ = get_total_active_balance cfg E.anchor_state
  apply get_total_active_balance_congr cfg
  · rw [hval]
    rfl
  · intro i
    rw [hval]
    simpa only [get_current_epoch,
      hT.externals_coherence.process_slots_slot _ _ hlt] using
      hsv.activity_constant_of_slot_le (cfg := cfg) hle hanchorN hHn.2.2 hHn.2.2

/-- The honest source is the head's `GJ`, or its `GU` when the head is one
epoch old.  When the head is two or more epochs old, the Phase0 boundary laws
bound only the source epoch by the head epoch; the source can be newer than
`GU`.  The balance floor gives the balance antecedent of that law. -/
theorem honest_attestation_source_selector
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hfloor : 2 * cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    {v : ValidatorIndex} {n s : ℕ} {index : CommitteeIndex}
    (hv : v ∈ E.honest) (hHn : E.WithinHorizon cfg n)
    (hn : E.slot_at cfg n = s)
    (hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots) :
    CheckpointReadsAs (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.source
        (B.state.realized_justified (get_head cfg (E.store cfg ext v n)).root) ∨
      CheckpointReadsAs (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.source
        (B.state.unrealized_justified (get_head cfg (E.store cfg ext v n)).root) ∧
      get_block_epoch cfg (E.store cfg ext v n)
        (get_head cfg (E.store cfg ext v n)).root < compute_epoch_at_slot cfg s ∨
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.source.epoch ≤
        get_block_epoch cfg (E.store cfg ext v n)
          (get_head cfg (E.store cfg ext v n)).root ∧
      get_block_epoch cfg (E.store cfg ext v n)
        (get_head cfg (E.store cfg ext v n)).root + 1 <
          compute_epoch_at_slot cfg s := by
  let store := E.store cfg ext v n
  let head := (get_head cfg store).root
  have hcausal := E.store_causal cfg ext v n
  have hprojection := ScheduledFFGInterpretation.causalStoreProjection B hcausal
  have hcore := E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT hcausal
  have hstateSlot : (store.block_states head).slot = (store.blocks head).slot :=
    hcore.2 head hhead
  obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis_structure
  have hheadLe : (store.blocks head).slot ≤ s := by
    have h := E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v n head hhead
    simpa only [store, E.store_current_slot, hn] using h
  by_cases hsame : get_block_epoch cfg store head = compute_epoch_at_slot cfg s
  · left
    change CheckpointReadsAs (honest_attestation_data cfg ext store s index).source
      (B.state.realized_justified head)
    rw [honest_attestation_data_source_eq_head_state hphase store s index
      (by rw [hstateSlot]; exact hsame)]
    exact hprojection.block_state_gj head hhead
  · have hold : get_block_epoch cfg store head < compute_epoch_at_slot cfg s :=
      Nat.lt_of_le_of_ne (Nat.div_le_div_right hheadLe) hsame
    have hstateEpoch : compute_epoch_at_slot cfg (store.block_states head).slot <
        compute_epoch_at_slot cfg s := by rw [hstateSlot]; exact hold
    have hstateLt : (store.block_states head).slot < s := by
      by_contra hnot
      exact (Nat.not_le_of_gt hstateEpoch)
        (Nat.div_le_div_right (Nat.le_of_not_gt hnot))
    have hsourceEq : (honest_attestation cfg ext store s index v).data.source =
        (ext.process_slots (store.block_states head) s).current_justified_checkpoint := by
      change (if (store.block_states head).slot < s then
        ext.process_slots (store.block_states head) s else store.block_states head
        ).current_justified_checkpoint = _
      rw [if_pos hstateLt]
    by_cases hone : compute_epoch_at_slot cfg s = get_block_epoch cfg store head + 1
    · refine Or.inr (Or.inl ⟨?_, hold⟩)
      rw [hsourceEq, hphaseBoundary.process_slots_one_boundary _ _ hstateLt
        (by rw [hstateSlot]; exact hone)]
      exact hprojection.pulled_up_gu head hhead
    · have hbalance : ∀ s' : Slot, (store.block_states head).slot < s' →
          s' ≤ s → 3 * cfg.effective_balance_increment < 2 *
            get_total_active_balance cfg
              (ext.process_slots (store.block_states head) s') := by
        intro s' hlt' hle'
        rw [E.process_slots_block_state_total_active cfg ext hT hsv hv hHn hhead
            hlt' (hle'.trans_eq hn.symm),
          E.total_active_eq_anchorActive_weight cfg (by omega)]
        have hinc := cfg.effective_balance_increment_pos
        omega
      rcases hphaseBoundary.process_slots_checkpoint_epoch _ _ hstateEpoch
          hbalance with hkeep | hle
      · left
        rw [hsourceEq, hkeep]
        exact hprojection.block_state_gj head hhead
      · refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · rw [hsourceEq]
          rw [hstateSlot] at hle
          exact hle
        · have h1 : get_block_epoch cfg store head + 1 ≤ compute_epoch_at_slot cfg s :=
            Nat.succ_le_of_lt hold
          exact Nat.lt_of_le_of_ne h1 (Ne.symm hone)

/-- Boundary alignment puts the initial slot at or before the anchor epoch. -/
theorem initial_slot_le_anchor_boundary
    (hT : E.ScheduledExecutionPremises cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := anchor)) :
    E.slot_at cfg 0 ≤ anchor.epoch * cfg.slots_per_epoch := by
  obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by rw [hanchor, hgen]; rfl
  have hbound : ablk.message.slot ≤ anchor.epoch * cfg.slots_per_epoch := by
    simpa only [InitialAnchorAtEpochBoundary, hgen, hroot,
      get_forkchoice_store, Function.update_self, compute_start_slot_at_epoch]
      using hboundary
  have hclock := E.store_current_slot cfg ext 0 0
  change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hclock
  rw [← hclock, hgen, get_current_slot_get_forkchoice_store cfg hT.whole_seconds,
    hslot]
  exact hbound

/-- An included finalization at the first delivery boundary has an earlier
honest finalizing vote. Its source carrier reaches the voter by the current
slot, unless the voter already has a sufficiently new finalized checkpoint. -/
theorem finalized_epoch_le_voter_justified_of_receiver_slot_le
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hfloor : 2 * cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (P : EpochCheckpointProjectionLaws B.anchor (E.RootKnownInScheduledPrefix cfg ext) B.state.checkpoint_at_epoch)
    (V : B.state.LinkCheckpointAgreement)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s n m : ℕ}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hm : E.slot_at cfg m ≤ s + 1) :
    (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      (E.store cfg ext v n).justified_checkpoint.epoch := by
  let N := m
  let F := (E.store cfg ext w N).finalized_checkpoint
  obtain ⟨ast, ablk, hgen, hgenSlot, _⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]; simp only [get_forkchoice_store]; omega
  have hanchorLeJ : B.anchor.epoch ≤
      (E.store cfg ext v n).justified_checkpoint.epoch := by
    obtain ⟨hcert⟩ := ScheduledFFGInterpretation.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext v n)
    exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
  rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate cfg ext B
      hgenShort hanchor (E.store_causal cfg ext w N) with
    hFanchor | ⟨carrier, _hcarrier, ⟨hFcert⟩⟩
  · rw [hFanchor]; exact hanchorLeJ
  by_cases hFa : F = B.anchor
  · change F.epoch ≤ _
    rw [hFa]; exact hanchorLeJ
  have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
    E.causalRealizedFinalizationLag_of_acceptedDelay cfg ext B hT hanchor hDelay
  have hlag := E.finalizedCheckpoint_twoEpochLag_of_causalLag cfg ext hLag
    (E.store_causal cfg ext w N) hFa
  have hfinalizedEpoch : F.epoch + 2 ≤ (s + 1) / cfg.slots_per_epoch := by
    have hlag' : F.epoch + 2 ≤ E.slot_at cfg m / cfg.slots_per_epoch := by
      simpa only [F, N, get_current_store_epoch, E.store_current_slot,
        compute_epoch_at_slot] using hlag
    exact hlag'.trans (Nat.div_le_div_right hm)
  have hanchorLeF : B.anchor.epoch ≤ F.epoch :=
    IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hFcert.justified
  have hchildStart : E.slot_at cfg 0 ≤ hFcert.child.epoch * cfg.slots_per_epoch :=
    (E.initial_slot_le_anchor_boundary cfg ext hT hanchor hboundary).trans
      (Nat.mul_le_mul_right cfg.slots_per_epoch
        (hanchorLeF.trans (by rw [hFcert.child_epoch]; exact Nat.le_succ _)))
  obtain ⟨i, t, k, index, hi, hHk, hk, htstart, htlast, hvote, hdue, hsource,
      _htarget⟩ := hFcert.finalizing_link.honest_vote_before_last_slot cfg
        B.state.includedAttestations.relation hT.honest_behavior
        hT.externals_coherence hbyz hspe hchildStart
  have hlastLe : hFcert.child.epoch * cfg.slots_per_epoch +
      (cfg.slots_per_epoch - 1) ≤ s := by
    have hscaled := (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hfinalizedEpoch
    rw [hFcert.child_epoch]
    change (F.epoch + 1) * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) ≤ s
    exact finalization_last_slot_le hspe hscaled
  have hts : t < s := htlast.trans_le hlastLe
  have hnext : E.slot_start cfg (E.slot_at cfg k + 1) ≤ n := by
    rw [hk]
    exact (E.slot_start_mono cfg (Nat.succ_le_of_lt hts)).trans
      (E.slot_start_le_of_slot_at cfg hT.whole_seconds hgenTime hn)
  have hklt : k < n := by
    have hb : k < E.slot_start cfg s :=
      (E.slot_at_lt_iff cfg hT.whole_seconds hgenTime).mp (hk ▸ hts)
    exact hb.trans_le (E.slot_start_le_of_slot_at cfg hT.whole_seconds hgenTime hn)
  have hhead := E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hi k hHk
  have hselector := E.honest_attestation_source_selector cfg ext B hT
    hphase hphaseBoundary hsv hfloor (index := index) hi hHk hk hhead
  -- `F` is a certified checkpoint other than the anchor, so its epoch is
  -- positive and every reading of it is equality.
  have hFpos : 0 < F.epoch := by
    rcases IncludedCertifiedJustified.eq_anchor_or_epoch_gt cfg hFcert.justified with
      hFeq | hFgt
    · exact absurd hFeq hFa
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hFgt
  rw [hsource.eq_of_epoch_pos hFpos] at hselector
  apply E.deadline_justified_epoch_le_of_carrier cfg ext B hT hrelay hanchor hboundary
    P V hacc hi hv hHk hHn hhead (by simpa only [hk] using hdue) hnext hklt
  rcases hselector with hgj | ⟨hgu, hold⟩ | ⟨hle, hlate⟩
  · exact Or.inl (hgj.eq_of_epoch_gt hFpos)
  · refine Or.inr ⟨hgu.eq_of_epoch_gt hFpos, ?_⟩
    simpa only [get_current_store_epoch, E.store_current_slot, hn] using
      hold.trans_le (ce_mono cfg hts.le)
  · -- The finalizing link's target epoch is `F.epoch + 1`, so a head two or
    -- more epochs older than the vote has a source older than `F`.
    exfalso
    have htEpoch : compute_epoch_at_slot cfg t = F.epoch + 1 := by
      rw [← hFcert.child_epoch]
      apply Nat.div_eq_of_lt_le htstart
      have hlt := htlast.trans_le (Nat.add_le_add_left
        (Nat.sub_le cfg.slots_per_epoch 1) _)
      simpa only [Nat.add_mul, one_mul] using hlt
    rw [htEpoch] at hlate
    exact (Nat.not_le_of_gt (Nat.lt_of_add_lt_add_right hlate)) hle

/-- The receiver checkpoint at the next slot start is no newer than the
honest voter's justification. -/
theorem next_boundary_finalized_epoch_le_voter_justified
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hfloor : 2 * cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (P : EpochCheckpointProjectionLaws B.anchor (E.RootKnownInScheduledPrefix cfg ext) B.state.checkpoint_at_epoch)
    (V : B.state.LinkCheckpointAgreement)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s n : ℕ}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n) :
    (E.store cfg ext w (E.slot_start cfg (s + 1))).finalized_checkpoint.epoch ≤
      (E.store cfg ext v n).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgen, _, _⟩ := hT.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]; simp only [get_forkchoice_store]; omega
  apply E.finalized_epoch_le_voter_justified_of_receiver_slot_le cfg ext B hT hrelay hbyz
    hphase hphaseBoundary hsv hfloor hanchor hboundary hspe hDelay P V hacc hv hs0 hn
    hHn
  rw [E.slot_at_slot_start cfg hT.whole_seconds
    (hs0.trans (Nat.le_succ s)) hgenTime]

end Execution
end FastConfirmation.Spec

end
