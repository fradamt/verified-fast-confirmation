module
public import FastConfirmationProofs.Checkpoints.DeadlineCarrierAdoption
public import FastConfirmationProofs.FFG.Certificates.EarlyFinalizingSigner
public import FastConfirmationProofs.FFG.State.FinalizationTiming
public import FastConfirmationProofs.FFG.SourceHistory.FFGSourceCoherence

@[expose] public section

/-! A next-slot finalized checkpoint is no newer than the voter's justification. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

private theorem finalization_last_slot_le {f S s : ℕ}
    (hS : 1 < S) (hbound : (f + 2) * S ≤ s + 1) :
    (f + 1) * S + (S - 1) ≤ s := by
  simp only [Nat.add_mul, one_mul] at hbound ⊢
  omega

/-- The honest source is the head's `GJ`, or its `GU` when the head is old. -/
theorem honest_attestation_source_selector
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    {v : ValidatorIndex} {n s : ℕ} {index : CommitteeIndex}
    (hn : E.slot_at cfg n = s)
    (hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots) :
    (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.source =
        B.state.GJ (get_head cfg (E.store cfg ext v n)).root ∨
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.source =
        B.state.GU (get_head cfg (E.store cfg ext v n)).root ∧
      get_block_epoch cfg (E.store cfg ext v n)
        (get_head cfg (E.store cfg ext v n)).root < compute_epoch_at_slot cfg s := by
  let store := E.store cfg ext v n
  let head := (get_head cfg store).root
  have hcausal := E.store_causal cfg ext v n
  have hprojection := CausalPrefixFFGInterpretation.causalStoreProjection B hcausal
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
    change (honest_attestation_data cfg ext store s index).source = B.state.GJ head
    rw [honest_attestation_data_source_eq_head_state hphase store s index
      (by rw [hstateSlot]; exact hsame)]
    exact hprojection.block_state_gj head hhead
  · have hold : get_block_epoch cfg store head < compute_epoch_at_slot cfg s :=
      Nat.lt_of_le_of_ne (Nat.div_le_div_right hheadLe) hsame
    refine Or.inr ⟨?_, hold⟩
    have hstateEpoch : compute_epoch_at_slot cfg (store.block_states head).slot <
        compute_epoch_at_slot cfg s := by rw [hstateSlot]; exact hold
    have hstateLt : (store.block_states head).slot < s := by
      by_contra hnot
      exact (Nat.not_le_of_gt hstateEpoch)
        (Nat.div_le_div_right (Nat.le_of_not_gt hnot))
    change (if (store.block_states head).slot < s then
      ext.process_slots (store.block_states head) s else store.block_states head
      ).current_justified_checkpoint = B.state.GU head
    rw [if_pos hstateLt, hphaseBoundary.process_slots_current_justified
      _ _ hstateLt hstateEpoch]
    exact hprojection.pulled_up_gu head hhead

/-- Boundary alignment puts the initial slot at or before the anchor epoch. -/
theorem initial_slot_le_anchor_boundary
    (hT : E.ScheduledPrefixPremises cfg ext)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    E.slot_at cfg 0 ≤ anchor.epoch * cfg.slots_per_epoch := by
  obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis_structure
  have hroot : anchor.root = ablk.root := by rw [hanchor, hgen]; rfl
  have hbound : ablk.message.slot ≤ anchor.epoch * cfg.slots_per_epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgen, hroot,
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
theorem next_boundary_finalized_epoch_le_voter_justified
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (P : EpochCheckpointClosure B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s n : ℕ}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n) :
    (E.store cfg ext w (E.slot_start cfg (s + 1))).finalized_checkpoint.epoch ≤
      (E.store cfg ext v n).justified_checkpoint.epoch := by
  let N := E.slot_start cfg (s + 1)
  let F := (E.store cfg ext w N).finalized_checkpoint
  obtain ⟨ast, ablk, hgen, hgenSlot, _⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]; simp only [get_forkchoice_store]; omega
  have hanchorLeJ : B.anchor.epoch ≤
      (E.store cfg ext v n).justified_checkpoint.epoch := by
    obtain ⟨hcert⟩ := CausalPrefixFFGInterpretation.endpointJustified_certificate
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
  have hNslot : E.slot_at cfg N = s + 1 :=
    E.slot_at_slot_start cfg hT.whole_seconds (hs0.trans (Nat.le_succ s)) hgenTime
  have hfinalizedEpoch : F.epoch + 2 ≤ (s + 1) / cfg.slots_per_epoch := by
    simpa only [F, get_current_store_epoch, E.store_current_slot, hNslot,
      compute_epoch_at_slot] using hlag
  have hanchorLeF : B.anchor.epoch ≤ F.epoch :=
    IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hFcert.justified
  have hchildStart : E.slot_at cfg 0 ≤ hFcert.child.epoch * cfg.slots_per_epoch :=
    (E.initial_slot_le_anchor_boundary cfg ext hT hanchor hboundary).trans
      (Nat.mul_le_mul_right cfg.slots_per_epoch
        (hanchorLeF.trans (by rw [hFcert.child_epoch]; exact Nat.le_succ _)))
  obtain ⟨i, t, k, index, hi, hHk, hk, htstart, htlast, hvote, hdue, hsource,
      _htarget⟩ := hFcert.finalizing_link.honest_vote_before_last_slot cfg
        B.state.includedAttestations.relation hA.honest_behavior
        hA.externals_coherence hA.byzantine_bound hspe hchildStart
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
    hphase hphaseBoundary (index := index) hk hhead
  rw [hsource] at hselector
  apply E.deadline_justified_epoch_le_of_carrier cfg ext B hT hA hanchor hboundary
    P V hacc hi hv hHk hHn hhead (by simpa only [hk] using hdue) hnext hklt
  rcases hselector with hgj | ⟨hgu, hold⟩
  · exact Or.inl hgj
  · refine Or.inr ⟨hgu, ?_⟩
    simpa only [get_current_store_epoch, E.store_current_slot, hn] using
      hold.trans_le (ce_mono cfg hts.le)

end Execution
end FastConfirmation.Spec

end
