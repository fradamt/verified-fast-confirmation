module
public import FastConfirmationProofs.Checkpoints.VotePathCheckpointCompatibility
public import FastConfirmationProofs.ForkChoice.Filter.QueryFilterViability
public import FastConfirmationProofs.FFG.SelectedSource.PhaseSourceCarriers

@[expose] public section

/-! Honest vote paths avoid the finalized guard before the next-slot tick.
The receiver's finalization lag and the source leaf's recency check use the
same slot epoch. Exact checkpoint accountability then handles reused roots. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable {E : Execution Root}

/-- An honest head's whole known ancestor path is admissible at the last
second of its slot. The proof uses only lower trajectory, certificate,
economic, honest-behavior, anchor, finalization-delay, and cutoff-relay facts.
It does not use vote landing, the vote-target cache, or the old block relay. -/
theorem head_path_admissible_before_next_tick
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (P : EpochCheckpointProjectionLaws B.anchor (E.RootKnownInScheduledPrefix cfg ext) B.state.checkpoint_at_epoch)
    (V : B.state.LinkCheckpointAgreement)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s n : ℕ} {walkSlot : Slot}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHN : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hwalk : WalkKnown (E.store cfg ext v n) walkSlot
      (get_head cfg (E.store cfg ext v n)).root) :
    VotePathAdmissible cfg ext E v n w (E.slot_start cfg (s + 1) - 1)
      walkSlot (get_head cfg (E.store cfg ext v n)).root := by
  let N := E.slot_start cfg (s + 1)
  let m := N - 1
  let source := E.store cfg ext v n
  let F := (E.store cfg ext w m).finalized_checkpoint
  let J := source.justified_checkpoint
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]; simp only [get_forkchoice_store]; omega
  have hnlt : n < N := (E.slot_at_lt_iff cfg hT.whole_seconds hgenTime).mp
    (by rw [hn]; exact Nat.lt_succ_self s)
  have hnm : n ≤ m := by dsimp only [m]; omega
  have hmN : m < N := by dsimp only [m]; omega
  have hmSlot : E.slot_at cfg m = s := by
    have hlow := E.slot_at_mono cfg hnm
    have hhigh : E.slot_at cfg m < s + 1 :=
      (E.slot_at_lt_iff cfg hT.whole_seconds hgenTime).mpr hmN
    exact Nat.le_antisymm (Nat.le_of_lt_succ hhigh) (hn ▸ hlow)
  have hHm : E.WithinHorizon cfg m := E.withinHorizon_mono cfg hmN.le hHN
  have hFleJ : F.epoch ≤ J.epoch :=
    E.finalized_epoch_le_voter_justified_of_receiver_slot_le cfg ext B hT hrelay hbyz
      hphase hphaseBoundary hanchor hboundary hspe hDelay P V hacc hv
      hs0 hn hHn (hmSlot.le.trans (Nat.le_succ s))
  have hFrealized := E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary (w := w) m
  have hanchorLe : B.anchor.epoch ≤ F.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg)
      (Classical.choice hFrealized.certified)
  have hanchorExact := acceptedAnchorExact_of_trajectory cfg ext E B hT
    hanchor hboundary
  have prefixOf {c : Checkpoint Root}
      (hc : ∃ tip, Nonempty (IncludedCertifiedJustified cfg E
        B.state.includedAttestations.Included B.anchor tip c))
      (hle : F.epoch ≤ c.epoch) : ExactCheckpointPrefix B.state.checkpoint_at_epoch F c := by
    obtain ⟨tip, ⟨cert⟩⟩ := hc
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate cfg ext B
        hgenShort hanchor (E.store_causal cfg ext w m) with
      hFa | ⟨ftip, _, ⟨fcert⟩⟩
    · change ExactCheckpointPrefix B.state.checkpoint_at_epoch
        (E.store cfg ext w m).finalized_checkpoint c
      rw [hFa]
      exact IncludedCertifiedJustified.anchor_prefix (cfg := cfg) P V hanchorExact cert
    · exact B.state.exactFinalizedPrefix_of_accountable cfg P V hanchorExact
        hacc fcert cert hle
  have hparent : ParentSlotLt source := E.store_parentSlotLt cfg ext
    hT.wellFormed hT.externals_coherence hT.genesis_structure
    hT.wellFormed.anchor_parent_unscheduled v n
  have hwalkK := E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
    hT.genesis_structure v n
  have hJknown := E.justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hv n hHn
  have hhead : (get_head cfg source).root ∈ get_filtered_block_tree cfg source ∨
      (get_head cfg source).root = J.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg _ _
  rcases hhead with hfiltered | hheadJ
  · obtain ⟨tip, htip, hdesc, _hleaf, hcheck, _hlocalF⟩ :=
      filtered_member_viableLeafBelow cfg hparent hwalkK hJknown hfiltered
    have hAU := (E.store_causal cfg ext v n).getVotingSource_AU cfg ext B htip
    obtain ⟨cert⟩ := B.state.includedJustifiedAtTip_of_AU cfg ext hAU
    have hFleSource : F.epoch ≤ (get_voting_source cfg source tip).epoch := by
      by_cases hFa : F = B.anchor
      · rw [hFa]
        exact IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) cert
      have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
        E.causalRealizedFinalizationLag_of_acceptedDelay cfg ext B hT
        hanchor hDelay
      have hlag := E.finalizedCheckpoint_twoEpochLag_of_causalLag cfg ext hLag
        (E.store_causal cfg ext w m) hFa
      have hlag' : F.epoch + 2 ≤ compute_epoch_at_slot cfg s := by
        simpa only [F, get_current_store_epoch, E.store_current_slot, hmSlot] using hlag
      have hclock : get_current_store_epoch cfg source = compute_epoch_at_slot cfg s := by
        simp only [source, get_current_store_epoch, E.store_current_slot, hn]
      rcases hcheck with hJzero | hsourceJ | hrecent
      · change J.epoch = 0 at hJzero
        exact (hFleJ.trans_eq hJzero).trans (Nat.zero_le _)
      · change (get_voting_source cfg source tip).epoch = J.epoch at hsourceJ
        exact hFleJ.trans_eq hsourceJ.symm
      · rw [hclock] at hrecent
        exact Nat.le_of_add_le_add_right (hlag'.trans hrecent)
    have hprefix := prefixOf ⟨tip, ⟨cert⟩⟩ hFleSource
    have htipWalk := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT hanchor hboundary
      v n hanchorLe htip
    have hcheckpoint := exactCheckpointPrefix_root_eq_at_sameTip cfg ext B.coherence
      (E.store_causal cfg ext v n) hparent htip hprefix hAU hFleSource htipWalk
    exact E.votePathAdmissible_of_checkpointCompatible_descendant cfg ext B hT
      hanchor hboundary hHm hFrealized.root_known hanchorLe hwalk htip hdesc hcheckpoint
  · have hJcert : ∃ tip, Nonempty (IncludedCertifiedJustified cfg E
        B.state.includedAttestations.Included B.anchor tip J) := by
      rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor
          (E.store_causal cfg ext v n) with hJa | hevidence
      · refine ⟨B.anchor.root, ?_⟩
        change J = B.anchor at hJa
        rw [hJa]
        exact ⟨.anchor⟩
      · obtain ⟨carrier⟩ := hevidence
        exact ⟨carrier.carrier, carrier.formed_evidence.certified⟩
    have hprefix := prefixOf hJcert hFleJ
    have hcheckpoint : F.root = get_checkpoint_block cfg source J.root F.epoch := by
      have heq : F = get_checkpoint_for_block cfg source J.root F.epoch := by
        exact hprefix.trans (B.coherence.checkpoint_of_known
          (E.store_causal cfg ext v n) J.root hJknown F.epoch)
      exact congrArg Checkpoint.root heq
    apply E.votePathAdmissible_of_checkpointCompatible cfg ext B hT hanchor
      hboundary hHm hFrealized.root_known hanchorLe hwalk
    rw [hheadJ]
    exact hcheckpoint

/-- G4: every known ancestor walk of a recorded honest vote avoids exclusion
at `boundary - 1`. No restriction to roots above finality is required. -/
theorem honest_vote_path_admissible
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hphaseBoundary : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (P : EpochCheckpointProjectionLaws B.anchor (E.RootKnownInScheduledPrefix cfg ext) B.state.checkpoint_at_epoch)
    (V : B.state.LinkCheckpointAgreement)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s n : ℕ} {a : Attestation Root} {walkSlot : Slot}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHN : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hvote : E.vote v s = some (n, a))
    (hwalk : WalkKnown (E.store cfg ext v n) walkSlot a.data.beacon_block_root) :
    VotePathAdmissible cfg ext E v n w (E.slot_start cfg (s + 1) - 1)
      walkSlot a.data.beacon_block_root := by
  have hassigned := hT.honest_behavior.votes_assigned v hv s (by rw [hvote]; simp)
  have hsH := E.slotWithinHorizon_of_le cfg (by rw [hn]) hHn
  obtain ⟨k, index, _, _, hown⟩ := hT.honest_behavior.votes_head v hv s hassigned hsH hs0
  rw [hvote] at hown
  have heq := Prod.mk.inj (Option.some.inj hown)
  obtain rfl := heq.1
  have hhead : a.data.beacon_block_root = (get_head cfg (E.store cfg ext v n)).root := by
    rw [heq.2]
    exact honest_attestation_data_beacon_block_root cfg ext _ s index
  rw [hhead] at hwalk ⊢
  exact E.head_path_admissible_before_next_tick cfg ext B hT hrelay hbyz hphase hphaseBoundary
    hanchor hboundary hspe hDelay P V hacc hv hs0 hn hHn hHN hwalk

/-- The public lower execution contracts derive the internal head-path
property. The cache and selected-margin domain are not inputs. -/
theorem honestHeadPathAdmissibility_of_accepted
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (P : EpochCheckpointProjectionLaws B.anchor (E.RootKnownInScheduledPrefix cfg ext) B.state.checkpoint_at_epoch)
    (V : B.state.LinkCheckpointAgreement) :
    HonestHeadPathAdmissibility cfg ext E := by
  have hacc : FFGAccountabilityAssumptions cfg ext E :=
    { genesis_store := by
        obtain ⟨ast, ablk, hgen, _⟩ := hT.genesis_structure
        exact ⟨ast, ablk, hgen⟩
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      externals_coherence := hT.externals_coherence
      static_validator_set := hC.static_validators
      byzantine_bound := hC.byzantine_bound }
  intro v hv n hHn w slot hHN hwalk
  exact E.head_path_admissible_before_next_tick cfg ext B hT
    hC.synchrony.deadline_block_relay hC.byzantine_bound
    hC.phase0_source hC.phase0_boundary_source hanchor hboundary hspe hDelay P V
    (CheckpointCertificateAccountability.of_assumptions cfg hacc)
    hv (E.slot_at_mono cfg (Nat.zero_le n)) rfl hHn hHN hwalk

end Execution



end FastConfirmation.Spec
end
