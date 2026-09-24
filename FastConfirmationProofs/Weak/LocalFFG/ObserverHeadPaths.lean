module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverCheckpointPrefix
public import FastConfirmationProofs.Weak.LocalFFG.ObserverReceiverPaths

/-! Honest head paths are admissible at the non-honest observer.
The receiver supplies local finalization, while each source uses shared FFG.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}
namespace ObserverLocalFFG

set_option maxRecDepth 4096 in
/-- G4 at the actual observer uses its local finalized certificate. It has
no vote-landing or block-delivery conclusion at that observer. -/
theorem honest_head_path (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn : E.WithinHorizon cfg n) {walkSlot : Slot}
    (hHN : E.WithinHorizon cfg (E.slot_start cfg (E.slot_at cfg n + 1)))
    (hwalk : WalkKnown (E.store cfg ext v n) walkSlot
      (get_head cfg (E.store cfg ext v n)).root) :
    VotePathAdmissible cfg ext E v n obs
      (E.slot_start cfg (E.slot_at cfg n + 1) - 1) walkSlot
      (get_head cfg (E.store cfg ext v n)).root := by
  let R := E.withoutObserver obs
  let S := core.semantics
  let hT := nonhonest_scheduledPrefix hobs core localInputs
  let hTR := ScheduledPrefixPremises.of_selectedMarginAssumptions
    cfg ext R core.base core.genesis
  let N := E.slot_start cfg (E.slot_at cfg n + 1)
  let m := N - 1
  let source := E.store cfg ext v n
  let F := (E.store cfg ext obs m).finalized_checkpoint
  let J := source.justified_checkpoint
  have hvne : v ≠ obs := by intro he; subst v; exact hobs hv
  have hvR : v ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hv
  have hstore : R.store cfg ext v n = source := withoutObserver_store cfg ext E obs v hvne n
  have hanchorEq : S.anchor = E.genesis_store.justified_checkpoint := core.anchor_eq
  obtain ⟨st, block, hg, hslot, hcommit, hparent⟩ := core.genesis
  have hgenShort : ∃ (st : BeaconState Root) (block : SignedBeaconBlock Root),
      R.genesis_store = get_forkchoice_store cfg st block ∧ st.slot = block.message.slot :=
    ⟨st, block, hg, hslot⟩
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    have hgE : E.genesis_store = get_forkchoice_store cfg st block := hg
    rw [hgE]; simp only [get_forkchoice_store]; omega
  have hnN : n < N := (E.slot_at_lt_iff cfg core.base.whole_seconds hgenTime).mp
    (Nat.lt_succ_self _)
  have hnm : n ≤ m := by dsimp only [m]; omega
  have hmN : m < N := by dsimp only [m]; omega
  have hmSlot : E.slot_at cfg m = E.slot_at cfg n := by
    have hlo := E.slot_at_mono cfg hnm
    have hhi : E.slot_at cfg m < E.slot_at cfg n + 1 :=
      (E.slot_at_lt_iff cfg core.base.whole_seconds hgenTime).mpr hmN
    exact Nat.le_antisymm (Nat.le_of_lt_succ hhi) hlo
  have hHm : E.WithinHorizon cfg m := E.withinHorizon_mono cfg hmN.le hHN
  have hFleJ : F.epoch ≤ J.epoch :=
    B.finalized_epoch_le_honest_justified hobs core localInputs hv hHn hmSlot.le
  have hFknown := B.finalized_root_known hobs core localInputs m
  have hanchorF : S.anchor.epoch ≤ F.epoch := by
    rw [hanchorEq]
    rcases B.finalized_certificate core (store_observerCausal m) with ha | ⟨tip, _, ⟨cert⟩⟩
    · change F = E.genesis_store.justified_checkpoint at ha
      rw [ha]
    · exact IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) cert.justified
  have hanchorExact := acceptedAnchorExact_of_trajectory cfg ext R S hTR
    core.anchor_eq core.anchor_boundary
  have prefixOf {tip c} (htip : tip ∈ source.block_roots)
      (hc : IncludedCertifiedJustified cfg R S.state.includedAttestations.Included
        S.anchor tip c) (hle : F.epoch ≤ c.epoch) :
      ExactCheckpointPrefix S.state.C F c := by
    rcases B.finalized_certificate core (store_observerCausal m) with ha | ⟨ftip, hftip, ⟨fcert⟩⟩
    · change F = E.genesis_store.justified_checkpoint at ha
      have hFa : F = S.anchor := ha.trans hanchorEq.symm
      rw [hFa]
      exact IncludedCertifiedJustified.anchor_prefix (cfg := cfg)
        core.checkpoint_projection core.exact_link_validity hanchorExact hc
    · exact B.finalized_prefix_shared hobs core localInputs hvne hftip
        (by rw [hstore]; exact htip) fcert hc hle
  have hparentSource : ParentSlotLt source := E.store_parentSlotLt cfg ext
    hT.wellFormed hT.externals_coherence hT.genesis_structure
    hT.wellFormed.anchor_parent_unscheduled v n
  have hwalkK := E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
    hT.genesis_structure v n
  have hJknown : J.root ∈ source.block_roots := by
    have hj := core.base.domain.justified_root_known v hvR n hHn
    rw [hstore] at hj
    exact hj
  have hhead : (get_head cfg source).root ∈ get_filtered_block_tree cfg source ∨
      (get_head cfg source).root = J.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg _ _
  rcases hhead with hfiltered | hheadJ
  · obtain ⟨tip, htip, hdesc, _hleaf, hcheck, _hlocalF⟩ :=
      filtered_member_viableLeafBelow cfg hparentSource hwalkK hJknown hfiltered
    have hAU := (R.store_causal cfg ext v n).getVotingSource_AU cfg ext S
      (show tip ∈ (R.store cfg ext v n).block_roots by rw [hstore]; exact htip)
    rw [hstore] at hAU
    obtain ⟨cert⟩ := S.state.includedJustifiedAtTip_of_AU cfg ext hAU
    have hFleSource : F.epoch ≤ (get_voting_source cfg source tip).epoch := by
      by_cases hFa : F = S.anchor
      · rw [hFa]
        exact IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) cert
      have hlag := (ObserverFFG.Execution.observerCausalStore_finalizationLag
        (cfg := cfg) (ext := ext) (E := E) (store_observerCausal m) B core localInputs).realized
      have hFaLocal : (E.store cfg ext obs m).finalized_checkpoint ≠
          E.genesis_store.justified_checkpoint := by
        intro he
        apply hFa
        exact he.trans hanchorEq.symm
      have hlag' : F.epoch + 2 ≤ compute_epoch_at_slot cfg (E.slot_at cfg n) := by
        simpa only [get_current_store_epoch, E.store_current_slot, hmSlot] using
          hlag.resolve_left hFaLocal
      have hclock : get_current_store_epoch cfg source =
          compute_epoch_at_slot cfg (E.slot_at cfg n) := by
        simp only [source, get_current_store_epoch, E.store_current_slot]
      rcases hcheck with hJzero | hsourceJ | hrecent
      · change J.epoch = 0 at hJzero
        exact (hFleJ.trans_eq hJzero).trans (Nat.zero_le _)
      · change (get_voting_source cfg source tip).epoch = J.epoch at hsourceJ
        exact hFleJ.trans_eq hsourceJ.symm
      · rw [hclock] at hrecent
        exact Nat.le_of_add_le_add_right (hlag'.trans hrecent)
    have hprefix := prefixOf htip cert hFleSource
    have htipWalk := R.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hTR
      core.anchor_eq core.anchor_boundary v n hanchorF
      (show tip ∈ (R.store cfg ext v n).block_roots by rw [hstore]; exact htip)
    have hcheckpoint := exactCheckpointPrefix_root_eq_at_sameTip cfg ext S.coherence
      (R.store_causal cfg ext v n)
      (by rw [hstore]; exact hparentSource)
      (show tip ∈ (R.store cfg ext v n).block_roots by rw [hstore]; exact htip)
      hprefix hAU hFleSource htipWalk
    rw [hstore] at hcheckpoint
    exact E.votePathAdmissible_of_checkpointCompatible_descendant_of_trajectory cfg ext hT
      hanchorEq core.anchor_boundary hHm hFknown hanchorF hwalk htip hdesc hcheckpoint
  · have hJcert : ∃ tip, tip ∈ source.block_roots ∧
        Nonempty (IncludedCertifiedJustified cfg R S.state.includedAttestations.Included
          S.anchor tip J) := by
      rcases S.globalJustified_anchor_or_AUEvidence hgenShort core.anchor_eq
          (R.store_causal cfg ext v n) with ha | hevidence
      · rw [hstore] at ha
        refine ⟨J.root, hJknown, ?_⟩
        change J = S.anchor at ha
        rw [ha]
        exact ⟨.anchor⟩
      · obtain ⟨carrier⟩ := hevidence
        have hc := S.state.includedJustifiedAtTip_of_AU cfg ext carrier.au
        refine ⟨carrier.tip, ?_, ?_⟩
        · simpa only [hstore] using carrier.tip_carrier.1
        · exact Eq.mp (congrArg (fun c => Nonempty (IncludedCertifiedJustified
            cfg R S.state.includedAttestations.Included S.anchor carrier.tip c))
            (congrArg Store.justified_checkpoint hstore)) hc
    obtain ⟨tip, htip, ⟨cert⟩⟩ := hJcert
    have hprefix := prefixOf htip cert hFleJ
    have hcheckpoint : F.root = get_checkpoint_block cfg source J.root F.epoch := by
      have he : F = get_checkpoint_for_block cfg (R.store cfg ext v n) J.root F.epoch :=
        hprefix.trans (S.coherence.checkpoint_of_known (R.store_causal cfg ext v n)
          J.root (by rw [hstore]; exact hJknown) F.epoch)
      rw [hstore] at he
      exact congrArg Checkpoint.root he
    apply E.votePathAdmissible_of_checkpointCompatible_of_trajectory cfg ext hT
      hanchorEq core.anchor_boundary hHm hFknown hanchorF hwalk
    rw [hheadJ]
    exact hcheckpoint

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
