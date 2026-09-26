module
public import FastConfirmationWitnesses.NonVacuity.FullTwelveFFG
public import FastConfirmationProofs.Safety.NextSlotSafety

@[expose] public section

/-! The twelve-second run satisfies the full next-slot safety bundle. -/

namespace FastConfirmation.Spec.FullTwelveWitness

open AcceptedActualFCRJointNonVacuityBase

set_option maxRecDepth 50000

private def callSecond (s : Fin 15) : ℕ := 12 * (s.val + 1) - 1

private theorem call_index {v n : ℕ}
    (hcall : run.IsScheduledFCRCallAt cfg ext v n)
    (hH : run.WithinHorizon cfg (n + 1)) :
    ∃ s : Fin 15, n = callSecond s := by
  have hn := horizon_time hH
  change get_current_slot cfg (run.store cfg ext v (n + 1)) >
    get_current_slot cfg (run.store cfg ext v n) at hcall
  rw [run.store_current_slot cfg ext v (n + 1),
    run.store_current_slot cfg ext v n, slot_at_eq, slot_at_eq] at hcall
  simp only [Slot] at hcall
  refine ⟨⟨n / 12, by omega⟩, ?_⟩
  change n = 12 * (n / 12 + 1) - 1
  omega

private theorem bounded_no_currentTargetAcceptedEdge_under_selector :
    ∀ (v : Fin 4) (n : Fin 15) (a c : WitnessRoot),
      getLatestSelectorGuard cfg
          (run.fcrStoreAtCall cfg ext
            v.val (callSecond n))
          (run.getLatestConfirmedTraceAt cfg
            ext v.val (callSecond n)).afterObserved →
        (a, c) ∈
          (findLatestSelectedTrace cfg ext
            (run.fcrStoreAtCall cfg ext
              v.val (callSecond n))
            (run.getLatestConfirmedTraceAt cfg
              ext v.val (callSecond n)).afterObserved).2.2 →
        get_block_epoch cfg
            (run.fcrStoreAtCall cfg ext
              v.val (callSecond n)).store a <
        get_block_epoch cfg
            (run.fcrStoreAtCall cfg ext
              v.val (callSecond n)).store c →
        False := by
  simp only [getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide

private theorem bounded_no_selectedPreviousResult_under_selector :
    ∀ (v : Fin 4) (n : Fin 15) (result : WitnessRoot),
      getLatestSelectorGuard cfg
          (run.fcrStoreAtCall cfg ext
            v.val (callSecond n))
          (run.getLatestConfirmedTraceAt cfg
            ext v.val (callSecond n)).afterObserved →
        find_latest_confirmed_descendant cfg ext
          (run.fcrStoreAtCall cfg ext
            v.val (callSecond n))
          (run.getLatestConfirmedTraceAt cfg
            ext v.val (callSecond n)).afterObserved = result →
        result ≠
          (run.getLatestConfirmedTraceAt cfg
            ext v.val (callSecond n)).afterObserved →
        get_block_epoch cfg
            (run.fcrStoreAtCall cfg ext
              v.val (callSecond n)).store result ≠
          get_current_store_epoch cfg
            (run.fcrStoreAtCall cfg ext
              v.val (callSecond n)).store →
        is_start_slot_at_epoch cfg
          (get_current_slot cfg
            (run.fcrStoreAtCall cfg ext
              v.val (callSecond n)).store) ≠ true →
        False := by
  simp only [getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide

/-- Whenever the executable selector is actually enabled in this witness,
its current-target edge antecedent is empty.  Tentative edges computed at
guard-false queries are deliberately outside this call-scoped statement. -/
theorem no_currentTargetAcceptedEdge_under_selector
    {v : ValidatorIndex} (hv : v ∈ run.honest) {n : ℕ}
    (hcall : run.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : run.WithinHorizon cfg (n + 1))
    (hselector : getLatestSelectorGuard cfg
      (run.fcrStoreAtCall cfg ext v n)
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved)
    (a c : WitnessRoot)
    (hedge : CurrentTargetSelectedEdge cfg ext
      (run.fcrStoreAtCall cfg ext v n)
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved a c) : False := by
  obtain ⟨nf, rfl⟩ := call_index hcall hHn1
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  let vf : Fin 4 := ⟨v, hvlt⟩
  rcases hedge with ⟨hmem, hlt⟩
  exact bounded_no_currentTargetAcceptedEdge_under_selector
    vf nf a c hselector hmem hlt

/-- At an actual selector invocation, the strict selected-result antecedent
from a previous block epoch is empty in this finite prefix. -/
theorem no_selectedPreviousResult_under_selector
    {v : ValidatorIndex} (hv : v ∈ run.honest) {n : ℕ}
    (hcall : run.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : run.WithinHorizon cfg (n + 1))
    (hselector : getLatestSelectorGuard cfg
      (run.fcrStoreAtCall cfg ext v n)
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved)
    (result : WitnessRoot)
    (hout : find_latest_confirmed_descendant cfg ext
      (run.fcrStoreAtCall cfg ext v n)
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved = result)
    (hstrict : result ≠
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved)
    (hprevious : get_block_epoch cfg
      (run.fcrStoreAtCall cfg ext v n).store
        result ≠ get_current_store_epoch cfg
          (run.fcrStoreAtCall cfg ext v n).store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg
        (run.fcrStoreAtCall cfg ext v n).store)
        ≠ true) : False := by
  obtain ⟨nf, rfl⟩ := call_index hcall hHn1
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  let vf : Fin 4 := ⟨v, hvlt⟩
  exact bounded_no_selectedPreviousResult_under_selector
    vf nf result hselector hout hstrict hprevious hnotStart

theorem witnessSelectedHelperProvisos
    {v : ValidatorIndex} (hv : v ∈ run.honest) {n : ℕ}
    (hcall : run.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : run.WithinHorizon cfg (n + 1))
    (hselector : getLatestSelectorGuard cfg
      (run.fcrStoreAtCall cfg ext v n)
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved) :
    SelectedPredictionVoteSupport cfg ext run
      v (n + 1)
      (run.fcrStoreAtCall cfg ext v n)
      (run.getLatestConfirmedTraceAt cfg
        ext v n).afterObserved := by
  refine
    { current_edge_vote_support := ?_
      previous_result_vote_support := ?_ }
  · intro a c hedge
    exact False.elim
      (no_currentTargetAcceptedEdge_under_selector
        hv hcall hHn1 hselector a c hedge)
  · intro result hout hstrict hprevious hnotStart
    exact False.elim
      (no_selectedPreviousResult_under_selector hv hcall hHn1 hselector
        result hout hstrict hprevious hnotStart)


structure LateStoreFacts (w : ValidatorIndex) (m : ℕ) : Prop where
  anchor_known : anchorRoot ∈
    (run.store cfg ext w m).block_roots
  child_known : childRoot ∈
    (run.store cfg ext w m).block_roots
  carrier_known : carrierRoot ∈
    (run.store cfg ext w m).block_roots
  child_target_key : childEpochOneCheckpoint ∈
    (run.store cfg ext w m
      ).checkpoint_state_keys
  anchor_epoch : get_block_epoch cfg
    (run.store cfg ext w m)
      anchorRoot = 0
  child_epoch : get_block_epoch cfg
    (run.store cfg ext w m)
      childRoot = 0
  carrier_epoch : get_block_epoch cfg
    (run.store cfg ext w m)
      carrierRoot = 1
  carrier_descends_anchor : is_ancestor
    (run.store cfg ext w m)
      (get_node_for_root carrierRoot) (get_node_for_root anchorRoot) = true
  carrier_descends_child : is_ancestor
    (run.store cfg ext w m)
      (get_node_for_root carrierRoot) (get_node_for_root childRoot) = true
  carrier_descends_self : is_ancestor
    (run.store cfg ext w m)
      (get_node_for_root carrierRoot) (get_node_for_root carrierRoot) = true
  head_descends_anchor : is_ancestor
    (run.store cfg ext w m)
      (get_head cfg
        (run.store cfg ext w m))
      (get_node_for_root anchorRoot) = true
  head_descends_child : is_ancestor
    (run.store cfg ext w m)
      (get_head cfg
        (run.store cfg ext w m))
      (get_node_for_root childRoot) = true
  head_descends_carrier : is_ancestor
    (run.store cfg ext w m)
      (get_head cfg
        (run.store cfg ext w m))
      (get_node_for_root carrierRoot) = true

private theorem late_table : ∀ (w : Fin 3) (s : Fin 8) (o : Fin 12),
    LateStoreFacts w (12 * (s.val + 8) + o.val) := by
  intro w s o
  constructor <;> revert o s w <;> decide

theorem lateStoreFacts (w : ValidatorIndex) (m : ℕ)
    (hHm : run.WithinHorizon cfg m) (h8m : 8 ≤ run.slot_at cfg m) :
    LateStoreFacts w m := by
  have hmlt := horizon_time hHm
  rw [slot_at_eq] at h8m
  simp only [Slot] at h8m
  have hs : m / 12 - 8 < 8 := by omega
  have ho : m % 12 < 12 := Nat.mod_lt _ (by decide)
  have htime : 12 * (m / 12 - 8 + 8) + m % 12 = m := by omega
  have h := late_table ⟨nodeClass w, nodeClass_lt w⟩ ⟨m / 12 - 8, hs⟩ ⟨m % 12, ho⟩
  dsimp only at h
  rw [htime] at h
  cases h
  constructor <;> rw [store_nodeClass w m] <;> assumption

theorem slot_at_ge_eight_of_epoch_two {m : ℕ}
    (_hHm : run.WithinHorizon cfg m)
    (hepoch : compute_epoch_at_slot cfg (run.slot_at cfg m) = 2) :
    8 ≤ run.slot_at cfg m := by
  change run.slot_at cfg m / 4 = 2 at hepoch
  simp only [Slot, Epoch] at *
  omega

theorem vote_received_by_from_eight {w m s : ℕ}
    (hs4 : 4 ≤ s) (hs6 : s ≤ 6) (hm8 : 96 ≤ m) :
    run.AttestationReceivedBy w m (vote s) := by
  refine ⟨12 * (s + 1), by omega, false, ?_⟩
  have h := vote_at_boundary
    (recorded_vote_some_iff.mpr ⟨by omega, rfl, rfl, rfl⟩ :
      run.vote (s % 4) s = some (12 * s + 3, vote s)) w
  simpa only [slot_start_eq] using h

theorem child_acceptedBlockAt :
    run.BlockKnownInScheduledPrefix cfg ext childRoot
      childSignedBlock.message := by
  refine ⟨childTransition.postStore, childTransition.post_causal, ?_, ?_⟩
  · simpa [childSignedBlock] using childTransition.root_known
  · simpa [childSignedBlock] using
      childTransition.inserted_message_fresh (by
        set_option maxRecDepth 50000 in decide)

theorem child_canonical_throughout_epoch_two :
    run.CanonicalThroughoutEpoch cfg ext
      childRoot 2 := by
  intro w hw m hHm hepoch
  have h8m := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8m
  exact ⟨hlate.child_known, hlate.head_descends_child⟩


/-! ## Exact positive Paper A3.2 support -/

noncomputable def witnessAnchorChildLinkSupportAt
    (w : ValidatorIndex) (m : ℕ) (tip : WitnessRoot)
    (hHm : run.WithinHorizon cfg m)
    (hepoch : compute_epoch_at_slot cfg
      (run.slot_at cfg m) = 2) :
    witnessAcceptedChainFFGState.PaperA32LinkSupportAt cfg
      ext w m tip anchorCheckpoint childEpochOneCheckpoint := by
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have h8m : 96 ≤ m := by rw [slot_at_eq] at h8slot; simp only [Slot] at h8slot; omega
  have hlate := lateStoreFacts w m hHm h8slot
  refine
    { view_within_horizon := hHm
      source_before_target := by decide
      target_epoch_within := by decide
      target_known := hlate.child_known
      target_state_keyed := hlate.child_target_key
      signers := {0, 1, 2}
      signers_not_slashable := ?_
      signers_in_registry := ?_
      signer_attestation := ?_
      supermajority := by decide }
  · intro i hi
    change i ∉ witnessAcceptedChainFFGState.slashableOnChain
      cfg ext tip
    rw [witness_slashableOnChain_eq_empty]
    simp
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [Execution.registry, Execution.anchor_state, run,
        anchorState, stateAt, anchorSignedBlock, get_forkchoice_store]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · refine ⟨vote4, vote_received_by_from_eight
          (s := 4) (by decide) (by decide) h8m, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
      · decide
      · apply (witness_valid_iff _ _).2
        refine ⟨?_, vote_mem_ground (by decide)⟩
        rw [(witnessStore_registryConstant w m).2 _ hlate.child_target_key]
        decide
      · exact slot_within_of_lt_sixteen (by decide)
      · simpa only [vote4, vote_data_slot, slot_at_eq] using
          (by omega : 4 ≤ m / 12)
      · decide
      · decide
      · rfl
      · rfl
    · refine ⟨vote5, vote_received_by_from_eight
          (s := 5) (by decide) (by decide) h8m, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
      · decide
      · apply (witness_valid_iff _ _).2
        refine ⟨?_, vote_mem_ground (by decide)⟩
        rw [(witnessStore_registryConstant w m).2 _ hlate.child_target_key]
        decide
      · exact slot_within_of_lt_sixteen (by decide)
      · simpa only [vote5, vote_data_slot, slot_at_eq] using
          (by omega : 5 ≤ m / 12)
      · decide
      · decide
      · rfl
      · rfl
    · refine ⟨vote6, vote_received_by_from_eight
          (s := 6) (by decide) (by decide) h8m, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
      · decide
      · apply (witness_valid_iff _ _).2
        refine ⟨?_, vote_mem_ground (by decide)⟩
        rw [(witnessStore_registryConstant w m).2 _ hlate.child_target_key]
        decide
      · exact slot_within_of_lt_sixteen (by decide)
      · simpa only [vote6, vote_data_slot, slot_at_eq] using
          (by omega : 6 ≤ m / 12)
      · decide
      · decide
      · rfl
      · rfl

theorem witnessPaperA32Support_child_one :
    witnessAcceptedChainFFGState.SourceTargetSupportThroughoutEpoch cfg
      ext childRoot 1 := by
  intro w hw m hHm hepoch
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8slot
  refine ⟨hlate.child_known, ?_, ?_⟩
  · simpa only [hlate.child_epoch] using (by decide : 0 ≤ 1)
  intro tip htip hdesc
  have hsource :
      (witnessAcceptedChainFFGState.checkpoint_inclusion_view cfg
        ext).voting_source_at cfg
          (run.store cfg ext w m)
          childRoot 1 = anchorCheckpoint := by
    change (if get_block_epoch cfg
        (run.store cfg ext w m)
          childRoot = 1 then
        witnessAcceptedChainFFGState.realized_justified childRoot
      else witnessAcceptedChainFFGState.unrealized_justified childRoot) = anchorCheckpoint
    rw [hlate.child_epoch]
    rfl
  simpa only [hsource, witnessC_child_one] using
    Nonempty.intro
      (witnessAnchorChildLinkSupportAt w m tip hHm hepoch)


theorem witnessPaperA32Support_anchor_one_false :
    ¬ witnessAcceptedChainFFGState.SourceTargetSupportThroughoutEpoch
      cfg ext anchorRoot 1 := by
  intro hsupport
  have hH8 : run.WithinHorizon cfg 96 :=
    time_within (by decide)
  have hepoch8 : compute_epoch_at_slot cfg
      (run.slot_at cfg 96) = 2 := by
    decide
  obtain ⟨_hanchorKnown, _hanchorEpoch, hall⟩ :=
    hsupport 0 (by decide) 96 hH8 hepoch8
  have hlate := lateStoreFacts 0 96 hH8 (by decide)
  have hdesc : is_ancestor
      (run.store cfg ext 0 96)
      (get_node_for_root carrierRoot)
      (get_node_for_root
        ((witnessAcceptedChainFFGState.checkpoint_inclusion_view cfg
          ext).C anchorRoot 1).root) = true := by
    simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view, witnessC_anchor_one] using
      hlate.carrier_descends_anchor
  obtain ⟨L⟩ := hall carrierRoot hlate.carrier_known hdesc
  have hsigners : L.signers.Nonempty := by
    by_contra hnone
    have hempty : L.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * run.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using L.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega)
        (run.total_active_pos cfg))
  obtain ⟨i, hi⟩ := hsigners
  obtain ⟨a, hreceived, _hiatt, _hvalid, _hslotH, _hslotLe,
    _hepoch, _hcommittee, _hsource, htarget⟩ :=
      L.signer_attestation i hi
  obtain ⟨k, hk, fromBlock, hmem⟩ := hreceived
  obtain ⟨s, hslt, rfl, _⟩ := scheduled_attestation hmem
  have htarget' : (vote s).data.target =
      ({ epoch := 1, root := anchorRoot } : Checkpoint WitnessRoot) := by
    simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view, witnessC_anchor_one] using
      htarget
  interval_cases s <;>
    simp [vote, voteData, anchorCheckpoint, childEpochOneCheckpoint,
      carrierEpochTwoCheckpoint, carrierEpochThreeCheckpoint,
      anchorRoot, childRoot, carrierRoot] at htarget'

/-! ## Universal Paper A3.2 -/

theorem witnessPaperA32Inclusion :
    witnessAcceptedChainFFGState.EventualCheckpointInclusion cfg
      ext := by
  constructor
  intro b bb e hb hbe hcanonical hsupport w hw m hHm hboundary
  cases e with
  | zero =>
      have h8slot : 8 ≤ run.slot_at cfg m := by
        simpa [compute_start_slot_at_epoch, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig] using hboundary
      have hlate := lateStoreFacts w m hHm h8slot
      rcases acceptedBlockAt_cases hb with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨carrierRoot, hlate.carrier_known, hlate.anchor_known,
          hlate.carrier_descends_anchor, ?_, ?_⟩
        · rw [hlate.carrier_epoch]
          decide
        · simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view,
            witnessC_anchor_zero] using witnessAU_carrier_anchor
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨carrierRoot, hlate.carrier_known, hlate.child_known,
          hlate.carrier_descends_child, ?_, ?_⟩
        · rw [hlate.carrier_epoch]
          decide
        · simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view,
            witnessC_child_zero] using witnessAU_carrier_anchor
      · rcases h with ⟨rfl, rfl⟩
        norm_num [carrierSignedBlock, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig,
          compute_epoch_at_slot] at hbe
  | succ e =>
      cases e with
      | zero =>
          rcases acceptedBlockAt_cases hb with h | h | h
          · rcases h with ⟨rfl, rfl⟩
            exact False.elim
              (witnessPaperA32Support_anchor_one_false hsupport)
          · rcases h with ⟨rfl, rfl⟩
            have h12slot : 12 ≤
                run.slot_at cfg m := by
              simpa [compute_start_slot_at_epoch, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig] using
                hboundary
            have h8slot : 8 ≤
                run.slot_at cfg m :=
              (by decide : 8 ≤ 12).trans h12slot
            have hlate := lateStoreFacts w m hHm h8slot
            refine ⟨carrierRoot, hlate.carrier_known, hlate.child_known,
              hlate.carrier_descends_child, ?_, ?_⟩
            · rw [hlate.carrier_epoch]
              decide
            · simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view,
                witnessC_child_one] using witnessAU_carrier_child
          · rcases h with ⟨rfl, rfl⟩
            have h12slot : 12 ≤
                run.slot_at cfg m := by
              simpa [compute_start_slot_at_epoch, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig] using
                hboundary
            have h8slot : 8 ≤
                run.slot_at cfg m :=
              (by decide : 8 ≤ 12).trans h12slot
            have hlate := lateStoreFacts w m hHm h8slot
            refine ⟨carrierRoot, hlate.carrier_known, hlate.carrier_known,
              hlate.carrier_descends_self, ?_, ?_⟩
            · rw [hlate.carrier_epoch]
              decide
            · simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view,
                witnessC_carrier_one] using witnessAU_carrier_child
      | succ e =>
          have hmlt := horizon_time hHm
          rw [slot_at_eq] at hboundary
          change (Nat.succ (Nat.succ e) + 2) * 4 ≤ m / 12 at hboundary
          omega

/-!
## Combined accepted bundle and public witness

The exact bundle and joint witness follow after the accepted-transition
finalization-delay witness below.
-/

theorem witnessAcceptedRealizedFinalizationDelay :
    run.ImportedBlockFinalizationLag cfg
      ext witnessAcceptedSemantics := by
  intro t
  change
    (t.postStore.block_states t.signedBlock.root).finalized_checkpoint =
        anchorCheckpoint ∨
      (t.postStore.block_states t.signedBlock.root
          ).finalized_checkpoint.epoch + 2 ≤
        compute_epoch_at_slot cfg t.signedBlock.message.slot
  rcases acceptedTransition_cases t with h | h
  · left
    rw [h.1]
    change (t.postStore.block_states childRoot).finalized_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl
  · left
    rw [h.1]
    change (t.postStore.block_states carrierRoot).finalized_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl



def completed_calls : run.ScheduledFCRCallPremises cfg ext where
  synchrony := next_slot_synchrony
  static_validators := static_validators
  byzantine_bound := byzantine_bound
  phase0_source := phase0_source
  phase0_boundary_source := phase0_boundary_source
  balance_floor := balance_floor
  delivery_lookahead := delivery_lookahead

def safety_premises : run.NextSlotSafetyPremises cfg ext where
  ffg_interpretation := witnessAcceptedSemantics
  trajectory := scheduled_prefix_premises
  completed_calls := completed_calls
  epoch_ends_fit := epoch_ends_fit
  anchor_eq := rfl
  anchor_boundary := anchor_boundary
  finalization_delay := witnessAcceptedRealizedFinalizationDelay
  slots_per_epoch_gt_one := by decide
  checkpoint_inclusion := witnessPaperA32Inclusion
  checkpoint_projection := witnessAcceptedEpochCheckpointProjection
  exact_link_validity := witnessExactLinkValidity

/-- The same FFG interpretation used by the premise bundle satisfies the
interpretation-fidelity record: each included vote is a valid body member of
its accepted carrier, validated on the prepared target state. -/
theorem ffg_interpretation_fidelity :
    FFGInterpretationFidelity cfg ext run
      safety_premises.ffg_interpretation where
  included_fidelity := by
    intro carrier a h
    exact witnessIncludedFidelity h
  realized_finalized_epoch_le_unrealized_finalized := by
    intro r hr
    rfl

/-- Full premises and a scheduled call that changes the confirmed root. -/
theorem full_bundle_witness :
    Nonempty (run.NextSlotSafetyPremises cfg ext) ∧
    cfg.slot_duration_ms = 12000 ∧ get_attestation_due_ms cfg = 3000 ∧
    run.IsScheduledFCRCallAt cfg ext 0 23 ∧
    run.confirmed cfg ext 0 23 = anchorRoot ∧
    run.confirmed cfg ext 0 24 = childRoot ∧ childRoot ≠ anchorRoot := by
  exact ⟨⟨safety_premises⟩, rfl, due_eq, changed_confirmed_root.2.2,
    changed_confirmed_root.1, changed_confirmed_root.2.1, by decide⟩

/-- Apply the public safety theorem to the changed output at second 24. -/
theorem changed_root_safe_from_next_slot (w m : ℕ)
    (hw : w ∈ run.honest) (hm : 36 ≤ m)
    (hH : run.WithinHorizon cfg m) :
    is_ancestor (run.store cfg ext w m)
      (get_head cfg (run.store cfg ext w m))
      (get_node_for_root childRoot) = true := by
  have hnext : run.slot_at cfg 24 + 1 ≤ run.slot_at cfg m := by
    rw [slot_at_eq, slot_at_eq]
    simp only [Slot]
    omega
  have h := confirmed_root_safe_from_next_slot cfg ext run safety_premises
    0 (by decide) 24 w hw m (by omega) hnext hH
  simpa only [changed_confirmed_root.2.1] using h
end FastConfirmation.Spec.FullTwelveWitness
end
