module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.TargetEdgeFFG
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Safety.FinalizedCheckpointNextSlotSafety

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
The full next-slot safety bundle admits a guarded current-target selected edge.

The call from second six to seven selects the epoch-one child from the
previous-epoch anchor. Its selector guard is true, the retained tentative
trace contains that edge, and an honest vote at slot seven still supports the
same target. `target_votes_support` proves the exact normative support
consequent for every in-horizon call. The accepted FFG interpretation and
positive Paper A3.2 support use the three votes in the slot-seven carrier.

The public non-vacuity, full-bundle, and safety theorems are at the end.
-/

namespace FastConfirmation.Spec
namespace TargetEdgePremiseWitness

open TargetEdgeWitness
open TargetEdgeFFG

set_option maxRecDepth 50000

/-! ## Positive selected-helper support -/

private theorem bounded_support :
    ∀ (v : Fin 4) (n : Fin 15) (s : Fin 16),
      compute_epoch_at_slot witnessConfig s.val =
        (get_current_target witnessConfig
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
            v.val n.val).store).epoch →
      n.val + 1 ≤ s.val →
      (vote s.val).data.target = get_current_target witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
          v.val n.val).store := by
  set_option maxRecDepth 50000 in decide

theorem target_votes_support
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hH : witnessExecution.WithinHorizon witnessConfig (n + 1)) :
    HonestVotesSupportTarget witnessConfig witnessExecution
      (get_current_target witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n).store)
      (n + 1) := by
  have hn : n < 15 := by have := time_lt_sixteen hH; omega
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  refine ⟨hH, ?_⟩
  intro i hi s hs hepoch hfuture k a ha
  obtain ⟨hslt, _, hk, ha'⟩ := witness_vote_some_iff.mp ha
  subst k
  subst a
  rw [slot_at_eq] at hfuture
  exact bounded_support ⟨v, hvlt⟩ ⟨n, hn⟩ ⟨s, hslt⟩ hepoch hfuture

private theorem witnessSelectedHelperProvisos
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hH : witnessExecution.WithinHorizon witnessConfig (n + 1))
    (_hselector : getLatestSelectorGuard witnessConfig
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved) :
    FCRPredictionSupportAt witnessConfig witnessExternals witnessExecution v (n + 1)
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved := by
  have h := target_votes_support hv hH
  exact ⟨fun _ _ _ => h, fun _ _ _ _ _ => h⟩

/-! ## Four-epoch support and accepted FFG closure -/

structure LateStoreFacts (w : ValidatorIndex) (m : ℕ) : Prop where
  anchor_known : anchorRoot ∈
    (witnessExecution.store witnessConfig witnessExternals w m).block_roots
  child_known : childRoot ∈
    (witnessExecution.store witnessConfig witnessExternals w m).block_roots
  carrier_known : carrierRoot ∈
    (witnessExecution.store witnessConfig witnessExternals w m).block_roots
  child_target_key : childEpochOneCheckpoint ∈
    (witnessExecution.store witnessConfig witnessExternals w m
      ).checkpoint_state_keys
  anchor_epoch : get_block_epoch witnessConfig
    (witnessExecution.store witnessConfig witnessExternals w m)
      anchorRoot = 0
  child_epoch : get_block_epoch witnessConfig
    (witnessExecution.store witnessConfig witnessExternals w m)
      childRoot = 1
  carrier_epoch : get_block_epoch witnessConfig
    (witnessExecution.store witnessConfig witnessExternals w m)
      carrierRoot = 1
  carrier_descends_anchor : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_node_for_root carrierRoot) (get_node_for_root anchorRoot) = true
  carrier_descends_child : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_node_for_root carrierRoot) (get_node_for_root childRoot) = true
  carrier_descends_self : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_node_for_root carrierRoot) (get_node_for_root carrierRoot) = true
  head_descends_anchor : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_head witnessConfig
        (witnessExecution.store witnessConfig witnessExternals w m))
      (get_node_for_root anchorRoot) = true
  head_descends_child : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_head witnessConfig
        (witnessExecution.store witnessConfig witnessExternals w m))
      (get_node_for_root childRoot) = true
  head_descends_carrier : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_head witnessConfig
        (witnessExecution.store witnessConfig witnessExternals w m))
      (get_node_for_root carrierRoot) = true

private theorem lateStoreFacts (w : ValidatorIndex) (m : ℕ)
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (h8m : 8 ≤ witnessExecution.slot_at witnessConfig m) :
    LateStoreFacts w m := by
  have hmlt := time_lt_sixteen hHm
  rw [slot_at_eq] at h8m
  constructor <;>
    rw [witness_store_symmetric w 0 m] <;>
    interval_cases m <;>
    set_option maxRecDepth 50000 in decide

private theorem slot_at_ge_eight_of_epoch_two {m : ℕ}
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (hepoch : compute_epoch_at_slot witnessConfig
      (witnessExecution.slot_at witnessConfig m) = 2) :
    8 ≤ witnessExecution.slot_at witnessConfig m := by
  have hmlt := time_lt_sixteen hHm
  rw [slot_at_eq] at hepoch ⊢
  interval_cases m <;>
    norm_num [witnessConfig, compute_epoch_at_slot] at hepoch <;>
    norm_num

private theorem vote_received_by_from_eight {w : ValidatorIndex} {m : ℕ}
    {s : Slot} (hs4 : 4 ≤ s) (hs6 : s ≤ 6) (hm8 : 8 ≤ m) :
    witnessExecution.AttestationReceivedBy w m (vote s) := by
  refine ⟨s + 1, ?_, false, ?_⟩
  · exact (Nat.succ_le_succ hs6).trans (by omega : 7 ≤ m)
  change Event.attestation (vote s) false ∈ witnessSchedule w (s + 1)
  interval_cases s <;>
    simp [witnessSchedule, vote4, vote5, vote6]

private theorem child_acceptedBlockAt :
    witnessExecution.AcceptedBlockAt witnessConfig witnessExternals childRoot
      childSignedBlock.message := by
  refine ⟨childTransition.postStore, childTransition.post_causal, ?_, ?_⟩
  · simpa [childSignedBlock] using childTransition.root_known
  · simpa [childSignedBlock] using
      childTransition.inserted_message_fresh (by
        set_option maxRecDepth 50000 in decide)

private theorem child_canonical_throughout_epoch_two :
    witnessExecution.CanonicalThroughoutEpoch witnessConfig witnessExternals
      childRoot 2 := by
  intro w hw m hHm hepoch
  have h8m := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8m
  exact ⟨hlate.child_known, hlate.head_descends_child⟩


/-! ## Exact positive Paper A3.2 support -/

private noncomputable def witnessAnchorChildLinkSupportAt
    (w : ValidatorIndex) (m : ℕ) (tip : WitnessRoot)
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (hepoch : compute_epoch_at_slot witnessConfig
      (witnessExecution.slot_at witnessConfig m) = 2) :
    witnessAcceptedChainFFGState.PaperA32LinkSupportAt witnessConfig
      witnessExternals w m tip anchorCheckpoint childEpochOneCheckpoint := by
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have h8m : 8 ≤ m := by simpa only [slot_at_eq] using h8slot
  have hlate := lateStoreFacts w m hHm h8slot
  refine
    { view_within_horizon := hHm
      source_before_target := by decide
      target_epoch_within := by decide
      target_known := hlate.child_known
      target_state_keyed := hlate.child_target_key
      signers := {3, 2, 1}
      signers_not_slashable := ?_
      signers_in_registry := ?_
      signer_attestation := ?_
      supermajority := by decide }
  · intro i hi
    change i ∉ witnessAcceptedChainFFGState.slashableOnChain
      witnessConfig witnessExternals tip
    rw [witness_slashableOnChain_eq_empty]
    simp
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [Execution.registry, Execution.anchor_state, witnessExecution,
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
          (by omega : 4 ≤ m)
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
          (by omega : 5 ≤ m)
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
          (by omega : 6 ≤ m)
      · decide
      · decide
      · rfl
      · rfl

theorem witnessPaperA32Support_child_one :
    witnessAcceptedChainFFGState.PaperA32SupportThroughoutEpoch witnessConfig
      witnessExternals childRoot 1 := by
  intro w hw m hHm hepoch
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8slot
  refine ⟨hlate.child_known, ?_, ?_⟩
  · simpa only [hlate.child_epoch] using (by decide : 1 ≤ 1)
  intro tip htip hdesc
  have hsource :
      (witnessAcceptedChainFFGState.paperA32Inputs witnessConfig
        witnessExternals).VSAt witnessConfig
          (witnessExecution.store witnessConfig witnessExternals w m)
          childRoot 1 = anchorCheckpoint := by
    change (if get_block_epoch witnessConfig
        (witnessExecution.store witnessConfig witnessExternals w m)
          childRoot = 1 then
        witnessAcceptedChainFFGState.GJ childRoot
      else witnessAcceptedChainFFGState.GU childRoot) = anchorCheckpoint
    rw [hlate.child_epoch]
    rfl
  simpa only [hsource, witnessC_child_one] using
    Nonempty.intro
      (witnessAnchorChildLinkSupportAt w m tip hHm hepoch)


private theorem witnessPaperA32Support_anchor_one_false :
    ¬ witnessAcceptedChainFFGState.PaperA32SupportThroughoutEpoch
      witnessConfig witnessExternals anchorRoot 1 := by
  intro hsupport
  have hH8 : witnessExecution.WithinHorizon witnessConfig 8 :=
    time_within_of_lt_sixteen (by decide)
  have hepoch8 : compute_epoch_at_slot witnessConfig
      (witnessExecution.slot_at witnessConfig 8) = 2 := by
    decide
  obtain ⟨_hanchorKnown, _hanchorEpoch, hall⟩ :=
    hsupport 0 (by decide) 8 hH8 hepoch8
  have hlate := lateStoreFacts 0 8 hH8 (by decide)
  have hdesc : is_ancestor
      (witnessExecution.store witnessConfig witnessExternals 0 8)
      (get_node_for_root carrierRoot)
      (get_node_for_root
        ((witnessAcceptedChainFFGState.paperA32Inputs witnessConfig
          witnessExternals).C anchorRoot 1).root) = true := by
    simpa only [CausalCarrierFFGState.paperA32Inputs, witnessC_anchor_one] using
      hlate.carrier_descends_anchor
  obtain ⟨L⟩ := hall carrierRoot hlate.carrier_known hdesc
  have hsigners : L.signers.Nonempty := by
    by_contra hnone
    have hempty : L.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * witnessExecution.total_active witnessConfig ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using L.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega)
        (witnessExecution.total_active_pos witnessConfig))
  obtain ⟨i, hi⟩ := hsigners
  obtain ⟨a, hreceived, _hiatt, _hvalid, _hslotH, _hslotLe,
    _hepoch, _hcommittee, _hsource, htarget⟩ :=
      L.signer_attestation i hi
  obtain ⟨k, hk, fromBlock, hmem⟩ := hreceived
  have hground := attestation_mem_schedule_ground hmem
  obtain ⟨s, hslt, rfl⟩ := groundVote_exists hground
  have htarget' : (vote s).data.target =
      ({ epoch := 1, root := anchorRoot } : Checkpoint WitnessRoot) := by
    simpa only [CausalCarrierFFGState.paperA32Inputs, witnessC_anchor_one] using
      htarget
  interval_cases s <;>
    simp [vote, voteData, anchorCheckpoint, childEpochOneCheckpoint,
      carrierEpochTwoCheckpoint, carrierEpochThreeCheckpoint,
      anchorRoot, childRoot, carrierRoot] at htarget'

/-! ## Universal Paper A3.2 -/

private theorem witnessPaperA32Inclusion :
    witnessAcceptedChainFFGState.PaperA32Inclusion witnessConfig
      witnessExternals := by
  constructor
  intro b bb e hb hbe hcanonical hsupport w hw m hHm hboundary
  cases e with
  | zero =>
      have h8slot : 8 ≤ witnessExecution.slot_at witnessConfig m := by
        simpa [compute_start_slot_at_epoch, witnessConfig] using hboundary
      have hlate := lateStoreFacts w m hHm h8slot
      rcases acceptedBlockAt_cases hb with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨carrierRoot, hlate.carrier_known, hlate.anchor_known,
          hlate.carrier_descends_anchor, ?_, ?_⟩
        · rw [hlate.carrier_epoch]
          decide
        · simpa only [CausalCarrierFFGState.paperA32Inputs,
            witnessC_anchor_zero] using witnessAU_carrier_anchor
      · rcases h with ⟨rfl, rfl⟩
        norm_num [childSignedBlock, witnessConfig, compute_epoch_at_slot] at hbe
      · rcases h with ⟨rfl, rfl⟩
        norm_num [carrierSignedBlock, witnessConfig,
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
                witnessExecution.slot_at witnessConfig m := by
              simpa [compute_start_slot_at_epoch, witnessConfig] using
                hboundary
            have h8slot : 8 ≤
                witnessExecution.slot_at witnessConfig m :=
              (by decide : 8 ≤ 12).trans h12slot
            have hlate := lateStoreFacts w m hHm h8slot
            refine ⟨carrierRoot, hlate.carrier_known, hlate.child_known,
              hlate.carrier_descends_child, ?_, ?_⟩
            · rw [hlate.carrier_epoch]
              decide
            · simpa only [CausalCarrierFFGState.paperA32Inputs,
                witnessC_child_one] using witnessAU_carrier_child
          · rcases h with ⟨rfl, rfl⟩
            have h12slot : 12 ≤
                witnessExecution.slot_at witnessConfig m := by
              simpa [compute_start_slot_at_epoch, witnessConfig] using
                hboundary
            have h8slot : 8 ≤
                witnessExecution.slot_at witnessConfig m :=
              (by decide : 8 ≤ 12).trans h12slot
            have hlate := lateStoreFacts w m hHm h8slot
            refine ⟨carrierRoot, hlate.carrier_known, hlate.carrier_known,
              hlate.carrier_descends_self, ?_, ?_⟩
            · rw [hlate.carrier_epoch]
              decide
            · simpa only [CausalCarrierFFGState.paperA32Inputs,
                witnessC_carrier_one] using witnessAU_carrier_child
      | succ e =>
          have hmlt := time_lt_sixteen hHm
          rw [slot_at_eq] at hboundary
          change (Nat.succ (Nat.succ e) + 2) * 4 ≤ m at hboundary
          omega

/-!
## Combined accepted bundle and public witness

The exact bundle and joint witness follow after the accepted-transition
finalization-delay witness below.
-/

private theorem witnessAcceptedRealizedFinalizationDelay :
    witnessExecution.RealizedFinalizationDelay witnessConfig
      witnessExternals witnessAcceptedSemantics := by
  intro t
  change
    (t.postStore.block_states t.signedBlock.root).finalized_checkpoint =
        anchorCheckpoint ∨
      (t.postStore.block_states t.signedBlock.root
          ).finalized_checkpoint.epoch + 2 ≤
        compute_epoch_at_slot witnessConfig t.signedBlock.message.slot
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

def witnessCompletedPrefixCallAssumptions :
    witnessExecution.CompletedFCRCallPremises
      witnessConfig witnessExternals where
  synchrony := witnessPaperSafetySynchrony
  static_validators := witnessStaticValidatorSet
  byzantine_bound := witnessByzantineBound
  phase0_source := witnessPhase0SourceCoherence
  phase0_boundary_source := witnessPhase0BoundarySourceCoherence
  balance_floor := witnessBalanceFloor
  delivery_lookahead := witnessHorizonVoteDeliveryLookahead
  helper_provisos := by
    intro v hv n _hcall hHn1 hselector
    exact witnessSelectedHelperProvisos hv hHn1 hselector

def witnessAcceptedActualFCRNextSlotSafetyAssumptions :
    witnessExecution.NextSlotSafetyPremises witnessConfig
      witnessExternals where
  semantics := witnessAcceptedSemantics
  trajectory := witnessScheduledPrefixTrajectoryAssumptions
  completed_calls := witnessCompletedPrefixCallAssumptions
  epoch_ends_fit := witnessEpochEndsFitUint64
  anchor_eq := by
    simpa only [witnessAcceptedSemantics] using witnessAnchorEquality.symm
  anchor_boundary := by
    simpa only [witnessAcceptedSemantics] using
      witnessTrustedAnchorBoundaryAligned
  finalization_delay := by exact witnessAcceptedRealizedFinalizationDelay
  slots_per_epoch_gt_one := by decide
  paper_a32 := by exact witnessPaperA32Inclusion
  checkpoint_projection := witnessAcceptedEpochCheckpointProjection
  exact_link_validity := witnessExactLinkValidity

/-- The same FFG interpretation used by the premise bundle satisfies the
interpretation-fidelity record: each included vote is a valid body member of
its accepted carrier, validated on the prepared target state. -/
theorem ffg_interpretation_fidelity :
    FFGInterpretationFidelity witnessConfig witnessExternals witnessExecution
      witnessAcceptedActualFCRNextSlotSafetyAssumptions.semantics where
  included_fidelity := by
    intro carrier a h
    exact witnessIncludedFidelity h
  attestation_validity := rfl
  gf_epoch_le_guf := by
    intro r hr
    rfl

theorem witnessPaperA32_child_one_conclusion :
    ∀ w ∈ witnessExecution.honest, ∀ m : ℕ,
      witnessExecution.WithinHorizon witnessConfig m →
      compute_start_slot_at_epoch witnessConfig 3 ≤
        witnessExecution.slot_at witnessConfig m →
      ∃ b' ∈
          (witnessExecution.store witnessConfig witnessExternals w m
            ).block_roots,
        childRoot ∈
            (witnessExecution.store witnessConfig witnessExternals w m
              ).block_roots ∧
          is_ancestor
            (witnessExecution.store witnessConfig witnessExternals w m)
            (get_node_for_root b') (get_node_for_root childRoot) = true ∧
          get_block_epoch witnessConfig
              (witnessExecution.store witnessConfig witnessExternals w m) b' <
            3 ∧
          witnessAcceptedChainFFGState.AU witnessConfig witnessExternals b'
            (witnessAcceptedChainFFGState.C childRoot 1) := by
  exact witnessPaperA32Inclusion.included child_acceptedBlockAt
    (by decide) child_canonical_throughout_epoch_two
      witnessPaperA32Support_child_one

private theorem second_sixteen_outside_horizon :
    ¬ witnessExecution.WithinHorizon witnessConfig 16 := by
  intro hH16
  exact (Nat.lt_irrefl 16) (time_lt_sixteen hH16)

/-- The call from second six to seven selects an accepted current-target edge. -/
theorem target_edge_support_exercised :
    witnessExecution.IsScheduledFCRCallAt witnessConfig witnessExternals 0 6 ∧
    witnessExecution.WithinHorizon witnessConfig 7 ∧
    0 ∈ witnessExecution.honest ∧
    getLatestSelectorGuard witnessConfig confirmingFcr
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals 0 6).afterObserved ∧
    CurrentTargetSelectedEdge witnessConfig witnessExternals confirmingFcr
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals 0 6).afterObserved anchorRoot childRoot := by
  refine ⟨?_, time_within_of_lt_sixteen (by decide), by decide, ?_, ?_⟩
  · change get_current_slot witnessConfig
        (witnessExecution.store witnessConfig witnessExternals 0 7) >
      get_current_slot witnessConfig
        (witnessExecution.store witnessConfig witnessExternals 0 6)
    decide
  · unfold getLatestSelectorGuard
    decide
  · unfold CurrentTargetSelectedEdge
    decide

/-- The call uses positive target support and still has an honest vote to come. -/
theorem target_edge_call_snapshot :
    get_current_target witnessConfig confirmingFcr.store = childEpochOneCheckpoint ∧
    get_current_target_score witnessConfig witnessExternals confirmingFcr.store = 3000 ∧
    compute_honest_ffg_support_for_current_target witnessConfig witnessExternals
      confirmingFcr.store = 3000 ∧
    get_attestation_score witnessConfig confirmingFcr.store (get_node_for_root childRoot)
      (get_current_balance_source confirmingFcr) = 3000 ∧
    compute_safety_threshold witnessConfig witnessExternals confirmingFcr.store childRoot
      (get_current_balance_source confirmingFcr) = 2760 ∧
    witnessExecution.vote 0 7 = some (7, vote7) ∧
    vote7.data.target = childEpochOneCheckpoint := by
  decide

/-- Full next-slot safety premises and the exercised guarded support field. -/
theorem full_bundle_witness :
    Nonempty (witnessExecution.NextSlotSafetyPremises witnessConfig witnessExternals) ∧
    witnessConfig.slot_duration_ms = 1000 ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 6 = anchorRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 7 = childRoot ∧
    childRoot ≠ anchorRoot ∧
    HonestVotesSupportTarget witnessConfig witnessExecution
      (get_current_target witnessConfig confirmingFcr.store) 7 := by
  refine ⟨⟨witnessAcceptedActualFCRNextSlotSafetyAssumptions⟩, rfl, ?_,
    actual_fcr_transition_strict_advance, by decide, ?_⟩
  · set_option maxRecDepth 50000 in decide
  · exact target_votes_support (by decide) (time_within_of_lt_sixteen (by decide))

/-- Apply the public safety theorem to the call's child output at second seven. -/
theorem target_edge_safe_from_next_slot (w m : ℕ)
    (hw : w ∈ witnessExecution.honest) (hm : 8 ≤ m)
    (hH : witnessExecution.WithinHorizon witnessConfig m) :
    is_ancestor (witnessExecution.store witnessConfig witnessExternals w m)
      (get_head witnessConfig (witnessExecution.store witnessConfig witnessExternals w m))
      (get_node_for_root childRoot) = true := by
  have hnext : witnessExecution.slot_at witnessConfig 7 + 1 ≤
      witnessExecution.slot_at witnessConfig m := by simpa only [slot_at_eq] using hm
  have h := confirmed_root_safe_from_next_slot witnessConfig witnessExternals
    witnessExecution witnessAcceptedActualFCRNextSlotSafetyAssumptions
    0 (by decide) 7 w hw m (by omega) hnext hH
  simpa only [actual_fcr_transition_strict_advance] using h

end TargetEdgePremiseWitness
end FastConfirmation.Spec

end
