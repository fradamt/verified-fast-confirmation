module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.ByzantineFFG
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Safety.FinalizedCheckpointNextSlotSafety

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
The full next-slot safety bundle admits Byzantine weight and a relayed
attester slashing.

Validator 4 is not honest and has weight 200 of the total active 4000. It
shares every committee of validator 3, so each one-slot committee has weight
1000 and a non-honest share of 20%. Validator 4 signs two slot-four votes with
the same target epoch. Every node applies the attester slashing at second
five, before the cutoff of that slot. The relay premise then applies to this
evidence.

The call from second six to seven reads the equivocation. It lowers the
child's safety threshold from 2760 to 2560 and confirms the child. The call
from second nine to ten confirms the epoch-two carrier in its own epoch. No
call selects a block of an earlier epoch, so the selected previous-result
proviso branch is not exercised by this run. `target_votes_support` proves
exact target support in this run. The accepted FFG interpretation and
positive Paper A3.2 support use the three votes in the slot-eight carrier.

The public non-vacuity, full-bundle, and safety theorems are at the end.
-/

namespace FastConfirmation.Spec
namespace ByzantinePremiseWitness

open ByzantineWitness
open ByzantineFFG

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
  obtain ⟨hslt, _, hk, ha'⟩ :=
    (witness_vote_some_iff (honest_ne_byzantine hi)).mp ha
  subst k
  subst a
  rw [slot_at_eq] at hfuture
  exact bounded_support ⟨v, hvlt⟩ ⟨n, hn⟩ ⟨s, hslt⟩ hepoch hfuture

private theorem bounded_previous_target_root_eq :
    ∀ (v : Fin 4) (n : Fin 15) (result : WitnessRoot),
      find_latest_confirmed_descendant witnessConfig witnessExternals
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v.val n.val)
        (witnessExecution.getLatestConfirmedTraceAt witnessConfig
          witnessExternals v.val n.val).afterObserved = result →
      result ≠ (witnessExecution.getLatestConfirmedTraceAt witnessConfig
          witnessExternals v.val n.val).afterObserved →
      get_block_epoch witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
          v.val n.val).store result ≠
        get_current_store_epoch witnessConfig
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
            v.val n.val).store →
      is_start_slot_at_epoch witnessConfig
        (get_current_slot witnessConfig
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
            v.val n.val).store) ≠ true →
      (get_current_target witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
          v.val n.val).store).root = result := by
  set_option maxRecDepth 50000 in decide

private theorem witnessSelectedHelperProvisos
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hH : witnessExecution.WithinHorizon witnessConfig (n + 1))
    (_hselector : getLatestSelectorGuard witnessConfig
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved) :
    SelectedPredictionVoteSupport witnessConfig witnessExternals witnessExecution v (n + 1)
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved := by
  have h := target_votes_support hv hH
  refine ⟨fun _ _ _ => h, ?_⟩
  intro result hout hstrict hprevious hnotStart
  have hn : n < 15 := by have := time_lt_sixteen hH; omega
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  have hroot := bounded_previous_target_root_eq ⟨v, hvlt⟩ ⟨n, hn⟩ result
    hout hstrict hprevious hnotStart
  refine ⟨hH, ?_⟩
  intro i hi sl hs hepoch hfuture k a ha
  have ht := h.2 i hi sl hs hepoch hfuture k a ha
  rw [ht]
  refine ⟨rfl, ?_⟩
  rw [hroot]
  exact .refl result

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
      carrierRoot = 2
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
    witnessExecution.BlockKnownInScheduledPrefix witnessConfig witnessExternals childRoot
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
        refine ⟨?_, Or.inl (vote_mem_ground (by decide))⟩
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
        refine ⟨?_, Or.inl (vote_mem_ground (by decide))⟩
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
        refine ⟨?_, Or.inl (vote_mem_ground (by decide))⟩
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
    witnessAcceptedChainFFGState.SourceTargetSupportThroughoutEpoch witnessConfig
      witnessExternals childRoot 1 := by
  intro w hw m hHm hepoch
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8slot
  refine ⟨hlate.child_known, ?_, ?_⟩
  · simpa only [hlate.child_epoch] using (by decide : 1 ≤ 1)
  intro tip htip hdesc
  have hsource :
      (witnessAcceptedChainFFGState.checkpoint_inclusion_view witnessConfig
        witnessExternals).voting_source_at witnessConfig
          (witnessExecution.store witnessConfig witnessExternals w m)
          childRoot 1 = anchorCheckpoint := by
    change (if get_block_epoch witnessConfig
        (witnessExecution.store witnessConfig witnessExternals w m)
          childRoot = 1 then
        witnessAcceptedChainFFGState.realized_justified childRoot
      else witnessAcceptedChainFFGState.unrealized_justified childRoot) = anchorCheckpoint
    rw [hlate.child_epoch]
    rfl
  simpa only [hsource, witnessC_child_one] using
    Nonempty.intro
      (witnessAnchorChildLinkSupportAt w m tip hHm hepoch)


private theorem witnessPaperA32Support_anchor_one_false :
    ¬ witnessAcceptedChainFFGState.SourceTargetSupportThroughoutEpoch
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
        ((witnessAcceptedChainFFGState.checkpoint_inclusion_view witnessConfig
          witnessExternals).C anchorRoot 1).root) = true := by
    simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view, witnessC_anchor_one] using
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
    simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view, witnessC_anchor_one] using
      htarget
  interval_cases s <;>
    simp [vote, voteData, anchorCheckpoint, childEpochOneCheckpoint,
      carrierEpochTwoCheckpoint, carrierEpochThreeCheckpoint,
      anchorRoot, childRoot, carrierRoot] at htarget'

/-! ## Universal Paper A3.2 -/

private theorem witnessPaperA32Inclusion :
    witnessAcceptedChainFFGState.EventualCheckpointInclusion witnessConfig
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
        refine ⟨anchorRoot, hlate.anchor_known, hlate.anchor_known,
          is_ancestor_refl _ _, ?_, Or.inl (Nat.zero_le _), ?_⟩
        · rw [hlate.anchor_epoch]
          decide
        · simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view,
            witnessC_anchor_zero] using witnessAU_anchor_anchor
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
              hlate.carrier_descends_child, ?_, Or.inr ?_, ?_⟩
            · rw [hlate.carrier_epoch]
              decide
            · rw [hlate.carrier_epoch]
              decide
            · simpa only [AcceptedBlockFFGState.checkpoint_inclusion_view,
                witnessC_child_one] using witnessAU_carrier_child
          · rcases h with ⟨rfl, rfl⟩
            norm_num [carrierSignedBlock, witnessConfig,
              compute_epoch_at_slot] at hbe
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
    witnessExecution.ImportedBlockFinalizationLag witnessConfig
      witnessExternals witnessAcceptedSemantics := by
  intro t
  change
    CheckpointReadsAs (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
        anchorCheckpoint ∨
      (t.postStore.block_states t.signedBlock.root
          ).finalized_checkpoint.epoch + 2 ≤
        compute_epoch_at_slot witnessConfig t.signedBlock.message.slot
  rcases acceptedTransition_cases t with h | h
  · left
    rw [h.1]
    apply CheckpointReadsAs.of_eq
    change (t.postStore.block_states childRoot).finalized_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl
  · left
    rw [h.1]
    apply CheckpointReadsAs.of_eq
    change (t.postStore.block_states carrierRoot).finalized_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl

def witnessCompletedPrefixCallAssumptions :
    witnessExecution.ScheduledFCRCallPremises
      witnessConfig witnessExternals where
  synchrony := witnessPaperSafetySynchrony
  static_validators := witnessStaticValidatorSet
  byzantine_bound := witnessByzantineBound
  phase0_source := witnessPhase0SourceCoherence
  phase0_boundary_source := witnessPhase0BoundarySourceCoherence
  balance_floor := witnessBalanceFloor

def witnessAcceptedActualFCRNextSlotSafetyAssumptions :
    witnessExecution.NextSlotSafetyPremises witnessConfig
      witnessExternals where
  ffg_interpretation := witnessAcceptedSemantics
  trajectory := witnessScheduledPrefixTrajectoryAssumptions
  completed_calls := witnessCompletedPrefixCallAssumptions
  epoch_ends_fit := witnessEpochEndsFitUint64
  anchor_eq := by
    simpa only [witnessAcceptedSemantics] using witnessAnchorEquality.symm
  anchor_state_checkpoints := Or.inl rfl
  anchor_boundary := by
    simpa only [witnessAcceptedSemantics] using
      witnessTrustedAnchorBoundaryAligned
  finalization_delay := by exact witnessAcceptedRealizedFinalizationDelay
  slots_per_epoch_gt_one := by decide
  checkpoint_inclusion := by exact witnessPaperA32Inclusion
  checkpoint_projection := witnessAcceptedEpochCheckpointProjection
  exact_link_validity := witnessExactLinkValidity

/-- The same FFG interpretation used by the premise bundle satisfies the
interpretation-fidelity record: each included vote is a valid body member of
its accepted carrier, validated on the prepared target state. -/
theorem ffg_interpretation_fidelity :
    FFGInterpretationFidelity witnessConfig witnessExternals witnessExecution
      witnessAcceptedActualFCRNextSlotSafetyAssumptions.ffg_interpretation where
  included_fidelity := by
    intro carrier a h
    exact witnessIncludedFidelity h
  realized_finalized_epoch_le_unrealized_finalized := by
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
          (1 ≤ GENESIS_EPOCH ∨ GENESIS_EPOCH + 1 < get_block_epoch witnessConfig
              (witnessExecution.store witnessConfig witnessExternals w m) b') ∧
          witnessAcceptedChainFFGState.AvailableCheckpoint witnessConfig witnessExternals b'
            (witnessAcceptedChainFFGState.checkpoint_at_epoch childRoot 1) := by
  exact witnessPaperA32Inclusion.included child_acceptedBlockAt
    (by decide) child_canonical_throughout_epoch_two
      witnessPaperA32Support_child_one

/-! ## Byzantine weight, equivocation, and slashing relay -/

/-- Validator 4 is outside the honest set. It has weight 200 of the total
active 4000, and it is 200 of the 1000 weight of the in-horizon span at slot
four. -/
theorem byzantine_weight_exercised :
    byzantineIndex ∉ witnessExecution.honest ∧
    witnessExecution.weight_of byzantineIndex = 200 ∧
    witnessExecution.total_active witnessConfig = 4000 ∧
    witnessExecution.SlotWithinHorizon witnessConfig 4 ∧
    witnessExecution.weight ((witnessExecution.span_committee 4 4).filter
      (fun i => i ∉ witnessExecution.honest)) = 200 ∧
    witnessExecution.weight (witnessExecution.span_committee 4 4) = 1000 ∧
    ∃ a b : Slot, witnessExecution.SlotWithinHorizon witnessConfig a ∧
      witnessExecution.SlotWithinHorizon witnessConfig b ∧
      0 < witnessExecution.weight ((witnessExecution.span_committee a b).filter
        (fun i => i ∉ witnessExecution.honest)) := by
  refine ⟨byzantine_not_honest, by decide, by decide,
    slot_within_of_lt_sixteen (by decide), by decide, by decide,
    4, 4, slot_within_of_lt_sixteen (by decide),
    slot_within_of_lt_sixteen (by decide), by decide⟩

/-- Validator 4 records one slot-four vote and signs a second vote with the
same target epoch. The slashing carries this slashable pair. -/
theorem byzantine_equivocation :
    witnessExecution.vote byzantineIndex 4 = some (4, byzantineVoteChild) ∧
    byzantineSlashing.attestation_1 = byzantineVoteChild ∧
    byzantineSlashing.attestation_2 = byzantineVoteAnchor ∧
    byzantineVoteChild.data ≠ byzantineVoteAnchor.data ∧
    byzantineVoteChild.data.target.epoch =
      byzantineVoteAnchor.data.target.epoch ∧
    is_slashable_attestation_data byzantineVoteChild.data
      byzantineVoteAnchor.data = true ∧
    byzantineIndex ∈ byzantineVoteChild.attesting_indices ∧
    byzantineIndex ∈ byzantineVoteAnchor.attesting_indices ∧
    byzantineIndex ∈ witnessExecution.committee 4 := by
  refine ⟨byzantine_vote_recorded, rfl, rfl, ?_⟩
  decide

/-- The exact scheduled prefix before the slashing event at second five. -/
def slashingPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 4
  processedCount := 1
  count_le := by decide

/-- Node 0 accepts the slashing event. Before second five no node holds the
evidence, and at second five every node holds it. -/
theorem slashing_applied_at_second_five (w : ValidatorIndex) :
    (witnessExecution.schedule 0 5)[1]? =
      some (Event.attester_slashing byzantineSlashing) ∧
    Event.attester_slashing byzantineSlashing ∈ witnessExecution.schedule w 5 ∧
    (on_attester_slashing witnessExternals
        (slashingPrefix.store witnessConfig witnessExternals)
        byzantineSlashing).map
      (fun post => decide (byzantineIndex ∈ post.equivocating_indices)) =
      some true ∧
    byzantineIndex ∉
      (witnessExecution.store witnessConfig witnessExternals w 4).equivocating_indices ∧
    byzantineIndex ∈
      (witnessExecution.store witnessConfig witnessExternals w 5).equivocating_indices := by
  rw [witness_store_symmetric w 0 4, witness_store_symmetric w 0 5]
  refine ⟨rfl, by simp [witnessExecution, witnessSchedule], ?_, ?_, ?_⟩ <;>
    decide

/-- The antecedent of `DeadlineAttesterSlashingRelay` holds for validator 4 at
honest node 0 and second five. Its conclusion also holds: every honest node
holds the index at every in-horizon second from six on. -/
theorem slashing_relay_exercised :
    0 ∈ witnessExecution.honest ∧
    witnessExecution.WithinHorizon witnessConfig 5 ∧
    byzantineIndex ∈
      (witnessExecution.store witnessConfig witnessExternals 0 5).equivocating_indices ∧
    5 ≤ witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig 5) +
      get_attestation_due_ms witnessConfig / 1000 ∧
    witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig 5 + 1) = 6 ∧
    ∀ w ∈ witnessExecution.honest, ∀ m,
      witnessExecution.WithinHorizon witnessConfig m →
      witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig 5 + 1) ≤ m → 5 < m →
      byzantineIndex ∈
        (witnessExecution.store witnessConfig witnessExternals w m).equivocating_indices := by
  have hH5 : witnessExecution.WithinHorizon witnessConfig 5 :=
    time_within_of_lt_sixteen (by decide)
  have hheld := (slashing_applied_at_second_five 0).2.2.2.2
  have hdue : 5 ≤ witnessExecution.slot_start witnessConfig
        (witnessExecution.slot_at witnessConfig 5) +
      get_attestation_due_ms witnessConfig / 1000 := by
    rw [slot_at_eq, slot_start_eq]
    exact Nat.le_add_right 5 _
  have hboundary : witnessExecution.slot_start witnessConfig
      (witnessExecution.slot_at witnessConfig 5 + 1) = 6 := by
    rw [slot_at_eq, slot_start_eq]
  refine ⟨by decide, hH5, hheld, hdue, hboundary, ?_⟩
  intro w _hw m _hm _hboundary hlt
  rw [← witness_store_symmetric 0 w m]
  exact (witnessExecution.store_storeLE witnessConfig witnessExternals 0
    hlt.le).2.2.1 hheld

/-- The later scheduled call from second six to seven reads the evidence.
Its equivocation score is 200, and the child's safety threshold is 2560. With
an empty equivocation set the same store would give threshold 2760. -/
theorem equivocation_read_at_call :
    witnessExecution.IsScheduledFCRCallAt witnessConfig witnessExternals 0 6 ∧
    byzantineIndex ∈ confirmingFcr.store.equivocating_indices ∧
    get_equivocation_score witnessConfig witnessExternals confirmingFcr.store
      (get_current_balance_source confirmingFcr) 4 6 = 200 ∧
    get_attestation_score witnessConfig confirmingFcr.store
      (get_node_for_root childRoot) (get_current_balance_source confirmingFcr) = 2800 ∧
    compute_safety_threshold witnessConfig witnessExternals confirmingFcr.store childRoot
      (get_current_balance_source confirmingFcr) = 2560 ∧
    compute_safety_threshold witnessConfig witnessExternals
      { confirmingFcr.store with equivocating_indices := ∅ } childRoot
      (get_current_balance_source confirmingFcr) = 2760 := by
  refine ⟨?_, ?_⟩
  · change get_current_slot witnessConfig
        (witnessExecution.store witnessConfig witnessExternals 0 7) >
      get_current_slot witnessConfig
        (witnessExecution.store witnessConfig witnessExternals 0 6)
    decide
  · decide

/-! ## Full bundle and safety -/

/-- Full next-slot safety premises with Byzantine weight and a relayed
slashing. The call from second six to seven changes the confirmed root. -/
theorem full_bundle_witness :
    Nonempty (witnessExecution.NextSlotSafetyPremises witnessConfig witnessExternals) ∧
    witnessConfig.slot_duration_ms = 1000 ∧
    byzantineIndex ∉ witnessExecution.honest ∧
    0 < witnessExecution.weight_of byzantineIndex ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 6 = anchorRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 7 = childRoot ∧
    childRoot ≠ anchorRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 9 = childRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 10 = carrierRoot := by
  refine ⟨⟨witnessAcceptedActualFCRNextSlotSafetyAssumptions⟩, rfl,
    byzantine_not_honest, by decide, ?_,
    actual_fcr_transition_strict_advance, by decide, ?_, ?_⟩
  all_goals set_option maxRecDepth 50000 in decide

/-- Apply the public safety theorem to the child output at second seven. -/
theorem changed_root_safe_from_next_slot (w m : ℕ)
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
  simpa only [actual_fcr_transition_strict_advance] using h.2

/-- Apply the public safety theorem to the carrier output at second ten. -/
theorem carrier_safe_from_next_slot (w m : ℕ)
    (hw : w ∈ witnessExecution.honest) (hm : 11 ≤ m)
    (hH : witnessExecution.WithinHorizon witnessConfig m) :
    is_ancestor (witnessExecution.store witnessConfig witnessExternals w m)
      (get_head witnessConfig (witnessExecution.store witnessConfig witnessExternals w m))
      (get_node_for_root carrierRoot) = true := by
  have hnext : witnessExecution.slot_at witnessConfig 10 + 1 ≤
      witnessExecution.slot_at witnessConfig m := by simpa only [slot_at_eq] using hm
  have hcarrier :
      witnessExecution.confirmed witnessConfig witnessExternals 0 10 = carrierRoot :=
    full_bundle_witness.2.2.2.2.2.2.2.2
  have h := confirmed_root_safe_from_next_slot witnessConfig witnessExternals
    witnessExecution witnessAcceptedActualFCRNextSlotSafetyAssumptions
    0 (by decide) 10 w hw m (by omega) hnext hH
  simpa only [hcarrier] using h.2

end ByzantinePremiseWitness
end FastConfirmation.Spec

end
