module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.FFGEvidence
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Safety.FinalizedCheckpointNextSlotSafety

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Joint accepted-FCR non-vacuity: paper inclusion and next-slot bundle

This file proves that one finite execution satisfies the complete next-slot
premise bundle. It combines the two parts of the horizon-four witness.  The
operational execution lives in `AcceptedActualFCRJointNonVacuityBase`; the
accepted FFG state and exact-link interpretation live in
`AcceptedActualFCRJointNonVacuityFFG`.  It supplies the paper A3.2 law, the
call-scoped helper provisos, and the public witness that packages them with the
reset-free accepted next-slot safety fold.

The finite reductions below are deliberately kept separate from the A3.2
argument.  They document the exact executable trajectory rather than hiding
it inside construction of the combined assumption record.
-/

namespace FastConfirmation.Spec
namespace NextSlotPremiseWitness

open AcceptedActualFCRJointNonVacuityBase
open AcceptedActualFCRJointNonVacuityFFG

/-! ## Exact executable FCR and reset classifiers -/

theorem confirmed_at_one {v : ValidatorIndex}
    (hv : v ∈ witnessExecution.honest) :
    witnessExecution.confirmed witnessConfig witnessExternals v 1 =
      anchorRoot := by
  rcases honest_eq_zero_or_one_or_two_or_three hv with
    rfl | rfl | rfl | rfl <;>
    set_option maxRecDepth 50000 in decide



/-! ## Positive next-slot finalized-reset regression -/





/-! ## Literal selected-helper provisos -/

private theorem bounded_no_currentTargetAcceptedEdge_under_selector :
    ∀ (v : Fin 4) (n : Fin 15) (a c : WitnessRoot),
      getLatestSelectorGuard witnessConfig
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
            v.val n.val)
          (witnessExecution.getLatestConfirmedTraceAt witnessConfig
            witnessExternals v.val n.val).afterObserved →
        (a, c) ∈
          (findLatestSelectedTrace witnessConfig witnessExternals
            (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
              v.val n.val)
            (witnessExecution.getLatestConfirmedTraceAt witnessConfig
              witnessExternals v.val n.val).afterObserved).2.2 →
        get_block_epoch witnessConfig
            (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
              v.val n.val).store a <
        get_block_epoch witnessConfig
            (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
              v.val n.val).store c →
        False := by
  simp only [getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide

private theorem bounded_no_previousAcceptedEdge_away_from_epoch_start :
    ∀ (v : Fin 4) (n : Fin 15) (a c : WitnessRoot),
      (a, c) ∈
          (findLatestSelectedTrace witnessConfig witnessExternals
            (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
              v.val n.val)
            (witnessExecution.getLatestConfirmedTraceAt witnessConfig
              witnessExternals v.val n.val).afterObserved).2.1 →
        is_start_slot_at_epoch witnessConfig
          (get_current_slot witnessConfig
            (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
              v.val n.val).store) ≠ true → False := by
  set_option maxRecDepth 50000 in decide

private theorem bounded_no_selectedPreviousResult_under_selector :
    ∀ (v : Fin 4) (n : Fin 15) (result : WitnessRoot),
      getLatestSelectorGuard witnessConfig
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
            v.val n.val)
          (witnessExecution.getLatestConfirmedTraceAt witnessConfig
            witnessExternals v.val n.val).afterObserved →
        find_latest_confirmed_descendant witnessConfig witnessExternals
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals
            v.val n.val)
          (witnessExecution.getLatestConfirmedTraceAt witnessConfig
            witnessExternals v.val n.val).afterObserved = result →
        result ≠
          (witnessExecution.getLatestConfirmedTraceAt witnessConfig
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
        False := by
  simp only [getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide

/-- Whenever the executable selector is actually enabled in this witness,
its current-target edge antecedent is empty.  Tentative edges computed at
guard-false queries are deliberately outside this call-scoped statement. -/
theorem no_currentTargetAcceptedEdge_under_selector
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hHn1 : witnessExecution.WithinHorizon witnessConfig (n + 1))
    (hselector : getLatestSelectorGuard witnessConfig
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved)
    (a c : WitnessRoot)
    (hedge : CurrentTargetSelectedEdge witnessConfig witnessExternals
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved a c) : False := by
  have hnlt := time_lt_sixteen hHn1
  have hnlt' : n < 15 := by omega
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  let vf : Fin 4 := ⟨v, hvlt⟩
  let nf : Fin 15 := ⟨n, hnlt'⟩
  rcases hedge with ⟨hmem, hlt⟩
  exact bounded_no_currentTargetAcceptedEdge_under_selector
    vf nf a c hselector hmem hlt

/-- A previous-loop edge can occur only through the epoch-start escape in
this witness, so the no-conflict proviso's non-start branch is empty. -/
theorem no_previousAcceptedEdge_away_from_epoch_start
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hHn1 : witnessExecution.WithinHorizon witnessConfig (n + 1))
    (a c : WitnessRoot)
    (hedge : PreviousEpochSelectedEdge witnessConfig witnessExternals
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved a c)
    (hnotStart : is_start_slot_at_epoch witnessConfig
      (get_current_slot witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n).store)
        ≠ true) : False := by
  have hnlt := time_lt_sixteen hHn1
  have hnlt' : n < 15 := by omega
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  let vf : Fin 4 := ⟨v, hvlt⟩
  let nf : Fin 15 := ⟨n, hnlt'⟩
  change (a, c) ∈
    (findLatestSelectedTrace witnessConfig witnessExternals
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved).2.1 at hedge
  exact bounded_no_previousAcceptedEdge_away_from_epoch_start
    vf nf a c hedge hnotStart

/-- At an actual selector invocation, the strict selected-result antecedent
from a previous block epoch is empty in this finite prefix. -/
theorem no_selectedPreviousResult_under_selector
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hHn1 : witnessExecution.WithinHorizon witnessConfig (n + 1))
    (hselector : getLatestSelectorGuard witnessConfig
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved)
    (result : WitnessRoot)
    (hout : find_latest_confirmed_descendant witnessConfig witnessExternals
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved = result)
    (hstrict : result ≠
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved)
    (hprevious : get_block_epoch witnessConfig
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n).store
        result ≠ get_current_store_epoch witnessConfig
          (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n).store)
    (hnotStart : is_start_slot_at_epoch witnessConfig
      (get_current_slot witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n).store)
        ≠ true) : False := by
  have hnlt := time_lt_sixteen hHn1
  have hnlt' : n < 15 := by omega
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;> decide
  let vf : Fin 4 := ⟨v, hvlt⟩
  let nf : Fin 15 := ⟨n, hnlt'⟩
  exact bounded_no_selectedPreviousResult_under_selector
    vf nf result hselector hout hstrict hprevious hnotStart

theorem witnessSelectedHelperProvisos
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hHn1 : witnessExecution.WithinHorizon witnessConfig (n + 1))
    (hselector : getLatestSelectorGuard witnessConfig
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved) :
    FCRPredictionSupportAt witnessConfig witnessExternals witnessExecution
      v (n + 1)
      (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n)
      (witnessExecution.getLatestConfirmedTraceAt witnessConfig
        witnessExternals v n).afterObserved := by
  refine
    { current_target := ?_
      no_conflict := ?_
      selected_previous_result_no_conflict := ?_ }
  · intro a c hedge
    exact False.elim
      (no_currentTargetAcceptedEdge_under_selector
        hv hHn1 hselector a c hedge)
  · intro a c hedge hnotStart
    exact False.elim
      (no_previousAcceptedEdge_away_from_epoch_start
        hv hHn1 a c hedge hnotStart)
  · intro result hout hstrict hprevious hnotStart
    exact False.elim
      (no_selectedPreviousResult_under_selector hv hHn1 hselector
        result hout hstrict hprevious hnotStart)

/-! ## Concrete late-prefix geometry used by Paper A3.2 -/

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
      childRoot = 0
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

theorem lateStoreFacts (w : ValidatorIndex) (m : ℕ)
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (h8m : 8 ≤ witnessExecution.slot_at witnessConfig m) :
    LateStoreFacts w m := by
  have hmlt := time_lt_sixteen hHm
  rw [slot_at_eq] at h8m
  constructor <;>
    rw [witness_store_symmetric w 0 m] <;>
    interval_cases m <;>
    set_option maxRecDepth 50000 in decide

theorem slot_at_ge_eight_of_epoch_two {m : ℕ}
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (hepoch : compute_epoch_at_slot witnessConfig
      (witnessExecution.slot_at witnessConfig m) = 2) :
    8 ≤ witnessExecution.slot_at witnessConfig m := by
  have hmlt := time_lt_sixteen hHm
  rw [slot_at_eq] at hepoch ⊢
  interval_cases m <;>
    norm_num [witnessConfig, compute_epoch_at_slot] at hepoch <;>
    norm_num

theorem vote_received_by_from_eight {w : ValidatorIndex} {m : ℕ}
    {s : Slot} (hs4 : 4 ≤ s) (hs6 : s ≤ 6) (hm8 : 8 ≤ m) :
    witnessExecution.AttestationReceivedBy w m (vote s) := by
  refine ⟨s + 1, ?_, false, ?_⟩
  · exact (Nat.succ_le_succ hs6).trans (by omega : 7 ≤ m)
  change Event.attestation (vote s) false ∈ witnessSchedule w (s + 1)
  interval_cases s <;>
    simp [witnessSchedule, vote4, vote5, vote6]

theorem child_acceptedBlockAt :
    witnessExecution.AcceptedBlockAt witnessConfig witnessExternals childRoot
      childSignedBlock.message := by
  refine ⟨childTransition.postStore, childTransition.post_causal, ?_, ?_⟩
  · simpa [childSignedBlock] using childTransition.root_known
  · simpa [childSignedBlock] using
      childTransition.inserted_message_fresh (by
        set_option maxRecDepth 50000 in decide)

theorem child_canonical_throughout_epoch_two :
    witnessExecution.CanonicalThroughoutEpoch witnessConfig witnessExternals
      childRoot 2 := by
  intro w hw m hHm hepoch
  have h8m := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8m
  exact ⟨hlate.child_known, hlate.head_descends_child⟩


/-! ## Exact positive Paper A3.2 support -/

noncomputable def witnessAnchorChildLinkSupportAt
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
      signers := {0, 1, 2}
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
  · simpa only [hlate.child_epoch] using (by decide : 0 ≤ 1)
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


theorem witnessPaperA32Support_anchor_one_false :
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

theorem witnessPaperA32Inclusion :
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
        refine ⟨carrierRoot, hlate.carrier_known, hlate.child_known,
          hlate.carrier_descends_child, ?_, ?_⟩
        · rw [hlate.carrier_epoch]
          decide
        · simpa only [CausalCarrierFFGState.paperA32Inputs,
            witnessC_child_zero] using witnessAU_carrier_anchor
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

theorem witnessAcceptedRealizedFinalizationDelay :
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
  finalization_delay := witnessAcceptedRealizedFinalizationDelay
  slots_per_epoch_gt_one := by decide
  paper_a32 := witnessPaperA32Inclusion
  checkpoint_projection := witnessAcceptedEpochCheckpointProjection
  exact_link_validity := witnessExactLinkValidity

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

theorem second_sixteen_outside_horizon :
    ¬ witnessExecution.WithinHorizon witnessConfig 16 := by
  intro hH16
  exact (Nat.lt_irrefl 16) (time_lt_sixteen hH16)

structure JointWitnessFacts : Prop where
  assumptions : Nonempty
    (witnessExecution.NextSlotSafetyPremises witnessConfig
      witnessExternals)
  strict_call : witnessExecution.IsScheduledFCRCallAt witnessConfig witnessExternals 0 1
  strict_input : witnessExecution.confirmed witnessConfig witnessExternals
    0 1 = anchorRoot
  strict_output : witnessExecution.confirmed witnessConfig witnessExternals
    0 2 = childRoot
  strict_changes_root : childRoot ≠ anchorRoot
  exact_selector : find_latest_confirmed_descendant witnessConfig
    witnessExternals confirmingFcr anchorRoot = childRoot
  substantive_a32_support :
    witnessAcceptedChainFFGState.PaperA32SupportThroughoutEpoch witnessConfig
      witnessExternals childRoot 1
  substantive_a32_conclusion :
    ∃ b' ∈
        (witnessExecution.store witnessConfig witnessExternals 0 12
          ).block_roots,
      childRoot ∈
          (witnessExecution.store witnessConfig witnessExternals 0 12
            ).block_roots ∧
        is_ancestor
          (witnessExecution.store witnessConfig witnessExternals 0 12)
          (get_node_for_root b') (get_node_for_root childRoot) = true ∧
        get_block_epoch witnessConfig
            (witnessExecution.store witnessConfig witnessExternals 0 12) b' <
          3 ∧
        witnessAcceptedChainFFGState.AU witnessConfig witnessExternals b'
          (witnessAcceptedChainFFGState.C childRoot 1)
  final_vote_ground : witnessExecution.vote 3 15 = some (15, vote15)
  final_vote_delivery : Event.attestation vote15 false ∈
    witnessExecution.schedule 0 16
  delivery_is_outside_horizon :
    ¬ witnessExecution.WithinHorizon witnessConfig 16
  public_safety_at_end : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals 0 15)
    (get_head witnessConfig
      (witnessExecution.store witnessConfig witnessExternals 0 15))
    (get_node_for_root childRoot) = true

theorem finite_execution_satisfies_premises : JointWitnessFacts := by
  refine
    { assumptions := ⟨witnessAcceptedActualFCRNextSlotSafetyAssumptions⟩
      strict_call := by
        change get_current_slot witnessConfig
            (witnessExecution.store witnessConfig witnessExternals 0 2) >
          get_current_slot witnessConfig
            (witnessExecution.store witnessConfig witnessExternals 0 1)
        set_option maxRecDepth 50000 in decide
      strict_input := confirmed_at_one (by decide)
      strict_output := actual_fcr_transition_strict_advance
      strict_changes_root := by decide
      exact_selector := find_latest_confirmed_descendant_strict_advance
      substantive_a32_support := witnessPaperA32Support_child_one
      substantive_a32_conclusion := ?_
      final_vote_ground := by decide
      final_vote_delivery := witness_slot15_delivery_at_second16 0
      delivery_is_outside_horizon := second_sixteen_outside_horizon
      public_safety_at_end := ?_ }
  · exact witnessPaperA32_child_one_conclusion 0 (by decide) 12
      (time_within_of_lt_sixteen (by decide)) (by decide)
  · have hsafe :=
      Execution.NextSlotSafetyPremises.confirmed_head_nextSlot
        witnessConfig witnessExternals witnessExecution
        witnessAcceptedActualFCRNextSlotSafetyAssumptions
        (v := 0) (n := 2) (w := 0) (m := 15)
        (by decide) (by decide) (by decide) (by decide)
        (time_within_of_lt_sixteen (by decide))
    simpa only [actual_fcr_transition_strict_advance] using hsafe

theorem next_slot_premises_nonempty :
    ∃ (cfg : Config) (ext : Externals WitnessRoot)
      (E : Execution WitnessRoot),
      Nonempty (E.NextSlotSafetyPremises cfg ext) := by
  exact ⟨witnessConfig, witnessExternals, witnessExecution,
    ⟨witnessAcceptedActualFCRNextSlotSafetyAssumptions⟩⟩

end NextSlotPremiseWitness
end FastConfirmation.Spec

end
