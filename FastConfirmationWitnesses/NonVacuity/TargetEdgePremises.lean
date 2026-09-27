module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.TargetEdgeRun
public import FastConfirmationProofs.ReviewTheorem
public import FastConfirmationInternal.FFG.InterpretationFidelity

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Current-target-edge witness: the safety premise with a selected edge

The run of `TargetEdgeBridgeRun` satisfies the public safety premise
`ConcreteBridge.SafetyPremises`. The call from second six to seven selects the
epoch-one child from the previous-epoch anchor. Its selector guard is true,
the retained tentative trace contains that edge, and an honest vote at slot
seven still supports the same target. `target_votes_support` proves the
support consequent for every in-horizon call. Paper A3.2 uses the three votes
in the body of the slot-eight carrier.
-/

namespace FastConfirmation.Spec
namespace TargetEdgePremiseWitness

open ConcreteFFG
open TargetEdgeBridgeRun

/-! ## Scheduled prefixes and known blocks -/

def childPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 3
  processedCount := 0
  count_le := by decide

def childPostPrefix : witnessExecution.ScheduledEventPrefix :=
  childPrefix.successor (by decide)

/-- At second eight the first event is the ordinary slot-seven receipt; the
carrier block is the exact next event. -/
def carrierPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 7
  processedCount := 1
  count_le := by decide

def carrierPostPrefix : witnessExecution.ScheduledEventPrefix :=
  carrierPrefix.successor (by decide)

theorem child_known_post :
    childRoot ∈ (childPostPrefix.store witnessConfig witnessExternals).block_roots := by
  set_option maxRecDepth 100000 in decide +kernel

theorem carrier_known_post :
    carrierRoot ∈ (carrierPostPrefix.store witnessConfig witnessExternals).block_roots := by
  set_option maxRecDepth 100000 in decide +kernel

theorem anchor_accepted :
    witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessExternals anchorRoot :=
  ⟨witnessExecution.genesis_store, .genesis, (genesis_roots_iff anchorRoot).mpr rfl⟩

theorem child_accepted :
    witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessExternals childRoot :=
  ⟨_, .scheduledPrefix childPostPrefix, child_known_post⟩

theorem carrier_accepted :
    witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessExternals carrierRoot :=
  ⟨_, .scheduledPrefix carrierPostPrefix, carrier_known_post⟩

theorem child_acceptedBlockAt :
    witnessExecution.BlockKnownInScheduledPrefix witnessConfig witnessExternals childRoot
      childSignedBlock.message := by
  refine ⟨_, .scheduledPrefix childPostPrefix, child_known_post, ?_⟩
  set_option maxRecDepth 100000 in decide +kernel

theorem carrier_acceptedBlockAt :
    witnessExecution.BlockKnownInScheduledPrefix witnessConfig witnessExternals carrierRoot
      carrierSignedBlock.message := by
  refine ⟨_, .scheduledPrefix carrierPostPrefix, carrier_known_post, ?_⟩
  set_option maxRecDepth 100000 in decide +kernel

/-! ## Finite block projection of every causal prefix -/

theorem scheduledBlock_cases {b : SignedBeaconBlock WitnessRoot}
    (h : IsScheduledBlock witnessExecution b) :
    b = childSignedBlock ∨ b = carrierSignedBlock := by
  obtain ⟨w, n, hmem⟩ := h
  rcases block_mem_schedule_iff.mp hmem with hchild | hcarrier
  · exact Or.inl hchild.2
  · exact Or.inr hcarrier.2

theorem genesis_blocks_anchor :
    witnessExecution.genesis_store.blocks anchorRoot = anchorSignedBlock.message := by
  set_option maxRecDepth 100000 in decide +kernel

/-- Causal stores range over arbitrary nodes, seconds, and prefix lengths, but
their known blocks have only these three rows. -/
theorem causal_known_table {store : Store WitnessRoot}
    (hstore : witnessExecution.ScheduledPrefixStore witnessConfig witnessExternals store)
    {r : WitnessRoot} (hr : r ∈ store.block_roots) :
    (r = anchorRoot ∧ store.blocks r = anchorSignedBlock.message) ∨
      (r = childRoot ∧ store.blocks r = childSignedBlock.message) ∨
      (r = carrierRoot ∧ store.blocks r = carrierSignedBlock.message) := by
  rcases hstore.blockProvenance witnessConfig witnessExternals witnessExecution r hr with
    hgen | hsched
  · have hrAnchor : r = anchorRoot := (genesis_roots_iff r).mp hgen.1
    left
    refine ⟨hrAnchor, ?_⟩
    rw [hgen.2, hrAnchor]
    exact genesis_blocks_anchor
  · obtain ⟨b, hb, hroot, hmessage⟩ := hsched
    rcases scheduledBlock_cases hb with rfl | rfl
    · right; left
      exact ⟨hroot.symm, hmessage⟩
    · right; right
      exact ⟨hroot.symm, hmessage⟩

theorem acceptedRoot_cases {r : WitnessRoot}
    (hr : witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessExternals r) :
    r = anchorRoot ∨ r = childRoot ∨ r = carrierRoot := by
  obtain ⟨store, hstore, hknown⟩ := hr
  rcases causal_known_table hstore hknown with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

theorem acceptedBlockAt_cases {r : WitnessRoot} {b : BeaconBlock WitnessRoot}
    (h : witnessExecution.BlockKnownInScheduledPrefix witnessConfig witnessExternals r b) :
    (r = anchorRoot ∧ b = anchorSignedBlock.message) ∨
      (r = childRoot ∧ b = childSignedBlock.message) ∨
      (r = carrierRoot ∧ b = carrierSignedBlock.message) := by
  obtain ⟨store, hstore, hr, hblock⟩ := h
  rcases causal_known_table hstore hr with h | h | h
  · left; exact ⟨h.1, hblock.symm.trans h.2⟩
  · right; left; exact ⟨h.1, hblock.symm.trans h.2⟩
  · right; right; exact ⟨h.1, hblock.symm.trans h.2⟩

/-! ## Concrete execution descent -/

theorem child_parentEdge : witnessExecution.ParentEdge childRoot anchorRoot :=
  Or.inr ⟨0, 4, childSignedBlock, block_mem_schedule_iff.mpr (Or.inl ⟨rfl, rfl⟩), rfl, rfl⟩

theorem carrier_parentEdge : witnessExecution.ParentEdge carrierRoot childRoot :=
  Or.inr ⟨0, 8, carrierSignedBlock, block_mem_schedule_iff.mpr (Or.inr ⟨rfl, rfl⟩), rfl, rfl⟩

theorem child_descends_anchor : witnessExecution.RootDescends childRoot anchorRoot :=
  .step child_parentEdge (.refl anchorRoot)

theorem carrier_descends_child : witnessExecution.RootDescends carrierRoot childRoot :=
  .step carrier_parentEdge (.refl childRoot)

theorem carrier_descends_anchor : witnessExecution.RootDescends carrierRoot anchorRoot :=
  Execution.RootDescends.trans witnessExecution carrier_descends_child child_descends_anchor

theorem parentEdge_val_lt {child parent : WitnessRoot}
    (h : witnessExecution.ParentEdge child parent) : parent.val < child.val := by
  rcases h with hgen | hsched
  · obtain ⟨r, hr, rfl, rfl⟩ := hgen
    have hrAnchor : child = anchorRoot := (genesis_roots_iff child).mp hr
    subst child
    change (witnessExecution.genesis_store.blocks anchorRoot).parent_root.val < 1
    rw [genesis_blocks_anchor]
    decide
  · obtain ⟨w, n, b, hb, hchild, hparent⟩ := hsched
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hchild, hparent]
      decide
    · rw [hchild, hparent]
      decide

theorem rootDescends_val_le {source target : WitnessRoot}
    (h : witnessExecution.RootDescends source target) : target.val ≤ source.val := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact ih.trans (Nat.le_of_lt (parentEdge_val_lt hedge))

theorem rootDescends_carrier_iff {r : WitnessRoot} :
    witnessExecution.RootDescends r carrierRoot ↔ r = carrierRoot := by
  constructor
  · intro hdesc
    have hle := rootDescends_val_le hdesc
    change 3 ≤ r.val at hle
    apply Fin.ext
    change r.val = 3
    have hrlt := r.isLt
    omega
  · rintro rfl
    exact .refl carrierRoot

/-! ## The bridge view -/

/-- The paper A3.2 view of the run. -/
noncomputable abbrev witnessView : CheckpointInclusionView witnessConfig witnessExecution :=
  witnessBridge.checkpointInclusionView witnessExecution

theorem known_bridge {r : WitnessRoot}
    (h : witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessExternals r) :
    witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessBridge.interface r := by
  rw [interface_eq]
  exact h

theorem known_of_bridge {r : WitnessRoot}
    (h : witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessBridge.interface r) :
    witnessExecution.RootKnownInScheduledPrefix witnessConfig witnessExternals r := by
  rw [← interface_eq]
  exact h

theorem blockAt_cases {r : WitnessRoot} {b : BeaconBlock WitnessRoot}
    (h : witnessView.BlockAt r b) :
    (r = anchorRoot ∧ b = anchorSignedBlock.message) ∨
      (r = childRoot ∧ b = childSignedBlock.message) ∨
      (r = carrierRoot ∧ b = carrierSignedBlock.message) := by
  change witnessExecution.BlockKnownInScheduledPrefix witnessConfig witnessBridge.interface r b
    at h
  rw [interface_eq] at h
  exact acceptedBlockAt_cases h

theorem checkpointAt_anchor_zero : witnessView.C anchorRoot 0 = anchorCheckpoint := by
  decide +kernel

theorem checkpointAt_child_one : witnessView.C childRoot 1 = childEpochOneCheckpoint := by
  decide +kernel

theorem checkpointAt_anchor_one :
    witnessView.C anchorRoot 1 = ({ epoch := 1, root := anchorRoot } : Checkpoint WitnessRoot) := by
  decide +kernel

theorem gj_child : witnessView.GJ childRoot = anchorCheckpoint := by
  decide +kernel

theorem realizedJustified_anchor :
    witnessBridge.realizedJustified anchorRoot = anchorCheckpoint := by
  decide +kernel

theorem realizedJustified_child : witnessBridge.realizedJustified childRoot = anchorCheckpoint := by
  decide +kernel

theorem unrealizedJustified_carrier :
    witnessBridge.unrealizedJustified carrierRoot = childEpochOneCheckpoint := by
  decide +kernel

theorem formed_anchor_anchor : witnessView.formed anchorRoot anchorCheckpoint :=
  ⟨known_bridge anchor_accepted, Or.inl realizedJustified_anchor.symm⟩

theorem formed_carrier_child : witnessView.formed carrierRoot childEpochOneCheckpoint :=
  ⟨known_bridge carrier_accepted, Or.inr (Or.inr (Or.inl unrealizedJustified_carrier.symm))⟩

/-! ### Body votes and `D_b` -/

theorem indexed_wireVote {s : Slot} (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    witnessBridge.indexed (wireVote s) = vote s := by
  rw [indexed_eq_indexedList]
  interval_cases s <;> decide +kernel

/-- The body votes of the accepted blocks of the run are the three carrier
votes. -/
theorem bodyIncluded_cases {carrier : WitnessRoot} {a : Attestation WitnessRoot}
    (h : witnessView.Included carrier a) :
    carrier = carrierRoot ∧ (a = vote 4 ∨ a = vote 5 ∨ a = vote 6) := by
  obtain ⟨-, -, wire, stateRoot, hopen, vote', hmem, rfl⟩ := h
  have hentry := List.mem_of_find?_eq_some (Option.map_eq_some_iff.mp hopen).choose_spec.1
  have hkey : ((Option.map_eq_some_iff.mp hopen).choose).1 = carrier := by
    simpa using List.find?_some (Option.map_eq_some_iff.mp hopen).choose_spec.1
  have hval := (Option.map_eq_some_iff.mp hopen).choose_spec.2
  revert hentry hkey hval
  generalize (Option.map_eq_some_iff.mp hopen).choose = e
  intro hentry hkey hval
  simp only [blockEntries, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl
  · simp only [Prod.mk.injEq] at hval
    rw [← hval.1] at hmem
    simp [childWire] at hmem
  · simp only [Prod.mk.injEq] at hval
    rw [← hval.1] at hmem
    refine ⟨hkey.symm, ?_⟩
    simp only [carrierWire, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact Or.inl (indexed_wireVote (by decide) (by decide))
    · exact Or.inr (Or.inl (indexed_wireVote (by decide) (by decide)))
    · exact Or.inr (Or.inr (indexed_wireVote (by decide) (by decide)))

theorem witness_hasSlashablePairOnChain_false (tip : WitnessRoot) (i : ValidatorIndex) :
    ¬ witnessView.HasSlashablePairOnChain witnessConfig tip i := by
  rintro ⟨a₁, a₂, ⟨carrier₁, -, hinc₁⟩, ⟨carrier₂, -, hinc₂⟩, hi₁, hi₂, hslash⟩
  obtain ⟨-, h₁⟩ := bodyIncluded_cases hinc₁
  obtain ⟨-, h₂⟩ := bodyIncluded_cases hinc₂
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    simp_all [vote, voteData, is_slashable_attestation_data, committeeIndex]

theorem witness_slashableOnChain_eq_empty (tip : WitnessRoot) :
    witnessView.slashableOnChain witnessConfig tip = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  unfold CheckpointInclusionView.slashableOnChain at hi
  exact witness_hasSlashablePairOnChain_false tip i (Finset.mem_filter.mp hi).2

/-! ## Late-prefix geometry -/

structure LateStoreFacts (w : ValidatorIndex) (m : ℕ) : Prop where
  anchor_known : anchorRoot ∈
    (witnessExecution.store witnessConfig witnessExternals w m).block_roots
  child_known : childRoot ∈
    (witnessExecution.store witnessConfig witnessExternals w m).block_roots
  carrier_known : carrierRoot ∈
    (witnessExecution.store witnessConfig witnessExternals w m).block_roots
  child_target_key : childEpochOneCheckpoint ∈
    (witnessExecution.store witnessConfig witnessExternals w m).checkpoint_state_keys
  anchor_epoch : get_block_epoch witnessConfig
    (witnessExecution.store witnessConfig witnessExternals w m) anchorRoot = 0
  child_epoch : get_block_epoch witnessConfig
    (witnessExecution.store witnessConfig witnessExternals w m) childRoot = 1
  carrier_epoch : get_block_epoch witnessConfig
    (witnessExecution.store witnessConfig witnessExternals w m) carrierRoot = 2
  carrier_descends_anchor : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_node_for_root carrierRoot) (get_node_for_root anchorRoot) = true
  carrier_descends_child : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_node_for_root carrierRoot) (get_node_for_root childRoot) = true
  head_descends_child : is_ancestor
    (witnessExecution.store witnessConfig witnessExternals w m)
      (get_head witnessConfig (witnessExecution.store witnessConfig witnessExternals w m))
      (get_node_for_root childRoot) = true

theorem lateStoreFacts (w : ValidatorIndex) (m : ℕ)
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (h8m : 8 ≤ witnessExecution.slot_at witnessConfig m) :
    LateStoreFacts w m := by
  have hmlt := time_lt_sixteen hHm
  rw [slot_at_eq] at h8m
  constructor <;> rw [witness_store_symmetric w 0 m] <;> interval_cases m <;>
    (set_option maxRecDepth 100000 in decide +kernel)

theorem slot_at_ge_eight_of_epoch_two {m : ℕ}
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (hepoch : compute_epoch_at_slot witnessConfig (witnessExecution.slot_at witnessConfig m) = 2) :
    8 ≤ witnessExecution.slot_at witnessConfig m := by
  have hmlt := time_lt_sixteen hHm
  rw [slot_at_eq] at hepoch ⊢
  interval_cases m <;> norm_num [witnessConfig, compute_epoch_at_slot] at hepoch <;> norm_num

theorem vote_received_by_from_eight {w : ValidatorIndex} {m : ℕ} {s : Slot}
    (hs4 : 4 ≤ s) (hs6 : s ≤ 6) (hm8 : 8 ≤ m) :
    witnessExecution.AttestationReceivedBy w m (vote s) := by
  refine ⟨s + 1, ?_, false, ?_⟩
  · exact (Nat.succ_le_succ hs6).trans (by omega : 7 ≤ m)
  change Event.attestation (vote s) false ∈ witnessSchedule w (s + 1)
  interval_cases s <;> simp [witnessSchedule]

theorem child_canonical_throughout_epoch_two :
    witnessExecution.CanonicalThroughoutEpoch witnessConfig witnessBridge.interface
      childRoot 2 := by
  rw [interface_eq]
  intro w hw m hHm hepoch
  have h8m := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8m
  exact ⟨hlate.child_known, hlate.head_descends_child⟩

/-! ## Paper A3.2 support -/

theorem registry_length : witnessExecution.registry.length = 4 := by
  rw [registry_eq]
  rfl

/-- The anchor-to-child link support at one view in epoch 2. -/
noncomputable def witnessAnchorChildLinkSupportAt (w : ValidatorIndex) (m : ℕ) (tip : WitnessRoot)
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (hepoch : compute_epoch_at_slot witnessConfig (witnessExecution.slot_at witnessConfig m) = 2) :
    SourceTargetLinkSupportAt witnessConfig witnessExternals witnessView w m tip
      anchorCheckpoint childEpochOneCheckpoint := by
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have h8m : 8 ≤ m := by simpa only [slot_at_eq] using h8slot
  have hlate := lateStoreFacts w m hHm h8slot
  have hkeyed : ((witnessExecution.store witnessConfig witnessExternals w m).checkpoint_states
      childEpochOneCheckpoint).validators = witnessScope.validators := by
    rw [← registry_eq]
    exact (witnessStore_registryConstant w m).2 _ hlate.child_target_key
  have hvalid : ∀ s, 4 ≤ s → s ≤ 6 → witnessExternals.is_valid_indexed_attestation
      ((witnessExecution.store witnessConfig witnessExternals w m).checkpoint_states
        childEpochOneCheckpoint) (vote s) = true := by
    intro s _ hs6
    have hs16 : s < 16 := hs6.trans_lt (by decide)
    refine (witness_valid_iff _ _).2 ⟨ground_structure hkeyed, ?_, vote_mem_ground hs16⟩
    rw [hkeyed]
    decide
  refine
    { view_within_horizon := hHm
      source_before_target := by decide
      target_epoch_within := by decide
      target_known := hlate.child_known
      target_state_keyed := hlate.child_target_key
      signers := {1, 2, 3}
      signers_not_slashable := ?_
      signers_in_registry := ?_
      signer_attestation := ?_
      supermajority := by decide +kernel }
  · intro i _
    rw [witness_slashableOnChain_eq_empty]
    simp
  · intro i hi
    rw [registry_length]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · refine ⟨vote 6, vote_received_by_from_eight (s := 6) (by decide) (by decide) h8m, ?_,
        hvalid 6 (by decide) (by decide), slot_within_of_lt_sixteen (by decide), ?_, ?_, ?_,
        Or.inl rfl, rfl⟩
      · decide
      · simpa only [vote_data_slot, slot_at_eq] using (by omega : 6 ≤ m)
      · decide
      · decide
    · refine ⟨vote 5, vote_received_by_from_eight (s := 5) (by decide) (by decide) h8m, ?_,
        hvalid 5 (by decide) (by decide), slot_within_of_lt_sixteen (by decide), ?_, ?_, ?_,
        Or.inl rfl, rfl⟩
      · decide
      · simpa only [vote_data_slot, slot_at_eq] using (by omega : 5 ≤ m)
      · decide
      · decide
    · refine ⟨vote 4, vote_received_by_from_eight (s := 4) (by decide) (by decide) h8m, ?_,
        hvalid 4 (by decide) (by decide), slot_within_of_lt_sixteen (by decide), ?_, ?_, ?_,
        Or.inl rfl, rfl⟩
      · decide
      · simpa only [vote_data_slot, slot_at_eq] using (by omega : 4 ≤ m)
      · decide
      · decide

theorem witnessPaperA32Support_child_one :
    SourceTargetSupportThroughoutEpoch witnessConfig witnessBridge.interface witnessView
      childRoot 1 := by
  rw [interface_eq]
  intro w hw m hHm hepoch
  have h8slot := slot_at_ge_eight_of_epoch_two hHm hepoch
  have hlate := lateStoreFacts w m hHm h8slot
  refine ⟨hlate.child_known, ?_, ?_⟩
  · rw [hlate.child_epoch]
  intro tip _ _
  have hsource : witnessView.voting_source_at witnessConfig
      (witnessExecution.store witnessConfig witnessExternals w m) childRoot 1 =
        anchorCheckpoint := by
    unfold CheckpointInclusionView.voting_source_at
    rw [hlate.child_epoch, if_pos rfl, gj_child]
  rw [hsource, checkpointAt_child_one]
  exact ⟨witnessAnchorChildLinkSupportAt w m tip hHm hepoch⟩

theorem witnessPaperA32Support_anchor_one_false :
    ¬ SourceTargetSupportThroughoutEpoch witnessConfig witnessBridge.interface witnessView
      anchorRoot 1 := by
  rw [interface_eq]
  intro hsupport
  have hH8 : witnessExecution.WithinHorizon witnessConfig 8 :=
    time_within_of_lt_sixteen (by decide)
  have hepoch8 :
      compute_epoch_at_slot witnessConfig (witnessExecution.slot_at witnessConfig 8) = 2 := by
    rw [slot_at_eq]
    decide
  obtain ⟨_, _, hall⟩ := hsupport 0 (by decide) 8 hH8 hepoch8
  have hlate := lateStoreFacts 0 8 hH8 (by rw [slot_at_eq])
  have hdesc : is_ancestor (witnessExecution.store witnessConfig witnessExternals 0 8)
      (get_node_for_root carrierRoot)
      (get_node_for_root (witnessView.C anchorRoot 1).root) = true := by
    rw [checkpointAt_anchor_one]
    exact hlate.carrier_descends_anchor
  obtain ⟨L⟩ := hall carrierRoot hlate.carrier_known hdesc
  have hsigners : L.signers.Nonempty := by
    by_contra hnone
    have hempty : L.signers = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * witnessExecution.total_active witnessConfig ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty, Nat.mul_zero] using
        L.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega) (witnessExecution.total_active_pos witnessConfig))
  obtain ⟨i, hi⟩ := hsigners
  obtain ⟨a, hreceived, -, -, -, -, -, -, -, htarget⟩ := L.signer_attestation i hi
  obtain ⟨k, -, fromBlock, hmem⟩ := hreceived
  obtain ⟨s, hslt, rfl⟩ := groundVote_exists (attestation_mem_schedule_ground hmem)
  rw [checkpointAt_anchor_one] at htarget
  interval_cases s <;>
    simp [vote, voteData, anchorCheckpoint, childEpochOneCheckpoint, carrierEpochTwoCheckpoint,
      carrierEpochThreeCheckpoint, anchorRoot, childRoot, carrierRoot] at htarget

/-! ## Paper A3.2 -/

theorem witnessPaperA32Inclusion :
    EventualCheckpointInclusion witnessConfig witnessBridge.interface witnessView := by
  constructor
  intro b bb e hb hbe hcanonical hsupport w hw m hHm hboundary
  rw [interface_eq]
  cases e with
  | zero =>
      have h8slot : 8 ≤ witnessExecution.slot_at witnessConfig m := by
        simpa [compute_start_slot_at_epoch, witnessConfig] using hboundary
      have hlate := lateStoreFacts w m hHm h8slot
      rcases blockAt_cases hb with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨anchorRoot, hlate.anchor_known, hlate.anchor_known, is_ancestor_refl _ _, ?_,
          Or.inl (Nat.zero_le _), ?_⟩
        · rw [hlate.anchor_epoch]
          decide
        · rw [checkpointAt_anchor_zero]
          exact ⟨anchorRoot, .refl anchorRoot, formed_anchor_anchor⟩
      · rcases h with ⟨rfl, rfl⟩
        norm_num [childSignedBlock, witnessConfig, compute_epoch_at_slot] at hbe
      · rcases h with ⟨rfl, rfl⟩
        norm_num [carrierSignedBlock, witnessConfig, compute_epoch_at_slot] at hbe
  | succ e =>
      cases e with
      | zero =>
          rcases blockAt_cases hb with h | h | h
          · rcases h with ⟨rfl, rfl⟩
            exact False.elim (witnessPaperA32Support_anchor_one_false hsupport)
          · rcases h with ⟨rfl, rfl⟩
            have h12slot : 12 ≤ witnessExecution.slot_at witnessConfig m := by
              simpa [compute_start_slot_at_epoch, witnessConfig] using hboundary
            have hlate := lateStoreFacts w m hHm ((by decide : 8 ≤ 12).trans h12slot)
            refine ⟨carrierRoot, hlate.carrier_known, hlate.child_known,
              hlate.carrier_descends_child, ?_, Or.inr ?_, ?_⟩
            · rw [hlate.carrier_epoch]
              decide
            · rw [hlate.carrier_epoch]
              decide
            · rw [checkpointAt_child_one]
              exact ⟨carrierRoot, .refl carrierRoot, formed_carrier_child⟩
          · rcases h with ⟨rfl, rfl⟩
            norm_num [carrierSignedBlock, witnessConfig, compute_epoch_at_slot] at hbe
      | succ e =>
          have hmlt := time_lt_sixteen hHm
          rw [slot_at_eq] at hboundary
          change (e + 1 + 1 + 2) * 4 ≤ m at hboundary
          omega

/-! ## The safety premise -/

theorem witnessAdmissible : witnessBridge.Admissible where
  setup := ⟨by decide, rfl, by decide +kernel⟩
  numeric := by norm_num [UINT64_MAX, witnessBridge, witnessSetup, witnessScope, witnessConfig,
    witnessPreset]

theorem witnessConcreteGenesis : witnessBridge.ConcreteGenesis witnessExecution :=
  ⟨anchorSignedBlock, rfl, rfl, by decide, rfl, by decide +kernel, rfl⟩

theorem witnessBodyAttestationsDelivered :
    witnessBridge.BodyAttestationsDelivered witnessExecution := by
  intro r b hb a ha
  change witnessExecution.BlockKnownInScheduledPrefix witnessConfig witnessBridge.interface r b
    at hb
  rw [interface_eq] at hb
  rcases acceptedBlockAt_cases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp [anchorSignedBlock] at ha
  · simp [childSignedBlock] at ha
  · refine ⟨0, 8, ?_⟩
    simp only [carrierSignedBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> simp [witnessExecution, witnessSchedule]

theorem committedState_cases {r : WitnessRoot} {cs : FFGBeaconState WitnessRoot}
    (h : witnessBridge.committedState r = some cs) :
    cs = witnessSetup.genesis ∨ cs = childFFGState ∨ cs = carrierFFGState := by
  unfold ConcreteBridge.committedState at h
  split_ifs at h
  · cases h
    exact Or.inl rfl
  · split at h
    · rcases stateEntries_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · cases h

theorem witnessEpochOneFinalizationScope :
    witnessBridge.EpochOneFinalizationScope witnessExecution := by
  intro r cs _ hcs _ _ _
  have hcheck : cs.finalized_checkpoint.epoch = 0 ∧ cs.previous_justified_checkpoint.epoch = 0 ∧
      cs.current_justified_checkpoint.epoch = 0 := by
    rcases committedState_cases hcs with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  refine ⟨fun h => absurd h (by rw [hcheck.1]; decide), ?_⟩
  intro eager heager hf
  obtain ⟨_, _, _, f, rfl, hcase⟩ := process_justification_and_finalization_outcome heager
  change f.epoch = GENESIS_EPOCH + 1 at hf
  exfalso
  rcases hcase with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl | rfl | rfl⟩
  · rw [hcheck.1] at hf
    exact absurd hf (by decide)
  · rw [hcheck.1] at hf
    exact absurd hf (by decide)
  · rw [hcheck.2.1] at hf
    exact absurd hf (by decide)
  · rw [hcheck.2.2] at hf
    exact absurd hf (by decide)

theorem witnessEpochEndsFitUint64 : EpochEndsFitUint64 witnessConfig := by
  refine ⟨2 ^ 62, ?_⟩
  norm_num [EpochEndsFitUint64, UINT64_MAX, witnessConfig]

/-- **The safety premise of the run.** -/
theorem witnessSafetyPremises : witnessBridge.SafetyPremises witnessExecution where
  admissible := witnessAdmissible
  genesis := witnessConcreteGenesis
  horizon_scope := rfl
  whole_seconds := by decide
  wellFormed := witnessWellFormedExecution
  externals_coherence := by
    rw [interface_eq]
    exact witnessExternalsCoherence
  honest_behavior := by
    rw [interface_eq]
    exact witnessHonestBehavior
  body_attestations_delivered := witnessBodyAttestationsDelivered
  synchrony := by
    rw [interface_eq]
    exact witnessPaperSafetySynchrony
  static_validators := witnessStaticValidatorSet
  byzantine_bound := witnessByzantineBound
  epoch_ends_fit := witnessEpochEndsFitUint64
  slots_per_epoch_gt_one := by decide
  epoch_one_finalization_scope := witnessEpochOneFinalizationScope
  checkpoint_inclusion := witnessPaperA32Inclusion

/-! ## Interpretation fidelity -/

theorem includedVote_data {s : Slot} (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    (vote s).data =
      { slot := s, index := 0, beacon_block_root := childRoot
        source := anchorCheckpoint, target := childEpochOneCheckpoint } := by
  interval_cases s <;> rfl

theorem child_known_bridge_post :
    childRoot ∈ (childPostPrefix.store witnessConfig witnessBridge.interface).block_roots := by
  rw [interface_eq]
  exact child_known_post

/-- Interpretation fidelity of each carrier body vote: it is a valid body
member of the accepted carrier, validated on the prepared target state. -/
noncomputable def includedFidelityAt (s : Slot) (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    Execution.IncludedAttestationFidelity witnessConfig witnessBridge.interface witnessExecution
      carrierRoot (vote s) where
  carrier_message := carrierSignedBlock.message
  carrier_accepted := by
    rw [interface_eq]
    exact carrier_acceptedBlockAt
  in_carrier_body := by
    interval_cases s <;> simp [carrierSignedBlock]
  head_descends_target := by
    rw [includedVote_data hlo hhi]
    exact .refl childRoot
  target_on_chain := by
    rw [includedVote_data hlo hhi]
    exact carrier_descends_child
  target_descends_source := by
    rw [includedVote_data hlo hhi]
    exact child_descends_anchor
  attesters_in_registry := by
    intro i hi
    have hi' : i = committeeIndex s := by simpa [vote] using hi
    subst i
    rw [registry_length]
    exact committeeIndex_lt_four s
  validation_state := witnessBridge.project childFFGState
  validation_registry := by
    rw [registry_eq]
    rfl
  valid := by
    rw [interface_eq]
    have hs16 : s < 16 := hhi.trans_lt (by decide)
    exact (witness_valid_iff _ (vote s)).2 ⟨ground_structure rfl, by decide, vote_mem_ground hs16⟩
  validation_store := childPostPrefix.store witnessConfig witnessBridge.interface
  validation_store_honest := by
    apply Execution.HonestPrefixStoreWithinHorizon.scheduledPrefix childPostPrefix
    · decide
    · exact time_within_of_lt_sixteen (show 4 < 16 by decide)
  validation_target_known := by
    rw [includedVote_data hlo hhi]
    exact child_known_bridge_post
  validation_state_from_target := by
    rw [interface_eq]
    interval_cases s <;> (set_option maxRecDepth 100000 in decide +kernel)

/-- The canonical interpretation that the safety premise gives, at validator 0
and second 0. -/
noncomputable def witnessInterpretation :
    ScheduledFFGInterpretation witnessConfig witnessBridge.interface witnessExecution :=
  (witnessSafetyPremises.nextSlotSafetyPremises (v := 0) (by decide) (n := 0)
    (time_within_of_lt_sixteen (by decide))).ffg_interpretation

/-- The canonical interpretation of the run satisfies the fidelity record:
each included vote is a valid body member of its accepted carrier, validated
on the prepared target state. -/
theorem ffg_interpretation_fidelity :
    FFGInterpretationFidelity witnessConfig witnessBridge.interface witnessExecution
      witnessInterpretation where
  included_fidelity := by
    intro carrier a h
    change witnessBridge.TargetIncludedAt witnessExecution carrier a at h
    obtain ⟨rfl, ha⟩ := bodyIncluded_cases
      (witnessBridge.bodyIncludedAt_of_targetIncludedAt witnessAdmissible witnessConcreteGenesis h)
    rcases ha with rfl | rfl | rfl
    · exact ⟨includedFidelityAt 4 (by decide) (by decide)⟩
    · exact ⟨includedFidelityAt 5 (by decide) (by decide)⟩
    · exact ⟨includedFidelityAt 6 (by decide) (by decide)⟩
  realized_finalized_epoch_le_unrealized_finalized := by
    intro r hr
    change (witnessBridge.realizedFinalized r).epoch ≤ (witnessBridge.unrealizedFinalized r).epoch
    rcases acceptedRoot_cases (known_of_bridge hr) with rfl | rfl | rfl <;> decide +kernel

/-! ## Selected-helper support -/

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
  set_option maxRecDepth 100000 in decide +kernel

theorem target_votes_support
    {v : ValidatorIndex} (hv : v ∈ witnessExecution.honest) {n : ℕ}
    (hH : witnessExecution.WithinHorizon witnessConfig (n + 1)) :
    HonestVotesSupportTarget witnessConfig witnessExecution
      (get_current_target witnessConfig
        (witnessExecution.fcrStoreAtCall witnessConfig witnessExternals v n).store)
      (n + 1) := by
  have hn : n < 15 := by have := time_lt_sixteen hH; omega
  have hvlt : v < 4 := by
    rcases honest_eq_zero_or_one_or_two_or_three hv with rfl | rfl | rfl | rfl <;> decide
  refine ⟨hH, ?_⟩
  intro i hi s hs hepoch hfuture k a ha
  obtain ⟨hslt, _, hk, ha'⟩ := witness_vote_some_iff.mp ha
  subst k a
  rw [slot_at_eq] at hfuture
  exact bounded_support ⟨v, hvlt⟩ ⟨n, hn⟩ ⟨s, hslt⟩ hepoch hfuture

/-! ## Public facts -/

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
    set_option maxRecDepth 100000 in decide +kernel
  · unfold getLatestSelectorGuard
    set_option maxRecDepth 100000 in decide +kernel
  · unfold CurrentTargetSelectedEdge
    set_option maxRecDepth 100000 in decide +kernel

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
    witnessExecution.vote 0 7 = some (7, vote 7) ∧
    (vote 7).data.target = childEpochOneCheckpoint := by
  set_option maxRecDepth 100000 in decide +kernel

/-- The safety premise of the run and the exercised support field. -/
theorem full_bundle_witness :
    witnessBridge.SafetyPremises witnessExecution ∧
    witnessConfig.slot_duration_ms = 1000 ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 6 = anchorRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 7 = childRoot ∧
    childRoot ≠ anchorRoot ∧
    HonestVotesSupportTarget witnessConfig witnessExecution
      (get_current_target witnessConfig confirmingFcr.store) 7 := by
  refine ⟨witnessSafetyPremises, rfl, ?_, actual_fcr_transition_strict_advance, by decide, ?_⟩
  · set_option maxRecDepth 100000 in decide +kernel
  · exact target_votes_support (by decide) (time_within_of_lt_sixteen (by decide))

/-- Apply the public safety theorem to the child output of the call at second
seven. -/
theorem target_edge_safe_from_next_slot (w m : ℕ)
    (hw : w ∈ witnessExecution.honest) (hm : 8 ≤ m)
    (hH : witnessExecution.WithinHorizon witnessConfig m) :
    is_ancestor (witnessExecution.store witnessConfig witnessBridge.interface w m)
      (get_head witnessConfig (witnessExecution.store witnessConfig witnessBridge.interface w m))
      (get_node_for_root childRoot) = true := by
  have hnext : witnessExecution.slot_at witnessBridge.setup.cfg 7 + 1 ≤
      witnessExecution.slot_at witnessBridge.setup.cfg m := by
    change witnessExecution.slot_at witnessConfig 7 + 1 ≤ witnessExecution.slot_at witnessConfig m
    simpa only [slot_at_eq] using hm
  have h := confirmed_root_safe_from_next_slot WitnessRoot witnessBridge witnessExecution
    witnessSafetyPremises 0 (by decide) 7 w hw m (by omega) hnext hH
  have hconf :
      witnessExecution.confirmed witnessConfig witnessBridge.interface 0 7 = childRoot := by
    rw [interface_eq]
    exact actual_fcr_transition_strict_advance
  have h2 := h.2
  change is_ancestor (witnessExecution.store witnessConfig witnessBridge.interface w m)
    (get_head witnessConfig (witnessExecution.store witnessConfig witnessBridge.interface w m))
    (get_node_for_root (witnessExecution.confirmed witnessConfig witnessBridge.interface 0 7)) =
      true at h2
  rw [hconf] at h2
  exact h2

end TargetEdgePremiseWitness
end FastConfirmation.Spec

end
