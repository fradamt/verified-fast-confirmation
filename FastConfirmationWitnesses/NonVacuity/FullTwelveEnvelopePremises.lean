module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopeRun
public import FastConfirmationProofs.ReviewTheorem
public import FastConfirmationInternal.FFG.InterpretationFidelity

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Twelve-second envelope witness: the safety premise with a verified payload

The run of `FullTwelveEnvelopeBridgeRun` satisfies the public safety premise
`ConcreteBridge.SafetyPremises`. It adds to the twelve-second run a verified
child envelope, which node 1 receives two seconds after the other nodes. The
envelope delivery and data-availability relays of the synchrony premise hold
with this envelope. The call from second 23 to 24 changes the confirmed root
from the anchor to the child.
-/

namespace FastConfirmation.Spec
namespace FullTwelveEnvelopeWitness

open ConcreteFFG
open FullTwelveEnvelopeBridgeRun

/-! ## Scheduled prefixes and known blocks -/

def childPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 11
  processedCount := 0
  count_le := by decide

def childPostPrefix : witnessExecution.ScheduledEventPrefix :=
  childPrefix.successor (by decide)

/-- At second 96 the first event is the ordinary slot-seven receipt; the
carrier block is the exact next event. -/
def carrierPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 95
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
  Or.inr ⟨0, 12, childSignedBlock, child_mem_schedule, rfl, rfl⟩

theorem carrier_parentEdge : witnessExecution.ParentEdge carrierRoot childRoot :=
  Or.inr ⟨0, 96, carrierSignedBlock, carrier_mem_schedule, rfl, rfl⟩

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
    rcases block_event_cases hb with ⟨rfl, -⟩ | ⟨rfl, -⟩
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

theorem checkpointAt_child_zero : witnessView.C childRoot 0 = anchorCheckpoint := by
  decide +kernel

theorem checkpointAt_child_one : witnessView.C childRoot 1 = childEpochOneCheckpoint := by
  decide +kernel

theorem checkpointAt_anchor_one :
    witnessView.C anchorRoot 1 = ({ epoch := 1, root := anchorRoot } : Checkpoint WitnessRoot) := by
  decide +kernel

theorem gu_child : witnessView.GU childRoot = anchorCheckpoint := by
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

theorem formed_child_anchor : witnessView.formed childRoot anchorCheckpoint :=
  ⟨known_bridge child_accepted, Or.inl realizedJustified_child.symm⟩

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
    simp_all [vote, voteData, is_slashable_attestation_data]

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
    (witnessExecution.store witnessConfig witnessExternals w m) childRoot = 0
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

private theorem late_table (w : Fin 3) (s : Fin 8) (o : Fin 12) :
    LateStoreFacts w.val (96 + 12 * s.val + o.val) := by
  constructor <;> revert w s o <;> (set_option maxRecDepth 100000 in decide +kernel)

theorem lateStoreFacts (w : ValidatorIndex) (m : ℕ)
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (h8m : 8 ≤ witnessExecution.slot_at witnessConfig m) :
    LateStoreFacts w m := by
  have hmlt := time_lt_horizon hHm
  rw [slot_at_eq] at h8m
  simp only [Slot] at h8m
  have h := late_table ⟨nodeClass w, nodeClass_lt w⟩ ⟨m / 12 - 8, by omega⟩
    ⟨m % 12, Nat.mod_lt m (by decide)⟩
  change LateStoreFacts (nodeClass w) (96 + 12 * (m / 12 - 8) + m % 12) at h
  rw [show 96 + 12 * (m / 12 - 8) + m % 12 = m by omega] at h
  cases h
  constructor <;> rw [store_nodeClass w m] <;> assumption

theorem slot_at_ge_eight_of_epoch_two {m : ℕ}
    (hHm : witnessExecution.WithinHorizon witnessConfig m)
    (hepoch : compute_epoch_at_slot witnessConfig (witnessExecution.slot_at witnessConfig m) = 2) :
    8 ≤ witnessExecution.slot_at witnessConfig m := by
  rw [slot_at_eq] at hepoch ⊢
  change m / 12 / 4 = 2 at hepoch
  simp only [Slot]
  omega

theorem vote_received_by_from_eight {w : ValidatorIndex} {m : ℕ} {s : Slot}
    (hs4 : 4 ≤ s) (hs6 : s ≤ 6) (hm8 : 96 ≤ m) :
    witnessExecution.AttestationReceivedBy w m (vote s) := by
  have hs16 : s < 16 := hs6.trans_lt (by decide)
  have hmem := vote_at_boundary (v := s % 4) (witness_vote_some_iff.mpr ⟨hs16, rfl, rfl, rfl⟩) w
  rw [slot_start_eq] at hmem
  refine ⟨12 * (s + 1), ?_, false, hmem⟩
  simp only [Slot] at *
  omega

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
  have h8m : 96 ≤ m := by
    rw [slot_at_eq] at h8slot
    simp only [Slot] at h8slot
    omega
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
      signers := {0, 1, 2}
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
    · refine ⟨vote 4, vote_received_by_from_eight (s := 4) (by decide) (by decide) h8m, ?_,
        hvalid 4 (by decide) (by decide), slot_within_of_lt_sixteen (by decide), ?_, ?_, ?_,
        Or.inl rfl, rfl⟩
      · decide
      · rw [vote_data_slot, slot_at_eq]
        simp only [Slot]
        omega
      · decide
      · decide
    · refine ⟨vote 5, vote_received_by_from_eight (s := 5) (by decide) (by decide) h8m, ?_,
        hvalid 5 (by decide) (by decide), slot_within_of_lt_sixteen (by decide), ?_, ?_, ?_,
        Or.inl rfl, rfl⟩
      · decide
      · rw [vote_data_slot, slot_at_eq]
        simp only [Slot]
        omega
      · decide
      · decide
    · refine ⟨vote 6, vote_received_by_from_eight (s := 6) (by decide) (by decide) h8m, ?_,
        hvalid 6 (by decide) (by decide), slot_within_of_lt_sixteen (by decide), ?_, ?_, ?_,
        Or.inl rfl, rfl⟩
      · decide
      · rw [vote_data_slot, slot_at_eq]
        simp only [Slot]
        omega
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
    decide
  intro tip _ _
  have hsource : witnessView.voting_source_at witnessConfig
      (witnessExecution.store witnessConfig witnessExternals w m) childRoot 1 =
        anchorCheckpoint := by
    unfold CheckpointInclusionView.voting_source_at
    rw [hlate.child_epoch, if_neg (by decide), gu_child]
  rw [hsource, checkpointAt_child_one]
  exact ⟨witnessAnchorChildLinkSupportAt w m tip hHm hepoch⟩

theorem witnessPaperA32Support_anchor_one_false :
    ¬ SourceTargetSupportThroughoutEpoch witnessConfig witnessBridge.interface witnessView
      anchorRoot 1 := by
  rw [interface_eq]
  intro hsupport
  have hH8 : witnessExecution.WithinHorizon witnessConfig 96 := time_within (by decide)
  have hepoch8 :
      compute_epoch_at_slot witnessConfig (witnessExecution.slot_at witnessConfig 96) = 2 := by
    rw [slot_at_eq]
    decide
  obtain ⟨_, _, hall⟩ := hsupport 0 (by decide) 96 hH8 hepoch8
  have hlate := lateStoreFacts 0 96 hH8 (by rw [slot_at_eq])
  have hdesc : is_ancestor (witnessExecution.store witnessConfig witnessExternals 0 96)
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
        refine ⟨childRoot, hlate.child_known, hlate.child_known, is_ancestor_refl _ _, ?_,
          Or.inl (Nat.zero_le _), ?_⟩
        · rw [hlate.child_epoch]
          decide
        · rw [checkpointAt_child_zero]
          exact ⟨childRoot, .refl childRoot, formed_child_anchor⟩
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
          have hmlt := time_lt_horizon hHm
          rw [slot_at_eq] at hboundary
          change (e + 1 + 1 + 2) * 4 ≤ m / 12 at hboundary
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
  · refine ⟨0, 96, ?_⟩
    simp only [carrierSignedBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
      simp [witnessExecution, witnessSchedule, slotEvents, boundarySchedule]

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
    have hi' : i = s % 4 := by simpa [vote] using hi
    subst i
    rw [registry_length]
    exact Nat.mod_lt s (by decide)
  validation_state := witnessBridge.interface.process_slots
    (witnessBridge.project childFFGState) 4
  validation_registry := by
    rw [registry_eq, interface_eq, witnessProcessSlots_registry]
    rfl
  valid := by
    rw [interface_eq]
    have hs16 : s < 16 := hhi.trans_lt (by decide)
    refine (witness_valid_iff _ (vote s)).2 ⟨ground_structure ?_, ?_, vote_mem_ground hs16⟩
    · rw [witnessProcessSlots_registry]
      rfl
    · rw [witnessProcessSlots_registry]
      decide
  validation_store := childPostPrefix.store witnessConfig witnessBridge.interface
  validation_store_honest := by
    apply Execution.HonestPrefixStoreWithinHorizon.scheduledPrefix childPostPrefix
    · decide
    · exact time_within (show 12 < 192 by decide)
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
    (time_within (by decide))).ffg_interpretation

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

/-! ## Public facts -/

/-- Node 1 receives the child block two seconds after node 0, and the
slot-zero vote two seconds after node 0. These receipts are its first. -/
theorem delayed_receipts_are_first :
    Event.block childSignedBlock ∈ witnessExecution.schedule 0 12 ∧
    Event.block childSignedBlock ∈ witnessExecution.schedule 1 14 ∧
    (∀ n < 14, Event.block childSignedBlock ∉ witnessExecution.schedule 1 n) ∧
    Event.attestation (vote 0) false ∈ witnessExecution.schedule 0 4 ∧
    Event.attestation (vote 0) false ∈ witnessExecution.schedule 1 6 ∧
    (∀ n < 6, Event.attestation (vote 0) false ∉ witnessExecution.schedule 1 n) := by
  refine ⟨child_mem_schedule, ?_, ?_, ?_, ?_, ?_⟩
  · simp [witnessExecution, witnessSchedule, slotEvents]
  · intro n hn
    interval_cases n <;> simp [witnessExecution, witnessSchedule, slotEvents, boundarySchedule]
  · simp [witnessExecution, witnessSchedule, slotEvents]
  · simp [witnessExecution, witnessSchedule, slotEvents]
  · intro n hn
    interval_cases n <;> simp [witnessExecution, witnessSchedule, slotEvents, boundarySchedule]

/-- The delayed child is in the store of node 0 at second 12, and in the
store of node 1 only from second 14. -/
theorem delayed_block_in_stores :
    childRoot ∈ (witnessExecution.store witnessConfig witnessExternals 0 12).block_roots ∧
    childRoot ∉ (witnessExecution.store witnessConfig witnessExternals 1 12).block_roots ∧
    childRoot ∈ (witnessExecution.store witnessConfig witnessExternals 1 14).block_roots := by
  set_option maxRecDepth 100000 in decide +kernel

theorem payload_accepted_with_delay :
    Event.execution_payload_envelope childEnvelope payloadObservation ∈
      witnessExecution.schedule 0 168 ∧
    Event.execution_payload_envelope childEnvelope payloadObservation ∈
      witnessExecution.schedule 1 170 ∧
    (∀ n < 170,
      Event.execution_payload_envelope childEnvelope payloadObservation ∉
        witnessExecution.schedule 1 n) ∧
    is_payload_verified (witnessExecution.store witnessConfig witnessExternals 0 168) childRoot = true ∧
    is_payload_verified (witnessExecution.store witnessConfig witnessExternals 1 170) childRoot = true ∧
    (∀ v ∈ witnessExecution.honest,
      is_payload_verified (witnessExecution.store witnessConfig witnessExternals v 180) childRoot = true) := by
  refine ⟨by simp [witnessExecution, witnessSchedule, slotEvents], by simp [witnessExecution, witnessSchedule, slotEvents], ?_, ?_, ?_, ?_⟩
  · intro n hn h
    obtain ⟨_, _, htime⟩ := scheduled_envelope_cases h
    rcases htime with h168 | h170 | h180
    · subst n
      simp [witnessExecution, witnessSchedule, slotEvents] at h
    · omega
    · omega
  · set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel
  · intro v hv
    rcases honest_eq_zero_or_one_or_two_or_three hv with
      rfl | rfl | rfl | rfl <;>
        set_option maxRecDepth 100000 in decide +kernel

/-- The verified child satisfies every source condition of
`DeadlineEnvelopeDelivery` at second 168. Its next boundary is second 180. -/
theorem envelope_relay_exercised :
    ∃ v n r, v ∈ witnessExecution.honest ∧ witnessExecution.WithinHorizon witnessConfig n ∧
      is_payload_verified (witnessExecution.store witnessConfig witnessExternals v n) r = true ∧
      r ∈ (witnessExecution.store witnessConfig witnessExternals v n).block_roots ∧
      n ≤ witnessExecution.slot_start witnessConfig (witnessExecution.slot_at witnessConfig n) +
        get_attestation_due_ms witnessConfig / 1000 ∧
      Event.execution_payload_envelope childEnvelope payloadObservation ∈
        witnessExecution.schedule 1 180 := by
  refine ⟨0, 168, childRoot, by decide, time_within (by decide),
    payload_accepted_with_delay.2.2.2.1,
    child_known_after14 0 (by decide), ?_, by simp [witnessExecution, witnessSchedule, slotEvents]⟩
  rw [slot_start_eq, slot_at_eq, due_eq]
  decide

/-- The scheduled source envelope and its available data satisfy every
source condition of `DeadlineDataAvailabilityRelay` at second 168. -/
theorem data_relay_exercised :
    ∃ (v k n : ℕ) (signed : SignedExecutionPayloadEnvelope WitnessRoot)
        (sourceObservation : EnvelopeObservation WitnessRoot),
      v ∈ witnessExecution.honest ∧ k ≤ n ∧ witnessExecution.WithinHorizon witnessConfig n ∧
      Event.execution_payload_envelope signed sourceObservation ∈
        witnessExecution.schedule v k ∧
      witnessExternals.is_data_available signed.message.beacon_block_root
        sourceObservation = true ∧
      n ≤ witnessExecution.slot_start witnessConfig (witnessExecution.slot_at witnessConfig n) +
        get_attestation_due_ms witnessConfig / 1000 ∧
      Event.execution_payload_envelope signed payloadObservation ∈
        witnessExecution.schedule 1 180 := by
  refine ⟨0, 168, 168, childEnvelope, payloadObservation,
    by decide, by decide, time_within (by decide),
    by simp [witnessExecution, witnessSchedule, slotEvents], ?_, ?_, by simp [witnessExecution, witnessSchedule, slotEvents]⟩
  · rfl
  · rw [slot_start_eq, slot_at_eq, due_eq]
    decide

/-- Payload verification adds a FULL child choice. Gloas weight gives the
EMPTY choice 400 and the FULL choice zero in this scheduled store. -/
theorem payload_status_branches :
    get_node_children (witnessExecution.store witnessConfig witnessExternals 0 167) []
        (get_node_for_root childRoot) =
      [ForkChoiceNode.mk childRoot .empty] ∧
    get_node_children (witnessExecution.store witnessConfig witnessExternals 0 168) []
        (get_node_for_root childRoot) =
      [ForkChoiceNode.mk childRoot .empty,
        ForkChoiceNode.mk childRoot .full] ∧
    get_weight witnessConfig (witnessExecution.store witnessConfig witnessExternals 0 168)
        (ForkChoiceNode.mk childRoot .empty) = 400 ∧
    get_weight witnessConfig (witnessExecution.store witnessConfig witnessExternals 0 168)
        (ForkChoiceNode.mk childRoot .full) = 0 := by
  set_option maxRecDepth 100000 in decide +kernel

/-- The safety premise of the run and a scheduled call that changes the
confirmed root. -/
theorem full_bundle_witness :
    witnessBridge.SafetyPremises witnessExecution ∧
    witnessConfig.slot_duration_ms = 12000 ∧ get_attestation_due_ms witnessConfig = 3000 ∧
    witnessExecution.IsScheduledFCRCallAt witnessConfig witnessExternals 0 23 ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 23 = anchorRoot ∧
    witnessExecution.confirmed witnessConfig witnessExternals 0 24 = childRoot ∧
    childRoot ≠ anchorRoot := by
  refine ⟨witnessSafetyPremises, rfl, due_eq, ?_, changed_confirmed_root.1,
    changed_confirmed_root.2, by decide⟩
  change get_current_slot witnessConfig
      (witnessExecution.store witnessConfig witnessExternals 0 24) >
    get_current_slot witnessConfig (witnessExecution.store witnessConfig witnessExternals 0 23)
  set_option maxRecDepth 100000 in decide +kernel

/-- Apply the public safety theorem to the changed output at second 24. -/
theorem changed_root_safe_from_next_slot (w m : ℕ)
    (hw : w ∈ witnessExecution.honest) (hm : 36 ≤ m)
    (hH : witnessExecution.WithinHorizon witnessConfig m) :
    is_ancestor (witnessExecution.store witnessConfig witnessBridge.interface w m)
      (get_head witnessConfig (witnessExecution.store witnessConfig witnessBridge.interface w m))
      (get_node_for_root childRoot) = true := by
  have hnext : witnessExecution.slot_at witnessBridge.setup.cfg 24 + 1 ≤
      witnessExecution.slot_at witnessBridge.setup.cfg m := by
    change witnessExecution.slot_at witnessConfig 24 + 1 ≤
      witnessExecution.slot_at witnessConfig m
    rw [slot_at_eq, slot_at_eq]
    simp only [Slot]
    omega
  have h := confirmed_root_safe_from_next_slot WitnessRoot witnessBridge witnessExecution
    witnessSafetyPremises 0 (by decide) 24 w hw m (by omega) hnext hH
  have hconf :
      witnessExecution.confirmed witnessConfig witnessBridge.interface 0 24 = childRoot := by
    rw [interface_eq]
    exact changed_confirmed_root.2
  have h2 := h.2
  change is_ancestor (witnessExecution.store witnessConfig witnessBridge.interface w m)
    (get_head witnessConfig (witnessExecution.store witnessConfig witnessBridge.interface w m))
    (get_node_for_root (witnessExecution.confirmed witnessConfig witnessBridge.interface 0 24)) =
      true at h2
  rw [hconf] at h2
  exact h2

end FullTwelveEnvelopeWitness
end FastConfirmation.Spec

end
