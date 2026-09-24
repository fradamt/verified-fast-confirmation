module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.ScheduledRun
public import FastConfirmationProofs.Handlers.BlockTransitionProvenance
public import FastConfirmationProofs.Execution.Calls.ScheduledPrefixGeometry
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Accepted FFG semantics for the joint non-vacuity witness

This module supplies the semantic half of the concrete horizon-four witness
from `AcceptedActualFCRJointNonVacuityBase`.  In particular, it interprets
every exact causal schedule prefix with one accepted FFG state.  The causal
store quantifier is discharged through block provenance; it is deliberately
not reduced by interval-casing the unbounded prefix second.
-/

namespace FastConfirmation.Spec
namespace AcceptedActualFCRJointNonVacuityFFG

open AcceptedActualFCRJointNonVacuityBase

/-! ## Exact accepted child and carrier transitions -/

def childPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 0
  processedCount := 0
  count_le := by decide

def childPostPrefix : witnessExecution.ScheduledEventPrefix :=
  childPrefix.successor (by decide)

set_option maxRecDepth 50000 in
theorem child_on_block_accepted :
    on_block witnessConfig witnessExternals
        (childPrefix.store witnessConfig witnessExternals) childSignedBlock =
      some (childPostPrefix.store witnessConfig witnessExternals) := by
  rfl

def childTransition :
    witnessExecution.AcceptedBlockTransition witnessConfig witnessExternals where
  atPrefix := childPrefix
  signedBlock := childSignedBlock
  event_at := by rfl
  postStore := childPostPrefix.store witnessConfig witnessExternals
  accepted := child_on_block_accepted

/-- At second seven the first event is the ordinary slot-six receipt; the
carrier block is the exact next event. -/
def carrierPrefix : witnessExecution.ScheduledEventPrefix where
  node := 0
  previousSecond := 6
  processedCount := 1
  count_le := by decide

def carrierPostPrefix : witnessExecution.ScheduledEventPrefix :=
  carrierPrefix.successor (by decide)

set_option maxRecDepth 50000 in
theorem carrier_on_block_accepted :
    on_block witnessConfig witnessExternals
        (carrierPrefix.store witnessConfig witnessExternals)
        carrierSignedBlock =
      some (carrierPostPrefix.store witnessConfig witnessExternals) := by
  rfl

def carrierTransition :
    witnessExecution.AcceptedBlockTransition witnessConfig witnessExternals where
  atPrefix := carrierPrefix
  signedBlock := carrierSignedBlock
  event_at := by rfl
  postStore := carrierPostPrefix.store witnessConfig witnessExternals
  accepted := carrier_on_block_accepted

theorem anchor_accepted :
    witnessExecution.AcceptedRoot witnessConfig witnessExternals anchorRoot := by
  refine ⟨witnessExecution.genesis_store, .genesis, ?_⟩
  simp [witnessExecution, get_forkchoice_store, anchorSignedBlock]

theorem child_accepted :
    witnessExecution.AcceptedRoot witnessConfig witnessExternals childRoot := by
  simpa [childSignedBlock] using childTransition.root_accepted

theorem carrier_accepted :
    witnessExecution.AcceptedRoot witnessConfig witnessExternals carrierRoot := by
  simpa [carrierSignedBlock] using carrierTransition.root_accepted

set_option maxRecDepth 50000 in
theorem carrier_acceptedBlockAt :
    witnessExecution.AcceptedBlockAt witnessConfig witnessExternals carrierRoot
      carrierSignedBlock.message := by
  refine ⟨carrierTransition.postStore, carrierTransition.post_causal, ?_, ?_⟩
  · simpa [carrierSignedBlock] using carrierTransition.root_known
  · simpa [carrierSignedBlock] using
      carrierTransition.inserted_message_fresh (by
        set_option maxRecDepth 50000 in decide)

/-! ## Finite block projection of every causal prefix -/

theorem scheduledBlock_cases {b : SignedBeaconBlock WitnessRoot}
    (h : IsScheduledBlock witnessExecution b) :
    b = childSignedBlock ∨ b = carrierSignedBlock := by
  obtain ⟨w, n, hmem⟩ := h
  rcases block_mem_schedule_iff.mp hmem with hchild | hcarrier
  · exact Or.inl hchild.2
  · exact Or.inr hcarrier.2

/-- Although causal stores range over arbitrary nodes, seconds, and exact
prefix lengths, their known block projection has only these three rows. -/
theorem causal_known_table {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store)
    {r : WitnessRoot} (hr : r ∈ store.block_roots) :
    (r = anchorRoot ∧ store.blocks r = anchorSignedBlock.message) ∨
      (r = childRoot ∧ store.blocks r = childSignedBlock.message) ∨
      (r = carrierRoot ∧ store.blocks r = carrierSignedBlock.message) := by
  rcases hstore.blockProvenance witnessConfig witnessExternals
      witnessExecution r hr with hgen | hsched
  · have hrAnchor : r = anchorRoot := by
      simpa [witnessExecution, get_forkchoice_store, anchorSignedBlock] using
        hgen.1
    left
    refine ⟨hrAnchor, ?_⟩
    rw [hgen.2, hrAnchor]
    simp [witnessExecution, get_forkchoice_store, anchorSignedBlock]
  · obtain ⟨b, hb, hroot, hmessage⟩ := hsched
    rcases scheduledBlock_cases hb with rfl | rfl
    · right; left
      exact ⟨hroot.symm, hmessage⟩
    · right; right
      exact ⟨hroot.symm, hmessage⟩

theorem causal_anchor_known {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store) :
    anchorRoot ∈ store.block_roots := by
  cases hstore with
  | genesis =>
      simp [witnessExecution, get_forkchoice_store, anchorSignedBlock]
  | scheduledPrefix p =>
      apply (p.genesisStoreLE witnessConfig witnessExternals).1
      simp [witnessExecution, get_forkchoice_store, anchorSignedBlock]

theorem causal_nonAnchor_parent_known {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store)
    {r : WitnessRoot} (hr : r ∈ store.block_roots) (hne : r ≠ anchorRoot) :
    (store.blocks r).parent_root ∈ store.block_roots := by
  cases hstore with
  | genesis =>
      have : r = anchorRoot := by
        simpa [witnessExecution, get_forkchoice_store, anchorSignedBlock] using hr
      exact (hne this).elim
  | scheduledPrefix p =>
      exact (p.nonAnchorParentKnown witnessConfig witnessExternals
        (show witnessExecution.genesis_store =
            get_forkchoice_store witnessConfig anchorState anchorSignedBlock by
          rfl) r hr).resolve_left hne

theorem causal_child_known_of_carrier_known {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store)
    (hcarrier : carrierRoot ∈ store.block_roots) :
    childRoot ∈ store.block_roots := by
  have hparent := causal_nonAnchor_parent_known hstore hcarrier
    (by decide : carrierRoot ≠ anchorRoot)
  rcases causal_known_table hstore hcarrier with h | h | h
  · exact False.elim ((by decide : carrierRoot ≠ anchorRoot) h.1)
  · exact False.elim ((by decide : carrierRoot ≠ childRoot) h.1)
  · rw [h.2] at hparent
    simpa [carrierSignedBlock] using hparent

theorem acceptedRoot_cases {r : WitnessRoot}
    (hr : witnessExecution.AcceptedRoot witnessConfig witnessExternals r) :
    r = anchorRoot ∨ r = childRoot ∨ r = carrierRoot := by
  obtain ⟨store, hstore, hknown⟩ := hr
  rcases causal_known_table hstore hknown with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

theorem acceptedBlockAt_cases {r : WitnessRoot} {b : BeaconBlock WitnessRoot}
    (h : witnessExecution.AcceptedBlockAt witnessConfig witnessExternals r b) :
    (r = anchorRoot ∧ b = anchorSignedBlock.message) ∨
      (r = childRoot ∧ b = childSignedBlock.message) ∨
      (r = carrierRoot ∧ b = carrierSignedBlock.message) := by
  obtain ⟨store, hstore, hr, hblock⟩ := h
  rcases causal_known_table hstore hr with h | h | h
  · left; exact ⟨h.1, hblock.symm.trans h.2⟩
  · right; left; exact ⟨h.1, hblock.symm.trans h.2⟩
  · right; right; exact ⟨h.1, hblock.symm.trans h.2⟩

/-! ## Concrete execution descent -/

theorem child_parentEdge :
    witnessExecution.ParentEdge childRoot anchorRoot := by
  exact Or.inr ⟨0, 1, childSignedBlock,
    block_mem_schedule_iff.mpr (Or.inl ⟨rfl, rfl⟩), rfl, rfl⟩

theorem carrier_parentEdge :
    witnessExecution.ParentEdge carrierRoot childRoot := by
  exact Or.inr ⟨0, 7, carrierSignedBlock,
    block_mem_schedule_iff.mpr (Or.inr ⟨rfl, rfl⟩), rfl, rfl⟩

theorem child_descends_anchor :
    witnessExecution.RootDescends childRoot anchorRoot :=
  .step child_parentEdge (.refl anchorRoot)

theorem carrier_descends_child :
    witnessExecution.RootDescends carrierRoot childRoot :=
  .step carrier_parentEdge (.refl childRoot)

theorem carrier_descends_anchor :
    witnessExecution.RootDescends carrierRoot anchorRoot :=
  Execution.RootDescends.trans witnessExecution carrier_descends_child
    child_descends_anchor

theorem parentEdge_val_lt {child parent : WitnessRoot}
    (h : witnessExecution.ParentEdge child parent) : parent.val < child.val := by
  rcases h with hgen | hsched
  · obtain ⟨r, hr, rfl, rfl⟩ := hgen
    have hrAnchor : child = anchorRoot := by
      simpa [witnessExecution, get_forkchoice_store, anchorSignedBlock] using hr
    subst child
    decide
  · obtain ⟨w, n, b, hb, hchild, hparent⟩ := hsched
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hchild, hparent]
      decide
    · rw [hchild, hparent]
      decide

theorem rootDescends_val_le {source target : WitnessRoot}
    (h : witnessExecution.RootDescends source target) :
    target.val ≤ source.val := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact ih.trans (Nat.le_of_lt (parentEdge_val_lt hedge))

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

theorem acceptedRoot_descends_anchor {r : WitnessRoot}
    (hr : witnessExecution.AcceptedRoot witnessConfig witnessExternals r) :
    witnessExecution.RootDescends r anchorRoot := by
  rcases acceptedRoot_cases hr with rfl | rfl | rfl
  · exact .refl anchorRoot
  · exact child_descends_anchor
  · exact carrier_descends_anchor

/-! ## Accepted inclusion and the substantive anchor-to-child link -/

def witnessIncluded (carrier : WitnessRoot)
    (a : Attestation WitnessRoot) : Prop :=
  carrier = carrierRoot ∧ (a = vote4 ∨ a = vote5 ∨ a = vote6)


theorem carrier_blockAt :
    witnessExecution.BlockAt carrierRoot carrierSignedBlock.message := by
  exact Or.inr ⟨0, 7, carrierSignedBlock,
    block_mem_schedule_iff.mpr (Or.inr ⟨rfl, rfl⟩), rfl, rfl⟩

theorem includedVote_true_scheduled {s : Slot} (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    Event.attestation (vote s) true ∈ witnessExecution.schedule 0 7 := by
  interval_cases s <;> simp [witnessExecution, witnessSchedule,
    vote4, vote5, vote6]

theorem includedVote_data {s : Slot} (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    (vote s).data =
      { slot := s, index := 0, beacon_block_root := childRoot
        source := anchorCheckpoint, target := childEpochOneCheckpoint } := by
  interval_cases s <;> rfl

def acceptedIncludedEvidenceAt (s : Slot) (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    Execution.CausalCarrierAttestationEvidence witnessConfig
      witnessExternals witnessExecution
      witnessExternals.is_valid_indexed_attestation carrierRoot (vote s) where
  carrier_message := carrierSignedBlock.message
  carrier_at := carrier_blockAt
  in_carrier_body := by
    interval_cases s <;> simp [carrierSignedBlock, vote4, vote5, vote6]
  received_from_block := ⟨0, 7, includedVote_true_scheduled hlo hhi⟩
  validation_state := witnessExternals.process_slots childState 4
  validation_registry := by
    simpa [witnessExternals] using witnessProcessSlots_registry childState 4
  valid := by
    apply (witness_valid_iff (witnessExternals.process_slots childState 4) (vote s)).2
    exact ⟨by decide, vote_mem_ground (hhi.trans_lt (by decide : 6 < 16))⟩
  slot_within_horizon := by
    rw [vote_data_slot]
    exact slot_within_of_lt_sixteen (hhi.trans_lt (by decide : 6 < 16))
  slot_before_carrier := by
    rw [vote_data_slot]
    simpa [carrierSignedBlock] using hhi.trans_lt (by decide : 6 < 7)
  target_epoch := by
    interval_cases s <;> decide
  head_descends_target := by
    rw [includedVote_data hlo hhi]
    exact .refl childRoot
  target_on_chain := by
    rw [includedVote_data hlo hhi]
    exact carrier_descends_child
  target_descends_source := by
    rw [includedVote_data hlo hhi]
    exact child_descends_anchor
  attesters_in_committee := by
    intro i hi
    rw [vote_data_slot]
    simpa [vote, witnessExecution, witnessCommittee] using hi
  attesters_in_registry := by
    intro i hi
    have hi' : i = s % 4 := by simpa [vote] using hi
    subst i
    exact Nat.mod_lt s (by decide)
  carrier_accepted := carrier_acceptedBlockAt
  validation_store := childPostPrefix.store witnessConfig witnessExternals
  validation_store_honest := by
    apply Execution.HonestCausalStore.scheduledPrefix childPostPrefix
    · decide
    · simpa [childPostPrefix, childPrefix] using
        (time_within_of_lt_sixteen (show 1 < 16 by decide))
  validation_target_known := by
    rw [includedVote_data hlo hhi]
    simpa [childSignedBlock] using childTransition.root_known
  validation_state_from_target := by
    interval_cases s <;> rfl

def witnessAcceptedIncludedAttestations :
    Execution.CausalCarrierAttestationRelation witnessConfig
      witnessExternals witnessExecution
      witnessExternals.is_valid_indexed_attestation where
  Included := witnessIncluded
  evidence := by
    intro carrier a h
    rw [h.1]
    by_cases h4 : a = vote4
    · subst a
      exact acceptedIncludedEvidenceAt 4 (by decide) (by decide)
    by_cases h5 : a = vote5
    · subst a
      exact acceptedIncludedEvidenceAt 5 (by decide) (by decide)
    have h6 : a = vote6 := by
      rcases h.2 with h4' | h5' | h6'
      · exact False.elim (h4 h4')
      · exact False.elim (h5 h5')
      · exact h6'
    subst a
    exact acceptedIncludedEvidenceAt 6 (by decide) (by decide)

/-- Every accepted included vote occurs in its carrier's actual FFG body. -/
theorem no_included_vote_missing_from_body
    {carrier : WitnessRoot} {a : Attestation WitnessRoot}
    (h : witnessAcceptedIncludedAttestations.Included carrier a) :
    ∃ b : BeaconBlock WitnessRoot,
      witnessExecution.AcceptedBlockAt witnessConfig witnessExternals carrier b ∧
        a ∈ b.attestations := by
  let ev := witnessAcceptedIncludedAttestations.evidence h
  exact ⟨ev.carrier_message, ev.carrier_accepted, ev.in_carrier_body⟩

def witnessIncludedAnchorChildLink :
    IncludedSupermajorityLink witnessConfig witnessExecution witnessIncluded
      carrierRoot anchorCheckpoint childEpochOneCheckpoint where
  signers := {0, 1, 2}
  source_before_target := by decide
  target_descends_source := child_descends_anchor
  target_epoch_within := by decide
  target_span_within := by
    constructor <;> exact slot_within_of_lt_sixteen (by decide)
  signers_in_epoch := by
    decide
  signer_attestation := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · refine ⟨vote4, ⟨carrierRoot, .refl carrierRoot, ?_⟩, ?_, ?_, ?_⟩
      · exact ⟨rfl, Or.inl rfl⟩
      · decide
      · rfl
      · rfl
    · refine ⟨vote5, ⟨carrierRoot, .refl carrierRoot, ?_⟩, ?_, ?_, ?_⟩
      · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
      · decide
      · rfl
      · rfl
    · refine ⟨vote6, ⟨carrierRoot, .refl carrierRoot, ?_⟩, ?_, ?_, ?_⟩
      · exact ⟨rfl, Or.inr (Or.inr rfl)⟩
      · decide
      · rfl
      · rfl
  supermajority := by
    decide

/-! ## The one global accepted FFG state -/

/-- The executable checkpoint walk on the three-block line.  Future epochs
stop at the supplied tip, exactly as `get_checkpoint_for_block` does. -/
def witnessC (r : WitnessRoot) (e : Epoch) : Checkpoint WitnessRoot :=
  { epoch := e
    root :=
      if r = anchorRoot then anchorRoot
      else if r = childRoot then
        if e = 0 then anchorRoot else childRoot
      else if r = carrierRoot then
        if e = 0 then anchorRoot
        else if e = 1 then childRoot else carrierRoot
      else anchorRoot }

@[simp] theorem witnessC_anchor (e : Epoch) :
    witnessC anchorRoot e = { epoch := e, root := anchorRoot } := by
  simp [witnessC]

@[simp] theorem witnessC_child_zero :
    witnessC childRoot 0 = anchorCheckpoint := by
  rfl


@[simp] theorem witnessC_carrier_zero :
    witnessC carrierRoot 0 = anchorCheckpoint := by
  rfl

@[simp] theorem witnessC_carrier_one :
    witnessC carrierRoot 1 = childEpochOneCheckpoint := by
  rfl


@[simp] theorem witnessC_anchor_zero :
    witnessC anchorRoot 0 = anchorCheckpoint := by rfl

@[simp] theorem witnessC_anchor_one :
    witnessC anchorRoot 1 =
      { epoch := 1, root := anchorRoot } := by rfl

@[simp] theorem witnessC_child_one :
    witnessC childRoot 1 = childEpochOneCheckpoint := by rfl

/-- Exactly three positive AU cells: the trusted anchor cell, an anchor cell
on the carrier, and the substantive child-at-epoch-one carrier cell. -/
def witnessFormed (r : WitnessRoot) (c : Checkpoint WitnessRoot) : Prop :=
  (r = anchorRoot ∧ c = anchorCheckpoint) ∨
    (r = carrierRoot ∧
      (c = anchorCheckpoint ∨ c = childEpochOneCheckpoint))

def witnessGU (r : WitnessRoot) : Checkpoint WitnessRoot :=
  if r = carrierRoot then childEpochOneCheckpoint else anchorCheckpoint

theorem witnessFormed_anchor : witnessFormed anchorRoot anchorCheckpoint := by
  exact Or.inl ⟨rfl, rfl⟩

theorem witnessFormed_carrier_anchor :
    witnessFormed carrierRoot anchorCheckpoint := by
  exact Or.inr ⟨rfl, Or.inl rfl⟩

theorem witnessFormed_carrier_child :
    witnessFormed carrierRoot childEpochOneCheckpoint := by
  exact Or.inr ⟨rfl, Or.inr rfl⟩

theorem carrier_child_formation_causal :
    HonestEarlierTargetVoteOnCarrierChain witnessConfig witnessExternals
      witnessExecution witnessIncluded carrierRoot childEpochOneCheckpoint := by
  refine ⟨carrierSignedBlock.message, carrier_acceptedBlockAt,
    0, ?_, 4, 4, vote4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [witnessExecution]
  · decide
  · exact slot_within_of_lt_sixteen (by decide)
  · exact (witness_vote_some_iff).2 ⟨by decide, rfl, rfl, rfl⟩
  · rfl
  · rfl
  · exact ⟨vote4, ⟨carrierRoot, .refl carrierRoot,
      ⟨rfl, Or.inl rfl⟩⟩, by decide, rfl⟩

def witnessAcceptedChainFFGState :
    CausalCarrierFFGState witnessConfig witnessExternals witnessExecution
      anchorCheckpoint where
  attestationValidity := witnessExternals.is_valid_indexed_attestation
  includedAttestations := witnessAcceptedIncludedAttestations
  formed := witnessFormed
  C := witnessC
  GJ := fun _ => anchorCheckpoint
  GU := witnessGU
  GF := fun _ => anchorCheckpoint
  GUF := fun _ => anchorCheckpoint
  checkpoint_epoch := by
    intro r e
    rfl
  formed_carrier_accepted := by
    intro r c h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · exact anchor_accepted
    · exact carrier_accepted
    · exact carrier_accepted
  formed_evidence := by
    intro r c h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · exact
        { certified := ⟨IncludedCertifiedJustified.anchor⟩
          on_chain := .refl anchorRoot
          causal := Or.inl rfl }
    · exact
        { certified := ⟨IncludedCertifiedJustified.anchor⟩
          on_chain := carrier_descends_anchor
          causal := Or.inl rfl }
    · exact
        { certified := ⟨IncludedCertifiedJustified.link
              IncludedCertifiedJustified.anchor witnessIncludedAnchorChildLink⟩
          on_chain := carrier_descends_child
          causal := Or.inr carrier_child_formation_causal }
  gj_mem := by
    intro r hr
    exact ⟨anchorRoot, acceptedRoot_descends_anchor hr,
      witnessFormed_anchor⟩
  gu_mem := by
    intro r hr
    by_cases hcarrier : r = carrierRoot
    · subst r
      exact ⟨carrierRoot, .refl carrierRoot,
        witnessFormed_carrier_child⟩
    · have hdesc := acceptedRoot_descends_anchor hr
      exact ⟨anchorRoot, hdesc, by
        simpa [witnessGU, hcarrier] using witnessFormed_anchor⟩
  gf_mem := by
    intro r hr
    exact ⟨anchorRoot, acceptedRoot_descends_anchor hr,
      witnessFormed_anchor⟩
  guf_mem := by
    intro r hr
    exact ⟨anchorRoot, acceptedRoot_descends_anchor hr,
      witnessFormed_anchor⟩
  gj_anchor_or_before := by
    intro r b haccepted
    exact Or.inl rfl
  gj_max := by
    intro r b c haccepted hformed hepoch
    obtain ⟨carrier, hdesc, hformed⟩ := hformed
    rcases hformed with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · simp [anchorCheckpoint]
    · simp [anchorCheckpoint]
    · have hr : r = carrierRoot := rootDescends_carrier_iff.mp hdesc
      subst r
      rcases acceptedBlockAt_cases haccepted with h | h | h <;>
        simp_all [witnessConfig, compute_epoch_at_slot, anchorSignedBlock,
          childSignedBlock, carrierSignedBlock, anchorRoot, childRoot,
          carrierRoot, anchorCheckpoint,
          childEpochOneCheckpoint]
  gu_max := by
    intro r c hr hformed
    obtain ⟨carrier, hdesc, hformed⟩ := hformed
    rcases hformed with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · simp [witnessGU, anchorCheckpoint]
    · simp [witnessGU, anchorCheckpoint]
    · have hrCarrier : r = carrierRoot := rootDescends_carrier_iff.mp hdesc
      subst r
      simp [witnessGU, childEpochOneCheckpoint]
  au_epoch_le_block := by
    intro r b c haccepted hformed
    obtain ⟨carrier, hdesc, hformed⟩ := hformed
    rcases hformed with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · simp [anchorCheckpoint]
    · simp [anchorCheckpoint]
    · have hr : r = carrierRoot := rootDescends_carrier_iff.mp hdesc
      subst r
      rcases acceptedBlockAt_cases haccepted with h | h | h <;>
        simp_all [witnessConfig, compute_epoch_at_slot, anchorSignedBlock,
          childSignedBlock, carrierSignedBlock, anchorRoot, childRoot,
          carrierRoot, childEpochOneCheckpoint]
  gf_evidence := by
    intro r hr
    exact Or.inl rfl
  guf_evidence := by
    intro r hr
    exact Or.inl rfl
  gf_epoch_le_gj := by
    intro r hr
    rfl
  guf_epoch_le_gu := by
    intro r hr
    simp [witnessGU, anchorCheckpoint, childEpochOneCheckpoint]
  gf_epoch_le_guf := by
    intro r hr
    rfl

/-! ## Checkpoint reflection at every exact causal prefix -/

theorem causal_anchor_message {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store) :
    store.blocks anchorRoot = anchorSignedBlock.message := by
  have hknown := causal_anchor_known hstore
  rcases causal_known_table hstore hknown with h | h | h
  · exact h.2
  · exact False.elim ((by decide : anchorRoot ≠ childRoot) h.1)
  · exact False.elim ((by decide : anchorRoot ≠ carrierRoot) h.1)

theorem causal_child_message {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store)
    (hknown : childRoot ∈ store.block_roots) :
    store.blocks childRoot = childSignedBlock.message := by
  rcases causal_known_table hstore hknown with h | h | h
  · exact False.elim ((by decide : childRoot ≠ anchorRoot) h.1)
  · exact h.2
  · exact False.elim ((by decide : childRoot ≠ carrierRoot) h.1)


theorem witnessCheckpointOfKnown {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store)
    (r : WitnessRoot) (hr : r ∈ store.block_roots) (e : Epoch) :
    witnessC r e = get_checkpoint_for_block witnessConfig store r e := by
  have hanchor := causal_anchor_message hstore
  rcases causal_known_table hstore hr with hroot | hroot | hroot
  · rcases hroot with ⟨rfl, hroot⟩
    apply checkpoint_eq_of_epoch_root_eq <;>
      simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
      compute_start_slot_at_epoch,
      get_ancestor, get_ancestor_aux, witnessConfig, anchorSignedBlock,
      hanchor]
  · rcases hroot with ⟨rfl, hchild⟩
    cases e with
    | zero =>
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
          compute_start_slot_at_epoch,
          get_ancestor, get_ancestor_aux, witnessConfig, anchorSignedBlock,
          childSignedBlock, hanchor, hchild]
    | succ e =>
        have hstop : ¬ 1 > (e + 1) * 4 := by omega
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
          compute_start_slot_at_epoch,
          get_ancestor, get_ancestor_aux, witnessConfig, childSignedBlock,
          hchild, hstop] <;>
          simp [anchorRoot, childRoot, carrierRoot]
  · rcases hroot with ⟨rfl, hcarrier⟩
    have hchildKnown := causal_child_known_of_carrier_known hstore hr
    have hchild := causal_child_message hstore hchildKnown
    cases e with
    | zero =>
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
          compute_start_slot_at_epoch,
          get_ancestor, get_ancestor_aux, witnessConfig, anchorSignedBlock,
          childSignedBlock, carrierSignedBlock, hanchor, hchild, hcarrier]
    | succ e =>
        cases e with
        | zero =>
            apply checkpoint_eq_of_epoch_root_eq <;>
              simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
              compute_start_slot_at_epoch,
              get_ancestor, get_ancestor_aux, witnessConfig,
              childSignedBlock, carrierSignedBlock, hchild, hcarrier] <;>
              simp [anchorRoot, childRoot, carrierRoot]
        | succ e =>
            have hstop : ¬ 7 > (e + 2) * 4 := by omega
            apply checkpoint_eq_of_epoch_root_eq <;>
              simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
              compute_start_slot_at_epoch,
              get_ancestor, get_ancestor_aux, witnessConfig,
              carrierSignedBlock, hcarrier, hstop] <;>
              simp [anchorRoot, childRoot, carrierRoot]

theorem witnessAU_cases {r : WitnessRoot} {c : Checkpoint WitnessRoot}
    (hAU : witnessAcceptedChainFFGState.AU witnessConfig witnessExternals r c) :
    c = anchorCheckpoint ∨
      (r = carrierRoot ∧ c = childEpochOneCheckpoint) := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  change witnessFormed carrier c at hformed
  rcases hformed with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rootDescends_carrier_iff.mp hdesc, rfl⟩

theorem witnessAUCheckpointOfKnown {store : Store WitnessRoot}
    (hstore : witnessExecution.CausalStore witnessConfig witnessExternals store)
    (r : WitnessRoot) (hr : r ∈ store.block_roots)
    (c : Checkpoint WitnessRoot)
    (hAU : witnessAcceptedChainFFGState.AU witnessConfig witnessExternals r c) :
    c = get_checkpoint_for_block witnessConfig store r c.epoch := by
  rcases witnessAU_cases hAU with rfl | ⟨rfl, rfl⟩
  · rcases causal_known_table hstore hr with h | h | h
    · rcases h with ⟨rfl, hmessage⟩
      simpa [anchorCheckpoint] using
        witnessCheckpointOfKnown hstore anchorRoot hr 0
    · rcases h with ⟨rfl, hmessage⟩
      simpa [anchorCheckpoint] using
        witnessCheckpointOfKnown hstore childRoot hr 0
    · rcases h with ⟨rfl, hmessage⟩
      simpa [anchorCheckpoint] using
        witnessCheckpointOfKnown hstore carrierRoot hr 0
  · simpa [childEpochOneCheckpoint] using
      witnessCheckpointOfKnown hstore carrierRoot hr 1

/-! ## Accepted selector-transition classification and coherence -/

theorem acceptedTransition_cases
    (t : witnessExecution.AcceptedBlockTransition witnessConfig
      witnessExternals) :
    (t.signedBlock = childSignedBlock ∧
      t.postStore.block_states childRoot = childState) ∨
    (t.signedBlock = carrierSignedBlock ∧
      t.postStore.block_states carrierRoot = carrierState) := by
  have heventMem : Event.block t.signedBlock ∈
      witnessExecution.schedule t.atPrefix.node
        (t.atPrefix.previousSecond + 1) := by
    obtain ⟨hlt, hevent⟩ :=
      List.getElem?_eq_some_iff.mp t.event_at
    have hmem := List.getElem_mem hlt
    rw [hevent] at hmem
    exact hmem
  rcases block_mem_schedule_iff.mp heventMem with hchild | hcarrier
  · left
    have hprev : t.atPrefix.previousSecond = 0 := by omega
    have hcountLe : t.atPrefix.processedCount ≤ 2 := by
      simpa [witnessExecution, witnessSchedule, hprev] using
        t.atPrefix.count_le
    have hevent := t.event_at
    simp only [witnessExecution, witnessSchedule, hprev] at hevent
    have hcount : t.atPrefix.processedCount = 0 := by
      interval_cases hp : t.atPrefix.processedCount <;> simp_all
    have hpostPrefix :
        t.successorPrefix.store witnessConfig witnessExternals =
          childPostPrefix.store witnessConfig witnessExternals := by
      simp only [Execution.AcceptedBlockTransition.successorPrefix,
        Execution.ScheduledEventPrefix.successor,
        Execution.ScheduledEventPrefix.store, childPostPrefix, childPrefix,
        hprev, hcount]
      rw [witness_store_symmetric t.atPrefix.node 0 0]
      rfl
    have hpostStore : t.postStore =
        childPostPrefix.store witnessConfig witnessExternals := by
      rw [← t.successorPrefix_store]
      exact hpostPrefix
    refine ⟨hchild.2, ?_⟩
    rw [hpostStore]
    rfl
  · right
    have hprev : t.atPrefix.previousSecond = 6 := by omega
    have hcountLe : t.atPrefix.processedCount ≤ 5 := by
      simpa [witnessExecution, witnessSchedule, hprev] using
        t.atPrefix.count_le
    have hevent := t.event_at
    simp only [witnessExecution, witnessSchedule, hprev] at hevent
    have hcount : t.atPrefix.processedCount = 1 := by
      interval_cases hp : t.atPrefix.processedCount <;> simp_all
    have hpostPrefix :
        t.successorPrefix.store witnessConfig witnessExternals =
          carrierPostPrefix.store witnessConfig witnessExternals := by
      simp only [Execution.AcceptedBlockTransition.successorPrefix,
        Execution.ScheduledEventPrefix.successor,
        Execution.ScheduledEventPrefix.store, carrierPostPrefix, carrierPrefix,
        hprev, hcount]
      rw [witness_store_symmetric t.atPrefix.node 0 6]
      rfl
    refine ⟨hcarrier.2, ?_⟩
    have hpostStore : t.postStore =
        carrierPostPrefix.store witnessConfig witnessExternals := by
      rw [← t.successorPrefix_store]
      exact hpostPrefix
    rw [hpostStore]
    set_option maxRecDepth 50000 in rfl

theorem genesis_known_eq_anchor {r : WitnessRoot}
    (hr : r ∈ witnessExecution.genesis_store.block_roots) :
    r = anchorRoot := by
  simpa [witnessExecution, get_forkchoice_store, anchorSignedBlock] using hr

def witnessAcceptedFFGTransitionCoherence :
    FFGSelectorsAndCheckpointReadsMatchBeaconStates witnessConfig witnessExternals
      witnessAcceptedChainFFGState where
  attestation_validity := rfl
  genesis_gj := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_gf := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_gu := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_guf := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_unrealized_justification := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  transition_gj := by
    intro t
    rcases acceptedTransition_cases t with h | h
    · rw [h.1]
      change (t.postStore.block_states childRoot).current_justified_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
    · rw [h.1]
      change (t.postStore.block_states carrierRoot).current_justified_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
  transition_gf := by
    intro t
    rcases acceptedTransition_cases t with h | h
    · rw [h.1]
      change (t.postStore.block_states childRoot).finalized_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
    · rw [h.1]
      change (t.postStore.block_states carrierRoot).finalized_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
  transition_gu := by
    intro t
    rcases acceptedTransition_cases t with h | h
    · rw [h.1]
      change (witnessPJF (t.postStore.block_states childRoot)).current_justified_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
    · rw [h.1]
      change (witnessPJF (t.postStore.block_states carrierRoot)).current_justified_checkpoint =
        childEpochOneCheckpoint
      rw [h.2]
      rfl
  transition_guf := by
    intro t
    rcases acceptedTransition_cases t with h | h
    · rw [h.1]
      change (witnessPJF (t.postStore.block_states childRoot)).finalized_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
    · rw [h.1]
      change (witnessPJF (t.postStore.block_states carrierRoot)).finalized_checkpoint =
        anchorCheckpoint
      rw [h.2]
      rfl
  checkpoint_of_known := by
    intro store hstore r hr e
    exact witnessCheckpointOfKnown hstore r hr e
  au_checkpoint_of_known := by
    intro store hstore r hr c hAU
    exact witnessAUCheckpointOfKnown hstore r hr c hAU

def witnessAcceptedSemantics :
    CausalPrefixFFGInterpretation witnessConfig witnessExternals
      witnessExecution where
  anchor := anchorCheckpoint
  state := witnessAcceptedChainFFGState
  coherence := witnessAcceptedFFGTransitionCoherence


/-! ## Public selector/AU reductions -/









theorem witnessAU_carrier_anchor :
    witnessAcceptedChainFFGState.AU witnessConfig witnessExternals
      carrierRoot anchorCheckpoint :=
  ⟨carrierRoot, .refl carrierRoot, witnessFormed_carrier_anchor⟩

theorem witnessAU_carrier_child :
    witnessAcceptedChainFFGState.AU witnessConfig witnessExternals
      carrierRoot childEpochOneCheckpoint :=
  ⟨carrierRoot, .refl carrierRoot, witnessFormed_carrier_child⟩

/-! ## Accepted checkpoint projection -/

def witnessAcceptedEpochCheckpointProjection :
    EpochCheckpointClosure anchorCheckpoint
      (witnessExecution.AcceptedRoot witnessConfig witnessExternals) witnessC where
  checkpoint_root_accepted := by
    intro r e hr hanchor
    rcases acceptedRoot_cases hr with rfl | rfl | rfl
    · simpa [witnessC] using anchor_accepted
    · cases e with
      | zero => simpa [witnessC] using anchor_accepted
      | succ e => simpa [witnessC] using child_accepted
    · cases e with
      | zero => simpa [witnessC] using anchor_accepted
      | succ e =>
          cases e with
          | zero => simpa [witnessC] using child_accepted
          | succ e => simpa [witnessC] using carrier_accepted
  checkpoint_comp := by
    intro r sourceEpoch targetEpoch hr hanchor hle
    rcases acceptedRoot_cases hr with rfl | rfl | rfl
    · simp [witnessC, anchorRoot, childRoot, carrierRoot]
    · cases targetEpoch with
      | zero =>
          have : sourceEpoch = 0 := Nat.eq_zero_of_le_zero hle
          subst sourceEpoch
          simp [witnessC, anchorRoot, childRoot, carrierRoot]
      | succ targetEpoch =>
          cases sourceEpoch with
          | zero => simp [witnessC, anchorRoot, childRoot, carrierRoot]
          | succ sourceEpoch =>
              simp [witnessC, anchorRoot, childRoot, carrierRoot]
    · cases targetEpoch with
      | zero =>
          have : sourceEpoch = 0 := Nat.eq_zero_of_le_zero hle
          subst sourceEpoch
          simp [witnessC, anchorRoot, childRoot, carrierRoot]
      | succ targetEpoch =>
          cases targetEpoch with
          | zero =>
              cases sourceEpoch with
              | zero => simp [witnessC, anchorRoot, childRoot, carrierRoot]
              | succ sourceEpoch =>
                  have : sourceEpoch = 0 :=
                    Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hle)
                  subst sourceEpoch
                  simp [witnessC, anchorRoot, childRoot, carrierRoot]
          | succ targetEpoch =>
              simp [witnessC, anchorRoot, childRoot, carrierRoot]

/-! ## Exact classification of every included link -/

theorem witnessIncludedLink_cases
    {carrier : WitnessRoot} {source target : Checkpoint WitnessRoot}
    (L : IncludedSupermajorityLink witnessConfig witnessExecution
      witnessIncluded carrier source target) :
    carrier = carrierRoot ∧ source = anchorCheckpoint ∧
      target = childEpochOneCheckpoint := by
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
  obtain ⟨a, ⟨containing, hdesc, hincluded⟩, hiatt,
      hsource, htarget⟩ := L.signer_attestation i hi
  change witnessIncluded containing a at hincluded
  rcases hincluded with ⟨rfl, rfl | rfl | rfl⟩
  · refine ⟨rootDescends_carrier_iff.mp hdesc, ?_, ?_⟩
    · simpa [vote4, vote, voteData] using hsource.symm
    · simpa [vote4, vote, voteData] using htarget.symm
  · refine ⟨rootDescends_carrier_iff.mp hdesc, ?_, ?_⟩
    · simpa [vote5, vote, voteData] using hsource.symm
    · simpa [vote5, vote, voteData] using htarget.symm
  · refine ⟨rootDescends_carrier_iff.mp hdesc, ?_, ?_⟩
    · simpa [vote6, vote, voteData] using hsource.symm
    · simpa [vote6, vote, voteData] using htarget.symm

def witnessExactLinkValidity :
    witnessAcceptedChainFFGState.ExactLinkValidity where
  carrier_accepted := by
    intro carrier source target L hcontributing _hdomain
    change IncludedSupermajorityLink witnessConfig witnessExecution
      witnessIncluded carrier source target at L
    rcases witnessIncludedLink_cases L with ⟨rfl, hsource, htarget⟩
    exact carrier_accepted
  endpoints_on_carrier := by
    intro carrier source target L hcontributing _hdomain
    change IncludedSupermajorityLink witnessConfig witnessExecution
      witnessIncluded carrier source target at L
    obtain ⟨rfl, rfl, rfl⟩ := witnessIncludedLink_cases L
    exact ⟨rfl, rfl⟩

/-! ## Included votes are pairwise non-slashable -/

theorem witness_hasSlashablePairOnChain_false (tip : WitnessRoot)
    (i : ValidatorIndex) :
    ¬ witnessAcceptedChainFFGState.HasSlashablePairOnChain
      witnessConfig witnessExternals tip i := by
  rintro ⟨a₁, a₂, ⟨carrier₁, hdesc₁, hinc₁⟩,
    ⟨carrier₂, hdesc₂, hinc₂⟩, hi₁, hi₂, hslash⟩
  change witnessIncluded carrier₁ a₁ at hinc₁
  change witnessIncluded carrier₂ a₂ at hinc₂
  rcases hinc₁ with ⟨rfl, rfl | rfl | rfl⟩ <;>
    rcases hinc₂ with ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp_all [vote4, vote5, vote6, vote, voteData,
      is_slashable_attestation_data]

theorem witness_slashableOnChain_eq_empty (tip : WitnessRoot) :
    witnessAcceptedChainFFGState.slashableOnChain
      witnessConfig witnessExternals tip = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  exact witness_hasSlashablePairOnChain_false tip i
    ((witnessAcceptedChainFFGState.mem_slashableOnChain
      witnessConfig witnessExternals tip i).mp hi)

end AcceptedActualFCRJointNonVacuityFFG
end FastConfirmation.Spec

end
