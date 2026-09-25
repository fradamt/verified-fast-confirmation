module
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelopeOperational

@[expose] public section

/-! The twelve-second run has an FFG interpretation at every causal prefix. -/

namespace FastConfirmation.Spec.FullTwelveEnvelopeWitness

open AcceptedActualFCRJointNonVacuityBase

set_option maxRecDepth 50000

theorem anchor_accepted :
    run.AcceptedRoot cfg ext anchorRoot := by
  refine ⟨run.genesis_store, .genesis, ?_⟩
  simp [run, get_forkchoice_store, anchorSignedBlock]

set_option maxRecDepth 50000 in
theorem carrier_acceptedBlockAt :
    run.AcceptedBlockAt cfg ext carrierRoot
      carrierSignedBlock.message := by
  refine ⟨carrierTransition.postStore, carrierTransition.post_causal, ?_, ?_⟩
  · simpa [carrierSignedBlock] using carrierTransition.root_known
  · simpa [carrierSignedBlock] using
      carrierTransition.inserted_message_fresh (by
        set_option maxRecDepth 50000 in decide)

/-! ## Finite block projection of every causal prefix -/

/-- Although causal stores range over arbitrary nodes, seconds, and exact
prefix lengths, their known block projection has only these three rows. -/
theorem causal_known_table {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store)
    {r : WitnessRoot} (hr : r ∈ store.block_roots) :
    (r = anchorRoot ∧ store.blocks r = anchorSignedBlock.message) ∨
      (r = childRoot ∧ store.blocks r = childSignedBlock.message) ∨
      (r = carrierRoot ∧ store.blocks r = carrierSignedBlock.message) := by
  rcases hstore.blockProvenance cfg ext
      run r hr with hgen | hsched
  · have hrAnchor : r = anchorRoot := by
      simpa [run, get_forkchoice_store, anchorSignedBlock] using
        hgen.1
    left
    refine ⟨hrAnchor, ?_⟩
    rw [hgen.2, hrAnchor]
    simp [run, get_forkchoice_store, anchorSignedBlock]
  · obtain ⟨b, hb, hroot, hmessage⟩ := hsched
    rcases scheduledBlock_cases hb with rfl | rfl
    · right; left
      exact ⟨hroot.symm, hmessage⟩
    · right; right
      exact ⟨hroot.symm, hmessage⟩

theorem causal_anchor_known {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store) :
    anchorRoot ∈ store.block_roots := by
  cases hstore with
  | genesis =>
      simp [run, get_forkchoice_store, anchorSignedBlock]
  | scheduledPrefix p =>
      apply (p.genesisStoreLE cfg ext).1
      simp [run, get_forkchoice_store, anchorSignedBlock]

theorem causal_nonAnchor_parent_known {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store)
    {r : WitnessRoot} (hr : r ∈ store.block_roots) (hne : r ≠ anchorRoot) :
    (store.blocks r).parent_root ∈ store.block_roots := by
  cases hstore with
  | genesis =>
      have : r = anchorRoot := by
        simpa [run, get_forkchoice_store, anchorSignedBlock] using hr
      exact (hne this).elim
  | scheduledPrefix p =>
      exact (p.nonAnchorParentKnown cfg ext
        (show run.genesis_store =
            get_forkchoice_store cfg anchorState anchorSignedBlock by
          rfl) r hr).resolve_left hne

theorem causal_child_known_of_carrier_known {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store)
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
    (hr : run.AcceptedRoot cfg ext r) :
    r = anchorRoot ∨ r = childRoot ∨ r = carrierRoot := by
  obtain ⟨store, hstore, hknown⟩ := hr
  rcases causal_known_table hstore hknown with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

theorem acceptedBlockAt_cases {r : WitnessRoot} {b : BeaconBlock WitnessRoot}
    (h : run.AcceptedBlockAt cfg ext r b) :
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
    run.ParentEdge childRoot anchorRoot := by
  exact Or.inr ⟨0, 12, childSignedBlock, by simp [run, schedule], rfl, rfl⟩

theorem carrier_parentEdge :
    run.ParentEdge carrierRoot childRoot := by
  exact Or.inr ⟨0, 84, carrierSignedBlock, by simp [run, schedule], rfl, rfl⟩

theorem child_descends_anchor :
    run.RootDescends childRoot anchorRoot :=
  .step child_parentEdge (.refl anchorRoot)

theorem carrier_descends_child :
    run.RootDescends carrierRoot childRoot :=
  .step carrier_parentEdge (.refl childRoot)

theorem carrier_descends_anchor :
    run.RootDescends carrierRoot anchorRoot :=
  Execution.RootDescends.trans run carrier_descends_child
    child_descends_anchor

theorem parentEdge_val_lt {child parent : WitnessRoot}
    (h : run.ParentEdge child parent) : parent.val < child.val := by
  rcases h with hgen | hsched
  · obtain ⟨r, hr, rfl, rfl⟩ := hgen
    have hrAnchor : child = anchorRoot := by
      simpa [run, get_forkchoice_store, anchorSignedBlock] using hr
    subst child
    decide
  · obtain ⟨w, n, b, hb, hchild, hparent⟩ := hsched
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl
    · rw [hchild, hparent]
      decide
    · rw [hchild, hparent]
      decide

theorem rootDescends_val_le {source target : WitnessRoot}
    (h : run.RootDescends source target) :
    target.val ≤ source.val := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact ih.trans (Nat.le_of_lt (parentEdge_val_lt hedge))

theorem rootDescends_carrier_iff {r : WitnessRoot} :
    run.RootDescends r carrierRoot ↔ r = carrierRoot := by
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
    (hr : run.AcceptedRoot cfg ext r) :
    run.RootDescends r anchorRoot := by
  rcases acceptedRoot_cases hr with rfl | rfl | rfl
  · exact .refl anchorRoot
  · exact child_descends_anchor
  · exact carrier_descends_anchor

/-! ## Accepted inclusion and the substantive anchor-to-child link -/

def witnessIncluded (carrier : WitnessRoot)
    (a : Attestation WitnessRoot) : Prop :=
  carrier = carrierRoot ∧ (a = vote4 ∨ a = vote5 ∨ a = vote6)


theorem carrier_blockAt :
    run.BlockAt carrierRoot carrierSignedBlock.message := by
  exact Or.inr ⟨0, 84, carrierSignedBlock, by simp [run, schedule], rfl, rfl⟩

theorem includedVote_true_scheduled {s : Slot} (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    Event.attestation (vote s) true ∈ run.schedule 0 84 := by
  interval_cases s <;> simp [run, schedule,
    vote4, vote5, vote6]

theorem includedVote_data {s : Slot} (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    (vote s).data =
      { slot := s, index := 0, beacon_block_root := childRoot
        source := anchorCheckpoint, target := childEpochOneCheckpoint } := by
  interval_cases s <;> rfl

def acceptedIncludedEvidenceAt (s : Slot) (hlo : 4 ≤ s) (hhi : s ≤ 6) :
    Execution.CausalCarrierAttestationEvidence cfg
      ext run
      ext.is_valid_indexed_attestation carrierRoot (vote s) where
  carrier_message := carrierSignedBlock.message
  carrier_at := carrier_blockAt
  in_carrier_body := by
    interval_cases s <;> simp [carrierSignedBlock, vote4, vote5, vote6]
  received_from_block := ⟨0, 84, includedVote_true_scheduled hlo hhi⟩
  validation_state := ext.process_slots childState 4
  validation_registry := by
    simpa [ext] using witnessProcessSlots_registry childState 4
  valid := by
    apply (witness_valid_iff (ext.process_slots childState 4) (vote s)).2
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
    simpa [vote, run, witnessCommittee] using hi
  attesters_in_registry := by
    intro i hi
    have hi' : i = s % 4 := by simpa [vote] using hi
    subst i
    exact Nat.mod_lt s (by decide)
  carrier_accepted := carrier_acceptedBlockAt
  validation_store := childPostPrefix.store cfg ext
  validation_store_honest := by
    apply Execution.HonestCausalStore.scheduledPrefix childPostPrefix
    · decide
    · simpa [childPostPrefix, childPrefix] using
        (time_within (show 12 < 192 by decide))
  validation_target_known := by
    rw [includedVote_data hlo hhi]
    simpa [childSignedBlock] using childTransition.root_known
  validation_state_from_target := by
    interval_cases s <;> rfl

def witnessAcceptedIncludedAttestations :
    Execution.CausalCarrierAttestationRelation cfg
      ext run
      ext.is_valid_indexed_attestation where
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
      run.AcceptedBlockAt cfg ext carrier b ∧
        a ∈ b.attestations := by
  let ev := witnessAcceptedIncludedAttestations.evidence h
  exact ⟨ev.carrier_message, ev.carrier_accepted, ev.in_carrier_body⟩

def witnessIncludedAnchorChildLink :
    IncludedSupermajorityLink cfg run witnessIncluded
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
    HonestEarlierTargetVoteOnCarrierChain cfg ext
      run witnessIncluded carrierRoot childEpochOneCheckpoint := by
  refine ⟨carrierSignedBlock.message, carrier_acceptedBlockAt,
    0, ?_, 4, 51, vote4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [run]
  · decide
  · exact slot_within_of_lt_sixteen (by decide)
  · exact (recorded_vote_some_iff).2 ⟨by decide, rfl, rfl, rfl⟩
  · rfl
  · rfl
  · exact ⟨carrierRoot, .refl carrierRoot,
      ⟨rfl, Or.inl rfl⟩⟩

def witnessAcceptedChainFFGState :
    CausalCarrierFFGState cfg ext run
      anchorCheckpoint where
  attestationValidity := ext.is_valid_indexed_attestation
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
        simp_all [cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig, compute_epoch_at_slot, anchorSignedBlock,
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
        simp_all [cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig, compute_epoch_at_slot, anchorSignedBlock,
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
    (hstore : run.CausalStore cfg ext store) :
    store.blocks anchorRoot = anchorSignedBlock.message := by
  have hknown := causal_anchor_known hstore
  rcases causal_known_table hstore hknown with h | h | h
  · exact h.2
  · exact False.elim ((by decide : anchorRoot ≠ childRoot) h.1)
  · exact False.elim ((by decide : anchorRoot ≠ carrierRoot) h.1)

theorem causal_child_message {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store)
    (hknown : childRoot ∈ store.block_roots) :
    store.blocks childRoot = childSignedBlock.message := by
  rcases causal_known_table hstore hknown with h | h | h
  · exact False.elim ((by decide : childRoot ≠ anchorRoot) h.1)
  · exact h.2
  · exact False.elim ((by decide : childRoot ≠ carrierRoot) h.1)


theorem witnessCheckpointOfKnown {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store)
    (r : WitnessRoot) (hr : r ∈ store.block_roots) (e : Epoch) :
    witnessC r e = get_checkpoint_for_block cfg store r e := by
  have hanchor := causal_anchor_message hstore
  rcases causal_known_table hstore hr with hroot | hroot | hroot
  · rcases hroot with ⟨rfl, hroot⟩
    apply checkpoint_eq_of_epoch_root_eq <;>
      simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
      compute_start_slot_at_epoch,
      get_ancestor, get_ancestor_aux, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig, anchorSignedBlock,
      hanchor]
  · rcases hroot with ⟨rfl, hchild⟩
    cases e with
    | zero =>
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
          compute_start_slot_at_epoch,
          get_ancestor, get_ancestor_aux, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig, anchorSignedBlock,
          childSignedBlock, hanchor, hchild]
    | succ e =>
        have hstop : ¬ 1 > (e + 1) * 4 := by (try simp only [Slot, Epoch] at *); omega
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
          compute_start_slot_at_epoch,
          get_ancestor, get_ancestor_aux, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig, childSignedBlock,
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
          get_ancestor, get_ancestor_aux, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig, anchorSignedBlock,
          childSignedBlock, carrierSignedBlock, hanchor, hchild, hcarrier]
    | succ e =>
        cases e with
        | zero =>
            apply checkpoint_eq_of_epoch_root_eq <;>
              simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
              compute_start_slot_at_epoch,
              get_ancestor, get_ancestor_aux, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig,
              childSignedBlock, carrierSignedBlock, hchild, hcarrier] <;>
              simp [anchorRoot, childRoot, carrierRoot]
        | succ e =>
            have hstop : ¬ 7 > (e + 2) * 4 := by (try simp only [Slot, Epoch] at *); omega
            apply checkpoint_eq_of_epoch_root_eq <;>
              simp [witnessC, get_checkpoint_for_block, get_checkpoint_block,
              compute_start_slot_at_epoch,
              get_ancestor, get_ancestor_aux, cfg, TwelveSecondSynchronyWitness.cfg, witnessConfig,
              carrierSignedBlock, hcarrier, hstop] <;>
              simp [anchorRoot, childRoot, carrierRoot]

theorem witnessAU_cases {r : WitnessRoot} {c : Checkpoint WitnessRoot}
    (hAU : witnessAcceptedChainFFGState.AU cfg ext r c) :
    c = anchorCheckpoint ∨
      (r = carrierRoot ∧ c = childEpochOneCheckpoint) := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  change witnessFormed carrier c at hformed
  rcases hformed with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rootDescends_carrier_iff.mp hdesc, rfl⟩

theorem witnessAUCheckpointOfKnown {store : Store WitnessRoot}
    (hstore : run.CausalStore cfg ext store)
    (r : WitnessRoot) (hr : r ∈ store.block_roots)
    (c : Checkpoint WitnessRoot)
    (hAU : witnessAcceptedChainFFGState.AU cfg ext r c) :
    c = get_checkpoint_for_block cfg store r c.epoch := by
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


private theorem block_event_time {w n : ℕ} {b : SignedBeaconBlock R}
    (h : Event.block b ∈ run.schedule w n) : n = 12 ∨ n = 14 ∨ n = 84 := by
  rw [schedule_by_slot] at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 ho h0 h1 hslot14 hw1 hslot15
  · simp at h
  · simp at h
  · right; left; omega
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rcases (block_mem_schedule_iff (w := w)).mp h with ⟨hs, _⟩ | ⟨hs, _⟩
    · left; omega
    · right; right; omega
  · simp at h

private theorem schedule_class (w n : ℕ) :
    run.schedule w n = run.schedule (nodeClass w) n := by
  simp only [schedule_by_slot]
  by_cases h0 : w = 0
  · subst w; rfl
  by_cases h1 : w = 1
  · subst w; rfl
  simp [slotEvents, nodeClass, h0, h1, witnessSchedule]

private def receiptPrevious (row : Fin 3) : ℕ :=
  if row = 0 then 11 else if row = 1 then 13 else 83

private def postAt (w k i : ℕ) : Store R :=
  ((run.schedule w (k + 1)).take (i + 1)).foldl
    (fun st e => (apply_event cfg ext st e).getD st)
    (on_tick cfg (run.store cfg ext w k) (run.time_at (k + 1)))

private theorem postAt_class (w k i : ℕ) :
    postAt w k i = postAt (nodeClass w) k i := by
  simp only [postAt, schedule_class w (k + 1), store_nodeClass w k]

private def matchesBlock (event : Option (Event R)) (b : SignedBeaconBlock R) : Bool :=
  match event with
  | some (.block b') => decide (b' = b)
  | _ => false

private theorem transition_table : ∀ (w row : Fin 3),
    (run.schedule w (receiptPrevious row + 1)).length ≤ 5 ∧
    ∀ i : Fin 5,
      (matchesBlock ((run.schedule w (receiptPrevious row + 1))[i.val]?) childSignedBlock = true →
        SameProjectedState ((postAt w (receiptPrevious row) i).block_states childRoot) childState) ∧
      (matchesBlock ((run.schedule w (receiptPrevious row + 1))[i.val]?) carrierSignedBlock = true →
        SameProjectedState ((postAt w (receiptPrevious row) i).block_states carrierRoot) carrierState) := by
  set_option maxRecDepth 50000 in decide

theorem acceptedTransition_cases
    (t : run.AcceptedBlockTransition cfg ext) :
    (t.signedBlock = childSignedBlock ∧
      t.postStore.block_states childRoot = childState) ∨
    (t.signedBlock = carrierSignedBlock ∧
      t.postStore.block_states carrierRoot = carrierState) := by
  have heventMem : Event.block t.signedBlock ∈
      run.schedule t.atPrefix.node (t.atPrefix.previousSecond + 1) := by
    obtain ⟨hlt, hevent⟩ := List.getElem?_eq_some_iff.mp t.event_at
    have hmem := List.getElem_mem hlt
    rw [hevent] at hmem
    exact hmem
  have hrow : ∃ row : Fin 3, t.atPrefix.previousSecond = receiptPrevious row := by
    rcases block_event_time heventMem with h | h | h
    · exact ⟨0, by change _ = 11; omega⟩
    · exact ⟨1, by change _ = 13; omega⟩
    · exact ⟨2, by change _ = 83; omega⟩
  obtain ⟨row, hrow⟩ := hrow
  let w : Fin 3 := ⟨nodeClass t.atPrefix.node, nodeClass_lt _⟩
  have hevent := t.event_at
  rw [schedule_class t.atPrefix.node, hrow] at hevent
  have hlt : t.atPrefix.processedCount < 5 := by
    have h := (List.getElem?_eq_some_iff.mp hevent).1
    exact h.trans_le (transition_table w row).1
  let i : Fin 5 := ⟨t.atPrefix.processedCount, hlt⟩
  have hpost : t.postStore = postAt w (receiptPrevious row) i := by
    rw [← t.successorPrefix_store]
    change postAt t.atPrefix.node t.atPrefix.previousSecond t.atPrefix.processedCount = _
    rw [postAt_class, hrow]
  rcases scheduledBlock_cases ⟨_, _, heventMem⟩ with hb | hb
  · left
    refine ⟨hb, ?_⟩
    rw [hpost]
    apply sameProjectedState_iff_eq.mp
    exact ((transition_table w row).2 i).1 (by simp only [hb] at hevent; simp [matchesBlock, hevent, i, w])
  · right
    refine ⟨hb, ?_⟩
    rw [hpost]
    apply sameProjectedState_iff_eq.mp
    exact ((transition_table w row).2 i).2 (by simp only [hb] at hevent; simp [matchesBlock, hevent, i, w])
theorem genesis_known_eq_anchor {r : WitnessRoot}
    (hr : r ∈ run.genesis_store.block_roots) :
    r = anchorRoot := by
  simpa [run, get_forkchoice_store, anchorSignedBlock] using hr

def witnessAcceptedFFGTransitionCoherence :
    FFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext
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
    CausalPrefixFFGInterpretation cfg ext
      run where
  anchor := anchorCheckpoint
  state := witnessAcceptedChainFFGState
  coherence := witnessAcceptedFFGTransitionCoherence


/-! ## Public selector/AU reductions -/









theorem witnessAU_carrier_anchor :
    witnessAcceptedChainFFGState.AU cfg ext
      carrierRoot anchorCheckpoint :=
  ⟨carrierRoot, .refl carrierRoot, witnessFormed_carrier_anchor⟩

theorem witnessAU_carrier_child :
    witnessAcceptedChainFFGState.AU cfg ext
      carrierRoot childEpochOneCheckpoint :=
  ⟨carrierRoot, .refl carrierRoot, witnessFormed_carrier_child⟩

/-! ## Accepted checkpoint projection -/

def witnessAcceptedEpochCheckpointProjection :
    EpochCheckpointClosure anchorCheckpoint
      (run.AcceptedRoot cfg ext) witnessC where
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
    (L : IncludedSupermajorityLink cfg run
      witnessIncluded carrier source target) :
    carrier = carrierRoot ∧ source = anchorCheckpoint ∧
      target = childEpochOneCheckpoint := by
  have hsigners : L.signers.Nonempty := by
    by_contra hnone
    have hempty : L.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * run.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using L.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by (try simp only [Slot, Epoch] at *); omega)
        (run.total_active_pos cfg))
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
    intro carrier source target L hcontributing
    change IncludedSupermajorityLink cfg run
      witnessIncluded carrier source target at L
    rcases witnessIncludedLink_cases L with ⟨rfl, hsource, htarget⟩
    exact carrier_accepted
  endpoints_on_carrier := by
    intro carrier source target L hcontributing
    change IncludedSupermajorityLink cfg run
      witnessIncluded carrier source target at L
    obtain ⟨rfl, rfl, rfl⟩ := witnessIncludedLink_cases L
    exact ⟨rfl, rfl⟩

/-! ## Included votes are pairwise non-slashable -/

theorem witness_hasSlashablePairOnChain_false (tip : WitnessRoot)
    (i : ValidatorIndex) :
    ¬ witnessAcceptedChainFFGState.HasSlashablePairOnChain
      cfg ext tip i := by
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
      cfg ext tip = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  exact witness_hasSlashablePairOnChain_false tip i
    ((witnessAcceptedChainFFGState.mem_slashableOnChain
      cfg ext tip i).mp hi)

end FastConfirmation.Spec.FullTwelveEnvelopeWitness
end
