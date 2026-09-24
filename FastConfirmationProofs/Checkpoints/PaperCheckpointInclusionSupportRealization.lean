module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.FFG.CurrentTarget.HonestVoteTargetCache
public import FastConfirmationProofs.Checkpoints.GlobalResetCheckpointRealization
public import FastConfirmationProofs.FFG.State.ScheduledFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.Certificates.FFGAccountability
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks
public import FastConfirmationProofs.FFG.SelectedSource.SelectedTraceFFGRealization
public import FastConfirmationProofs.ModelFacts
public import FastConfirmationProofs.FCRRule.MinimalSelectedDomain
public import FastConfirmationProofs.FFG.Certificates.PaperCheckpointInclusionProjectionCore

@[expose] public section

/-!
# Concrete realization of one paper-A3.2 support record

The repaired A3.2 interface keeps one fixed source while the descendant only
indexes `D_b'`.  This module packages the mechanical endpoint step: a concrete
honest quorum produced by the current-target gate becomes the exact
source-specific, received, valid, non-slashable support record at an honest
epoch-`e+1` view.

No AU inclusion, filter, head, ancestry, or safety conclusion is assumed.  The
target root and checkpoint-state key are ordinary endpoint-domain facts; they
remain explicit because the totalized executable maps otherwise contain junk
outside their finite domains.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- `slot_start` is monotone in its slot argument. -/
private theorem slot_start_mono_for_paperA32 {a b : Slot} (hab : a ≤ b) :
    E.slot_start cfg a ≤ E.slot_start cfg b := by
  simp only [Execution.slot_start]
  apply Nat.sub_le_sub_right
  apply Nat.add_le_add_left
  exact Nat.div_le_div_right
    (Nat.mul_le_mul_right cfg.slot_duration_ms hab)

/-- A concrete committee assignment is necessarily a ground-registry index.
Outside the list domain, `getD` is the inactive default validator, contrary to
`committee_members_active`. -/
private theorem concreteVote_signer_in_registry
    (hec : BeaconExternalsPremises cfg ext E)
    {i : ValidatorIndex} {deadline : Slot} {target : Checkpoint Root}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target) :
    i ∈ Finset.range E.registry.length := by
  rw [Finset.mem_range]
  have hactive := hec.committee_members_active i vote.slot
    vote.slot_within_horizon vote.assigned
  by_contra hi
  have hget : E.registry.getD i default = default := by
    simp [List.getD, Nat.le_of_not_gt hi]
  rw [hget] at hactive
  simp only [is_active_validator, decide_eq_true_eq] at hactive
  have hbad : compute_epoch_at_slot cfg vote.slot < 0 := by
    simpa only [Validator.exit_epoch, default] using hactive.2
  exact (Nat.not_lt_zero _ hbad)

/-- Honest validators are absent from the generic paper view's concrete
block-local slashing set.  The proof uses the retained inclusion evidence;
it does not assume a broad block-body completeness principle. -/
theorem honest_not_mem_paperA32SlashableOnChain
    (hhb : HonestBehavior cfg ext E)
    (V : PaperA32StateView cfg E)
    {tip : Root} {i : ValidatorIndex} (hi : i ∈ E.honest) :
    i ∉ V.slashableOnChain cfg tip := by
  classical
  intro hmem
  have hpair : V.HasSlashablePairOnChain cfg tip i :=
    (Finset.mem_filter.mp hmem).2
  obtain ⟨a₁, a₂, hinc₁, hinc₂, hi₁, hi₂, hslash⟩ := hpair
  obtain ⟨_carrier₁, _hdesc₁, hincluded₁⟩ := hinc₁
  obtain ⟨_carrier₂, _hdesc₂, hincluded₂⟩ := hinc₂
  obtain ⟨w₁, n₁, hsched₁⟩ :=
    (V.includedAttestations.evidence hincluded₁).received_from_block
  obtain ⟨w₂, n₂, hsched₂⟩ :=
    (V.includedAttestations.evidence hincluded₂).received_from_block
  obtain ⟨k₁, vote₁, _hcausal₁, hvote₁, hdata₁⟩ :=
    hhb.no_forgery w₁ n₁ a₁ true hsched₁ i hi hi₁
  obtain ⟨k₂, vote₂, _hcausal₂, hvote₂, hdata₂⟩ :=
    hhb.no_forgery w₂ n₂ a₂ true hsched₂ i hi hi₂
  have hslashGround :
      is_slashable_attestation_data vote₁.data vote₂.data = true := by
    rw [← hdata₁, ← hdata₂]
    exact hslash
  have hnot := hhb.not_slashable i hi a₁.data.slot a₂.data.slot
    k₁ k₂ vote₁ vote₂ hvote₁ hvote₂
  rw [hslashGround] at hnot
  contradiction

/-- Concrete honest gate votes realize one exact paper-facing support record
at every endpoint after their common deadline.

`hsource` is only equality of the actual vote data with the fixed source; its
state-semantic derivation is G3's phase0/source-coherence result.  `hknown` and
`hkeyed` are finite-map domain facts, not an AU or safety conclusion. -/
theorem paperA32LinkSupportAtCore_of_concreteHonestTargetVotes
    (hhb : HonestBehavior cfg ext E)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    {V : PaperA32StateView cfg E}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hdeadline : deadline ≤ E.slot_at cfg m)
    {b' : Root}
    (hknown : target.root ∈ (E.store cfg ext w m).block_roots)
    (hkeyed : target ∈ (E.store cfg ext w m).checkpoint_state_keys) :
    Nonempty (PaperA32LinkSupportAtCore cfg ext V
      w m b' Q.source target) := by
  refine ⟨{
    view_within_horizon := hHm
    source_before_target := Q.source_before_target
    target_epoch_within := Q.target_epoch_within
    target_known := hknown
    target_state_keyed := hkeyed
    signers := Q.signers
    signers_not_slashable := ?_
    signers_in_registry := ?_
    signer_attestation := ?_
    supermajority := Q.supermajority }⟩
  · intro i hi
    obtain ⟨vote⟩ := Q.votes i hi
    exact E.honest_not_mem_paperA32SlashableOnChain cfg ext
      hhb V vote.honest
  · intro i hi
    obtain ⟨vote⟩ := Q.votes i hi
    exact concreteVote_signer_in_registry (cfg := cfg) (ext := ext)
      (E := E) hec vote
  · intro i hi
    obtain ⟨vote⟩ := Q.votes i hi
    let a := honest_attestation cfg ext (E.store cfg ext i vote.time)
      vote.slot vote.index i
    have hslot : vote.slot + 1 ≤ E.slot_at cfg m :=
      (Nat.succ_le_of_lt vote.before_deadline).trans hdeadline
    refine ⟨a,
      E.concreteVote_receivedBy cfg ext hsync hdiv hgenTime vote hw hHm hslot,
      ?_, ?_, vote.slot_within_horizon, ?_, vote.slot_epoch,
      vote.assigned, ?_, ?_⟩
    · simp only [a, honest_attestation_attesting_indices,
        List.mem_singleton]
    · apply hec.honest_attestation_valid _ a
        ((E.honestCausalStore_store cfg ext w m hw hHm).checkpointState
          cfg ext hkeyed) i vote.honest
      · simp only [a, honest_attestation_attesting_indices]
      · simpa only [a, honest_attestation_data_eq,
          honest_attestation_data_slot] using vote.assigned
      · exact ⟨vote.time, a,
          by simpa only [a] using vote.vote, rfl⟩
    · exact (Nat.le_succ vote.slot).trans hslot
    · simpa only [a] using Q.source_agreement i hi vote
    · simpa only [a] using vote.target_eq



/-- One fixed concrete gate quorum realizes the complete support antecedent
of paper Assumption 3.2 throughout the following epoch.

The proof does not assume endpoint target knownness or cache membership.  A
single signer exists because the certified quorum has positive total weight.
Its honest vote supplies the target root in the source store; block relay
propagates that root, and the actual attestation handler supplies and preserves
the checkpoint-state key.  Cross-store block agreement keeps Definition 7's
fixed `VSAt(b,e)` source identical in every view. -/
theorem paperA32SupportThroughoutEpochCore_of_concreteQuorum
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {V : PaperA32StateView cfg E}
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {b : Root} {e : Epoch}
    (hbQuery : b ∈ (E.store cfg ext v q).block_roots)
    (hbEpochQuery : get_block_epoch cfg (E.store cfg ext v q) b = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg (e + 1)) (V.C b e))
    (hsourceQuery : Q.source =
      V.VSAt cfg (E.store cfg ext v q) b e) :
    PaperA32SupportThroughoutEpochCore cfg ext V b e := by
  classical
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hanchorParent⟩ := hgen
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk
      hgenSlot hanchorParent
  have hgenTime :
      E.genesis_store.genesis_time ≤ E.genesis_store.time :=
    hgws.time_ge_genesis
  have hsignersNonempty : Q.signers.Nonempty := by
    by_contra hnone
    have hempty : Q.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * E.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using Q.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega) (E.total_active_pos cfg))
  obtain ⟨i, hiSigner⟩ := hsignersNonempty
  obtain ⟨vote⟩ := Q.votes i hiSigner
  let voteStore := E.store cfg ext i vote.time
  let a := honest_attestation cfg ext voteStore vote.slot vote.index i
  have hvoteFromZero : E.slot_at cfg 0 ≤ vote.slot := by
    rw [← vote.slot_at_time]
    exact E.slot_at_mono cfg (Nat.zero_le vote.time)
  have hvoteWalk : WalkKnown voteStore
      (compute_start_slot_at_epoch cfg a.data.target.epoch)
      (get_head cfg voteStore).root := by
    simpa only [voteStore, a] using
      hwalkDomain i vote.honest vote.slot vote.time vote.index
        hvoteFromZero vote.time_within_horizon vote.slot_at_time vote.vote
  have hvoteHeadKnown : a.data.beacon_block_root ∈
      voteStore.block_roots := by
    simpa only [a, honest_attestation_data_eq,
      honest_attestation_data_beacon_block_root] using hvoteWalk.root_mem
  have hvoteParentSlots : ParentSlotLt voteStore := by
    simpa only [voteStore] using
      E.store_parentSlotLt cfg ext hwf hec
        ⟨ast, ablk, hgenEq, hgenSlot, hanchorParent⟩
        hwf.anchor_parent_unscheduled i vote.time
  have hvoteTargetKnown : (V.C b e).root ∈ voteStore.block_roots := by
    have htargetData : (honest_attestation_data cfg ext voteStore
        vote.slot vote.index).target = V.C b e := by
      simpa only [voteStore, honest_attestation_data_eq] using vote.target_eq
    have hroot : (V.C b e).root = get_checkpoint_block cfg voteStore
        (get_head cfg voteStore).root (V.C b e).epoch := by
      calc
        (V.C b e).root =
            (honest_attestation_data cfg ext voteStore
              vote.slot vote.index).target.root :=
          congrArg Checkpoint.root htargetData.symm
        _ = get_checkpoint_block cfg voteStore
            (get_head cfg voteStore).root (V.C b e).epoch := by
          rw [honest_attestation_data_target_root]
          exact congrArg (get_checkpoint_block cfg voteStore
            (get_head cfg voteStore).root)
            (congrArg Checkpoint.epoch htargetData)
    have hancestorRoot :
        (get_ancestor voteStore
          (ForkChoiceNode.mk (get_head cfg voteStore).root .pending)
          (compute_start_slot_at_epoch cfg (V.C b e).epoch)).root =
            (V.C b e).root := by
      simpa only [get_checkpoint_block] using hroot.symm
    have hspec := get_ancestor_spec hvoteParentSlots (by
      simpa only [a, honest_attestation_data_eq, htargetData] using hvoteWalk)
    rw [hancestorRoot] at hspec
    exact hspec.1
  intro w hw m hHm hmEpoch
  have hview := hcanonical w hw m hHm hmEpoch
  have hbView : b ∈ (E.store cfg ext w m).block_roots := hview.1
  have hbBlocks : (E.store cfg ext v q).blocks b =
      (E.store cfg ext w m).blocks b :=
    hwf.blocks_agree
      (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m)
      hbQuery hbView
  have hbEpochView : get_block_epoch cfg (E.store cfg ext w m) b = e := by
    simp only [get_block_epoch]
    rw [← hbBlocks]
    exact hbEpochQuery
  refine ⟨hbView, hbEpochView.le, ?_⟩
  intro b' hb' _hb'Target
  have hdeadline : compute_start_slot_at_epoch cfg (e + 1) ≤
      E.slot_at cfg m := by
    have hepochLe : e + 1 ≤
        compute_epoch_at_slot cfg (E.slot_at cfg m) := hmEpoch.ge
    simpa only [compute_start_slot_at_epoch] using
      (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hepochLe
  have hvoteSlotDelivery : vote.slot + 1 ≤ E.slot_at cfg m :=
    (Nat.succ_le_of_lt vote.before_deadline).trans hdeadline
  have hdeliveryLe : E.slot_start cfg (vote.slot + 1) ≤ m := by
    exact (slot_start_mono_for_paperA32 cfg E hvoteSlotDelivery).trans
      (E.slot_start_le_of_slot_at cfg hdiv hgenTime rfl)
  have htargetKeyed : V.C b e ∈
      (E.store cfg ext w m).checkpoint_state_keys := by
    have hcached := E.honestVoteTarget_cached cfg ext hwf hhb hsync hpaths hec
      hdiv ⟨ast, ablk, hgenEq, hgenSlot, hanchorParent⟩
      vote.honest hw vote.slot_at_time vote.time_within_horizon vote.vote
      hvoteHeadKnown hvoteWalk hdeliveryLe hHm
    simpa only [a, voteStore, vote.target_eq] using hcached
  have htargetKnown : (V.C b e).root ∈
      (E.store cfg ext w m).block_roots := by
    have hreceived := E.honestVoteTarget_known cfg ext hwf hhb hsync hpaths hec
      hdiv ⟨ast, ablk, hgenEq, hgenSlot, hanchorParent⟩
      vote.honest hw vote.slot_at_time vote.time_within_horizon vote.vote
      hvoteHeadKnown hvoteWalk hdeliveryLe hHm
    simpa only [a, voteStore, vote.target_eq] using hreceived
  have hsourceView : Q.source =
      V.VSAt cfg (E.store cfg ext w m) b e := by
    apply hsourceQuery.trans
    simp only [PaperA32StateView.VSAt]
    rw [hbEpochQuery, hbEpochView]
  have hsupport := E.paperA32LinkSupportAtCore_of_concreteHonestTargetVotes
    cfg ext hhb hsync hpaths hec hdiv hgenTime Q (V := V)
      hw hHm hdeadline
      (b' := b') htargetKnown htargetKeyed
  rw [← hsourceView]
  exact hsupport


/-- Accepted-state realization of the full source-specific A.3.2 support
antecedent.  It shares the generic proof and introduces no legacy state. -/
theorem accepted_paperA32SupportThroughoutEpoch_of_concreteQuorum
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    {S : CausalCarrierFFGState cfg ext E anchor}
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {b : Root} {e : Epoch}
    (hbQuery : b ∈ (E.store cfg ext v q).block_roots)
    (hbEpochQuery : get_block_epoch cfg (E.store cfg ext v q) b = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg (e + 1)) (S.C b e))
    (hsourceQuery : Q.source =
      S.VSAt cfg ext (E.store cfg ext v q) b e) :
    S.PaperA32SupportThroughoutEpoch cfg ext b e :=
  E.paperA32SupportThroughoutEpochCore_of_concreteQuorum cfg ext
    hwf hhb hsync hpaths hec hdiv hgen hwalkDomain hv hqH hbQuery
    hbEpochQuery hcanonical Q hsourceQuery

/-- Accepted end-to-end A.3.2 consumer: one concrete fixed-source quorum
realizes the full next-epoch support antecedent, and the paper assumption
returns an exact AU/formed-carrier witness together with its executable
projection.  No migration state occurs in this dependency theorem. -/
theorem accepted_paperA32IncludedAtTip_of_concreteQuorum
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    {S : CausalCarrierFFGState cfg ext E anchor}
    (hcoh : FFGSelectorsMatchBeaconStates cfg ext S)
    (hpaper : S.PaperA32Inclusion cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {b : Root} {e : Epoch}
    (hbQuery : b ∈ (E.store cfg ext v q).block_roots)
    (hbEpochQuery : get_block_epoch cfg (E.store cfg ext v q) b = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg (e + 1)) (S.C b e))
    (hsourceQuery : Q.source =
      S.VSAt cfg ext (E.store cfg ext v q) b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg (S.paperA32Inputs cfg ext)
        (E.store cfg ext w m) e b seed := by
  have hsupport :=
    E.accepted_paperA32SupportThroughoutEpoch_of_concreteQuorum cfg ext
      hwf hhb hsync hpaths hec hdiv hgen hwalkDomain hv hqH hbQuery
      hbEpochQuery hcanonical Q hsourceQuery
  exact E.accepted_paperA32IncludedAtTip_of_paper_at_known cfg ext
    hcoh hpaper hbQuery hbEpochQuery.le hcanonical hsupport
    hw hHm hboundary

end Execution

end FastConfirmation.Spec

end
