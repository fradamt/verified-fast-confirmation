module
public import FastConfirmationProofs.FFG.SelectedSource.PhaseSourceCarriers
public import FastConfirmationProofs.Handlers.ResetAdoption
public import FastConfirmationProofs.Safety.FinalizedCheckpointNextSlotSafety
public import FastConfirmationProofs.Weak.Safety.WeakOneShotSafety
public import FastConfirmationProofs.Weak.Selection.WeakAncestryEndpoint

@[expose] public section

/-!
# Honest origin of a store-read finalized checkpoint

The accepted finalized-adoption theorem
`finalized_epoch_le_remoteJustified_of_synchrony` relays *every* root held by
the store whose finalized field is read.  That relay step is exactly the
observer-honesty site the weak model removes: a non-honest observer's store
contents propagate nowhere.

This file replaces that step by the finalizing certificate's own honest
signer.  A non-anchor finalized field carried by any exact causal store owns
an included finalizing link; two quorums of that link intersect in an honest
validator, whose genuine attestation read its source off its own store.  The
honest voting-source readback
(`acceptedHonestAttestationDataSourceEqVSAtTarget`) turns that read into the
executable `get_voting_source` of the link's target at the signer's store, and
the vote precedes the reading store's current slot because the including block
does.  Honest-to-honest block relay then carries the signer's own seed root to
every honest endpoint, where accepted justified maximality adopts the epoch.

Nothing here assumes the reading store's node is honest, and no conclusion is
a confirmation, filter, head, ancestry, or `SafeFrom` statement.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Anchor geometry at an exact causal store

The three store-local facts the inclusion-timing argument needs below hold at
every exact causal store, not only at the per-second boundary stores: the
genesis case *is* a boundary store, and the strict in-second prefixes have
their own geometry lemmas. -/

private theorem causalStore_nonAnchorParentKnown
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    NonAnchorParentKnown ablk.root store := by
  cases hstore with
  | genesis => exact E.store_nonAnchorParentKnown cfg ext hgen 0 0
  | scheduledPrefix p => exact p.nonAnchorParentKnown cfg ext hgen

private theorem causalStore_anchorBlock
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hr : ablk.root ∈ store.block_roots) :
    store.blocks ablk.root = ablk.message := by
  cases hstore with
  | genesis => exact E.store_anchor_block cfg ext hwf hgen 0 0 hr
  | scheduledPrefix p => exact p.anchorBlock cfg ext hwf hgen hr

private theorem causalStore_blocks_slot_le_current
    (hT : E.ScheduledPrefixPremises cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    ∀ r ∈ store.block_roots,
      (store.blocks r).slot ≤ get_current_slot cfg store := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  cases hstore with
  | genesis =>
      exact E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgenEq, hslot⟩ 0 0
  | scheduledPrefix p => exact p.blocksSlotLeCurrent cfg ext E hT

/-- A semantic execution ancestor of a root known at an exact causal store is
itself known there.  This is the knownness half of
`store_known_ancestor_of_rootDescends_for_storeReflection`, re-proved without
the executable-ancestry conclusion so that it needs no walk geometry and
applies at strict in-second prefixes. -/
private theorem causalStore_known_ancestor_of_rootDescends
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {tip ancestor : Root}
    (htip : tip ∈ store.block_roots)
    (hancestorRoot : E.ExecutionRoot ancestor)
    (hdesc : E.RootDescends tip ancestor) :
    ancestor ∈ store.block_roots := by
  have hprovenance : BlockProvenance E store :=
    Execution.CausalStore.blockProvenance cfg ext E hstore
  have hnonAnchor : NonAnchorParentKnown ablk.root store :=
    E.causalStore_nonAnchorParentKnown cfg ext hgen hstore
  have hreflect : ∀ {a b : Root}, E.RootDescends a b →
      a ∈ store.block_roots → E.ExecutionRoot b → b ∈ store.block_roots := by
    intro a b hab
    induction hab with
    | refl r =>
        intro hr _
        exact hr
    | @step child parent target hedge hrest ih =>
        intro hchild htargetRoot
        have hparentRoot : E.ExecutionRoot parent :=
          RootDescends.source_executionRoot_for_storeReflection
            (E := E) hrest htargetRoot
        have hpEq : parent = (store.blocks child).parent_root :=
          E.parentEdge_parent_eq_of_store_known_for_storeReflection
            hwf hprovenance hchild hedge
        have hchildNeAnchor : child ≠ ablk.root := by
          intro hchildAnchor
          subst child
          have hanchorBlock : store.blocks ablk.root = ablk.message :=
            E.causalStore_anchorBlock cfg ext hwf hgen hstore hchild
          have hpEq' : parent = ablk.message.parent_root := by
            rw [hanchorBlock] at hpEq
            exact hpEq
          apply E.anchorParent_not_executionRoot_for_storeReflection
            cfg hwf hgen hparent
          rwa [← hpEq']
        have hparentKnown : parent ∈ store.block_roots := by
          have hp := (hnonAnchor child hchild).resolve_left hchildNeAnchor
          rwa [← hpEq] at hp
        exact ih hparentKnown htargetRoot
  exact hreflect hdesc htip hancestorRoot

/-- Causal-store form of `includedAttestationSlot_lt_acceptedCarrierBlock`:
an attestation included on a known carrier's chain was cast strictly before
the reading store's current slot.

Unlike the carrier-block form, this bound is stated against the store clock,
which is what a relay gate consumes. -/
theorem includedAttestationSlot_lt_causalStoreCurrentSlot
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {carrier : Root} (hcarrier : carrier ∈ store.block_roots)
    {a : Attestation Root}
    (hchain : AttestationIncludedOnChain E
      B.state.includedAttestations.Included carrier a) :
    a.data.slot < get_current_slot cfg store := by
  obtain ⟨containing, hcarrierContaining, hincluded⟩ := hchain
  have hevidence := B.state.includedAttestations.evidence hincluded
  obtain ⟨_ast, _ablk, hgenEq, _hslot, hparent⟩ := hT.genesis_structure
  have hcontainingRoot : E.ExecutionRoot containing :=
    ⟨hevidence.carrier_message, hevidence.carrier_at⟩
  have hcontainingKnown : containing ∈ store.block_roots :=
    E.causalStore_known_ancestor_of_rootDescends cfg ext hT.wellFormed
      hgenEq hparent hstore hcarrier hcontainingRoot hcarrierContaining
  have hcontainingBlock : store.blocks containing =
      hevidence.carrier_message :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed hstore hcontainingKnown).mp hevidence.carrier_accepted
  calc
    a.data.slot < hevidence.carrier_message.slot :=
      hevidence.slot_before_carrier
    _ = (store.blocks containing).slot :=
      (congrArg BeaconBlock.slot hcontainingBlock).symm
    _ ≤ get_current_slot cfg store :=
      E.causalStore_blocks_slot_le_current cfg ext hT hstore
        containing hcontainingKnown

/-! ## The honest origin of a finalized field -/

/-- The honest origin of a non-anchor finalized checkpoint read at some exact
causal store.

`signer` is an honest signer of the certificate's finalizing link, `time` the
second at which it cast that link's attestation, and `seed` the link's target
root, known at the signer's own store.  The two readback fields record what
the signer's store computed at that root: its executable voting source is the
finalized checkpoint itself, and the signer's clock was exactly one epoch
above it.

The record deliberately mentions the reading store only through its finalized
field and its clock.  No membership, honesty, or delivery property of the
reading node is asserted. -/
structure FinalizedHonestVotingSourceOrigin
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (store : Store Root) where
  signer : ValidatorIndex
  signer_honest : signer ∈ E.honest
  time : ℕ
  time_within : E.WithinHorizon cfg time
  slot_before : E.slot_at cfg time < get_current_slot cfg store
  seed : Root
  seed_known : seed ∈ (E.store cfg ext signer time).block_roots
  time_due : time ≤ E.slot_start cfg (E.slot_at cfg time) +
    get_attestation_due_ms cfg / 1000
  seed_walk_slot : Slot
  seed_head_walk : WalkKnown (E.store cfg ext signer time) seed_walk_slot
    (get_head cfg (E.store cfg ext signer time)).root
  seed_lands : (get_ancestor (E.store cfg ext signer time)
    (get_node_for_root (get_head cfg (E.store cfg ext signer time)).root)
    seed_walk_slot).root = seed
  seed_epoch : get_current_store_epoch cfg (E.store cfg ext signer time) =
    store.finalized_checkpoint.epoch + 1
  voting_source_eq :
    get_voting_source cfg (E.store cfg ext signer time) seed =
      store.finalized_checkpoint

/-- Every finalized field of an exact causal store is either the trusted
anchor or has an honest voting-source origin.

The honest signer is produced by self-intersection of the finalizing link's
quorum; genuineness of its attestation comes from `no_forgery` plus
`votes_head`, and the source readback from the accepted VSAt bridge at the
finalizing link's *target* (not the reading store's current target).  The
readback's non-genesis side condition is re-derived here from
`B.anchor.epoch < child.epoch`, which the certificate supplies through
`CertifiedJustified.anchor_epoch_le` and the link's `source_before_target`. -/
theorem finalizedHonestVotingSourceOrigin_of_causalStore
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.finalized_checkpoint = B.anchor ∨
      Nonempty (E.FinalizedHonestVotingSourceOrigin cfg ext B store) := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate cfg ext B
      hgenShort hanchor hstore with hanchorField | ⟨tip, htip, ⟨F⟩⟩
  · exact Or.inl hanchorField
  right
  -- The finalizing link and its honest signer.
  let child := F.child
  let globalLink : SupermajorityLink cfg E store.finalized_checkpoint child :=
    IncludedSupermajorityLink.toSupermajorityLink (cfg := cfg)
      (Execution.CausalCarrierAttestationRelation.relation cfg ext E
        B.state.includedAttestations) F.finalizing_link
  obtain ⟨i, hiGlobal, _hiGlobal', hiHonest⟩ :=
    E.links_intersect_honest cfg ext hacc globalLink globalLink
  have hiLink : i ∈ F.finalizing_link.signers := hiGlobal
  obtain ⟨a, hchain, hiAttests, _haSource, haTarget⟩ :=
    F.finalizing_link.signer_attestation i hiLink
  obtain ⟨_containing, _hcarrierContaining, hincluded⟩ := hchain
  have hevidence := B.state.includedAttestations.evidence hincluded
  -- Genuineness: the included attestation is the signer's own honest vote.
  obtain ⟨sender, sentAt, hscheduled⟩ := hevidence.received_from_block
  obtain ⟨_groundTime, groundVote, _hcausal, hvoteGround, hdataGround⟩ :=
    hacc.honest_behavior.no_forgery sender sentAt a true hscheduled
      i hiHonest hiAttests
  have hcommittee : i ∈ E.committee a.data.slot :=
    hevidence.attesters_in_committee i hiAttests
  -- The link's target epoch is strictly above the trusted anchor.
  have hsourceCertified : CertifiedJustified cfg E B.anchor
      store.finalized_checkpoint :=
    IncludedCertifiedJustified.toCertifiedJustified (cfg := cfg)
      (Execution.CausalCarrierAttestationRelation.relation cfg ext E
        B.state.includedAttestations) F.justified
  have hanchorLtTarget : B.anchor.epoch < child.epoch :=
    lt_of_le_of_lt
      (CertifiedJustified.anchor_epoch_le (cfg := cfg) hsourceCertified)
      F.finalizing_link.source_before_target
  have hslotEpoch : compute_epoch_at_slot cfg a.data.slot = child.epoch := by
    rw [← hevidence.target_epoch, haTarget]
  -- The vote is not older than the anchor boundary, so `votes_head` applies.
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hslotZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext i 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg hacc.whole_seconds]
      at hcurrent0
    exact hcurrent0.symm
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstartVote : compute_start_slot_at_epoch cfg child.epoch ≤
      a.data.slot := by
    have hmulDiv := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
    have hdiv : a.data.slot / cfg.slots_per_epoch = child.epoch := by
      simpa only [compute_epoch_at_slot] using hslotEpoch
    rw [hdiv] at hmulDiv
    simpa only [compute_start_slot_at_epoch] using hmulDiv
  have hfromZero : E.slot_at cfg 0 ≤ a.data.slot := by
    calc
      E.slot_at cfg 0 = ast.slot := hslotZero
      _ = ablk.message.slot := hslot
      _ ≤ compute_start_slot_at_epoch cfg B.anchor.epoch := hboundary'
      _ ≤ compute_start_slot_at_epoch cfg child.epoch :=
        Nat.mul_le_mul_right cfg.slots_per_epoch hanchorLtTarget.le
      _ ≤ a.data.slot := hstartVote
  obtain ⟨k, index, hHk, hkSlot, hvoteHead⟩ :=
    hacc.honest_behavior.votes_head i hiHonest a.data.slot hcommittee
      hevidence.slot_within_horizon hfromZero
  rw [hvoteHead] at hvoteGround
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteGround
  obtain ⟨_, hgroundVote⟩ := hvoteGround
  have hdata : a.data =
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data :=
    hdataGround.trans
      (congrArg (fun x : Attestation Root => x.data) hgroundVote.symm)
  -- Store geometry at the signer's own store.
  have hvoteCausal : E.CausalStore cfg ext (E.store cfg ext i k) :=
    E.store_causal cfg ext i k
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore_of_trajectory cfg ext hT
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hparentSlots : ParentSlotLt (E.store cfg ext i k) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled i k
  have htargetData : (honest_attestation_data cfg ext
      (E.store cfg ext i k) a.data.slot index).target = child := by
    rw [← honest_attestation_data_eq, ← hdata]
    exact haTarget
  have hwalk : WalkKnown (E.store cfg ext i k)
      (compute_start_slot_at_epoch cfg child.epoch)
      (get_head cfg (E.store cfg ext i k)).root := by
    have hwalkVote := hwalkDomain i hiHonest a.data.slot k index hfromZero
      hHk hkSlot hvoteHead
    simpa only [honest_attestation_data_eq, htargetData] using hwalkVote
  -- The link target is known at the signer's store, at or below the boundary.
  have hlands : (get_ancestor (E.store cfg ext i k)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (compute_start_slot_at_epoch cfg child.epoch)).root = child.root := by
    have hroot := honest_attestation_data_target_root cfg ext
      (E.store cfg ext i k) a.data.slot index
    rw [htargetData] at hroot
    have hcheckpoint : get_checkpoint_block cfg (E.store cfg ext i k)
        (get_head cfg (E.store cfg ext i k)).root child.epoch =
        child.root := hroot.symm
    simp only [get_checkpoint_block] at hcheckpoint
    simpa only [get_node_for_root] using hcheckpoint
  have hseedSpec : child.root ∈ (E.store cfg ext i k).block_roots ∧
      ((E.store cfg ext i k).blocks child.root).slot ≤
        compute_start_slot_at_epoch cfg child.epoch := by
    have hspec := get_ancestor_spec hparentSlots hwalk
    unfold get_node_for_root at hlands
    rw [hlands] at hspec
    exact hspec
  -- The signer's clock sits exactly at the link target's epoch.
  have hcurrentEpoch : get_current_store_epoch cfg (E.store cfg ext i k) =
      child.epoch := by
    simp only [get_current_store_epoch, E.store_current_slot, hkSlot]
    exact hslotEpoch
  have hseedEpochLe : get_block_epoch cfg (E.store cfg ext i k) child.root ≤
      child.epoch := by
    simp only [get_block_epoch, compute_epoch_at_slot]
    calc
      ((E.store cfg ext i k).blocks child.root).slot / cfg.slots_per_epoch ≤
          compute_start_slot_at_epoch cfg child.epoch /
            cfg.slots_per_epoch :=
        Nat.div_le_div_right hseedSpec.2
      _ = child.epoch := by
        simp only [compute_start_slot_at_epoch]
        exact Nat.mul_div_cancel child.epoch cfg.slots_per_epoch_pos
  -- Source readback at the signer's store.
  have hheadStateSlotLe :
      ((E.store cfg ext i k).block_states
        (get_head cfg (E.store cfg ext i k)).root).slot ≤ a.data.slot := by
    rw [(hcore hvoteCausal).2 _ hwalk.root_mem]
    calc
      ((E.store cfg ext i k).blocks
          (get_head cfg (E.store cfg ext i k)).root).slot ≤
          get_current_slot cfg (E.store cfg ext i k) :=
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          i k _ hwalk.root_mem
      _ = a.data.slot := by rw [E.store_current_slot cfg ext i k, hkSlot]
  have hcurrentNonGenesis : ∀ r ∈ (E.store cfg ext i k).block_roots,
      get_block_epoch cfg (E.store cfg ext i k) r = child.epoch →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hcurrent hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgenEq] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorBlock : (E.store cfg ext i k).blocks ablk.root =
        ablk.message :=
      E.store_anchor_block cfg ext hT.wellFormed hgenEq i k hr
    have hanchorEpoch : B.anchor.epoch = get_current_epoch cfg ast := by
      rw [hanchor, hgenEq]
      rfl
    have hrootEpoch : get_block_epoch cfg (E.store cfg ext i k) ablk.root =
        B.anchor.epoch := by
      simp only [get_block_epoch]
      rw [hanchorBlock, ← hslot]
      simpa only [get_current_epoch] using hanchorEpoch.symm
    exact (Nat.ne_of_lt hanchorLtTarget) (hrootEpoch.symm.trans hcurrent)
  have hsourceVSAt := E.acceptedHonestAttestationDataSourceEqVSAtTarget
    cfg ext B hT.wellFormed hcore hphase hboundaryPhase hvoteCausal
    hparentSlots hslotEpoch hwalk htargetData hheadStateSlotLe
    hcurrentNonGenesis
  have hsourceData : (honest_attestation_data cfg ext
      (E.store cfg ext i k) a.data.slot index).source =
      store.finalized_checkpoint := by
    rw [← honest_attestation_data_eq, ← hdata]
    exact _haSource
  -- Convert the accepted selector back to the executable voting source.
  have hvotingSource : get_voting_source cfg (E.store cfg ext i k) child.root =
      store.finalized_checkpoint := by
    rw [hvoteCausal.getVotingSource_eq_acceptedSelector cfg ext B hseedSpec.1,
      ← hsourceData, hsourceVSAt]
    simp only [CausalCarrierFFGState.VSAt, hcurrentEpoch]
    by_cases hseedCurrent :
        get_block_epoch cfg (E.store cfg ext i k) child.root = child.epoch
    · rw [if_pos hseedCurrent,
        if_neg (by rw [hseedCurrent]; exact lt_irrefl _)]
    · rw [if_neg hseedCurrent,
        if_pos (Nat.lt_of_le_of_ne hseedEpochLe hseedCurrent)]
  exact ⟨
    { signer := i
      signer_honest := hiHonest
      time := k
      time_within := hHk
      slot_before := by
        rw [hkSlot]
        exact E.includedAttestationSlot_lt_causalStoreCurrentSlot cfg ext B hT
          hstore htip.known ⟨_containing, _hcarrierContaining, hincluded⟩
      seed := child.root
      seed_known := hseedSpec.1
      time_due := by
        rw [hkSlot]
        exact (hacc.honest_behavior.vote_deadline i hiHonest a.data.slot k _ hvoteHead).2
      seed_walk_slot := compute_start_slot_at_epoch cfg child.epoch
      seed_head_walk := hwalk
      seed_lands := hlands
      seed_epoch := by
        rw [hcurrentEpoch]
        exact F.child_epoch
      voting_source_eq := hvotingSource }⟩

/-! ## Endpoint adoption without an observer relay -/

/-- Weak twin of `finalized_epoch_le_remoteJustified_of_synchrony`: the
finalized epoch carried by *any* store, honest or not, is adopted by every
honest endpoint whose slot is not behind.

The strong theorem relays the reading node's whole store and therefore needs
that node to be honest.  Here the only relayed root is the honest signer's own
seed, and the signer voted strictly before the reading store's slot, so the
gate is `E.slot_at cfg q ≤ E.slot_at cfg m` — same-slot endpoints included.
This is a property of the certificate route: the strong next-slot theorems are
not upgraded by it.

The reading second's horizon premise is kept for interface parity with the
strong theorem and is deliberately unused: nothing is relayed *from* that
store. -/
theorem weak_finalized_epoch_le_remoteJustified
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    {v w : ValidatorIndex} (hw : w ∈ E.honest) {q m : ℕ}
    (_hHq : E.WithinHorizon cfg q)
    (hHm : E.WithinHorizon cfg m)
    (hrelay : E.slot_at cfg q ≤ E.slot_at cfg m) :
    (E.store cfg ext v q).finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hendpoint : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  rcases E.finalizedHonestVotingSourceOrigin_of_causalStore cfg ext B hT hacc
      hphase hboundaryPhase hanchor hboundary
      (E.store_causal cfg ext v q) with hanchorField | horigin
  · rw [hanchorField]
    exact E.anchor_epoch_le_acceptedGlobalJustified cfg ext B hgenShort
      hanchor hendpoint
  · obtain ⟨O⟩ := horigin
    -- The signer's vote precedes the reading store's slot, so its seed is
    -- relayed to the endpoint even in that same slot.
    have hvoteSlot : E.slot_at cfg O.time < E.slot_at cfg q := by
      simpa only [E.store_current_slot cfg ext v q] using O.slot_before
    have hslotM : E.slot_at cfg O.time < E.slot_at cfg m :=
      hvoteSlot.trans_le hrelay
    have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
      rw [hgenEq]; simp only [get_forkchoice_store]; omega
    obtain ⟨hnext, hlt⟩ := E.past_slot_deadline_target_gate cfg
      hT.whole_seconds hgenTime hslotM
    have hHnext : E.WithinHorizon cfg
        (E.slot_start cfg (E.slot_at cfg O.time + 1)) :=
      E.withinHorizon_mono cfg hnext hHm
    have hpath := hpaths O.signer O.signer_honest O.time O.time_within w
      O.seed_walk_slot hHnext O.seed_head_walk
    have hparentSource : ParentSlotLt (E.store cfg ext O.signer O.time) :=
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩
        hT.wellFormed.anchor_parent_unscheduled O.signer O.time
    have hnot := VotePathAdmissible.ancestor_not_excluded cfg ext E
      hparentSource hpath O.seed_lands
    have hseedEndpoint : O.seed ∈ (E.store cfg ext w m).block_roots :=
      (hsync.deadline_block_relay O.signer O.signer_honest O.time O.seed
        O.time_within O.seed_known O.time_due w hw m hHm hnext hlt).resolve_right hnot
    have hblockAgree :
        (E.store cfg ext O.signer O.time).blocks O.seed =
          (E.store cfg ext w m).blocks O.seed :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext O.signer O.time)
        (E.blockProvenance cfg ext w m) O.seed_known hseedEndpoint
    have hclock : get_current_store_epoch cfg
          (E.store cfg ext O.signer O.time) ≤
        get_current_store_epoch cfg (E.store cfg ext w m) := by
      simp only [get_current_store_epoch, E.store_current_slot]
      exact ce_mono cfg ((Nat.le_of_lt hvoteSlot).trans hrelay)
    have hadopt := B.votingSource_epoch_le_remoteJustified_of_known
      hT.whole_seconds hgenShort hanchor
      (E.store_causal cfg ext O.signer O.time) hendpoint
      O.seed_known hseedEndpoint
      (congrArg BeaconBlock.slot hblockAgree) hclock
    rwa [O.voting_source_eq] at hadopt

/-! ## `SafeFrom` for a finalized field read at a non-honest observer

Weak twins of `finalizedReset_justifiedDom_of_nextSlotSynchrony` and
`finalizedReset_safeFrom_of_nextSlotSynchrony`
(`AcceptedFinalizedNextSlotSafety.lean:35,122`).  The reading node `v` need not
be honest: the single honesty site of the strong originals — the call to
`finalizedReset_epoch_le_remoteJustified_nextSlot`, which relays the whole
reading store from an honest `v` — is replaced by `weak_finalized_epoch_le_
remoteJustified`, which relays only the finalizing certificate's own honest
signer. Every other ingredient (`finalizedCheckpoint_resetRealizedAt_of_
acceptedGlobalTrajectory`, `storeDomainK_of_acceptedGlobalTrajectory`,
`CausalPrefixFFGInterpretation.endpointJustified_certificate`,
`acceptedGlobalFinalized_anchor_or_includedCertificate`,
`certified_finalized_prefix`, `store_known_ancestor_of_rootDescends_for_
storeReflection`) is already honesty-free and reused unchanged.

The improved relay gate (`slot_at q ≤ slot_at m`, no `+ 1`) lets the
conclusion start at the *query slot's own start* rather than one slot after a
separately-quantified next-slot marker: no `hnextQ`-style timing premise is
needed, only the endpoint's raw time being at or after
`E.slot_start cfg (E.slot_at cfg q)`. -/

/-- At every honest endpoint whose raw time is at or after the start of the
query slot, the query's finalized checkpoint (read at `v`, honest or not) is
known and lies on the endpoint's realized justified chain. -/
theorem weak_finalizedReset_justifiedDom_of_synchrony
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    {v : ValidatorIndex} {q : ℕ}
    (hHq : E.WithinHorizon cfg q) :
    ∀ w ∈ E.honest, ∀ m : ℕ, E.slot_start cfg (E.slot_at cfg q) ≤ m →
      E.WithinHorizon cfg m →
      let finalized := (E.store cfg ext v q).finalized_checkpoint
      finalized.root ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root
            (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root finalized.root) = true := by
  intro w hw m hqm hHm
  let finalized := (E.store cfg ext v q).finalized_checkpoint
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  have hqueryCausal : E.CausalStore cfg ext (E.store cfg ext v q) :=
    E.store_causal cfg ext v q
  have hendpointCausal : E.CausalStore cfg ext
      (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) q
  have hfinalizedKnownQuery : finalized.root ∈
      (E.store cfg ext v q).block_roots := hrealized.root_known
  have hfinalizedRoot : E.ExecutionRoot finalized.root :=
    ⟨(E.store cfg ext v q).blocks finalized.root,
      E.blockAt_of_store_known cfg ext hfinalizedKnownQuery⟩
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  obtain ⟨_hparent, _hwalk, hjustifiedKnown⟩ :=
    hdomainK w hw m hHm
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgen]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time :=
    hgws.time_ge_genesis
  have hslotEq : E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q)) =
      E.slot_at cfg q :=
    E.slot_at_slot_start cfg hT.whole_seconds
      (E.slot_at_mono cfg (Nat.zero_le q)) hgenTime
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← hslotEq]
    exact E.slot_at_mono cfg hqm
  have hepoch : finalized.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
    simpa only [finalized] using
      E.weak_finalized_epoch_le_remoteJustified cfg ext B hT hacc hphase
        hboundaryPhase hanchor hboundary hsync hpaths hw hHq hHm hslotQM
  obtain ⟨hjustified⟩ :=
    CausalPrefixFFGInterpretation.endpointJustified_certificate
      (E := E) cfg ext B hgenShort hanchor hendpointCausal
  have hsemantic : E.RootDescends
      (E.store cfg ext w m).justified_checkpoint.root finalized.root := by
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
        cfg ext B hgenShort hanchor hqueryCausal with
      hfieldAnchor | ⟨carrier, _hcarrier, hincluded⟩
    · have hfinalizedAnchor : finalized = B.anchor := by
        simpa only [finalized] using hfieldAnchor
      rw [hfinalizedAnchor]
      exact hjustified.descends_anchor cfg
    · obtain ⟨hincluded⟩ := hincluded
      have hincludedFinalized : IncludedCertifiedFinalized cfg E
          B.state.includedAttestations.Included B.anchor carrier
          finalized := by
        simpa only [finalized] using hincluded
      have hfinalized : CertifiedFinalized cfg E B.anchor finalized :=
        IncludedCertifiedFinalized.toCertifiedFinalized
          (cfg := cfg)
          (Execution.CausalCarrierAttestationRelation.relation
            cfg ext E B.state.includedAttestations)
          hincludedFinalized
      exact E.certified_finalized_prefix cfg ext hacc
        hfinalized hjustified hepoch
  exact E.store_known_ancestor_of_rootDescends_for_storeReflection
    cfg ext hT.wellFormed hT.externals_coherence hgen hslot hparent
      hjustifiedKnown hfinalizedRoot hsemantic

/-- A query's finalized checkpoint, read at a non-honest observer, is
genuinely `SafeFrom` from the start of the query's own slot. -/
theorem weak_finalizedReset_safeFrom_of_synchrony
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    {v : ValidatorIndex} {q : ℕ}
    (hHq : E.WithinHorizon cfg q) :
    E.SafeFrom cfg ext (E.store cfg ext v q).finalized_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)) := by
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  apply E.safeFrom_of_justified_dom_K cfg ext hdomainK
  intro w hw m hqm hHm
  exact E.weak_finalizedReset_justifiedDom_of_synchrony
    cfg ext B hT hacc hphase hboundaryPhase hanchor hboundary hsync hpaths hHq
      w hw m hqm hHm

/-! ## Self-contained one-shot weak safety from the finalized checkpoint

The finalized-base corollary: feed `weak_finalizedReset_safeFrom_of_synchrony`
(the `SafeFrom` base, honesty-free on the reading node) as `hbase` into
`weak_safeFrom_find_latest_confirmed_descendant`
(`WeakOneShotSafety.lean:1038`, honesty-free on the observer). The result
needs no separately-supplied `SafeFrom`/knownness premise for the finalized
root: both come from the accepted FFG semantics bundle `B` together with the
ordinary phase/anchor floor already used throughout the accepted pipeline.

Every field of `hW.base : SelectedMarginAssumptions` this corollary needs
beyond the ratified floor is derived, not assumed:
`ScheduledPrefixPremises.of_selectedMarginAssumptions` and
`SelectedMarginAssumptions.toFFGAccountabilityAssumptions` project the
narrower trajectory and accountability interfaces the finalized-base
machinery actually consumes. The FFG accountability statements
(`certified_justified_unique`, `certified_links_not_surround`) are downstream
theorems of `hW.base`, not additional premises. -/

/-- **The self-contained finalized-base corollary.** The weak selector's
output, seeded at the observer's own finalized checkpoint (read at `(obs,
q)`, `obs` honest or not) rather than at a separately-supplied `SafeFrom`
input, is `SafeFrom` at the actual query second.

Observer-wise the premise surface is `hW : WeakObserverPremises` — the
floor and committee readback at the observer's own store. The observer may be honest.
`B`/`hanchor`/`hboundary` are carried here anyway and `hT` is derived from
`hW.base`, so `ObserverCoherence.justified_root_known` is *derived* via
`WeakObserverPremises.toMarginAssumptions`, not assumed. -/
theorem weak_safeFrom_find_latest_confirmed_descendant_from_finalized
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (hmargin :
      Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root ≠
        fcr_store.store.finalized_checkpoint.root →
      E.SelectedCoveredMarginSupplyAt cfg ext
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)
        fcr_store.store.finalized_checkpoint.root obs q fcr_store) :
    E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext fcr_store
        fcr_store.store.finalized_checkpoint.root) q := by
  have hT := ScheduledPrefixPremises.of_selectedMarginAssumptions
    cfg ext E hW.base hW.genesis
  have hacc := SelectedMarginAssumptions.toFFGAccountabilityAssumptions
    cfg ext E hW.base
  have hlcr : fcr_store.store.finalized_checkpoint.root ∈
      fcr_store.store.block_roots := by
    rw [hstore]
    exact (E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) q).root_known
  have hbase : E.SafeFrom cfg ext fcr_store.store.finalized_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)) := by
    rw [hstore]
    exact E.weak_finalizedReset_safeFrom_of_synchrony cfg ext B hT hacc hphase
      hboundaryPhase hanchor hboundary hW.base.synchrony
      hW.base.domain.honest_head_paths hqH
  -- the observer's `justified_root_known` is derived from `B`/`hT`/`hanchor`/
  -- `hboundary`, all already carried here, rather than assumed
  have hWM := hW.toMarginAssumptions cfg ext E B hT hanchor hboundary
  exact weak_safeFrom_find_latest_confirmed_descendant cfg ext hWM q hqH
    fcr_store hstore fcr_store.store.finalized_checkpoint.root hlcr hbase
    hmargin

/-- Endpoint form of the finalized-base corollary: the weak selector's output,
seeded at the observer's own finalized checkpoint, is canonical at every
honest endpoint at or after the query second. -/
theorem weak_confirmed_head_from_finalized
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (hmargin :
      Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root ≠
        fcr_store.store.finalized_checkpoint.root →
      E.SelectedCoveredMarginSupplyAt cfg ext
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)
        fcr_store.store.finalized_checkpoint.root obs q fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hqm : q ≤ m) (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)) = true :=
  weak_safeFrom_find_latest_confirmed_descendant_from_finalized cfg ext hW B
    hanchor hboundary hphase hboundaryPhase q hqH fcr_store hstore hmargin
    w hw m hqm hHm

end Execution

end FastConfirmation.Spec

end
