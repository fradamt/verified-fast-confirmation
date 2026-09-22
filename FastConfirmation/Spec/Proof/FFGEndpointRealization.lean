module
public import FastConfirmation.Spec.Proof.FFGStateTrajectory
public import FastConfirmation.Spec.Proof.SelectedFFGRealization
public import FastConfirmation.Spec.Proof.PaperA32Projection
public import FastConfirmation.Spec.Proof.MinimalSelectedDomain

@[expose] public section

/-!
# Endpoint facts derivable from the block-local FFG projection

This module records the endpoint-facing consequences which really follow from
`ChainFFGState`, `FFGTransitionCoherence`, and the reachable-store trajectory.
It deliberately does not fill the remaining endpoint records with free
assumptions.

What is derivable:

* every `GJ`, `GU`, and executable voting-source read has a concrete
  `CertifiedJustified` certificate;
* executable store ancestry induces ancestry in the concrete execution parent
  graph; and
* AU monotonicity/maximality proves `VotingSourceEpochChainPersistence` at
  every reachable store.

What is not derivable from the current projection is documented at the end:
the store-global justified/finalized checkpoints do not retain which block
state or eager pull-up installed them.  Consequently the second field of
`EndpointSelectorRealization` and both fields of
`FinalizedBoundaryRealization` still need historical/global-checkpoint
producers.  A sound finalized-boundary constructor below exposes the exact
AU/carrier/walk data which would suffice.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Certificates inherited from AU -/

namespace ChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Every available/unrealized checkpoint has a concrete global certificate.
The proof only forgets carrier-local block-body inclusion from the stronger
certificate already stored in `FormedCheckpointEvidence`. -/
theorem certifiedJustified_of_AU
    (S : ChainFFGState cfg E anchor)
    {tip : Root} {c : Checkpoint Root}
    (hAU : S.AU cfg tip c) :
    Nonempty (CertifiedJustified cfg E anchor c) := by
  obtain ⟨carrier, _hdesc, hevidence⟩ :=
    ChainFFGState.AU.evidence (cfg := cfg) S hAU
  obtain ⟨hcertified⟩ := hevidence.certified
  exact ⟨IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg) S.includedAttestations hcertified⟩

/-- The realized selector is concretely certified. -/
theorem gj_certified
    (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    Nonempty (CertifiedJustified cfg E anchor (S.GJ r)) :=
  S.certifiedJustified_of_AU cfg (S.gj_AU cfg r hr)

/-- The eager/unrealized selector is concretely certified. -/
theorem gu_certified
    (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    Nonempty (CertifiedJustified cfg E anchor (S.GU r)) :=
  S.certifiedJustified_of_AU cfg (S.gu_AU cfg r hr)

end ChainFFGState

namespace Execution

variable (E : Execution Root)

/-- The first field of `EndpointSelectorRealization` follows outright from
the exact reachable-store projection.  The non-future premise is retained in
the theorem signature because that is the consumer's domain, although
certificate extraction itself does not need it. -/
theorem votingSource_certified_of_ffgState
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (m : ℕ) (tip : Root)
    (htip : tip ∈ (E.store cfg ext w m).block_roots)
    (_htipSlot : ((E.store cfg ext w m).blocks tip).slot ≤
      get_current_slot cfg (E.store cfg ext w m)) :
    Nonempty (CertifiedJustified cfg E anchor
      (get_voting_source cfg (E.store cfg ext w m) tip)) := by
  have htipRoot : E.ExecutionRoot tip :=
    ⟨(E.store cfg ext w m).blocks tip,
      E.blockAt_of_store_known cfg ext htip⟩
  rw [E.get_voting_source_eq hcoh w m htip]
  split_ifs
  · exact S.gu_certified cfg tip htipRoot
  · exact S.gj_certified cfg tip htipRoot

/-! ## Executable ancestry projected to the execution parent graph -/

/-- Every known store edge is a concrete execution parent edge. -/
theorem parentEdge_of_store_known
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    {r : Root} (hr : r ∈ store.block_roots) :
    E.ParentEdge r (store.blocks r).parent_root := by
  rcases hprovenance r hr with hgen | hsched
  · obtain ⟨hrGenesis, hblock⟩ := hgen
    exact Or.inl ⟨r, hrGenesis, rfl,
      congrArg BeaconBlock.parent_root hblock⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hblock⟩ := hsched
    exact Or.inr ⟨w, n, sb, hscheduled, hroot.symm,
      congrArg BeaconBlock.parent_root hblock⟩

/-- A known fork-choice walk which lands on `ancestor` is the same parent
chain in the concrete execution graph.  This is the missing direction needed
to apply AU monotonicity to an executable `is_ancestor` fact. -/
theorem rootDescends_of_getAncestor
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    (hwf : ParentSlotLt store)
    {tip ancestor : Root}
    (hwalk : WalkKnown store (store.blocks ancestor).slot tip)
    (hlands : get_ancestor store (ForkChoiceNode.mk tip)
      (store.blocks ancestor).slot = ForkChoiceNode.mk ancestor) :
    E.RootDescends tip ancestor := by
  induction hwalk with
  | @stop r hr hle =>
      rw [get_ancestor_stop hle] at hlands
      have hre : r = ancestor :=
        congrArg ForkChoiceNode.root hlands
      subst r
      exact .refl ancestor
  | @step r hr hgt hp ih =>
      rw [get_ancestor_step hwf hr hgt hp] at hlands
      exact .step (E.parentEdge_of_store_known hprovenance hr) (ih hlands)

/-- Boolean store ancestry implies semantic execution ancestry on the known
walk domain. -/
theorem rootDescends_of_store_ancestor
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    (hwf : ParentSlotLt store)
    {tip ancestor : Root}
    (hwalk : WalkKnown store (store.blocks ancestor).slot tip)
    (hancestor : is_ancestor store (get_node_for_root tip)
      (get_node_for_root ancestor) = true) :
    E.RootDescends tip ancestor := by
  apply E.rootDescends_of_getAncestor hprovenance hwf hwalk
  simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hancestor

end Execution

/-! ## AU selector monotonicity -/

namespace ChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- `GU` epochs are monotone along semantic block descent. -/
theorem gu_epoch_le_of_descends
    (S : ChainFFGState cfg E anchor)
    {seed tip : Root}
    (hseedRoot : E.ExecutionRoot seed)
    (htipRoot : E.ExecutionRoot tip)
    (htipSeed : E.RootDescends tip seed) :
    (S.GU seed).epoch ≤ (S.GU tip).epoch := by
  apply S.gu_max htipRoot
  exact ChainFFGState.AU.mono (cfg := cfg) S htipSeed
    (S.gu_AU cfg seed hseedRoot)

/-- `GJ` epochs are monotone when the descendant block is no earlier than the
seed block.  The anchor case uses the concrete certificate's anchor lower
bound; the non-anchor case uses `gj_max`. -/
theorem gj_epoch_le_of_descends
    (S : ChainFFGState cfg E anchor)
    {seed tip : Root} {seedBlock tipBlock : BeaconBlock Root}
    (hseedAt : E.BlockAt seed seedBlock)
    (htipAt : E.BlockAt tip tipBlock)
    (htipSeed : E.RootDescends tip seed)
    (hepoch : compute_epoch_at_slot cfg seedBlock.slot ≤
      compute_epoch_at_slot cfg tipBlock.slot) :
    (S.GJ seed).epoch ≤ (S.GJ tip).epoch := by
  rcases S.gj_anchor_or_before hseedAt with hanchor | hbefore
  · rw [hanchor]
    obtain ⟨htipCertified⟩ := S.gj_certified cfg tip ⟨tipBlock, htipAt⟩
    exact CertifiedJustified.anchor_epoch_le (cfg := cfg) htipCertified
  · apply S.gj_max htipAt
      (ChainFFGState.AU.mono (cfg := cfg) S htipSeed
        (S.gj_AU cfg seed ⟨seedBlock, hseedAt⟩))
    exact hbefore.trans_le hepoch

/-- An unrealized source at an older seed is below the realized selector of a
strictly later-epoch descendant. -/
theorem gu_epoch_le_gj_of_descends
    (S : ChainFFGState cfg E anchor)
    {seed tip : Root} {tipBlock : BeaconBlock Root}
    (hseedRoot : E.ExecutionRoot seed)
    (htipAt : E.BlockAt tip tipBlock)
    (htipSeed : E.RootDescends tip seed)
    (hbefore : (S.GU seed).epoch <
      compute_epoch_at_slot cfg tipBlock.slot) :
    (S.GU seed).epoch ≤ (S.GJ tip).epoch := by
  exact S.gj_max htipAt
    (ChainFFGState.AU.mono (cfg := cfg) S htipSeed
      (S.gu_AU cfg seed hseedRoot)) hbefore

end ChainFFGState

namespace Execution

variable (E : Execution Root)

/-- The complete voting-source epoch-persistence record is a theorem of the
block-local FFG semantics and the reachable execution trajectory.

There are four selector branches.  Old-to-old uses `GU` maximality;
old-to-current uses `gj_max`; current-to-current uses `GJ` maximality; and
current-to-old contradicts block-epoch monotonicity on the descendant chain.
-/
theorem votingSourceEpochChainPersistence_of_ffgState
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (w : ValidatorIndex) (m : ℕ) :
    VotingSourceEpochChainPersistence cfg (E.store cfg ext w m) := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hgenSlots : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  let store := E.store cfg ext w m
  have hwf : ParentSlotLt store :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      hgen hA.wellFormed.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r :=
    E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence
      hgen w m
  have hnonfuture : ∀ r ∈ store.block_roots,
      (store.blocks r).slot ≤ get_current_slot cfg store :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlots w m
  constructor
  intro seed tip hseed htip htipSeed
  have hwalk : WalkKnown store (store.blocks seed).slot tip :=
    hwalkK seed hseed tip htip
  have hslotLe : (store.blocks seed).slot ≤ (store.blocks tip).slot :=
    ancestor_slot_le hwf hwalk htipSeed
  have hepochLe : compute_epoch_at_slot cfg (store.blocks seed).slot ≤
      compute_epoch_at_slot cfg (store.blocks tip).slot :=
    ce_mono cfg hslotLe
  have hseedEpochCurrent : compute_epoch_at_slot cfg
      (store.blocks seed).slot ≤ get_current_store_epoch cfg store := by
    simpa only [get_current_store_epoch] using
      ce_mono cfg (hnonfuture seed hseed)
  have htipEpochCurrent : compute_epoch_at_slot cfg
      (store.blocks tip).slot ≤ get_current_store_epoch cfg store := by
    simpa only [get_current_store_epoch] using
      ce_mono cfg (hnonfuture tip htip)
  have hsemantic : E.RootDescends tip seed :=
    E.rootDescends_of_store_ancestor (E.blockProvenance cfg ext w m)
      hwf hwalk htipSeed
  have hseedAt : E.BlockAt seed (store.blocks seed) := by
    simpa only [store] using E.blockAt_of_store_known cfg ext hseed
  have htipAt : E.BlockAt tip (store.blocks tip) := by
    simpa only [store] using E.blockAt_of_store_known cfg ext htip
  have hseedRoot : E.ExecutionRoot seed := ⟨store.blocks seed, hseedAt⟩
  have htipRoot : E.ExecutionRoot tip := ⟨store.blocks tip, htipAt⟩
  rw [E.get_voting_source_eq hcoh w m hseed,
    E.get_voting_source_eq hcoh w m htip]
  by_cases hseedOld : get_current_store_epoch cfg store >
      compute_epoch_at_slot cfg (store.blocks seed).slot
  · rw [if_pos hseedOld]
    by_cases htipOld : get_current_store_epoch cfg store >
        compute_epoch_at_slot cfg (store.blocks tip).slot
    · rw [if_pos htipOld]
      exact S.gu_epoch_le_of_descends cfg hseedRoot htipRoot hsemantic
    · rw [if_neg htipOld]
      have htipCurrent : compute_epoch_at_slot cfg (store.blocks tip).slot =
          get_current_store_epoch cfg store :=
        Nat.le_antisymm htipEpochCurrent (Nat.le_of_not_gt htipOld)
      have hguSeedBlock : (S.GU seed).epoch ≤
          compute_epoch_at_slot cfg (store.blocks seed).slot :=
        S.au_epoch_le_block hseedAt (S.gu_AU cfg seed hseedRoot)
      have hguBeforeTip : (S.GU seed).epoch <
          compute_epoch_at_slot cfg (store.blocks tip).slot := by
        rw [htipCurrent]
        exact hguSeedBlock.trans_lt hseedOld
      exact S.gu_epoch_le_gj_of_descends cfg hseedRoot htipAt hsemantic
        hguBeforeTip
  · rw [if_neg hseedOld]
    by_cases htipOld : get_current_store_epoch cfg store >
        compute_epoch_at_slot cfg (store.blocks tip).slot
    · rw [if_pos htipOld]
      have hcurrentSeed : get_current_store_epoch cfg store ≤
          compute_epoch_at_slot cfg (store.blocks seed).slot :=
        Nat.le_of_not_gt hseedOld
      exact False.elim ((Nat.not_lt_of_ge
        (hcurrentSeed.trans hepochLe)) htipOld)
    · rw [if_neg htipOld]
      exact S.gj_epoch_le_of_descends cfg hseedAt htipAt hsemantic hepochLe

/-! ## The exact finalized-boundary projection which would suffice -/

/-- If a known carrier's walk to the finalized epoch boundary is available
and the finalized root is the corresponding checkpoint block, both fields of
`FinalizedBoundaryRealization` are mechanical consequences of
`get_ancestor_spec`.

This theorem is intentionally store-local.  The missing global historical
producer is precisely the carrier, walk, and root equation in its premises. -/
theorem finalizedBoundaryRealization_of_checkpointBlock
    {store : Store Root} (hwf : ParentSlotLt store)
    {carrier : Root}
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch)
      carrier)
    (hroot : store.finalized_checkpoint.root =
      get_checkpoint_block cfg store carrier
        store.finalized_checkpoint.epoch) :
    FinalizedBoundaryRealization cfg store := by
  have hspec := get_ancestor_spec hwf hwalk
  have hknown : store.finalized_checkpoint.root ∈ store.block_roots := by
    rw [hroot]
    exact hspec.1
  have hslot : (store.blocks store.finalized_checkpoint.root).slot ≤
      compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch := by
    rw [hroot]
    exact hspec.2
  exact ⟨hknown, hslot⟩

/-- The boundary record is genuinely impossible when the store's finalized
root lies strictly after its declared epoch boundary.  In particular, a
checkpoint-sync initialization whose trusted anchor is mid-epoch cannot
satisfy `FinalizedBoundaryRealization` while that anchor remains finalized.
This is a semantic incompatibility, not a missing induction lemma. -/
theorem not_finalizedBoundaryRealization_of_midEpochRoot
    {store : Store Root}
    (hmid : compute_start_slot_at_epoch cfg
        store.finalized_checkpoint.epoch <
      (store.blocks store.finalized_checkpoint.root).slot) :
    ¬ FinalizedBoundaryRealization cfg store := by
  intro hrealization
  exact (Nat.not_lt_of_ge hrealization.finalized_root_slot_le_boundary) hmid

/-- Concrete initialization specialization of the preceding obstruction.
`get_forkchoice_store` declares the anchor block itself finalized at the
anchor state's epoch.  If that anchor block is after the epoch's first slot,
the required finalized-boundary inequality is false already at initialization.
-/
theorem not_finalizedBoundary_getForkchoiceStore_of_midEpoch
    (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root)
    (hslot : anchorState.slot = anchorBlock.message.slot)
    (hmid : compute_start_slot_at_epoch cfg
        (get_current_epoch cfg anchorState) < anchorBlock.message.slot) :
    ¬ FinalizedBoundaryRealization cfg
      (get_forkchoice_store cfg anchorState anchorBlock) := by
  apply not_finalizedBoundaryRealization_of_midEpochRoot cfg
  simpa only [get_forkchoice_store, Function.update_self, hslot] using hmid

/-- `FFGTransitionCoherence.au_checkpoint_of_known` supplies the root equation
in the preceding constructor whenever the store-global finalized checkpoint
is known to be AU at a known carrier.  The remaining boundary walk is kept
explicit because it can fail for a mid-epoch checkpoint-sync anchor. -/
theorem finalizedBoundaryRealization_of_ffgAU
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hwf : ParentSlotLt (E.store cfg ext w m))
    {carrier : Root}
    (hcarrier : carrier ∈ (E.store cfg ext w m).block_roots)
    (hAU : S.AU cfg carrier
      (E.store cfg ext w m).finalized_checkpoint)
    (hwalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch)
      carrier) :
    FinalizedBoundaryRealization cfg (E.store cfg ext w m) := by
  have hcheckpoint := hcoh.au_checkpoint_of_known w hw m hHm carrier
    hcarrier (E.store cfg ext w m).finalized_checkpoint hAU
  exact finalizedBoundaryRealization_of_checkpointBlock cfg hwf hwalk
    (congrArg Checkpoint.root hcheckpoint)

/-!
## Remaining producer interfaces

The constructors above leave the following exact producers:

1. **Endpoint selector, realized-source upper bound (historical trajectory).**
   `FFGStateTrajectory` identifies each reachable block state's `GJ`, pulled-up
   `GU`, and unrealized-map entry, but does not track the store-global maximum
   which installed `store.justified_checkpoint`.  A handler induction showing
   that every source whose block is now in an earlier epoch has been absorbed
   by the latest epoch-boundary `update_checkpoints` would discharge
   `EndpointSelectorRealization.source_realized_le_justified`.  This is not an
   FFG safety assumption; it is missing historical bookkeeping.

2. **Finalized carrier provenance (historical plus architecture projection).**
   The reachable projection identifies block-local `GF`/`GUF`, but not which
   one last installed the store-global finalized checkpoint.  Moreover,
   `gf_evidence`/`guf_evidence` provide a carrier-local finalization
   certificate but do not expose `S.AU carrier finalized` or an explicit
   `RootDescends carrier finalized.root`.  Those are the inputs needed by
   `au_checkpoint_of_known` and the constructor above.

3. **Finalized checkpoint-block boundary (protocol semantic).**
   For an ordinary formed finalized checkpoint, the missing producer must say
   that its root is the epoch checkpoint block on the installing carrier and
   that the carrier walk is defined down to that boundary.  This is exactly
   what `finalizedBoundaryRealization_of_ffgAU` consumes.

4. **Checkpoint-sync trusted anchor (semantic incompatibility).**
   A mid-epoch trusted anchor is declared finalized by `get_forkchoice_store`,
   while `FinalizedBoundaryRealization` requires its block slot to be no later
   than that epoch's start.  The two formal impossibility lemmas above show
   that no producer can close this case.  The filter/realization contract must
   special-case the trusted anchor (as the certificate layer already does),
   or the theorem scope must require a boundary-aligned anchor.
-/

end Execution

end FastConfirmation.Spec

end
