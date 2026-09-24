module
public import FastConfirmationProofs.Weak.Common.WeakSelectedStrictEdgeFilterSupply
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionCarriedBranch
public import FastConfirmationProofs.Checkpoints.TrustedSameEpochSegmentRealization

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {E : Execution Root} {trusted : Store Root → Prop}

noncomputable def
    StrictSelectorAdvanceAt.trusted_extendHistoricalLineage_sameEpoch_actual
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : Weak.LatestConfirmedCallTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hinputKnown : trace.afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.afterObserved e Cert Supp)
    (hinputEpoch : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      trace.afterObserved = e)
    (hresultEpoch : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      trace.result = e) :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e
      Cert Supp := by
  let query := E.weakFcrStep cfg ext obs n
  let ast : BeaconState Root := Classical.choose hT.genesis_structure
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis_structure)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis_structure)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hgenSlot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hgenParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore
      hT.externals_coherence.state_transition_slot hgenCore
  have hstore : E.CausalStore cfg ext query.store := by
    simpa only [query, E.weakFcrStep_store] using
      E.store_causal cfg ext obs (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hcoh (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.weakFcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.weakFcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have hinputKnownQ : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query] using hinputKnown
  have hgeometry := hselector.geometry cfg ext hparent hwalk hhead
    hinputKnownQ
  have hlands : (get_ancestor query.store
      (get_node_for_root trace.result)
      (query.store.blocks trace.afterObserved).slot).root =
        trace.afterObserved := by
    simpa only [is_ancestor_get_node_for_root, decide_eq_true_eq] using
      hgeometry.descends_input
  have hinputEpochQ : get_block_epoch cfg query.store
      trace.afterObserved = e := by
    simpa only [query] using hinputEpoch
  have hresultEpochQ : get_block_epoch cfg query.store trace.result = e := by
    simpa only [query] using hresultEpoch
  have hsame : compute_epoch_at_slot cfg
        (query.store.blocks trace.afterObserved).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      hinputEpochQ.trans hresultEpochQ.symm
  have hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [query, E.weakFcrStep_store] using hr
    have hanchorBlock : query.store.blocks ablk.root = ablk.message := by
      simpa only [query, E.weakFcrStep_store] using
        E.store_anchor_block cfg ext hT.wellFormed hgen obs (n + 1)
          hanchorKnown
    have hinputKnownN1 : trace.afterObserved ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [query, E.weakFcrStep_store] using hinputKnownQ
    have hanchorLeInput : ablk.message.slot ≤
        (query.store.blocks trace.afterObserved).slot := by
      simpa only [query, E.weakFcrStep_store] using
        E.store_anchor_min_slot cfg ext hT.wellFormed
          hT.externals_coherence hgen hgenSlot hgenParent obs (n + 1)
            trace.afterObserved hinputKnownN1
    have hbad : (query.store.blocks trace.afterObserved).slot <
        ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeInput) hbad
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store trace.afterObserved
        trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor_root cfg hparent
      (hwalk trace.afterObserved hinputKnownQ trace.result
        hgeometry.result_known)
      hlands hsame hstrictNonGenesis
  have hsegment : TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state
      trace.afterObserved trace.result :=
    E.trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment
      cfg ext hT.wellFormed hcore hstore hknownSegment
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore
      hgeometry.result_known
  exact hlineage.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [query, get_block_epoch] using hresultEpoch)
    (E.trusted_acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

end Weak
end FastConfirmation.Spec
end
