module
public import FastConfirmationProofs.Checkpoints.SameEpochSegmentRealization
public import FastConfirmationProofs.FFG.SourceHistory.TrustedFFGSourceCoherence

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {trusted : Store Root → Prop}

theorem trusted_acceptedProjectedSameEpochTransition_of_known_parent
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hwf : WellFormedExecution E)
    (hcore : ExactCausalStoreWellFormedCore cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {parent child : Root}
    (hparentKnown : parent ∈ store.block_roots)
    (hchildKnown : child ∈ store.block_roots)
    (hchildNonGenesis : child ∉ E.genesis_store.block_roots)
    (hparent : (store.blocks child).parent_root = parent)
    (hsame : compute_epoch_at_slot cfg (store.blocks parent).slot =
      compute_epoch_at_slot cfg (store.blocks child).slot) :
    TrustedAcceptedProjectedSameEpochTransition cfg ext E S parent child := by
  obtain ⟨writer⟩ :=
    hstore.acceptedBlockLastWriterProvenance child hchildKnown
      hchildNonGenesis
  let t := writer.transition
  have htRoot : t.signedBlock.root = child := writer.root_eq
  have htMessage : t.signedBlock.message = store.blocks child :=
    writer.message_eq
  have htParent : t.signedBlock.message.parent_root = parent :=
    (congrArg BeaconBlock.parent_root htMessage).trans hparent
  have htParentKnown : t.signedBlock.message.parent_root ∈
      (t.atPrefix.store cfg ext).block_roots :=
    t.parent_known writer.fresh
  have hprefixParentKnown : parent ∈
      (t.atPrefix.store cfg ext).block_roots := by
    rw [← htParent]
    exact htParentKnown
  have hprefixParentAt : E.AcceptedBlockAt cfg ext parent
      ((t.atPrefix.store cfg ext).blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext
      (.scheduledPrefix t.atPrefix) hprefixParentKnown
  have hstoreParentAt : E.AcceptedBlockAt cfg ext parent
      (store.blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hparentKnown
  have hparentMessage :
      (t.atPrefix.store cfg ext).blocks parent = store.blocks parent :=
    hprefixParentAt.unique cfg ext E hwf hstoreParentAt
  have hprefixCore : WellFormedStoreCore
      (t.atPrefix.store cfg ext) :=
    hcore (.scheduledPrefix t.atPrefix)
  have hinsertionSameEpoch :
      compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).block_states
            t.signedBlock.message.parent_root).slot =
        compute_epoch_at_slot cfg t.signedBlock.message.slot := by
    calc
      compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).block_states
            t.signedBlock.message.parent_root).slot =
          compute_epoch_at_slot cfg
            ((t.atPrefix.store cfg ext).block_states parent).slot := by
        rw [htParent]
      _ = compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).blocks parent).slot :=
        congrArg (compute_epoch_at_slot cfg)
          (hprefixCore.2 parent hprefixParentKnown)
      _ = compute_epoch_at_slot cfg (store.blocks parent).slot :=
        congrArg (fun b => compute_epoch_at_slot cfg b.slot)
          hparentMessage
      _ = compute_epoch_at_slot cfg (store.blocks child).slot := hsame
      _ = compute_epoch_at_slot cfg t.signedBlock.message.slot :=
        (congrArg (fun b => compute_epoch_at_slot cfg b.slot)
          htMessage).symm
  have hedge := TrustedAcceptedProjectedSameEpochTransition.of_transition
    (S := S) t writer.fresh htParentKnown hinsertionSameEpoch
  rw [htParent, htRoot] at hedge
  exact hedge

/-! ## Segment lift -/

/-- Every concrete known same-epoch ancestry segment in an exact causal store
lifts to accepted edges.  The reflexive constructor is the explicit genesis
base case; each nontrivial child is non-genesis by the source relation and is
therefore realized through last-writer provenance. -/
theorem trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hwf : WellFormedExecution E)
    (hcore : ExactCausalStoreWellFormedCore cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {first last : Root}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots store first last) :
    TrustedAcceptedProjectedSameEpochSegment cfg ext E S first last := by
  induction hsegment with
  | refl known =>
      exact .refl first (store.blocks first)
        (E.acceptedBlockAt_of_causal_known cfg ext hstore known)
  | @tail parent child hprefix hchild hnonGenesis hparent hsame ih =>
      exact .tail ih
        (trusted_acceptedProjectedSameEpochTransition_of_known_parent
          cfg ext hwf hcore hstore hprefix.last_known hchild hnonGenesis
          hparent hsame)

/-- Mechanical specialization using the standard state-transition slot law
and a genesis core witness. -/
theorem trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment_of_core
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hwf : WellFormedExecution E)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hbase : WellFormedStoreCore E.genesis_store)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {first last : Root}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots store first last) :
    TrustedAcceptedProjectedSameEpochSegment cfg ext E S first last :=
  trusted_knownSameEpochAncestrySegment_toTrustedAcceptedProjectedSameEpochSegment
    cfg ext hwf (E.exactCausalStoreWellFormedCore hst_slot hbase) hstore hsegment

end Execution
end FastConfirmation.Spec
end
