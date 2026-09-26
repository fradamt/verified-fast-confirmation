module
public import FastConfirmationProofs.FFG.State.DynamicFinalizedPlacement
public import FastConfirmationProofs.FFG.SelectedSource.PhaseSourceCarriers
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationProofs.ForkChoice.Filter.QueryFilterViability

@[expose] public section

/-!
# Path-local finalized transport for accepted retained tips

The executable query filter can certify a finalized checkpoint in an earlier
query store.  Transporting that certificate to a retained endpoint tip reads
only the two concrete parent walks involved; it does not require the query's
entire block domain to be contained in the endpoint store.

This module records that path-local transport and separates the two positive
early-finality branches from the genuinely insufficient numeric-recency arm:

* exact stable finality is carried by paired query/endpoint boundary walks;
* exact anchor finality is reflected from accepted AU at the retained tip;
* source recency by itself still supplies no finalized/source dominance.

No visibility, finalized-seed, filter membership, or safety conclusion is
postulated by the retained-source results below.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-! ## Paired-walk block transport -/

omit [Inhabited Root] in
/-- Two stores compute the same ancestor along paired known walks when they
agree only at roots encountered by both walks.  Unlike `get_ancestor_congr`,
this theorem needs no one-sided agreement over an entire store domain.
Agreement at each child and its known parent also fixes the payload status
chosen by each Gloas parent step. -/
theorem get_ancestor_eq_of_paired_walks
    {source target : Store Root}
    (hsourceParent : ParentSlotLt source)
    (htargetParent : ParentSlotLt target)
    (hagree : ∀ r, r ∈ source.block_roots →
      r ∈ target.block_roots → source.blocks r = target.blocks r)
    {slot : Slot} {r : Root}
    (hsourceWalk : WalkKnown source slot r)
    (htargetWalk : WalkKnown target slot r) :
    get_ancestor source (get_node_for_root r) slot =
      get_ancestor target (get_node_for_root r) slot := by
  suffices hstatus : ∀ status : PayloadStatus,
      get_ancestor source (ForkChoiceNode.mk r status) slot =
        get_ancestor target (ForkChoiceNode.mk r status) slot from
    hstatus .pending
  induction hsourceWalk with
  | @stop r hsourceRoot hsourceLe =>
      intro status
      cases htargetWalk with
      | stop htargetRoot htargetLe =>
          rw [get_ancestor_stop_status hsourceLe,
            get_ancestor_stop_status htargetLe]
      | step htargetRoot htargetGt htargetTail =>
          have hblock := hagree r hsourceRoot htargetRoot
          have hsourceGt : slot < (source.blocks r).slot := by
            simpa only [hblock] using htargetGt
          exact False.elim ((Nat.not_lt_of_ge hsourceLe) hsourceGt)
  | @step r hsourceRoot hsourceGt hsourceTail ih =>
      intro status
      cases htargetWalk with
      | stop htargetRoot htargetLe =>
          have hblock := hagree r hsourceRoot htargetRoot
          have hsourceLe : (source.blocks r).slot ≤ slot := by
            simpa only [hblock] using htargetLe
          exact False.elim ((Nat.not_lt_of_ge hsourceLe) hsourceGt)
      | step htargetRoot htargetGt htargetTail =>
          have hblock := hagree r hsourceRoot htargetRoot
          have htargetTail' : WalkKnown target slot
              (source.blocks r).parent_root := by
            simpa only [hblock] using htargetTail
          have hparentBlock := hagree (source.blocks r).parent_root
            hsourceTail.root_mem htargetTail'.root_mem
          have hparentRoot : (source.blocks r).parent_root =
              (target.blocks r).parent_root :=
            congrArg BeaconBlock.parent_root hblock
          have hparentStatus :
              get_parent_payload_status source (source.blocks r) =
                get_parent_payload_status target (target.blocks r) := by
            simp only [get_parent_payload_status, ← hblock, hparentBlock]
          rw [get_ancestor_step_status hsourceParent hsourceRoot hsourceGt
              hsourceTail,
            get_ancestor_step_status htargetParent htargetRoot htargetGt
              htargetTail,
            ← hparentRoot, ← hparentStatus]
          exact ih htargetTail' _

omit [Inhabited Root] in
/-- Checkpoint-block form of `get_ancestor_eq_of_paired_walks`. -/
theorem get_checkpoint_block_eq_of_paired_walks
    {source target : Store Root}
    (hsourceParent : ParentSlotLt source)
    (htargetParent : ParentSlotLt target)
    (hagree : ∀ r, r ∈ source.block_roots →
      r ∈ target.block_roots → source.blocks r = target.blocks r)
    {epoch : Epoch} {r : Root}
    (hsourceWalk : WalkKnown source
      (compute_start_slot_at_epoch cfg epoch) r)
    (htargetWalk : WalkKnown target
      (compute_start_slot_at_epoch cfg epoch) r) :
    get_checkpoint_block cfg source r epoch =
      get_checkpoint_block cfg target r epoch := by
  exact congrArg ForkChoiceNode.root
    (get_ancestor_eq_of_paired_walks hsourceParent htargetParent hagree
      hsourceWalk htargetWalk)

namespace Execution


end Execution

/-! ## Exact-stable query transport -/

/-- The exact query-filter leaf witness together with its one actually used
path down to `result`'s slot.  This is the path-local refinement of
`FilterViableLeafBelow`: it retains no walk or agreement fact about unrelated
query roots. -/
def PathLocalFilterViableLeafBelow
    (store : Store Root) (result : Root) : Prop :=
  ∃ tip : Root,
    tip ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root tip)
        (get_node_for_root result) = true ∧
      store.block_roots.filter
          (fun r => (store.blocks r).parent_root = tip) = [] ∧
      (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
        (get_voting_source cfg store tip).epoch =
            store.justified_checkpoint.epoch ∨
        (get_voting_source cfg store tip).epoch + 2 ≥
          get_current_store_epoch cfg store) ∧
      (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
        store.finalized_checkpoint.root =
          get_checkpoint_block cfg store tip
            store.finalized_checkpoint.epoch) ∧
      WalkKnown store (store.blocks result).slot tip


namespace Execution


namespace AcceptedRetainedPhaseSourceCarrierAt


/-- Exact-anchor F2 for an accepted retained source carrier.

Positive accepted AU at the carrier tip supplies an included justification
certificate.  The trusted anchor is therefore an exact prefix of that source,
so a single finalized-boundary walk reflects the anchor at the same tip.  No
visibility, source/finalized dominance assumption, or safety premise is used. -/
theorem finalizedRoot_eq_checkpointBlock_of_anchor
    {E : Execution Root}
    (B : ScheduledFFGInterpretation cfg ext E)
    (P : EpochCheckpointProjectionLaws B.anchor
      (E.RootKnownInScheduledPrefix cfg ext) B.state.checkpoint_at_epoch)
    (V : B.state.LinkCheckpointAgreement)
    (hanchorExact : B.anchor =
      B.state.checkpoint_at_epoch B.anchor.root B.anchor.epoch)
    {store : Store Root} (hparent : ParentSlotLt store)
    {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected)
    (hfinalizedAnchor : store.finalized_checkpoint = B.anchor)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg
        store.finalized_checkpoint.epoch) h.tip) :
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store h.tip
        store.finalized_checkpoint.epoch := by
  obtain ⟨hsourceJustified⟩ :=
    B.state.includedJustifiedAtTip_of_AU cfg ext h.source_au
  have hprefix : ExactCheckpointPrefix B.state.checkpoint_at_epoch B.anchor
      (normalizeAnchorCheckpoint B.anchor (get_voting_source cfg store h.tip)) :=
    IncludedCertifiedJustified.anchor_prefix
      (cfg := cfg) P V hanchorExact hsourceJustified
  have hepoch : B.anchor.epoch ≤
      (normalizeAnchorCheckpoint B.anchor (get_voting_source cfg store h.tip)).epoch :=
    IncludedCertifiedJustified.anchor_epoch_le
      (cfg := cfg) hsourceJustified
  have hwalkAnchor : WalkKnown store
      (compute_start_slot_at_epoch cfg B.anchor.epoch) h.tip := by
    simpa only [hfinalizedAnchor] using hwalk
  have hreflect : B.anchor.root =
      get_checkpoint_block cfg store h.tip B.anchor.epoch :=
    exactCheckpointPrefix_root_eq_at_sameTip cfg ext B.coherence
      h.store_causal hparent h.tip_known hprefix h.source_au hepoch
        hwalkAnchor
  simpa only [hfinalizedAnchor] using hreflect

end AcceptedRetainedPhaseSourceCarrierAt

end Execution

end FastConfirmation.Spec

end
