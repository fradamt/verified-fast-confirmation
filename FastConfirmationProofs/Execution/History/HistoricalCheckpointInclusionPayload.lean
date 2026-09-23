module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.ForkChoice.Filter.FilterViability
public import FastConfirmationProofs.Execution.History.SelectedPreQueryHistoricalSIR

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted historical A3.2 payloads

Paper Lemma 27 needs more than the fact that a current checkpoint was once
certified.  Its later A3.2 use needs the original target, the exact
`start(e+1)` deadline, and the common source of the concrete quorum.  This
file retains precisely that safety-free payload over the production
accepted-prefix FFG state.

The payload is store-independent after construction.  Transport is permitted
only when checkpoint reflection is available in one causal store and source
constancy is witnessed by an actual accepted same-epoch transition segment.
No canonicity, endpoint head conclusion, `SafeFrom`, or historical SIR result
is a field of the payload.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- A dependent quorum package whose equalities expose the exact historical
target and deadline without casting the vote object across indices. -/
structure AcceptedHistoricalA32QuorumAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (origin : Root) (e : Epoch) where
  deadline : Slot
  target : Checkpoint Root
  quorum : ConcreteA32QuorumBefore cfg ext E deadline target
  deadline_eq : deadline = compute_start_slot_at_epoch cfg (e + 1)
  target_eq : target = B.state.C origin e
  target_ne_anchor : target ≠ B.anchor
  source_eq : quorum.source = B.state.GJ origin

/-- The irreducible paper-A3.2 data retained from a successful accepted
current-target gate.  In the non-anchor branch, the target and deadline are
indexed exactly and the quorum source is the block-local realized justified
checkpoint of the original current-epoch carrier. -/
structure AcceptedHistoricalA32GatePayloadAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (origin : Root) (e : Epoch) where
  origin_block : BeaconBlock Root
  origin_at : E.AcceptedBlockAt cfg ext origin origin_block
  origin_epoch : compute_epoch_at_slot cfg origin_block.slot = e
  certified : Nonempty
    (CertifiedJustified cfg E B.anchor (B.state.C origin e))
  support_branch :
    B.state.C origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)

namespace AcceptedHistoricalA32GatePayloadAt

/-- Initialize the historical payload at a carrier whose exact accepted
checkpoint is the trusted anchor.

This is the only payload constructor needed by the current-epoch finalized
reset branch.  It introduces no quorum: paper A3.2's anchor disjunct is
recorded directly, while the accepted carrier and its epoch remain explicit.
-/
def of_anchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {origin : Root} {originBlock : BeaconBlock Root}
    (horiginAt : E.AcceptedBlockAt cfg ext origin originBlock)
    {e : Epoch}
    (horiginEpoch : compute_epoch_at_slot cfg originBlock.slot = e)
    (hcheckpoint : B.state.C origin e = B.anchor) :
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e :=
  { origin_block := originBlock
    origin_at := horiginAt
    origin_epoch := horiginEpoch
    certified := by
      rw [hcheckpoint]
      exact ⟨CertifiedJustified.anchor⟩
    support_branch := Or.inl hcheckpoint }

/-- Construct the historical payload from the fixed-source accepted gate at
its original current-epoch carrier.  The theorem performs only dependent
rewriting: all votes, the source agreement, and the certificate were already
constructed by the gate realization. -/
def of_fixedSourceCurrentTarget
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {origin : Root} (horigin : origin ∈ store.block_roots)
    {e : Epoch} (horiginEpoch : get_block_epoch cfg store origin = e)
    (htarget : get_current_target cfg store = B.state.C origin e)
    (hgate : AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store origin) :
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e := by
  refine {
    origin_block := store.blocks origin
    origin_at := E.acceptedBlockAt_of_causal_known cfg ext hstore horigin
    origin_epoch := ?_
    certified := ?_
    support_branch := ?_
  }
  · simpa only [get_block_epoch] using horiginEpoch
  · rw [← htarget]
    exact hgate.certified
  · rcases hgate.support_branch with hanchor | ⟨hne, Q, hsource⟩
    · exact Or.inl (htarget.symm.trans hanchor)
    · right
      have htargetEpoch : (get_current_target cfg store).epoch = e := by
        calc
          (get_current_target cfg store).epoch =
              (B.state.C origin e).epoch := congrArg Checkpoint.epoch htarget
          _ = e := B.state.checkpoint_epoch origin e
      have hsource' : Q.source = B.state.GJ origin := by
        simpa only [AcceptedChainFFGState.VSAt, PaperA32StateView.VSAt,
          htargetEpoch, horiginEpoch, if_pos] using hsource
      exact ⟨
        { deadline := compute_start_slot_at_epoch cfg
            ((get_current_target cfg store).epoch + 1)
          target := get_current_target cfg store
          quorum := Q
          deadline_eq := by rw [htargetEpoch]
          target_eq := htarget
          target_ne_anchor := hne
          source_eq := hsource' }⟩

/-- Same-epoch transport of the retained payload.

Checkpoint constancy is derived in the concrete causal store from executable
ancestry and accepted checkpoint reflection.  Source constancy is derived
separately from the exact accepted transition segment.  The concrete quorum
itself is unchanged. -/
def transport_sameEpoch
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    {origin tip : Root} {e : Epoch}
    (hpayload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e)
    (horigin : origin ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (horiginEpoch : get_block_epoch cfg store origin = e)
    (htipEpoch : get_block_epoch cfg store tip = e)
    (hancestor : is_ancestor store (get_node_for_root tip)
      (get_node_for_root origin) = true)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) tip)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      origin tip) :
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B tip e := by
  have hboundary : compute_start_slot_at_epoch cfg e ≤
      (store.blocks origin).slot := by
    rw [← horiginEpoch]
    exact start_slot_at_block_epoch_le cfg store origin
  have hcheckpointBlock : get_checkpoint_block cfg store tip e =
      get_checkpoint_block cfg store origin e :=
    get_checkpoint_block_of_ancestor cfg hparent hancestor hboundary hwalk
  have hcheckpoint : B.state.C tip e = B.state.C origin e := by
    calc
      B.state.C tip e = get_checkpoint_for_block cfg store tip e :=
        B.coherence.checkpoint_of_known hstore tip htip e
      _ = get_checkpoint_for_block cfg store origin e := by
        exact congrArg (Checkpoint.mk e) hcheckpointBlock
      _ = B.state.C origin e :=
        (B.coherence.checkpoint_of_known hstore origin horigin e).symm
  have hsource : B.state.GJ tip = B.state.GJ origin :=
    hsegment.gj_eq_first hphase
      B.coherence.toAcceptedFFGSelectorCoherence
  refine {
    origin_block := store.blocks tip
    origin_at := E.acceptedBlockAt_of_causal_known cfg ext hstore htip
    origin_epoch := ?_
    certified := ?_
    support_branch := ?_
  }
  · simpa only [get_block_epoch] using htipEpoch
  · rw [hcheckpoint]
    exact hpayload.certified
  · rcases hpayload.support_branch with hanchor | hquorum
    · exact Or.inl (hcheckpoint.trans hanchor)
    · obtain ⟨hquorum⟩ := hquorum
      exact Or.inr ⟨
        { deadline := hquorum.deadline
          target := hquorum.target
          quorum := hquorum.quorum
          deadline_eq := hquorum.deadline_eq
          target_eq := hquorum.target_eq.trans hcheckpoint.symm
          target_ne_anchor := hquorum.target_ne_anchor
          source_eq := hquorum.source_eq.trans hsource.symm }⟩

end AcceptedHistoricalA32GatePayloadAt

/-- Concatenation of accepted same-epoch segments.  Every nontrivial edge in
the result is still owned by the original exact accepted transition carrier. -/
theorem acceptedProjectedSameEpochSegment_trans
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {a b c : Root}
    (hab : AcceptedProjectedSameEpochSegment cfg ext E B.state a b)
    (hbc : AcceptedProjectedSameEpochSegment cfg ext E B.state b c) :
    AcceptedProjectedSameEpochSegment cfg ext E B.state a c := by
  induction hbc with
  | refl => exact hab
  | tail hprefix hedge ih => exact .tail ih hedge

/-- A safety-free historical lineage.  The fixed-source payload remains at
the invocation which created it; later current-epoch candidates retain only
semantic descent and an exact accepted same-epoch transition segment from
that origin. -/
structure AcceptedHistoricalA32LineageAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (tip : Root) (e : Epoch) where
  origin : Root
  payload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e
  tip_block : BeaconBlock Root
  tip_at : E.AcceptedBlockAt cfg ext tip tip_block
  tip_epoch : compute_epoch_at_slot cfg tip_block.slot = e
  descends : E.RootDescends tip origin
  same_epoch_segment : AcceptedProjectedSameEpochSegment cfg ext E B.state
    origin tip

namespace AcceptedHistoricalA32LineageAt

/-- Initialize a historical lineage at the gate carrier itself. -/
def refl
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {origin : Root} {e : Epoch}
    (hpayload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B origin e :=
  { origin := origin
    payload := hpayload
    tip_block := hpayload.origin_block
    tip_at := hpayload.origin_at
    tip_epoch := hpayload.origin_epoch
    descends := .refl origin
    same_epoch_segment := .refl origin hpayload.origin_block hpayload.origin_at }

/-- Extend a retained lineage by a separately proved semantic descent and an
actual accepted same-epoch segment.  This is the induction step used by a
future concrete FCR-call trajectory; it has no endpoint-safety premise. -/
def extend
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {middle tip : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B middle e)
    (htipBlock : BeaconBlock Root)
    (htipAt : E.AcceptedBlockAt cfg ext tip htipBlock)
    (htipEpoch : compute_epoch_at_slot cfg htipBlock.slot = e)
    (hdesc : E.RootDescends tip middle)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      middle tip) :
    E.AcceptedHistoricalA32LineageAt cfg ext B tip e :=
  { origin := hlineage.origin
    payload := hlineage.payload
    tip_block := htipBlock
    tip_at := htipAt
    tip_epoch := htipEpoch
    descends := Execution.RootDescends.trans E hdesc hlineage.descends
    same_epoch_segment := E.acceptedProjectedSameEpochSegment_trans cfg ext
      hlineage.same_epoch_segment hsegment }

/-- Materialize the retained origin payload at the current tip in one causal
store.  This is the exact bridge needed before a historical A3.2 consumer can
use the later candidate as its carrier. -/
def payloadAtTip
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hphase : Phase0SourceCoherence cfg ext)
    {tip : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B tip e)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (horigin : hlineage.origin ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (horiginEpoch : get_block_epoch cfg store hlineage.origin = e)
    (htipEpoch : get_block_epoch cfg store tip = e)
    (hancestor : is_ancestor store (get_node_for_root tip)
      (get_node_for_root hlineage.origin) = true)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) tip) :
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B tip e :=
  AcceptedHistoricalA32GatePayloadAt.transport_sameEpoch cfg ext B hphase
    hstore hparent hlineage.payload horigin htip horiginEpoch htipEpoch
    hancestor hwalk hlineage.same_epoch_segment

end AcceptedHistoricalA32LineageAt

/-- Historical producer with the retained A3.2 payload.  This is deliberately
stronger than the old certificate-only producer but has the same executable
current/no-crossing call boundary. -/
def AcceptedHistoricalA32PayloadProducerAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (query : FastConfirmationStore Root) (input result : Root) : Prop :=
  get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store →
  (¬ ∃ a c : Root, CurrentTargetSelectedEdge cfg ext query input a c) →
    ∃ e : Epoch,
      get_current_target cfg query.store = B.state.C result e ∧
      Nonempty (E.AcceptedHistoricalA32GatePayloadAt cfg ext B result e)

/-- Compatibility adapter for the existing SIR pipeline.  It is intentionally
one-way: a certificate-only producer cannot reconstruct the erased quorum,
source, or deadline. -/
theorem acceptedHistoricalA32PayloadProducerAt_to_certificateProducer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {q : ℕ} {query : FastConfirmationStore Root} {input result : Root}
    (hproducer : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query input result) :
    E.HistoricalCurrentTargetCertificateProducerAt cfg ext B.anchor q
      query input result := by
  intro hcurrent hnoCrossing
  obtain ⟨e, htarget, ⟨hpayload⟩⟩ := hproducer hcurrent hnoCrossing
  rw [htarget]
  exact hpayload.certified

end Execution


end FastConfirmation.Spec

end
