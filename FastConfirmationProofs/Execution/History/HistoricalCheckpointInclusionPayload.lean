module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetCheckpointInclusionSupport
public import FastConfirmationProofs.ForkChoice.Filter.FilterViability
public import FastConfirmationProofs.Execution.History.SelectedPreQueryHistoricalSIR

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted historical A3.2 payloads

Paper Lemma 27 needs more than the fact that a current checkpoint was once
selected. Its later A3.2 use needs the original call and target, the exact
`start(e+1)` deadline, and the common source of the concrete quorum.  This
file retains precisely that safety-free payload over the production
accepted-prefix FFG state.

The certificate and quorum are delayed until a cutoff after the target epoch.
Earlier endpoints use the original gate and vote support before the endpoint.
Transport is permitted
only when checkpoint reflection is available in one causal store and source
constancy is witnessed by an actual accepted same-epoch transition segment.
No canonicity, endpoint head conclusion, `SafeFrom`, or historical SIR result
is a field of the payload.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

/-- Support truncated at an endpoint slot `sl`: only votes of slots before
`sl` are constrained.  This is what an endpoint-slot induction hypothesis
can supply at endpoint slot `sl`. -/
def HonestVotesSupportTargetBefore (E : Execution Root) (T : Checkpoint Root) (q : ℕ)
    (sl : Slot) : Prop :=
  E.WithinHorizon cfg q ∧
    ∀ v ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = T.epoch → E.slot_at cfg q ≤ s →
      s < sl → ∀ k a, E.vote v s = some (k, a) → a.data.target = T

/-- A dependent quorum package whose equalities expose the exact historical
target and deadline without casting the vote object across indices. -/
structure AcceptedHistoricalA32QuorumAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (origin : Root) (e : Epoch) where
  deadline : Slot
  target : Checkpoint Root
  quorum : ConcreteA32QuorumBefore cfg ext E deadline target
  deadline_eq : deadline = compute_start_slot_at_epoch cfg (e + 1)
  target_eq : target = B.state.checkpoint_at_epoch origin e
  target_ne_anchor : target ≠ B.anchor
  source_eq : CheckpointReadsAs quorum.source (B.state.realized_justified origin)

/-- The irreducible paper-A3.2 data retained from a successful accepted
current-target gate.  In the non-anchor branch, the target and deadline are
indexed exactly and the quorum source is the block-local realized justified
checkpoint of the original current-epoch carrier. -/
structure AcceptedHistoricalA32GatePayloadAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (origin : Root) (e : Epoch) where
  origin_block : BeaconBlock Root
  origin_at : E.BlockKnownInScheduledPrefix cfg ext origin origin_block
  origin_epoch : compute_epoch_at_slot cfg origin_block.slot = e
  /-- The original invocation remains fixed under same-epoch transport. -/
  original_call : Option (ValidatorIndex × ℕ)
  original_honest : ∀ v n, original_call = some (v, n) → v ∈ E.honest
  original_target : ∀ v n, original_call = some (v, n) →
    B.state.checkpoint_at_epoch origin e = get_current_target cfg (E.store cfg ext v (n + 1))
  original_gate : ∀ v n, original_call = some (v, n) →
    will_current_target_be_justified cfg ext (E.store cfg ext v (n + 1)) = true
  anchor_case : original_call = none → B.state.checkpoint_at_epoch origin e = B.anchor
  anchor_epoch_le : B.anchor.epoch ≤ e
  /-- Derived in the joint call fold, or from the strict endpoint-slot IH.
  No certificate or quorum is made by this field. -/
  support_before : ∀ v n, original_call = some (v, n) → ∀ cutoff,
    E.HonestVotesSupportTargetBefore cfg
      (get_current_target cfg (E.store cfg ext v (n + 1))) (n + 1) cutoff
  certified : ∀ cutoff, compute_start_slot_at_epoch cfg (e + 1) ≤ cutoff →
    Nonempty (CertifiedJustified cfg E B.anchor (B.state.checkpoint_at_epoch origin e))
  support_branch : ∀ cutoff, compute_start_slot_at_epoch cfg (e + 1) ≤ cutoff →
    B.state.checkpoint_at_epoch origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)

namespace AcceptedHistoricalA32GatePayloadAt

/-- Initialize the historical payload at a carrier whose exact accepted
checkpoint is the trusted anchor.

This is the only payload constructor needed by the current-epoch finalized
reset branch.  It introduces no quorum: paper A3.2's anchor disjunct is
recorded directly, while the accepted carrier and its epoch remain explicit.
-/
def of_anchor
    (B : ScheduledFFGInterpretation cfg ext E)
    {origin : Root} {originBlock : BeaconBlock Root}
    (horiginAt : E.BlockKnownInScheduledPrefix cfg ext origin originBlock)
    {e : Epoch}
    (horiginEpoch : compute_epoch_at_slot cfg originBlock.slot = e)
    (hcheckpoint : B.state.checkpoint_at_epoch origin e = B.anchor) :
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e :=
  { origin_block := originBlock
    origin_at := horiginAt
    origin_epoch := horiginEpoch
    original_call := none
    original_honest := by intros; contradiction
    original_target := by intros; contradiction
    original_gate := by intros; contradiction
    anchor_case := fun _ => hcheckpoint
    anchor_epoch_le := by
      have he := congrArg Checkpoint.epoch hcheckpoint
      simpa only [B.state.checkpoint_epoch] using he.symm.le
    support_before := by intros; contradiction
    certified := fun _ _ => by
      rw [hcheckpoint]
      exact ⟨CertifiedJustified.anchor⟩
    support_branch := fun _ _ => Or.inl hcheckpoint }

/-- Retain the original fixed-source gate producer. The constructor records the
call and derived vote support. It does not apply the producer until a cutoff
after the target epoch is supplied. -/
def of_fixedSourceCurrentTarget
    (B : ScheduledFFGInterpretation cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    (hquery : store = E.store cfg ext v (n + 1))
    {origin : Root} (horigin : origin ∈ store.block_roots)
    {e : Epoch} (horiginEpoch : get_block_epoch cfg store origin = e)
    (htarget : get_current_target cfg store = B.state.checkpoint_at_epoch origin e)
    (hanchorLe : B.anchor.epoch ≤ e)
    (hgate : will_current_target_be_justified cfg ext store = true)
    (hsupport : HonestVotesSupportTarget cfg E (get_current_target cfg store) (n + 1))
    (hproducer : HonestVotesSupportTarget cfg E (get_current_target cfg store) (n + 1) →
      AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
        B.anchor B.state store origin) :
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e := by
  have htargetEpoch : (get_current_target cfg store).epoch = e := by
    rw [htarget, B.state.checkpoint_epoch]
  have hbefore (cutoff : Slot) : E.HonestVotesSupportTargetBefore cfg
      (get_current_target cfg store) (n + 1) cutoff :=
    ⟨hsupport.1, fun i hi sl hslH he hqsl _ k a hvote =>
      hsupport.2 i hi sl hslH he hqsl k a hvote⟩
  -- Demand the original producer only after every target-epoch vote slot.
  have realize (cutoff : Slot)
      (hafter : compute_start_slot_at_epoch cfg (e + 1) ≤ cutoff) :
      AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
        B.anchor B.state store origin := by
    apply hproducer
    refine ⟨(hbefore cutoff).1, ?_⟩
    intro i hi sl hslH he hqsl k a hvote
    apply (hbefore cutoff).2 i hi sl hslH he hqsl _ k a hvote
    apply lt_of_lt_of_le _ hafter
    rw [htargetEpoch] at he
    change sl / cfg.slots_per_epoch = e at he
    exact Nat.lt_mul_of_div_lt (by rw [he]; exact Nat.lt_succ_self _) cfg.slots_per_epoch_pos
  refine {
    origin_block := store.blocks origin
    origin_at := E.acceptedBlockAt_of_causal_known cfg ext hstore horigin
    origin_epoch := horiginEpoch
    original_call := some (v, n)
    original_honest := ?_
    original_target := ?_
    original_gate := ?_
    anchor_case := by intro h; contradiction
    anchor_epoch_le := hanchorLe
    support_before := ?_
    certified := ?_
    support_branch := ?_ }
  · intro w k heq
    cases Option.some.inj heq
    exact hv
  · intro w k heq
    cases Option.some.inj heq
    simpa only [hquery] using htarget.symm
  · intro w k heq
    cases Option.some.inj heq
    simpa only [hquery] using hgate
  · intro w k heq cutoff
    cases Option.some.inj heq
    simpa only [hquery] using hbefore cutoff
  · intro cutoff hafter
    rw [← htarget]
    exact (realize cutoff hafter).certified
  · intro cutoff hafter
    rcases (realize cutoff hafter).support_branch with hanchor | ⟨hne, Q, hsource⟩
    · exact Or.inl (htarget.symm.trans hanchor)
    · right
      have hsource' : CheckpointReadsAs Q.source (B.state.realized_justified origin) := by
        simpa only [AcceptedBlockFFGState.voting_source_at, CheckpointInclusionView.voting_source_at,
          htargetEpoch, horiginEpoch, if_pos] using hsource
      exact ⟨{
        deadline := compute_start_slot_at_epoch cfg ((get_current_target cfg store).epoch + 1)
        target := get_current_target cfg store
        quorum := Q
        deadline_eq := by rw [htargetEpoch]
        target_eq := htarget
        target_ne_anchor := hne
        source_eq := hsource' }⟩

/-- Same-epoch transport of the retained payload.

Checkpoint constancy is derived in the concrete causal store from executable
ancestry and accepted checkpoint reflection.  Source constancy is derived
separately from the exact accepted transition segment.  The original producer, call, target, source, and deadline are unchanged. -/
def transport_sameEpoch
    (B : ScheduledFFGInterpretation cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
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
  have hcheckpoint : B.state.checkpoint_at_epoch tip e = B.state.checkpoint_at_epoch origin e := by
    calc
      B.state.checkpoint_at_epoch tip e = get_checkpoint_for_block cfg store tip e :=
        B.coherence.checkpoint_of_known hstore tip htip e
      _ = get_checkpoint_for_block cfg store origin e := by
        exact congrArg (Checkpoint.mk e) hcheckpointBlock
      _ = B.state.checkpoint_at_epoch origin e :=
        (B.coherence.checkpoint_of_known hstore origin horigin e).symm
  have hsource : B.state.realized_justified tip = B.state.realized_justified origin :=
    hsegment.gj_eq_first hphase
      B.coherence.toFFGStateReadAgreement
  refine {
    origin_block := store.blocks tip
    origin_at := E.acceptedBlockAt_of_causal_known cfg ext hstore htip
    origin_epoch := ?_
    original_call := hpayload.original_call
    original_honest := hpayload.original_honest
    original_target := fun v n hc => hcheckpoint.trans (hpayload.original_target v n hc)
    original_gate := hpayload.original_gate
    anchor_case := fun hc => hcheckpoint.trans (hpayload.anchor_case hc)
    anchor_epoch_le := hpayload.anchor_epoch_le
    support_before := hpayload.support_before
    certified := ?_
    support_branch := ?_
  }
  · simpa only [get_block_epoch] using htipEpoch
  · intro cutoff hafter
    rw [hcheckpoint]
    exact hpayload.certified cutoff hafter
  · intro cutoff hafter
    rcases hpayload.support_branch cutoff hafter with hanchor | hquorum
    · exact Or.inl (hcheckpoint.trans hanchor)
    · obtain ⟨hquorum⟩ := hquorum
      exact Or.inr ⟨
        { deadline := hquorum.deadline
          target := hquorum.target
          quorum := hquorum.quorum
          deadline_eq := hquorum.deadline_eq
          target_eq := hquorum.target_eq.trans hcheckpoint.symm
          target_ne_anchor := hquorum.target_ne_anchor
          source_eq := hquorum.source_eq.trans (CheckpointReadsAs.of_eq hsource.symm) }⟩

end AcceptedHistoricalA32GatePayloadAt

/-- Concatenation of accepted same-epoch segments.  Every nontrivial edge in
the result is still owned by the original exact accepted transition carrier. -/
theorem acceptedProjectedSameEpochSegment_trans
    {B : ScheduledFFGInterpretation cfg ext E}
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
    (B : ScheduledFFGInterpretation cfg ext E)
    (tip : Root) (e : Epoch) where
  origin : Root
  payload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e
  tip_block : BeaconBlock Root
  tip_at : E.BlockKnownInScheduledPrefix cfg ext tip tip_block
  tip_epoch : compute_epoch_at_slot cfg tip_block.slot = e
  descends : E.RootDescends tip origin
  same_epoch_segment : AcceptedProjectedSameEpochSegment cfg ext E B.state
    origin tip

namespace AcceptedHistoricalA32LineageAt

/-- Initialize a historical lineage at the gate carrier itself. -/
def refl
    {B : ScheduledFFGInterpretation cfg ext E}
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
    {B : ScheduledFFGInterpretation cfg ext E}
    {middle tip : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B middle e)
    (htipBlock : BeaconBlock Root)
    (htipAt : E.BlockKnownInScheduledPrefix cfg ext tip htipBlock)
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
    {B : ScheduledFFGInterpretation cfg ext E}
    (hphase : Phase0SourceCoherence cfg ext)
    {tip : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B tip e)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
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
    (B : ScheduledFFGInterpretation cfg ext E)
    (query : FastConfirmationStore Root) (input result : Root) : Prop :=
  get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store →
  (¬ ∃ a c : Root, CurrentTargetSelectedEdge cfg ext query input a c) →
    ∃ e : Epoch,
      get_current_target cfg query.store = B.state.checkpoint_at_epoch result e ∧
      Nonempty (E.AcceptedHistoricalA32GatePayloadAt cfg ext B result e)

/-- Compatibility adapter for the existing SIR pipeline.  It is intentionally
one-way: a certificate-only producer cannot reconstruct the erased quorum,
source, or deadline. -/
theorem acceptedHistoricalA32PayloadProducerAt_to_certificateProducer
    (B : ScheduledFFGInterpretation cfg ext E)
    {q : ℕ} {query : FastConfirmationStore Root} {input result : Root}
    (hproducer : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query input result) :
    E.HistoricalCurrentTargetCertificateProducerAt cfg ext B.anchor q
      query input result := by
  intro hcurrent hnoCrossing
  obtain ⟨e, htarget, ⟨hpayload⟩⟩ := hproducer hcurrent hnoCrossing
  rw [htarget]
  exact hpayload.certified (compute_start_slot_at_epoch cfg (e + 1)) (Nat.le_refl _)

end Execution


end FastConfirmation.Spec

end
