module
public import FastConfirmation.Spec.Proof.CurrentTargetA32Support
public import FastConfirmation.Spec.Proof.FilterViability
public import FastConfirmation.Spec.Proof.SelectedPreQueryHistoricalSIR
public import FastConfirmation.Spec.Proof.ModelFacts

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

/-- Deferred, epoch-indexed form of the payload's paper-A3.2 support branch.

`docs/epoch-indexed-restructure.md` §5 establishes that **every** positive
consumption of the retained quorum is guarded by `e + 2 ≤ currentEpoch` at the
consuming store — the target epoch is at least two epochs behind the consumer,
so the quorum's `start_slot (e+1)` deadline places all of its votes a full
epoch in the consumer's past.  Stating the branch in this guarded form records
that fact in the *type*: the anchor-or-quorum content can only be read at a
late honest endpoint, and a future per-epoch discharge layer only has to
supply it there.

The conclusion does not mention `w` or `m`; the binders exist solely to carry
the guard.  `AcceptedHistoricalA32LineageAt.lateVisibleSeedAt`
(`AcceptedSelectedStrictEdgeFilterSupply.lean`) is the sole consumer, and its
`hlate`/`hmH`/`hw` hypotheses are exactly this antecedent. -/
def AcceptedHistoricalA32DeferredSupportAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (origin : Root) (e : Epoch) : Prop :=
  ∀ w : ValidatorIndex, w ∈ E.honest → ∀ m : ℕ, E.WithinHorizon cfg m →
    e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
      B.state.C origin e = B.anchor ∨
        Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)

/-- The irreducible paper-A3.2 data retained from a successful accepted
current-target gate, **parameterized by its certification and support
obligations**.

`docs/crossing-call-support-residue.md` §4.3/§5.3 is the reason for the two
predicate parameters.  The record's *shape* — accepted origin block, its
epoch, the anchor-epoch bound — is shared by both trunks; what differs is how
much positive content the two trunks can afford to carry at construction time:

* the **eager** instantiation (`AcceptedHistoricalA32GatePayloadAt` below)
  carries the actual `CertifiedJustified` certificate and the guarded
  anchor-or-quorum disjunction, exactly as before.  Every existing caller,
  strong and weak, keeps working against it verbatim because the abbreviation
  is reducible;
* a **lazy** instantiation records only origin-call data and manufactures the
  positive content at the consuming call, under a hypothetical safety
  antecedent.  That is what breaks the same-step circularity of the crossing
  branch.

`Cert` is a predicate on the *checkpoint*, so same-epoch transport re-indexes
it with a single `rw`.  `Supp` is a predicate on `(origin, epoch)` because the
retained quorum record is indexed by the origin root; transport therefore
takes an explicit re-indexing hypothesis. -/
structure AcceptedHistoricalA32GatePayloadCoreAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (origin : Root) (e : Epoch)
    (Cert : Checkpoint Root → Prop) (Supp : Root → Epoch → Prop) where
  origin_block : BeaconBlock Root
  origin_at : E.AcceptedBlockAt cfg ext origin origin_block
  origin_epoch : compute_epoch_at_slot cfg origin_block.slot = e
  /-- The trusted anchor is not above the payload's own epoch.

  This is the *only* consequence of the positive certification that the
  boundary-walk consumers (`AcceptedHistoricalA32LineageAt.payloadAtQuery_nonempty`
  and its four siblings) read; recording it as its own field decouples them
  from `certified`, which the epoch-indexed restructure moves behind an
  `e + 2 ≤ currentEpoch` guard.  Every constructor below discharges it
  without extra input: the anchor branch by checkpoint equality and the
  gate branch by `CertifiedJustified.anchor_epoch_le`. -/
  anchor_epoch_le : B.anchor.epoch ≤ e
  certified : Cert (B.state.C origin e)
  support_branch : Supp origin e

/-- The eager certification obligation: an actual anchored FFG certificate on
the retained checkpoint. -/
abbrev AcceptedHistoricalA32EagerCert
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (c : Checkpoint Root) : Prop :=
  Nonempty (CertifiedJustified cfg E B.anchor c)

/-- The eager support obligation: the guarded anchor-or-quorum disjunction. -/
abbrev AcceptedHistoricalA32EagerSupp
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (origin : Root) (e : Epoch) : Prop :=
  E.AcceptedHistoricalA32DeferredSupportAt cfg ext B origin e

/-- The eager instantiation of the retained payload — the record every
existing caller (strong and weak) already uses.  It is a reducible
abbreviation, so dot notation, anonymous-constructor notation and the existing
constructor names all resolve exactly as before. -/
abbrev AcceptedHistoricalA32GatePayloadAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (origin : Root) (e : Epoch) :=
  E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
    (E.AcceptedHistoricalA32EagerCert cfg ext B)
    (E.AcceptedHistoricalA32EagerSupp cfg ext B)

namespace AcceptedHistoricalA32GatePayloadCoreAt

/-- Re-instantiate the certification obligation pointwise. -/
def mapCert
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {origin : Root} {e : Epoch}
    {Cert Cert' : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hmap : Cert (B.state.C origin e) → Cert' (B.state.C origin e))
    (h : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert Supp) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert' Supp :=
  { origin_block := h.origin_block
    origin_at := h.origin_at
    origin_epoch := h.origin_epoch
    anchor_epoch_le := h.anchor_epoch_le
    certified := hmap h.certified
    support_branch := h.support_branch }

/-- Re-instantiate the support obligation pointwise. -/
def mapSupp
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {origin : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp Supp' : Root → Epoch → Prop}
    (hmap : Supp origin e → Supp' origin e)
    (h : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert Supp) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert Supp' :=
  { origin_block := h.origin_block
    origin_at := h.origin_at
    origin_epoch := h.origin_epoch
    anchor_epoch_le := h.anchor_epoch_le
    certified := h.certified
    support_branch := hmap h.support_branch }

/-- Generic anchor constructor.  Both obligations are discharged from the
anchor equality alone, which every instantiation of interest satisfies. -/
def of_anchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {origin : Root} {originBlock : BeaconBlock Root}
    (horiginAt : E.AcceptedBlockAt cfg ext origin originBlock)
    {e : Epoch}
    (horiginEpoch : compute_epoch_at_slot cfg originBlock.slot = e)
    (hcheckpoint : B.state.C origin e = B.anchor)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e') :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert Supp :=
  { origin_block := originBlock
    origin_at := horiginAt
    origin_epoch := horiginEpoch
    anchor_epoch_le := by
      have hepoch := congrArg Checkpoint.epoch hcheckpoint
      rw [B.state.checkpoint_epoch] at hepoch
      exact le_of_eq hepoch.symm
    certified := by
      rw [hcheckpoint]
      exact hanchorCert
    support_branch := hanchorSupp origin e hcheckpoint }

/-- The weakest generic constructor: an accepted current-epoch carrier, the
trusted-anchor epoch bound, and the two obligations.

The anchor bound is taken as a hypothesis rather than read off a certificate,
which is exactly what lets the lazy instantiation build a payload without ever
constructing the positive certification content — at an actual call it is the
ambient `trustedAnchor_epoch_le_currentEpoch` fact. -/
def of_causalKnown
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {origin : Root} (horigin : origin ∈ store.block_roots)
    {e : Epoch} (horiginEpoch : get_block_epoch cfg store origin = e)
    (hanchorLe : B.anchor.epoch ≤ e)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hcert : Cert (B.state.C origin e))
    (hsupp : Supp origin e) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert Supp :=
  { origin_block := store.blocks origin
    origin_at := E.acceptedBlockAt_of_causal_known cfg ext hstore horigin
    origin_epoch := by simpa only [get_block_epoch] using horiginEpoch
    anchor_epoch_le := hanchorLe
    certified := hcert
    support_branch := hsupp }

/-- Generic fixed-source gate constructor.  The gate realization is still
required — it is what bounds the anchor epoch — but the two payload
obligations are supplied by the caller, which is what lets the strong trunk
defer them. -/
def of_fixedSourceCurrentTarget
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {origin : Root} (horigin : origin ∈ store.block_roots)
    {e : Epoch} (horiginEpoch : get_block_epoch cfg store origin = e)
    (htarget : get_current_target cfg store = B.state.C origin e)
    (hgate : AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store origin)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hcert : Cert (B.state.C origin e))
    (hsupp : Supp origin e) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e Cert Supp := by
  refine {
    origin_block := store.blocks origin
    origin_at := E.acceptedBlockAt_of_causal_known cfg ext hstore horigin
    origin_epoch := ?_
    anchor_epoch_le := ?_
    certified := hcert
    support_branch := hsupp
  }
  · simpa only [get_block_epoch] using horiginEpoch
  · have hle := CertifiedJustified.anchor_epoch_le (cfg := cfg)
      (Classical.choice hgate.certified)
    rw [htarget, B.state.checkpoint_epoch] at hle
    exact hle

/-- The eager support branch of the fixed-source gate constructor, retained as
its own lemma so that both the eager wrapper and any future instantiation can
reuse the dependent rewriting verbatim. -/
theorem eagerSupport_of_fixedSourceCurrentTarget
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root}
    {origin : Root}
    {e : Epoch} (horiginEpoch : get_block_epoch cfg store origin = e)
    (htarget : get_current_target cfg store = B.state.C origin e)
    (hgate : AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state store origin) :
    B.state.C origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e) := by
  rcases hgate.support_branch with hanchor | ⟨hne, Q, hsource⟩
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

/-- Re-index the retained anchor-or-quorum disjunction along a same-epoch
segment.  This is the transport step shared by the eager and the lazy support
instantiations. -/
theorem quorumDisjunction_transport
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {origin tip : Root} {e : Epoch}
    (hcheckpoint : B.state.C tip e = B.state.C origin e)
    (hsource : B.state.GJ tip = B.state.GJ origin)
    (h : B.state.C origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)) :
    B.state.C tip e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B tip e) := by
  rcases h with hanchor | hquorum
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

/-- Generic same-epoch transport of the retained payload.

Checkpoint constancy is derived in the concrete causal store from executable
ancestry and accepted checkpoint reflection.  Source constancy is derived
separately from the exact accepted transition segment.  `Cert` moves by a
single `rw`; `Supp` moves by the caller-supplied re-indexing, which is handed
both derived equalities. -/
def transport_sameEpoch
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    {origin tip : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hpayload : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      Cert Supp)
    (horigin : origin ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (horiginEpoch : get_block_epoch cfg store origin = e)
    (htipEpoch : get_block_epoch cfg store tip = e)
    (hancestor : is_ancestor store (get_node_for_root tip)
      (get_node_for_root origin) = true)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) tip)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      origin tip)
    (hsuppT : B.state.C tip e = B.state.C origin e →
      B.state.GJ tip = B.state.GJ origin → Supp origin e → Supp tip e) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B tip e Cert Supp := by
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
    anchor_epoch_le := hpayload.anchor_epoch_le
    certified := ?_
    support_branch := hsuppT hcheckpoint hsource hpayload.support_branch
  }
  · simpa only [get_block_epoch] using htipEpoch
  · rw [hcheckpoint]
    exact hpayload.certified

end AcceptedHistoricalA32GatePayloadCoreAt

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
  AcceptedHistoricalA32GatePayloadCoreAt.of_anchor cfg ext B horiginAt
    horiginEpoch hcheckpoint ⟨CertifiedJustified.anchor⟩
    (fun _ _ h _ _ _ _ _ => Or.inl h)

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
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e :=
  AcceptedHistoricalA32GatePayloadCoreAt.of_fixedSourceCurrentTarget cfg ext B
    hstore horigin horiginEpoch htarget hgate
    (by rw [← htarget]; exact hgate.certified)
    (fun _ _ _ _ _ =>
      AcceptedHistoricalA32GatePayloadCoreAt.eagerSupport_of_fixedSourceCurrentTarget
        cfg ext B horiginEpoch htarget hgate)

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
    E.AcceptedHistoricalA32GatePayloadAt cfg ext B tip e :=
  AcceptedHistoricalA32GatePayloadCoreAt.transport_sameEpoch cfg ext B hphase
    hstore hparent hpayload horigin htip horiginEpoch htipEpoch hancestor
    hwalk hsegment
    (fun hcheckpoint hsource hsupp w hw m hmH hlate =>
      AcceptedHistoricalA32GatePayloadCoreAt.quorumDisjunction_transport
        cfg ext hcheckpoint hsource (hsupp w hw m hmH hlate))

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
structure AcceptedHistoricalA32LineageCoreAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (tip : Root) (e : Epoch)
    (Cert : Checkpoint Root → Prop) (Supp : Root → Epoch → Prop) where
  origin : Root
  payload : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
    Cert Supp
  tip_block : BeaconBlock Root
  tip_at : E.AcceptedBlockAt cfg ext tip tip_block
  tip_epoch : compute_epoch_at_slot cfg tip_block.slot = e
  descends : E.RootDescends tip origin
  same_epoch_segment : AcceptedProjectedSameEpochSegment cfg ext E B.state
    origin tip

/-- The eager instantiation of the retained lineage — the record every
existing caller already uses. -/
abbrev AcceptedHistoricalA32LineageAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (tip : Root) (e : Epoch) :=
  E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e
    (E.AcceptedHistoricalA32EagerCert cfg ext B)
    (E.AcceptedHistoricalA32EagerSupp cfg ext B)

namespace AcceptedHistoricalA32LineageCoreAt

/-- Initialize a historical lineage at the gate carrier itself. -/
def refl
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {origin : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hpayload : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      Cert Supp) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B origin e Cert Supp :=
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
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B middle e
      Cert Supp)
    (htipBlock : BeaconBlock Root)
    (htipAt : E.AcceptedBlockAt cfg ext tip htipBlock)
    (htipEpoch : compute_epoch_at_slot cfg htipBlock.slot = e)
    (hdesc : E.RootDescends tip middle)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      middle tip) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert Supp :=
  { origin := hlineage.origin
    payload := hlineage.payload
    tip_block := htipBlock
    tip_at := htipAt
    tip_epoch := htipEpoch
    descends := Execution.RootDescends.trans E hdesc hlineage.descends
    same_epoch_segment := E.acceptedProjectedSameEpochSegment_trans cfg ext
      hlineage.same_epoch_segment hsegment }

/-- Re-instantiate the support obligation pointwise along a lineage. -/
def mapSupp
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {tip : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp Supp' : Root → Epoch → Prop}
    (hmap : ∀ o : Root, Supp o e → Supp' o e)
    (h : E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert Supp) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert Supp' :=
  { origin := h.origin
    payload := h.payload.mapSupp cfg ext (hmap h.origin)
    tip_block := h.tip_block
    tip_at := h.tip_at
    tip_epoch := h.tip_epoch
    descends := h.descends
    same_epoch_segment := h.same_epoch_segment }

/-- Re-instantiate the certification obligation pointwise along a lineage. -/
def mapCert
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {tip : Root} {e : Epoch}
    {Cert Cert' : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hmap : ∀ o : Root, Cert (B.state.C o e) → Cert' (B.state.C o e))
    (h : E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert Supp) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert' Supp :=
  { origin := h.origin
    payload := h.payload.mapCert cfg ext (hmap h.origin)
    tip_block := h.tip_block
    tip_at := h.tip_at
    tip_epoch := h.tip_epoch
    descends := h.descends
    same_epoch_segment := h.same_epoch_segment }

/-- Materialize the retained origin payload at the current tip in one causal
store, generically in the two payload obligations. -/
def payloadAtTip
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hphase : Phase0SourceCoherence cfg ext)
    {tip : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e Cert Supp)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (horigin : hlineage.origin ∈ store.block_roots)
    (htip : tip ∈ store.block_roots)
    (horiginEpoch : get_block_epoch cfg store hlineage.origin = e)
    (htipEpoch : get_block_epoch cfg store tip = e)
    (hancestor : is_ancestor store (get_node_for_root tip)
      (get_node_for_root hlineage.origin) = true)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e) tip)
    (hsuppT : B.state.C tip e = B.state.C hlineage.origin e →
      B.state.GJ tip = B.state.GJ hlineage.origin →
      Supp hlineage.origin e → Supp tip e) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B tip e Cert Supp :=
  AcceptedHistoricalA32GatePayloadCoreAt.transport_sameEpoch cfg ext B hphase
    hstore hparent hlineage.payload horigin htip horiginEpoch htipEpoch
    hancestor hwalk hlineage.same_epoch_segment hsuppT

end AcceptedHistoricalA32LineageCoreAt

namespace AcceptedHistoricalA32LineageAt

/-- Initialize a historical lineage at the gate carrier itself. -/
def refl
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {origin : Root} {e : Epoch}
    (hpayload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B origin e :=
  AcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload

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
  AcceptedHistoricalA32LineageCoreAt.extend cfg ext hlineage htipBlock htipAt
    htipEpoch hdesc hsegment

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
  (¬ ∃ a c : Root, CurrentTargetAcceptedEdge cfg ext query input a c) →
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
