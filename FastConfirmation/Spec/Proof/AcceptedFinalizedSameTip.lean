module
public import FastConfirmation.Spec.Proof.AcceptedResetCheckpointRealization
public import FastConfirmation.Spec.Proof.ExactCheckpointLinks
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Accepted finalized/justified evidence on one concrete tip

Included certificates are indexed by a carrier tip because their attestations
must occur on that tip's chain.  AU selectors may inherit a formed checkpoint
from an earlier carrier, so the certificate initially exposed by
`formed_evidence` is indexed by that earlier carrier.  The first section proves
the missing, purely structural reindexing along `RootDescends`.

The second section uses it to put `GF` with `GJ`, and `GUF` with `GU`, on the
same accepted tip.  Exact link validity and checkpoint accountability then
derive an exact epoch-indexed finalized prefix.  Finally, causal-store
reflection plus one concrete boundary walk turns that prefix into the exact
`get_checkpoint_block` equation consumed by the executable finalized leaf
check.

There is no ordinary-root-ancestry substitution, legacy transition history,
justification interface, filter conclusion, or safety premise in this file.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Carrier transport for included certificates -/

namespace AttestationIncludedOnChain

/-- Inclusion on `carrier`'s chain remains inclusion on every semantic
descendant tip. -/
theorem transport_descendant
    {E : Execution Root} {included : Root → Attestation Root → Prop}
    {tip carrier : Root} {a : Attestation Root}
    (htip : E.RootDescends tip carrier)
    (h : AttestationIncludedOnChain E included carrier a) :
    AttestationIncludedOnChain E included tip a := by
  obtain ⟨bodyCarrier, hcarrier, hincluded⟩ := h
  exact ⟨bodyCarrier, Execution.RootDescends.trans E htip hcarrier,
    hincluded⟩

end AttestationIncludedOnChain

namespace IncludedSupermajorityLink

/-- Reindex an included link from an ancestor carrier onto a descendant tip.
All signer and link data are unchanged; only the on-chain inclusion witness is
composed. -/
def transport_descendant
    {E : Execution Root} {included : Root → Attestation Root → Prop}
    {tip carrier : Root} {source target : Checkpoint Root}
    (htip : E.RootDescends tip carrier)
    (L : IncludedSupermajorityLink cfg E included carrier source target) :
    IncludedSupermajorityLink cfg E included tip source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨a, haincluded, hia, hsource, htarget⟩ :=
      L.signer_attestation i hi
    exact ⟨a, haincluded.transport_descendant htip, hia, hsource, htarget⟩
  supermajority := L.supermajority

end IncludedSupermajorityLink

namespace IncludedCertifiedJustified

/-- Reindex every link in an included justification certificate onto a
semantic descendant tip. -/
def transport_descendant
    {E : Execution Root} {included : Root → Attestation Root → Prop}
    {anchor : Checkpoint Root} {tip carrier : Root} {c : Checkpoint Root}
    (htip : E.RootDescends tip carrier)
    (hcertificate : IncludedCertifiedJustified cfg E included
      anchor carrier c) :
    IncludedCertifiedJustified cfg E included anchor tip c := by
  induction hcertificate with
  | anchor => exact .anchor
  | link hsource hlink ih =>
      exact .link ih (hlink.transport_descendant cfg htip)

end IncludedCertifiedJustified

namespace IncludedCertifiedFinalized

/-- Reindex an included finalization certificate and its finalizing link onto
a semantic descendant tip. -/
def transport_descendant
    {E : Execution Root} {included : Root → Attestation Root → Prop}
    {anchor : Checkpoint Root} {tip carrier : Root} {c : Checkpoint Root}
    (htip : E.RootDescends tip carrier)
    (F : IncludedCertifiedFinalized cfg E included anchor carrier c) :
    IncludedCertifiedFinalized cfg E included anchor tip c where
  justified := F.justified.transport_descendant cfg htip
  child := F.child
  child_epoch := F.child_epoch
  finalizing_link := F.finalizing_link.transport_descendant cfg htip

end IncludedCertifiedFinalized

/-! ## Same-tip accepted certificate packages -/

namespace AcceptedChainFFGState

/-- Any AU checkpoint has an included justification certificate reindexed to
the AU tip itself. -/
theorem includedJustifiedAtTip_of_AU
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor)
    {tip : Root} {c : Checkpoint Root}
    (hAU : S.AU cfg ext tip c) :
    Nonempty (IncludedCertifiedJustified cfg E
      S.includedAttestations.Included anchor tip c) := by
  obtain ⟨carrier, htip, hformed⟩ := hAU
  obtain ⟨hcertificate⟩ := (S.formed_evidence hformed).certified
  exact ⟨hcertificate.transport_descendant cfg htip⟩

end AcceptedChainFFGState

/-- Realized finalized and justified selectors, with both certificates owned
by one accepted tip.  The finalized anchor exception is retained explicitly. -/
structure AcceptedRealizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor) (tip : Root) : Prop where
  tip_accepted : E.AcceptedRoot cfg ext tip
  justified : Nonempty (IncludedCertifiedJustified cfg E
    S.includedAttestations.Included anchor tip (S.GJ tip))
  finalized : S.GF tip = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
    S.includedAttestations.Included anchor tip (S.GF tip))
  anchor_epoch_le_finalized : anchor.epoch ≤ (S.GF tip).epoch
  finalized_epoch_le_justified : (S.GF tip).epoch ≤ (S.GJ tip).epoch

/-- Pulled-up finalized and unrealized-justified selectors on one accepted
tip. -/
structure AcceptedUnrealizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor) (tip : Root) : Prop where
  tip_accepted : E.AcceptedRoot cfg ext tip
  justified : Nonempty (IncludedCertifiedJustified cfg E
    S.includedAttestations.Included anchor tip (S.GU tip))
  finalized : S.GUF tip = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
    S.includedAttestations.Included anchor tip (S.GUF tip))
  anchor_epoch_le_finalized : anchor.epoch ≤ (S.GUF tip).epoch
  finalized_epoch_le_justified : (S.GUF tip).epoch ≤ (S.GU tip).epoch

namespace AcceptedChainFFGState

/-- Construct the realized `GF`/`GJ` same-tip package directly from the
accepted state. -/
def realizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor)
    {tip : Root} (htip : E.AcceptedRoot cfg ext tip) :
    AcceptedRealizedFinalitySameTipAt cfg ext S tip := by
  have hjustified := S.includedJustifiedAtTip_of_AU cfg ext
    (S.gj_AU cfg ext htip)
  have hfinalized := S.gf_evidence tip htip
  have hanchorLe : anchor.epoch ≤ (S.GF tip).epoch := by
    rcases hfinalized with hanchor | hcertificate
    · rw [hanchor]
    · obtain ⟨hcertificate⟩ := hcertificate
      exact IncludedCertifiedJustified.anchor_epoch_le
        (cfg := cfg) hcertificate.justified
  exact {
    tip_accepted := htip
    justified := hjustified
    finalized := hfinalized
    anchor_epoch_le_finalized := hanchorLe
    finalized_epoch_le_justified := S.gf_epoch_le_gj tip htip
  }

/-- Construct the pulled-up `GUF`/`GU` same-tip package directly from the
accepted state. -/
def unrealizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor)
    {tip : Root} (htip : E.AcceptedRoot cfg ext tip) :
    AcceptedUnrealizedFinalitySameTipAt cfg ext S tip := by
  have hjustified := S.includedJustifiedAtTip_of_AU cfg ext
    (S.gu_AU cfg ext htip)
  have hfinalized := S.guf_evidence tip htip
  have hanchorLe : anchor.epoch ≤ (S.GUF tip).epoch := by
    rcases hfinalized with hanchor | hcertificate
    · rw [hanchor]
    · obtain ⟨hcertificate⟩ := hcertificate
      exact IncludedCertifiedJustified.anchor_epoch_le
        (cfg := cfg) hcertificate.justified
  exact {
    tip_accepted := htip
    justified := hjustified
    finalized := hfinalized
    anchor_epoch_le_finalized := hanchorLe
    finalized_epoch_le_justified := S.guf_epoch_le_gu tip htip
  }

end AcceptedChainFFGState

namespace AcceptedRealizedFinalitySameTipAt

/-- Exact accountable finalized prefix with source and target certificates on
the same accepted tip. -/
theorem exactPrefix
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor} {tip : Root}
    (h : AcceptedRealizedFinalitySameTipAt cfg ext S tip)
    (P : AcceptedEpochCheckpointProjection anchor
      (E.AcceptedRoot cfg ext) S.C)
    (V : S.ExactLinkValidity)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor) :
    ExactCheckpointPrefix S.C (S.GF tip) (S.GJ tip) := by
  obtain ⟨hjustified⟩ := h.justified
  rcases h.finalized with hanchor | hfinalized
  · rw [hanchor]
    exact IncludedCertifiedJustified.anchor_prefix
      (cfg := cfg) P V hanchorExact hjustified
  · obtain ⟨hfinalized⟩ := hfinalized
    exact S.exactFinalizedPrefix_of_accountable cfg P V hanchorExact hacc
      hfinalized hjustified h.finalized_epoch_le_justified

end AcceptedRealizedFinalitySameTipAt

namespace AcceptedUnrealizedFinalitySameTipAt

/-- Exact accountable pulled-up finalized prefix with both certificates on
the same accepted tip. -/
theorem exactPrefix
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor} {tip : Root}
    (h : AcceptedUnrealizedFinalitySameTipAt cfg ext S tip)
    (P : AcceptedEpochCheckpointProjection anchor
      (E.AcceptedRoot cfg ext) S.C)
    (V : S.ExactLinkValidity)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor) :
    ExactCheckpointPrefix S.C (S.GUF tip) (S.GU tip) := by
  obtain ⟨hjustified⟩ := h.justified
  rcases h.finalized with hanchor | hfinalized
  · rw [hanchor]
    exact IncludedCertifiedJustified.anchor_prefix
      (cfg := cfg) P V hanchorExact hjustified
  · obtain ⟨hfinalized⟩ := hfinalized
    exact S.exactFinalizedPrefix_of_accountable cfg P V hanchorExact hacc
      hfinalized hjustified h.finalized_epoch_le_justified

end AcceptedUnrealizedFinalitySameTipAt

/-! ## Exact executable equation at the same tip -/

/-- An exact semantic prefix whose target is AU at a concrete causal-store
tip becomes the exact executable checkpoint equation at that same tip.

The one walk starts at the source epoch boundary.  Monotonicity shortens it to
the target boundary to establish target-root knownness; checkpoint composition
then returns to the source boundary. -/
theorem exactCheckpointPrefix_root_eq_at_sameTip
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hcoh : AcceptedFFGTransitionCoherence cfg ext S)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    {tip : Root} (htip : tip ∈ store.block_roots)
    {source target : Checkpoint Root}
    (hprefix : ExactCheckpointPrefix S.C source target)
    (hAU : S.AU cfg ext tip target)
    (hepoch : source.epoch ≤ target.epoch)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg source.epoch) tip) :
    source.root = get_checkpoint_block cfg store tip source.epoch := by
  have htargetCheckpoint : target =
      get_checkpoint_for_block cfg store tip target.epoch :=
    hcoh.au_checkpoint_of_known hstore tip htip target hAU
  have hsourceBoundaryLeTarget : compute_start_slot_at_epoch cfg source.epoch ≤
      compute_start_slot_at_epoch cfg target.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hepoch
  have htargetWalk : WalkKnown store
      (compute_start_slot_at_epoch cfg target.epoch) tip :=
    hwalk.mono hsourceBoundaryLeTarget
  have htargetRoot : target.root =
      get_checkpoint_block cfg store tip target.epoch := by
    have hr := congrArg Checkpoint.root htargetCheckpoint
    simpa only [get_checkpoint_for_block] using hr
  have htargetKnown : target.root ∈ store.block_roots := by
    rw [htargetRoot]
    exact (get_ancestor_spec hparent htargetWalk).1
  have hsourceCheckpoint : source =
      get_checkpoint_for_block cfg store target.root source.epoch := by
    calc
      source = S.C target.root source.epoch := hprefix
      _ = get_checkpoint_for_block cfg store target.root source.epoch :=
        hcoh.checkpoint_of_known hstore target.root htargetKnown source.epoch
  have hcomp := get_checkpoint_for_block_comp cfg hparent hepoch hwalk
  have hsourceAtTip : source =
      get_checkpoint_for_block cfg store tip source.epoch := by
    calc
      source = get_checkpoint_for_block cfg store target.root source.epoch :=
        hsourceCheckpoint
      _ = get_checkpoint_for_block cfg store tip source.epoch := by
        rw [htargetCheckpoint]
        exact hcomp
  have hr := congrArg Checkpoint.root hsourceAtTip
  simpa only [get_checkpoint_for_block] using hr

namespace AcceptedRealizedFinalitySameTipAt

/-- F2's realized-state leaf equation: exact finalized compatibility at the
same accepted tip that carries the justified source. -/
theorem finalizedRoot_eq_checkpointBlock_at_tip
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor} {tip : Root}
    (h : AcceptedRealizedFinalitySameTipAt cfg ext S tip)
    (hcoh : AcceptedFFGTransitionCoherence cfg ext S)
    (P : AcceptedEpochCheckpointProjection anchor
      (E.AcceptedRoot cfg ext) S.C)
    (V : S.ExactLinkValidity)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (htip : tip ∈ store.block_roots)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg (S.GF tip).epoch) tip) :
    (S.GF tip).root =
      get_checkpoint_block cfg store tip (S.GF tip).epoch := by
  exact exactCheckpointPrefix_root_eq_at_sameTip cfg ext hcoh hstore hparent
    htip (h.exactPrefix cfg ext P V hanchorExact hacc)
    (S.gj_AU cfg ext h.tip_accepted) h.finalized_epoch_le_justified hwalk

end AcceptedRealizedFinalitySameTipAt

namespace AcceptedUnrealizedFinalitySameTipAt

/-- F2's pulled-up-state leaf equation on one accepted tip. -/
theorem finalizedRoot_eq_checkpointBlock_at_tip
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor} {tip : Root}
    (h : AcceptedUnrealizedFinalitySameTipAt cfg ext S tip)
    (hcoh : AcceptedFFGTransitionCoherence cfg ext S)
    (P : AcceptedEpochCheckpointProjection anchor
      (E.AcceptedRoot cfg ext) S.C)
    (V : S.ExactLinkValidity)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (htip : tip ∈ store.block_roots)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg (S.GUF tip).epoch) tip) :
    (S.GUF tip).root =
      get_checkpoint_block cfg store tip (S.GUF tip).epoch := by
  exact exactCheckpointPrefix_root_eq_at_sameTip cfg ext hcoh hstore hparent
    htip (h.exactPrefix cfg ext P V hanchorExact hacc)
    (S.gu_AU cfg ext h.tip_accepted) h.finalized_epoch_le_justified hwalk

end AcceptedUnrealizedFinalitySameTipAt


end FastConfirmation.Spec

end
