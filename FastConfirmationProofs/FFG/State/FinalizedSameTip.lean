module
public import FastConfirmationProofs.Checkpoints.ProcessedResetCheckpointRealization
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks
public import FastConfirmationProofs.ModelFacts

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


end IncludedCertifiedFinalized

/-! ## Same-tip accepted certificate packages -/

namespace CausalCarrierFFGState

/-- Any AU checkpoint has an included justification certificate reindexed to
the AU tip itself. -/
theorem includedJustifiedAtTip_of_AU
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : CausalCarrierFFGState cfg ext E anchor)
    {tip : Root} {c : Checkpoint Root}
    (hAU : S.AU cfg ext tip c) :
    Nonempty (IncludedCertifiedJustified cfg E
      S.includedAttestations.Included anchor tip c) := by
  obtain ⟨carrier, htip, hformed⟩ := hAU
  obtain ⟨hcertificate⟩ := (S.formed_evidence hformed).certified
  exact ⟨hcertificate.transport_descendant cfg htip⟩

end CausalCarrierFFGState

/-- Realized finalized and justified selectors, with both certificates owned
by one accepted tip.  The finalized anchor exception is retained explicitly. -/
structure AcceptedRealizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : CausalCarrierFFGState cfg ext E anchor) (tip : Root) : Prop where
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
    (S : CausalCarrierFFGState cfg ext E anchor) (tip : Root) : Prop where
  tip_accepted : E.AcceptedRoot cfg ext tip
  justified : Nonempty (IncludedCertifiedJustified cfg E
    S.includedAttestations.Included anchor tip (S.GU tip))
  finalized : S.GUF tip = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
    S.includedAttestations.Included anchor tip (S.GUF tip))
  anchor_epoch_le_finalized : anchor.epoch ≤ (S.GUF tip).epoch
  finalized_epoch_le_justified : (S.GUF tip).epoch ≤ (S.GU tip).epoch

namespace CausalCarrierFFGState



end CausalCarrierFFGState

namespace AcceptedRealizedFinalitySameTipAt


end AcceptedRealizedFinalitySameTipAt

namespace AcceptedUnrealizedFinalitySameTipAt


end AcceptedUnrealizedFinalitySameTipAt

/-! ## Exact executable equation at the same tip -/

/-- An exact semantic prefix whose target is AU at a concrete causal-store
tip becomes the exact executable checkpoint equation at that same tip.

The one walk starts at the source epoch boundary.  Monotonicity shortens it to
the target boundary to establish target-root knownness; checkpoint composition
then returns to the source boundary. -/
theorem exactCheckpointPrefix_root_eq_at_sameTip
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : CausalCarrierFFGState cfg ext E anchor}
    (hcoh : FFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext S)
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


end AcceptedRealizedFinalitySameTipAt

namespace AcceptedUnrealizedFinalitySameTipAt


end AcceptedUnrealizedFinalitySameTipAt


end FastConfirmation.Spec

end
