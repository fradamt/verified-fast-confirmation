module
public import FastConfirmationProofs.FFG.State.FinalizedSameTip
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {trusted : Store Root → Prop}

namespace TrustedCausalCarrierFFGState

/-- Any AU checkpoint has an included justification certificate reindexed to
the AU tip itself. -/
theorem includedJustifiedAtTip_of_AU
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {tip : Root} {c : Checkpoint Root}
    (hAU : S.AU cfg ext tip c) :
    Nonempty (IncludedCertifiedJustified cfg E
      S.includedAttestations.Included anchor tip c) := by
  obtain ⟨carrier, htip, hformed⟩ := hAU
  obtain ⟨hcertificate⟩ := (S.formed_evidence hformed).certified
  exact ⟨hcertificate.transport_descendant cfg htip⟩

end TrustedCausalCarrierFFGState

/-- Realized finalized and justified selectors, with both certificates owned
by one accepted tip.  The finalized anchor exception is retained explicitly. -/
structure TrustedAcceptedRealizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) (tip : Root) : Prop where
  tip_accepted : E.AcceptedRoot cfg ext tip
  justified : Nonempty (IncludedCertifiedJustified cfg E
    S.includedAttestations.Included anchor tip (S.GJ tip))
  finalized : S.GF tip = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
    S.includedAttestations.Included anchor tip (S.GF tip))
  anchor_epoch_le_finalized : anchor.epoch ≤ (S.GF tip).epoch
  finalized_epoch_le_justified : (S.GF tip).epoch ≤ (S.GJ tip).epoch

/-- Pulled-up finalized and unrealized-justified selectors on one accepted
tip. -/
structure TrustedAcceptedUnrealizedFinalitySameTipAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) (tip : Root) : Prop where
  tip_accepted : E.AcceptedRoot cfg ext tip
  justified : Nonempty (IncludedCertifiedJustified cfg E
    S.includedAttestations.Included anchor tip (S.GU tip))
  finalized : S.GUF tip = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
    S.includedAttestations.Included anchor tip (S.GUF tip))
  anchor_epoch_le_finalized : anchor.epoch ≤ (S.GUF tip).epoch
  finalized_epoch_le_justified : (S.GUF tip).epoch ≤ (S.GU tip).epoch

namespace TrustedCausalCarrierFFGState



end TrustedCausalCarrierFFGState

namespace TrustedAcceptedRealizedFinalitySameTipAt


end TrustedAcceptedRealizedFinalitySameTipAt

namespace TrustedAcceptedUnrealizedFinalitySameTipAt


end TrustedAcceptedUnrealizedFinalitySameTipAt

/-! ## Exact executable equation at the same tip -/

/-- An exact semantic prefix whose target is AU at a concrete causal-store
tip becomes the exact executable checkpoint equation at that same tip.

The one walk starts at the source epoch boundary.  Monotonicity shortens it to
the target boundary to establish target-root knownness; checkpoint composition
then returns to the source boundary. -/
theorem trusted_exactCheckpointPrefix_root_eq_at_sameTip
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext S)
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

namespace TrustedAcceptedRealizedFinalitySameTipAt


end TrustedAcceptedRealizedFinalitySameTipAt

namespace TrustedAcceptedUnrealizedFinalitySameTipAt


end TrustedAcceptedUnrealizedFinalitySameTipAt


end FastConfirmation.Spec
end
