module
public import FastConfirmationProofs.FFG.SourceHistory.FFGJustifiedMaximality
public import FastConfirmationProofs.Checkpoints.ResetCheckpointClassification
public import FastConfirmationProofs.Safety.ObservedResetSafety

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted reset adoption

This file separates the two reset inputs used by `get_latest_confirmed`.

* A store-global finalized checkpoint has an accepted historical selector
  carrier.  Once synchrony relays that carrier to another honest store, the
  accepted justified-maximality ledger proves that the endpoint has adopted
  a justified epoch at least as new as the finalized field.  The `GUF` case
  uses the included finalizing certificate to show that `GUF` is strictly
  older than its carrier block, so it is covered by the carrier's `GJ`
  maximum.
* The analogous observed source-lock is not a consequence of root knownness
  and `JustifiedIn`.  The final section therefore records a narrow,
  restart-scoped law rather than hiding that obligation in a safety or head
  premise.

No theorem in this file assumes a confirmation, filter, head, ancestry, or
`SafeFrom` conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## Included finality is strictly older than its accepted carrier -/

/-- An included non-anchor finalization is strictly older than the block
which carries its certificate.

This is the carrier-local form of the timing argument used by reset
classification.  It does not mention the current epoch of any store. -/
theorem includedCertifiedFinalized_epoch_lt_acceptedCarrierBlock
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    {v : ValidatorIndex} {q : ℕ} {carrier : Root}
    (hcarrier : carrier ∈
      (E.store cfg ext v q).block_roots)
    {c : Checkpoint Root}
    (F : IncludedCertifiedFinalized cfg E
      B.state.includedAttestations.Included B.anchor carrier c) :
    c.epoch < compute_epoch_at_slot cfg
      ((E.store cfg ext v q).blocks carrier).slot := by
  have hsigners : F.finalizing_link.signers.Nonempty := by
    by_contra hnone
    have hempty : F.finalizing_link.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * E.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using F.finalizing_link.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega) (E.total_active_pos cfg))
  obtain ⟨i, hi⟩ := hsigners
  obtain ⟨a, ⟨containing, hcarrierContaining, hincluded⟩,
      _hiAttests, _haSource, haTarget⟩ :=
    F.finalizing_link.signer_attestation i hi
  have hevidence := B.state.includedAttestations.evidence hincluded
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hcontainingRoot : E.ExecutionRoot containing :=
    ⟨hevidence.carrier_message, hevidence.carrier_at⟩
  have hreflection :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hT.wellFormed hT.externals_coherence
      hgenEq hslot hparent hcarrier hcontainingRoot
      hcarrierContaining
  have hcontainingKnown := hreflection.1
  have hancestor := hreflection.2
  have hparentSlots : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled v q
  have hwalkK : ∀ target ∈ (E.store cfg ext v q).block_roots,
      ∀ r ∈ (E.store cfg ext v q).block_roots,
        WalkKnown (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks target).slot r :=
    E.store_walkKnownK cfg ext hT.wellFormed
      hT.externals_coherence ⟨ast, ablk, hgenEq, hslot, hparent⟩ v q
  have hslotLe : ((E.store cfg ext v q).blocks containing).slot ≤
      ((E.store cfg ext v q).blocks carrier).slot :=
    ancestor_slot_le hparentSlots
      (hwalkK containing hcontainingKnown carrier hcarrier) hancestor
  have hcontainingBlock : (E.store cfg ext v q).blocks containing =
      hevidence.carrier_message :=
    (Execution.ScheduledPrefixStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed (E.store_causal cfg ext v q) hcontainingKnown).mp
        hevidence.carrier_accepted
  have hattestationBeforeCarrier : a.data.slot <
      ((E.store cfg ext v q).blocks carrier).slot := by
    calc
      a.data.slot < hevidence.carrier_message.slot :=
        hevidence.slot_before_carrier
      _ = ((E.store cfg ext v q).blocks containing).slot :=
        (congrArg BeaconBlock.slot hcontainingBlock).symm
      _ ≤ ((E.store cfg ext v q).blocks carrier).slot := hslotLe
  have hchildEpoch : c.epoch + 1 =
      compute_epoch_at_slot cfg a.data.slot := by
    calc
      c.epoch + 1 = F.child.epoch := F.child_epoch.symm
      _ = a.data.target.epoch :=
        congrArg Checkpoint.epoch haTarget.symm
      _ = compute_epoch_at_slot cfg a.data.slot := hevidence.target_epoch
  apply Nat.lt_of_succ_le
  simpa only [Nat.succ_eq_add_one, hchildEpoch] using
    ce_mono cfg (Nat.le_of_lt hattestationBeforeCarrier)

/-! ## Relayed finalized carrier implies endpoint epoch adoption -/

/-- Every accepted store-global justified field is no older than the trusted
anchor. -/
theorem anchor_epoch_le_acceptedGlobalJustified
    (B : ScheduledFFGInterpretation cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store) :
    B.anchor.epoch ≤ store.justified_checkpoint.epoch := by
  rcases B.globalJustified_anchor_or_AUEvidence hgen hanchor hstore with
    hfieldAnchor | hevidence
  · rw [hfieldAnchor]
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hcertificate⟩ := carrier.formed_evidence.certified
    exact CertifiedJustified.anchor_epoch_le (cfg := cfg)
      (IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedBlockAttestationInclusion.relation
          cfg ext E B.state.includedAttestations) hcertificate)

/-- Once the accepted carrier of a store-global finalized selector is known
at another causal store, that store's realized justified epoch is at least as
new as the finalized field.

This is the semantic "carrier processing" fact needed by finalized reset
takeover.  The premise is only carrier membership, not same-root state
adoption or a pre-assumed finalized/justified ordering. -/
theorem finalized_epoch_le_justified_of_acceptedCarrierKnown
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {v w : ValidatorIndex} {q m : ℕ}
    (hcarriers : ∀ r,
      r ∈ (E.store cfg ext v q).block_roots →
      ((E.store cfg ext v q).finalized_checkpoint = B.state.realized_finalized r ∨
        (E.store cfg ext v q).finalized_checkpoint = B.state.unrealized_finalized r) →
        r ∈ (E.store cfg ext w m).block_roots) :
    (E.store cfg ext v q).finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hsource : E.ScheduledPrefixStore cfg ext (E.store cfg ext v q) :=
    E.store_causal cfg ext v q
  have hendpoint : E.ScheduledPrefixStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hmax := hendpoint.acceptedFFGJustifiedMaximality
    B hT.whole_seconds hgenShort hanchor
  rcases (B.causalStoreGlobalProjection hgenShort hanchor hsource
      ).storeGlobal.finalized with hfieldAnchor |
      ⟨tip, htipSource, hfieldGF | hfieldGUF⟩
  · rw [hfieldAnchor]
    exact E.anchor_epoch_le_acceptedGlobalJustified cfg ext B
      hgenShort hanchor hendpoint
  · have htipEndpointKnown : tip ∈
        (E.store cfg ext w m).block_roots :=
      hcarriers tip htipSource.known (Or.inl hfieldGF)
    have htipEndpoint : E.AcceptedCarrierIn
        (cfg := cfg) (ext := ext) (E.store cfg ext w m) tip :=
      Execution.AcceptedCarrierIn.of_causal_known hendpoint
        htipEndpointKnown
    rw [hfieldGF]
    exact (B.state.realized_finalized_epoch_le_realized_justified tip htipSource.acceptedRoot).trans
      (hmax.ledger.gj_epoch_le_justified tip htipEndpoint)
  · have htipEndpointKnown : tip ∈
        (E.store cfg ext w m).block_roots :=
      hcarriers tip htipSource.known (Or.inr hfieldGUF)
    have htipEndpoint : E.AcceptedCarrierIn
        (cfg := cfg) (ext := ext) (E.store cfg ext w m) tip :=
      Execution.AcceptedCarrierIn.of_causal_known hendpoint
        htipEndpointKnown
    rw [hfieldGUF]
    exact (B.state.unrealized_finalized_epoch_le_realized_justified tip
        htipSource.acceptedRoot).trans
      (hmax.ledger.gj_epoch_le_justified tip htipEndpoint)

/-! ## The observed seam is a narrow source-lock law -/


end Execution

end FastConfirmation.Spec

end
