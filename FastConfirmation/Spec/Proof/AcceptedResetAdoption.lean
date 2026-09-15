import FastConfirmation.Spec.Proof.AcceptedFFGJustifiedMaximality
import FastConfirmation.Spec.Proof.AcceptedResetCheckpointClassification
import FastConfirmation.Spec.Proof.ObservedResetSafety

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
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Included finality is strictly older than its accepted carrier -/

/-- An attestation included on a carrier's chain was cast strictly before the
carrier block itself.

The including block is an ancestor of the carrier inside the observing store,
so the store's parent-slot order carries the inclusion-time bound
`slot_before_carrier` up to the carrier.  Only knownness of the carrier is
required, no certificate and no checkpoint. -/
theorem includedAttestationSlot_lt_acceptedCarrierBlock
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {q : ℕ} {carrier : Root}
    (hcarrier : carrier ∈
      (E.store cfg ext v q).block_roots)
    {a : Attestation Root}
    (hchain : AttestationIncludedOnChain E
      B.state.includedAttestations.Included carrier a) :
    a.data.slot < ((E.store cfg ext v q).blocks carrier).slot := by
  obtain ⟨containing, hcarrierContaining, hincluded⟩ := hchain
  have hevidence := B.state.includedAttestations.evidence hincluded
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
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
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed (E.store_causal cfg ext v q) hcontainingKnown).mp
        hevidence.carrier_accepted
  calc
    a.data.slot < hevidence.carrier_message.slot :=
      hevidence.slot_before_carrier
    _ = ((E.store cfg ext v q).blocks containing).slot :=
      (congrArg BeaconBlock.slot hcontainingBlock).symm
    _ ≤ ((E.store cfg ext v q).blocks carrier).slot := hslotLe

/-- An included non-anchor finalization is strictly older than the block
which carries its certificate.

This is the carrier-local form of the timing argument used by reset
classification.  It does not mention the current epoch of any store. -/
theorem includedCertifiedFinalized_epoch_lt_acceptedCarrierBlock
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
  obtain ⟨a, hchain, _hiAttests, _haSource, haTarget⟩ :=
    F.finalizing_link.signer_attestation i hi
  have hattestationBeforeCarrier : a.data.slot <
      ((E.store cfg ext v q).blocks carrier).slot :=
    E.includedAttestationSlot_lt_acceptedCarrierBlock cfg ext B hT
      hcarrier hchain
  obtain ⟨_containing, _hcarrierContaining, hincluded⟩ := hchain
  have hevidence := B.state.includedAttestations.evidence hincluded
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
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    B.anchor.epoch ≤ store.justified_checkpoint.epoch := by
  rcases B.globalJustified_anchor_or_AUEvidence hgen hanchor hstore with
    hfieldAnchor | hevidence
  · rw [hfieldAnchor]
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hcertificate⟩ := carrier.formed_evidence.certified
    exact CertifiedJustified.anchor_epoch_le (cfg := cfg)
      (IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedIncludedAttestationRelation.relation
          cfg ext E B.state.includedAttestations) hcertificate)

/-- Once the accepted carrier of a store-global finalized selector is known
at another causal store, that store's realized justified epoch is at least as
new as the finalized field.

This is the semantic "carrier processing" fact needed by finalized reset
takeover.  The premise is only carrier membership, not same-root state
adoption or a pre-assumed finalized/justified ordering. -/
theorem finalized_epoch_le_justified_of_acceptedCarrierKnown
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {v w : ValidatorIndex} {q m : ℕ}
    (hcarriers : ∀ r,
      r ∈ (E.store cfg ext v q).block_roots →
        r ∈ (E.store cfg ext w m).block_roots) :
    (E.store cfg ext v q).finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hsource : E.CausalStore cfg ext (E.store cfg ext v q) :=
    E.store_causal cfg ext v q
  have hendpoint : E.CausalStore cfg ext (E.store cfg ext w m) :=
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
      hcarriers tip htipSource.known
    have htipEndpoint : E.AcceptedCarrierIn
        (cfg := cfg) (ext := ext) (E.store cfg ext w m) tip :=
      Execution.AcceptedCarrierIn.of_causal_known hendpoint
        htipEndpointKnown
    rw [hfieldGF]
    exact (B.state.gf_epoch_le_gj tip htipSource.acceptedRoot).trans
      (hmax.ledger.gj_epoch_le_justified tip htipEndpoint)
  · have htipEndpointKnown : tip ∈
        (E.store cfg ext w m).block_roots :=
      hcarriers tip htipSource.known
    have htipEndpoint : E.AcceptedCarrierIn
        (cfg := cfg) (ext := ext) (E.store cfg ext w m) tip :=
      Execution.AcceptedCarrierIn.of_causal_known hendpoint
        htipEndpointKnown
    rcases B.state.guf_evidence tip htipSource.acceptedRoot with
      hgufAnchor | hcertificate
    · rw [hfieldGUF, hgufAnchor]
      exact E.anchor_epoch_le_acceptedGlobalJustified cfg ext B
        hgenShort hanchor hendpoint
    · obtain ⟨hcertificate⟩ := hcertificate
      have hgufLt : (B.state.GUF tip).epoch <
          compute_epoch_at_slot cfg
            ((E.store cfg ext v q).blocks tip).slot :=
        E.includedCertifiedFinalized_epoch_lt_acceptedCarrierBlock
          cfg ext B hT htipSource.known hcertificate
      have htipAt : E.AcceptedBlockAt cfg ext tip
          ((E.store cfg ext v q).blocks tip) :=
        E.acceptedBlockAt_of_causal_known cfg ext hsource htipSource.known
      have hgufLeGJ : (B.state.GUF tip).epoch ≤
          (B.state.GJ tip).epoch :=
        B.state.gj_max htipAt
          (B.state.guf_mem tip htipSource.acceptedRoot) hgufLt
      rw [hfieldGUF]
      exact hgufLeGJ.trans
        (hmax.ledger.gj_epoch_le_justified tip htipEndpoint)

/-- Synchrony discharges the carrier-membership premise after the ordinary
one-slot relay gate.  This is the endpoint adoption theorem needed by the
corrected finalized-reset facade. -/
theorem finalized_epoch_le_remoteJustified_of_synchrony
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hsync : PaperSafetySynchrony cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    (hw : w ∈ E.honest) {q m : ℕ}
    (hHq : E.WithinHorizon cfg q)
    (hHm : E.WithinHorizon cfg m)
    (hrelay : E.slot_at cfg q + 1 ≤ E.slot_at cfg (m + 1)) :
    (E.store cfg ext v q).finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  apply E.finalized_epoch_le_justified_of_acceptedCarrierKnown
    cfg ext B hT hanchor
  intro r hr
  exact hsync.block_relay v hv q r hHq hr w hw m hHm hrelay

/-- Cleaner next-slot form.  Unlike the preceding end-of-slot relay boundary,
this is directly shaped like `Spec_Safety_next_slot`. -/
theorem finalized_epoch_le_remoteJustified_nextSlot
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hsync : PaperSafetySynchrony cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    (hw : w ∈ E.honest) {q m : ℕ}
    (hHq : E.WithinHorizon cfg q)
    (hHm : E.WithinHorizon cfg m)
    (hnext : E.slot_at cfg q + 1 ≤ E.slot_at cfg m) :
    (E.store cfg ext v q).finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  exact E.finalized_epoch_le_remoteJustified_of_synchrony cfg ext B hT
    hanchor hsync hv hw hHq hHm
      (hnext.trans (E.slot_at_mono cfg (Nat.le_succ m)))

/-- The actual finalized reset used by an FCR call inherits the same
next-slot adoption theorem. -/
theorem finalizedReset_epoch_le_remoteJustified_nextSlot
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hsync : PaperSafetySynchrony cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    (hw : w ∈ E.honest) {n m : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hHm : E.WithinHorizon cfg m)
    (hnext : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg m) :
    (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  rw [E.fcrStep_store]
  exact E.finalized_epoch_le_remoteJustified_nextSlot cfg ext B hT
    hanchor hsync hv hw hHn1 hHm hnext

/-! ## The observed seam is a narrow source-lock law -/

/-- Minimal protocol-facing source-lock for an active observed restart.

The guard scopes the law to the branch which actually replaces the carried
root.  The epoch premise scopes it further to the endpoint-adopted branch;
when the endpoint justified epoch still lags, the filter/LMD branch is the
appropriate consumer.  The conclusion is only semantic checkpoint descent,
which ordinary execution reflection can turn into concrete store ancestry.

Knownness, `JustifiedIn`, and ordinary certificate accountability do not imply
this cross-carrier descent.  The accepted selector record therefore states the
required source-lock law explicitly. -/
def ObservedRestartJustifiedSourceLockAt
    (query : FastConfirmationStore Root) (endpoint : Store Root) : Prop :=
  ObservedRestartCompatible cfg query →
    query.current_epoch_observed_justified_checkpoint.epoch ≤
      endpoint.justified_checkpoint.epoch →
    E.RootDescends endpoint.justified_checkpoint.root
      query.current_epoch_observed_justified_checkpoint.root

end Execution

end FastConfirmation.Spec
