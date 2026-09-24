module
public import FastConfirmationProofs.Checkpoints.ResetCheckpointClassification
public import FastConfirmationProofs.Checkpoints.TrustedProcessedResetCheckpointRealization
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_acceptedGlobalFinalized_anchor_or_includedCertificate
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.finalized_checkpoint = B.anchor ∨
      ∃ tip, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store tip ∧
        Nonempty (IncludedCertifiedFinalized cfg E
          B.state.includedAttestations.Included B.anchor tip
          store.finalized_checkpoint) := by
  have horigins :=
    (B.causalStoreGlobalProjection hgen hanchor hstore).storeGlobal
  rcases horigins.finalized with
    hanchorField | ⟨tip, htip, hgf | hguf⟩
  · exact Or.inl hanchorField
  · rcases B.state.gf_evidence tip htip.acceptedRoot with
      hlocalAnchor | hcertificate
    · exact Or.inl (hgf.trans hlocalAnchor)
    · right
      refine ⟨tip, htip, ?_⟩
      rwa [hgf]
  · rcases B.state.guf_evidence tip htip.acceptedRoot with
      hlocalAnchor | hcertificate
    · exact Or.inl (hguf.trans hlocalAnchor)
    · right
      refine ⟨tip, htip, ?_⟩
      rwa [hguf]

/-- A non-anchor included finalization carried in a reachable store is
strictly older than that store's current epoch.

The minimum-total-balance rule makes the finalizing signer set nonempty.  One
signer's target attestation has epoch `c.epoch + 1` and is included strictly
before a block on the known carrier's chain.  Hence the store has already
reached at least the next epoch. -/
theorem trusted_includedCertifiedFinalized_epoch_lt_current_of_acceptedCarrier
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {w : ValidatorIndex} {m : ℕ} {carrier : Root}
    (hcarrier : carrier ∈ (E.store cfg ext w m).block_roots)
    {c : Checkpoint Root}
    (F : IncludedCertifiedFinalized cfg E
      B.state.includedAttestations.Included B.anchor carrier c) :
    c.epoch < get_current_store_epoch cfg (E.store cfg ext w m) := by
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
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hcontainingRoot : E.ExecutionRoot containing :=
    ⟨hevidence.carrier_message, hevidence.carrier_at⟩
  have hcontainingKnown : containing ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hT.wellFormed hT.externals_coherence hgenEq hslot hparent
      hcarrier hcontainingRoot hcarrierContaining).1
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hcontainingBlock :
      (E.store cfg ext w m).blocks containing =
        hevidence.carrier_message :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed hstore hcontainingKnown).mp
        hevidence.carrier_accepted
  have hattestationBeforeCurrent : a.data.slot <
      get_current_slot cfg (E.store cfg ext w m) := by
    calc
      a.data.slot < hevidence.carrier_message.slot :=
        hevidence.slot_before_carrier
      _ = ((E.store cfg ext w m).blocks containing).slot :=
        (congrArg BeaconBlock.slot hcontainingBlock).symm
      _ ≤ get_current_slot cfg (E.store cfg ext w m) :=
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          w m containing hcontainingKnown
  have hchildEpoch : c.epoch + 1 =
      compute_epoch_at_slot cfg a.data.slot := by
    calc
      c.epoch + 1 = F.child.epoch := F.child_epoch.symm
      _ = a.data.target.epoch :=
        congrArg Checkpoint.epoch haTarget.symm
      _ = compute_epoch_at_slot cfg a.data.slot := hevidence.target_epoch
  have hnextLeCurrent : c.epoch + 1 ≤
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    rw [hchildEpoch]
    exact ce_mono cfg (Nat.le_of_lt hattestationBeforeCurrent)
  exact Nat.lt_of_succ_le hnextLeCurrent

/-- Therefore a store-global finalized checkpoint at the store's current
epoch is necessarily the trusted anchor. -/
theorem trusted_finalizedCheckpoint_eq_anchor_of_epoch_eq_current
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {w : ValidatorIndex} {m : ℕ}
    (hepoch : (E.store cfg ext w m).finalized_checkpoint.epoch =
      get_current_store_epoch cfg (E.store cfg ext w m)) :
    (E.store cfg ext w m).finalized_checkpoint = B.anchor := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hstore : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  rcases E.trusted_acceptedGlobalFinalized_anchor_or_includedCertificate
      cfg ext B hgenShort hanchor hstore with hanchorField |
      ⟨carrier, hcarrier, hcertificate⟩
  · exact hanchorField
  · obtain ⟨hcertificate⟩ := hcertificate
    have hlt := E.trusted_includedCertifiedFinalized_epoch_lt_current_of_acceptedCarrier
      cfg ext B hT hcarrier.known hcertificate
    exact False.elim (Nat.ne_of_lt hlt hepoch)

/-! ## Actual finalized-reset current-epoch classifier -/

/-- If the actual finalized reset root is in the query's current epoch, its
checkpoint field is the trusted anchor. -/
theorem trusted_actualFinalizedReset_eq_anchor_of_root_current
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint = B.anchor := by
  have hrealized :=
    E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hcurrent' : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.store cfg ext v (n + 1)).finalized_checkpoint.root =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.fcrStep_store] using hcurrent
  have hepoch := hrealized.checkpoint_epoch_eq_current_of_root_current
    (E := E) (cfg := cfg) hcurrent'
  have hfield := E.trusted_finalizedCheckpoint_eq_anchor_of_epoch_eq_current
    cfg ext B hT hanchor hepoch
  simpa only [E.fcrStep_store] using hfield

/-- Stronger checkpoint-shaped form consumed by historical reset
classification: the current-epoch checkpoint of the actual finalized input is
exactly the trusted anchor. -/
theorem trusted_actualFinalizedReset_currentCheckpoint_eq_anchor
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) :
    get_checkpoint_for_block cfg (E.fcrStoreAtCall cfg ext v n).store
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root
        (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store) =
      B.anchor := by
  have hrealized :=
    E.trusted_finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hcurrent' : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.store cfg ext v (n + 1)).finalized_checkpoint.root =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.fcrStep_store] using hcurrent
  have hcheckpoint := hrealized.current_checkpoint_eq
    (E := E) (cfg := cfg) hcurrent'
  have hfield := E.trusted_actualFinalizedReset_eq_anchor_of_root_current
    cfg ext B hT hanchor hboundary v n hcurrent
  have hfield' : (E.store cfg ext v (n + 1)).finalized_checkpoint =
      B.anchor := by
    simpa only [E.fcrStep_store] using hfield
  simpa only [E.fcrStep_store] using hcheckpoint.trans hfield'

/-! ## Active observed-restart classifier -/

/-- Accepted tag for an active observed restart at the exact evaluator phase. -/
structure TrustedAcceptedObservedRestartInputAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (query : FastConfirmationStore Root)
    (trace : LatestConfirmedCallTrace cfg ext query) : Prop where
  afterObserved_eq : trace.afterObserved =
    query.current_epoch_observed_justified_checkpoint.root
  realized : E.ResetCheckpointRealizedAt cfg B.anchor query.store
    query.current_epoch_observed_justified_checkpoint
  previous_epoch : get_block_epoch cfg query.store
      query.current_epoch_observed_justified_checkpoint.root + 1 =
    get_current_store_epoch cfg query.store

namespace TrustedAcceptedObservedRestartInputAt

theorem root_known
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {query : FastConfirmationStore Root}
    {trace : LatestConfirmedCallTrace cfg ext query}
    (h : E.TrustedAcceptedObservedRestartInputAt cfg ext B query trace) :
    query.current_epoch_observed_justified_checkpoint.root ∈
      query.store.block_roots :=
  h.realized.root_known

end TrustedAcceptedObservedRestartInputAt

/-- The active Boolean observed branch gives an exact, known previous-epoch
selector input.  Root coincidences with the carried or finalized candidates do
not erase this branch tag. -/
theorem trusted_actualObservedRestartInputAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n))
    (hactive : getLatestObservedRestartGuard cfg (E.fcrStoreAtCall cfg ext v n)
      trace.afterFinalized = true) :
    E.TrustedAcceptedObservedRestartInputAt cfg ext B
      (E.fcrStoreAtCall cfg ext v n) trace := by
  have hfacts := LatestConfirmedCallTrace.observedRestart_facts
    cfg ext trace hactive
  have hafterObserved : trace.afterObserved =
      (E.fcrStoreAtCall cfg ext v n
        ).current_epoch_observed_justified_checkpoint.root := by
    rcases trace.afterObserved_cases with ⟨hunchanged, hfalse⟩ |
        ⟨hrestarted, _htrue⟩
    · rw [hactive] at hfalse
      contradiction
    · exact hrestarted
  have hrealized :=
    E.trusted_fcrStep_observed_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary v n
  exact {
    afterObserved_eq := hafterObserved
    realized := by simpa only [E.fcrStep_store] using hrealized
    previous_epoch := hfacts.2.1
  }

end Execution
end FastConfirmation.Spec
end
