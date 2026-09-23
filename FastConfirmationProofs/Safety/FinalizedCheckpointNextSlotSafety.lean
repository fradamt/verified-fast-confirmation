module
public import FastConfirmationProofs.FCRRule.FCRCallInvariants
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.FFG.SourceHistory.CandidateHistoryRecurrence
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Accepted finalized-reset safety from the next slot

Ordinary synchrony does not force another honest endpoint to adopt a newly
received finalized checkpoint in the same call second. It does provide that
adoption once the endpoint is in a strictly later slot, which is the deadline
used by the accepted public theorem.

This module combines accepted finalization certificates, execution reflection,
and `finalizedReset_epoch_le_remoteJustified_nextSlot` to prove genuine
`SafeFrom` at every time whose slot is strictly after the reset query's slot.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- At every endpoint at or after a chosen next-slot time, the query's
finalized checkpoint is known and lies on the endpoint's realized justified
chain.

Synchrony supplies the endpoint justified-epoch bound; accepted certificate
semantics and execution reflection supply the chain relation and knownness. -/
theorem finalizedReset_justifiedDom_of_nextSlotSynchrony
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n q : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hnextQ : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg q) :
    ∀ w ∈ E.honest, ∀ m : ℕ, q ≤ m →
      E.WithinHorizon cfg m →
      let finalized :=
        (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint
      finalized.root ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root
            (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root finalized.root) = true := by
  intro w hw m hqm hHm
  let finalized :=
    (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  have hqueryCausal : E.CausalStore cfg ext
      (E.store cfg ext v (n + 1)) :=
    E.store_causal cfg ext v (n + 1)
  have hendpointCausal : E.CausalStore cfg ext
      (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hfinalizedKnownQuery : finalized.root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [finalized, E.fcrStep_store] using hrealized.root_known
  have hfinalizedRoot : E.ExecutionRoot finalized.root :=
    ⟨(E.store cfg ext v (n + 1)).blocks finalized.root,
      E.blockAt_of_store_known cfg ext hfinalizedKnownQuery⟩
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  obtain ⟨_hparent, _hwalk, hjustifiedKnown⟩ :=
    hdomainK w hw m hHm
  have hepoch : finalized.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
    have hnextM : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg m :=
      hnextQ.trans (E.slot_at_mono cfg hqm)
    simpa only [finalized] using
      E.finalizedReset_epoch_le_remoteJustified_nextSlot
        cfg ext B hT hanchor hsync hv hw hHn1 hHm hnextM
  obtain ⟨hjustified⟩ :=
    ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate
      (E := E) cfg ext B hgenShort hanchor hendpointCausal
  have hsemantic : E.RootDescends
      (E.store cfg ext w m).justified_checkpoint.root finalized.root := by
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
        cfg ext B hgenShort hanchor hqueryCausal with
      hfieldAnchor | ⟨carrier, _hcarrier, hincluded⟩
    · have hfinalizedAnchor : finalized = B.anchor := by
        simpa only [finalized, E.fcrStep_store] using hfieldAnchor
      rw [hfinalizedAnchor]
      exact hjustified.descends_anchor cfg
    · obtain ⟨hincluded⟩ := hincluded
      have hincludedFinalized : IncludedCertifiedFinalized cfg E
          B.state.includedAttestations.Included B.anchor carrier
          finalized := by
        simpa only [finalized, E.fcrStep_store] using hincluded
      have hfinalized : CertifiedFinalized cfg E B.anchor finalized :=
        IncludedCertifiedFinalized.toCertifiedFinalized
          (cfg := cfg)
          (Execution.AcceptedIncludedAttestationRelation.relation
            cfg ext E B.state.includedAttestations)
          hincludedFinalized
      exact E.certified_finalized_prefix cfg ext hacc
        hfinalized hjustified hepoch
  exact E.store_known_ancestor_of_rootDescends_for_storeReflection
    cfg ext hT.wellFormed hT.externals_coherence hgen hslot hparent
      hjustifiedKnown hfinalizedRoot hsemantic

/-- A query's finalized checkpoint is genuinely `SafeFrom` any time whose
slot is strictly later than the query slot.  No same-moment finalized-adoption
law is used. -/
theorem finalizedReset_safeFrom_of_nextSlotSynchrony
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n q : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hnextQ : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg q) :
    E.SafeFrom cfg ext
      (E.fcrStoreAtCall cfg ext v n).store.finalized_checkpoint.root q := by
  have hdomainK := E.storeDomainK_of_acceptedGlobalTrajectory
    cfg ext B hT hanchor hboundary
  apply E.safeFrom_of_justified_dom_K cfg ext hdomainK
  intro w hw m hqm hHm
  exact E.finalizedReset_justifiedDom_of_nextSlotSynchrony
    cfg ext B hT hacc hanchor hboundary hsync hv hHn1 hnextQ
      w hw m hqm hHm

/-- Exact active-branch presentation: when `get_latest_confirmed` selected
the finalized reset input, that input is safe from any chosen next-slot time.
-/
theorem finalizedResetCandidateInput_safeFrom_of_nextSlotSynchrony
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n q : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n)}
    (hinput : FinalizedResetCandidateInputAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace)
    (hnextQ : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg q) :
    E.SafeFrom cfg ext trace.afterObserved q := by
  rw [hinput.input_eq]
  exact E.finalizedReset_safeFrom_of_nextSlotSynchrony
    cfg ext B hT hacc hanchor hboundary hsync hv hHn1 hnextQ

end Execution

end FastConfirmation.Spec

end
