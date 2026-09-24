module
public import FastConfirmationProofs.FFG.SelectedSource.EndpointJustifiedOrientation
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness
public import FastConfirmationProofs.FFG.State.TrustedFinalizedSameTip
public import FastConfirmationProofs.ModelFacts.TrustedFFGState

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem TrustedCausalPrefixFFGInterpretation.unrealizedJustified_certificate
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    Nonempty (CertifiedJustified cfg E B.anchor
      store.unrealized_justified_checkpoint) := by
  have horigins :=
    (B.causalStoreGlobalProjection hgen hanchor hstore).storeGlobal
  rcases horigins.unrealized_justified with
      hfieldAnchor | ⟨tip, htip, hfield⟩
  · rw [hfieldAnchor]
    exact ⟨CertifiedJustified.anchor⟩
  · have hAU : B.state.AU cfg ext tip
        store.unrealized_justified_checkpoint := by
      rw [hfield]
      exact B.state.gu_AU cfg ext htip.acceptedRoot
    obtain ⟨hincluded⟩ :=
      B.state.includedJustifiedAtTip_of_AU cfg ext hAU
    exact ⟨IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      B.state.includedAttestations.relation hincluded⟩

/-- Accepted global checkpoint geometry supplies the sole store-domain field
of the otherwise protocol-level no-conflict arithmetic bundle. -/
def trusted_noConflictPinningAssumptions_of_acceptedGlobalTrajectory
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    NoConflictPinningAssumptions cfg ext E where
  genesis := hT.genesis_structure
  wellFormed := hT.wellFormed
  whole_seconds := hT.whole_seconds
  honest_behavior := hT.honest_behavior
  externals_coherence := hT.externals_coherence
  static_validators := hstatic
  byzantine_bound := hbyz
  justified_root_known := by
    intro w hw m hmH
    exact E.trusted_justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hw m hmH

end Execution
end FastConfirmation.Spec
end
