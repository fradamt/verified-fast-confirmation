module
public import FastConfirmationProofs.Checkpoints.PaperCheckpointInclusionSupportRealization
public import FastConfirmationProofs.FFG.Certificates.TrustedPaperCheckpointInclusionProjectionCore

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_accepted_paperA32IncludedAtTip_of_concreteQuorum
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hpaths : HonestHeadPathAdmissibility cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (hpaper : S.PaperA32Inclusion cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {b : Root} {e : Epoch}
    (hbQuery : b ∈ (E.store cfg ext v q).block_roots)
    (hbEpochQuery : get_block_epoch cfg (E.store cfg ext v q) b = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg (e + 1)) (S.C b e))
    (hsourceQuery : Q.source =
      S.VSAt cfg ext (E.store cfg ext v q) b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg (S.paperA32Inputs cfg ext)
        (E.store cfg ext w m) e b seed := by
  have hsupport :=
    E.paperA32SupportThroughoutEpochCore_of_concreteQuorum cfg ext
      (V := S.paperA32Inputs cfg ext)
      hwf hhb hsync hpaths hec hdiv hgen hwalkDomain hv hqH hbQuery
      hbEpochQuery hcanonical Q hsourceQuery
  exact E.trusted_accepted_paperA32IncludedAtTip_of_paper_at_known cfg ext
    hcoh hpaper hbQuery hbEpochQuery.le hcanonical hsupport
    hw hHm hboundary

end Execution
end FastConfirmation.Spec
end
