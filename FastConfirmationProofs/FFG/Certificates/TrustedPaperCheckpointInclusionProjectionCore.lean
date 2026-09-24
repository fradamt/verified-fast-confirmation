module
public import FastConfirmationProofs.FFG.Certificates.PaperCheckpointInclusionProjectionCore
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGStateTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {trusted : Store Root → Prop}
namespace TrustedCausalCarrierFFGState

def paperA32RootProjectionAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {r : Root} (hr : r ∈ store.block_roots) :
    PaperA32RootProjectionAt cfg ext (S.paperA32Inputs cfg ext) store r where
  causal_store := hstore
  root_known := hr
  gu_max := by
    intro c hAU
    change c.epoch ≤ (S.GU r).epoch
    apply S.gu_max (E.acceptedRoot_of_causal_known cfg ext hstore hr)
    change S.AU cfg ext r c at hAU
    exact hAU
  unrealized_justification := by
    change store.unrealized_justifications r = S.GU r
    exact (hstore.trustedAcceptedFFGStoreProjection hcoh).unrealized_justification
      r hr

end TrustedCausalCarrierFFGState
namespace Execution
variable {E : Execution Root}

theorem trusted_accepted_paperA32IncludedAtTip_of_paper
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (hpaper : S.PaperA32Inclusion cfg ext)
    {b : Root} {bb : BeaconBlock Root} {e : Epoch}
    (hb : E.AcceptedBlockAt cfg ext b bb)
    (hbe : compute_epoch_at_slot cfg bb.slot ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : S.PaperA32SupportThroughoutEpoch cfg ext b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg (S.paperA32Inputs cfg ext)
        (E.store cfg ext w m) e b seed := by
  apply E.paperA32IncludedAtTip_of_paperCore cfg ext hpaper hb hbe
    hcanonical hsupport hw hHm hboundary
  intro r hr
  exact S.paperA32RootProjectionAt cfg ext hcoh
    (E.store_causal cfg ext w m) hr


/-- Strong reachable-store specialization deriving the accepted base-block
witness from finite-domain knownness. -/
theorem trusted_accepted_paperA32IncludedAtTip_of_paper_at_known
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (hpaper : S.PaperA32Inclusion cfg ext)
    {u : ValidatorIndex} {q : ℕ} {b : Root}
    (hbKnown : b ∈ (E.store cfg ext u q).block_roots)
    {e : Epoch}
    (hbe : get_block_epoch cfg (E.store cfg ext u q) b ≤ e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext b (e + 1))
    (hsupport : S.PaperA32SupportThroughoutEpoch cfg ext b e)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m) :
    ∃ seed : Root,
      PaperA32IncludedAtTip cfg (S.paperA32Inputs cfg ext)
        (E.store cfg ext w m) e b seed := by
  let bb := (E.store cfg ext u q).blocks b
  have hb : E.AcceptedBlockAt cfg ext b bb :=
    E.acceptedBlockAt_of_store_known cfg ext u q hbKnown
  apply E.trusted_accepted_paperA32IncludedAtTip_of_paper cfg ext hcoh hpaper hb
  · simpa only [bb, get_block_epoch] using hbe
  · exact hcanonical
  · exact hsupport
  · exact hw
  · exact hHm
  · exact hboundary


end Execution
end FastConfirmation.Spec
end
