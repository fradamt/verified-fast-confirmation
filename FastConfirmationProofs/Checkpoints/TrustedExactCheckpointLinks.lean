module
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {E : Execution Root} {anchor : Checkpoint Root}
namespace TrustedCausalCarrierFFGState
variable {trusted : Store Root → Prop}

theorem exactFinalizedPrefix_of_accountable
    {ext : Externals Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (P : EpochCheckpointClosure anchor
      (E.AcceptedRoot cfg ext) S.C)
    (V : S.ExactLinkValidity)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor)
    {finalizedCarrier justifiedCarrier : Root}
    {finalized justified : Checkpoint Root}
    (hfinalized : IncludedCertifiedFinalized cfg E
      S.includedAttestations.Included anchor finalizedCarrier finalized)
    (hjustified : IncludedCertifiedJustified cfg E
      S.includedAttestations.Included anchor justifiedCarrier justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    ExactCheckpointPrefix S.C finalized justified := by
  let I := S.includedAttestations.relation
  exact IncludedCertifiedFinalized.exact_prefix_of_accountable
    (cfg := cfg) I P V hanchorExact hacc hfinalized hjustified hepoch

end TrustedCausalCarrierFFGState
end FastConfirmation.Spec
end
