module
public import FastConfirmationProofs.FFG.Certificates.CurrentTargetCertificateRealization
public import FastConfirmationProofs.FFG.SourceHistory.TrustedFFGSourceCoherence

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

def TrustedAcceptedConcreteA32QuorumSourceGeometry
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (common : Root) : Prop :=
  ∀ i ∈ Q.signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      TrustedAcceptedHonestSourceEvidence B.state
          (E.store cfg ext i vote.time) vote.slot vote.index ∧
        TrustedAcceptedProjectedSameEpochSegment cfg ext E B.state common
          (get_head cfg (E.store cfg ext i vote.time)).root

end Execution
end FastConfirmation.Spec
end
