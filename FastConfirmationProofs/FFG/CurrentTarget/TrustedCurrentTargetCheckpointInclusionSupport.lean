module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetCheckpointInclusionSupport
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E : Execution Root} {trusted : Store Root → Prop}
namespace Execution

abbrev TrustedAcceptedCurrentTargetA32GateRealization
    (anchor : Checkpoint Root)
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (store : Store Root) : Prop :=
  CurrentTargetA32GateRealizationCore cfg ext E anchor
    (S.paperA32Inputs cfg ext) store

abbrev TrustedAcceptedCurrentTargetA32GateRealizationProducerAt
    (anchor : Checkpoint Root)
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (q : ℕ) (query : FastConfirmationStore Root) : Prop :=
  CurrentTargetA32GateRealizationProducerAtCore cfg ext E anchor
    (S.paperA32Inputs cfg ext) q query

abbrev TrustedAcceptedFixedSourceCurrentTargetA32GateRealization
    (anchor : Checkpoint Root)
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (store : Store Root) (b : Root) : Prop :=
  FixedSourceCurrentTargetA32GateRealizationCore cfg ext E anchor
    (S.paperA32Inputs cfg ext) store b

abbrev TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
    (anchor : Checkpoint Root)
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (q : ℕ) (query : FastConfirmationStore Root) (b : Root) : Prop :=
  FixedSourceCurrentTargetA32GateRealizationProducerAtCore cfg ext E anchor
    (S.paperA32Inputs cfg ext) q query b

end Execution
end FastConfirmation.Spec
end
