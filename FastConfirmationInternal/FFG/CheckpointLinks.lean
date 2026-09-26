module
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationInternal.FFG.ScheduledState

@[expose] public section

/-! Exact checkpoint-link predicates used by FFG proofs. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
/-- The exact epoch-indexed checkpoint-prefix relation represented by `C`. -/
def ExactCheckpointPrefix
    (C : Root → Epoch → Checkpoint Root)
    (source target : Checkpoint Root) : Prop :=
  source = C target.root source.epoch

variable {anchor : Checkpoint Root}
namespace IncludedSupermajorityLink
end IncludedSupermajorityLink

variable {E : Execution Root}
namespace AcceptedBlockFFGState
end AcceptedBlockFFGState
namespace ChainFFGState

end ChainFFGState
end FastConfirmation.Spec

end
