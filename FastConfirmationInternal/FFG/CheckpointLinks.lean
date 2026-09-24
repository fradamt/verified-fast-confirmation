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
/-- Both endpoints of a contributing link are formed on its accepted
certificate carrier. -/
structure IncludedLinkEndpointsFormed
    (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root)
    (formed : Root → Checkpoint Root → Prop)
    (Accepted : Root → Prop) : Prop where
  carrier_accepted : ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
    Accepted carrier
  endpoints_formed : ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
    formed carrier source ∧ formed carrier target

variable {E : Execution Root}
namespace CausalCarrierFFGState
end CausalCarrierFFGState
namespace ChainFFGState
/-- Exact-link validity specialized to the scheduled-root state. -/
abbrev ExactLinkValidity
    (S : ChainFFGState cfg E anchor) (Accepted : Root → Prop) : Prop :=
  ExactIncludedLinkValidity cfg E S.includedAttestations.Included anchor
    S.C Accepted

end ChainFFGState
end FastConfirmation.Spec

end
