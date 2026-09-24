module
public import FastConfirmationStatements.Premises.FFGCertificates
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationInternal.FFG.Certificates
public import FastConfirmationInternal.FFG.ScheduledState
public import FastConfirmationInternal.FFG.CheckpointLinks
public import FastConfirmationInternal.Network.SynchronyConversion
public import FastConfirmationProofs.ModelFacts.ScheduledPrefixes

@[expose] public section

/-!
# ModelFacts / FFGState

Proofs about Model/FFGCertificates. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
namespace Execution
variable (E : Execution Root)
theorem RootDescends.trans {a b c : Root}
    (hab : E.RootDescends a b) (hbc : E.RootDescends b c) :
    E.RootDescends a c := by
  induction hab with
  | refl => exact hbc
  | step hedge _ ih => exact .step hedge (ih hbc)

end Execution
end FastConfirmation.Spec

/-!
# FFGStateSemantics model facts

Proofs about Model/FFGStateSemantics. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
namespace CausalCarrierAttestationRelation

end CausalCarrierAttestationRelation
end Execution

namespace IncludedSupermajorityLink
end IncludedSupermajorityLink
namespace IncludedCertifiedJustified
end IncludedCertifiedJustified
namespace IncludedCertifiedFinalized
end IncludedCertifiedFinalized
namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}



/-- Every AU checkpoint has concrete certified, on-chain, causal formation
evidence at some carrier. -/
theorem AU.evidence (S : ChainFFGState cfg E anchor)
    {tip : Root} {c : Checkpoint Root} (hAU : S.AU cfg tip c) :
    ∃ carrier : Root,
      E.RootDescends tip carrier ∧
        FormedCheckpointEvidence cfg E
          S.includedAttestations.Included anchor carrier c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨carrier, hdesc, S.formed_evidence hformed⟩






end ChainFFGState
namespace CausalCarrierFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
theorem hasSlashablePairOnChain_in_registry
    (S : CausalCarrierFFGState cfg ext E anchor)
    {tip : Root} {i : ValidatorIndex}
    (h : S.HasSlashablePairOnChain cfg ext tip i) :
    i < E.registry.length := by
  obtain ⟨a₁, _a₂, hinc₁, _hinc₂, hi₁, _hi₂, _hslash⟩ := h
  obtain ⟨carrier, _hdesc, hincluded⟩ := hinc₁
  exact (S.includedAttestations.evidence hincluded).attesters_in_registry i hi₁

@[simp] theorem mem_slashableOnChain
    (S : CausalCarrierFFGState cfg ext E anchor)
    (tip : Root) (i : ValidatorIndex) :
    i ∈ S.slashableOnChain cfg ext tip ↔
      S.HasSlashablePairOnChain cfg ext tip i := by
  classical
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
          (S.hasSlashablePairOnChain_in_registry (cfg := cfg) (ext := ext) h), h⟩

theorem AU.mono (S : CausalCarrierFFGState cfg ext E anchor)
    {old new : Root} {c : Checkpoint Root}
    (hdesc : E.RootDescends new old) (hAU : S.AU cfg ext old c) :
    S.AU cfg ext new c := by
  obtain ⟨carrier, holdCarrier, hformed⟩ := hAU
  exact ⟨carrier, Execution.RootDescends.trans E hdesc holdCarrier, hformed⟩

theorem AU.evidence (S : CausalCarrierFFGState cfg ext E anchor)
    {tip : Root} {c : Checkpoint Root} (hAU : S.AU cfg ext tip c) :
    ∃ carrier, E.RootDescends tip carrier ∧
      IncludedVoteCheckpointCertificate cfg ext E
        S.includedAttestations.Included anchor carrier c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨carrier, hdesc, S.formed_evidence hformed⟩

theorem gj_AU (S : CausalCarrierFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GJ r) :=
  S.gj_mem r hr

theorem gu_AU (S : CausalCarrierFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GU r) :=
  S.gu_mem r hr

theorem gf_AU (S : CausalCarrierFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GF r) :=
  S.gf_mem r hr

theorem guf_AU (S : CausalCarrierFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GUF r) :=
  S.guf_mem r hr

theorem gj_epoch_le_gu (S : CausalCarrierFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    (S.GJ r).epoch ≤ (S.GU r).epoch :=
  S.gu_max hr (S.gj_mem r hr)

end CausalCarrierFFGState


namespace PaperA32StateView
variable {E : Execution Root}
end PaperA32StateView
namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
end ChainFFGState
namespace CausalCarrierFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
end CausalCarrierFFGState
end FastConfirmation.Spec

end
