module
public import FastConfirmationProofs.ModelFacts.FFGState
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace TrustedCausalCarrierFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}

theorem AU.mono {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {old new : Root} {c : Checkpoint Root}
    (hdesc : E.RootDescends new old) (hAU : S.AU cfg ext old c) :
    S.AU cfg ext new c := by
  obtain ⟨carrier, holdCarrier, hformed⟩ := hAU
  exact ⟨carrier, Execution.RootDescends.trans E hdesc holdCarrier, hformed⟩

theorem AU.evidence {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {tip : Root} {c : Checkpoint Root} (hAU : S.AU cfg ext tip c) :
    ∃ carrier, E.RootDescends tip carrier ∧
      IncludedVoteCheckpointCertificate cfg ext E
        S.includedAttestations.Included anchor carrier c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨carrier, hdesc, S.formed_evidence hformed⟩

theorem gj_AU {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GJ r) := S.gj_mem r hr

theorem gu_AU {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GU r) := S.gu_mem r hr

theorem gf_AU {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GF r) := S.gf_mem r hr

theorem guf_AU {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GUF r) := S.guf_mem r hr

theorem gj_epoch_le_gu {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    (S.GJ r).epoch ≤ (S.GU r).epoch :=
  S.gu_max hr (S.gj_mem r hr)

end TrustedCausalCarrierFFGState
end FastConfirmation.Spec
end
