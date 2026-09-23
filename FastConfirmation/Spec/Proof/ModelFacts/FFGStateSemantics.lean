module
public import FastConfirmation.Spec.Model.FFGStateSemantics
public import FastConfirmation.Spec.Proof.ModelFacts.FFGCertificates
public import FastConfirmation.Spec.Proof.ModelFacts.AcceptedExecution

@[expose] public section

/-!
# FFGStateSemantics model facts

Proofs about Model/FFGStateSemantics. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
namespace AcceptedIncludedAttestationRelation
theorem carrier_root_accepted
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : AcceptedIncludedAttestationRelation cfg ext E validity)
    {carrier : Root} {a : Attestation Root} (h : I.Included carrier a) :
    E.AcceptedRoot cfg ext carrier := by
  obtain ⟨store, hstore, hroot, _hmessage⟩ := (I.evidence h).carrier_accepted
  exact ⟨store, hstore, hroot⟩

end AcceptedIncludedAttestationRelation
end Execution
/-- Forgetting inclusion recovers the older causal ground-vote interface. -/
theorem HonestTargetIncludedBeforeCarrier.toHonestTargetBeforeCarrier
    {E : Execution Root}
    {included : Root → Attestation Root → Prop}
    {carrier : Root} {c : Checkpoint Root}
    (h : HonestTargetIncludedBeforeCarrier cfg E included carrier c) :
    E.HonestTargetBeforeCarrier cfg carrier c := by
  obtain ⟨b, hb, i, hi, s, k, a, hslot, hH, hvote, _haSlot,
    htarget, _hincluded⟩ := h
  exact ⟨b, hb, i, hi, s, k, a, hslot, hH, hvote, htarget⟩

namespace IncludedSupermajorityLink
end IncludedSupermajorityLink
namespace IncludedCertifiedJustified
end IncludedCertifiedJustified
namespace IncludedCertifiedFinalized
end IncludedCertifiedFinalized
namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
/-- Valid included attestations name only ground-registry validators, so the
finite registry filter in `D_b` loses no semantic offenders. -/
theorem hasSlashablePairOnChain_in_registry
    (S : ChainFFGState cfg E anchor) {tip : Root} {i : ValidatorIndex}
    (h : S.HasSlashablePairOnChain cfg tip i) :
    i < E.registry.length := by
  obtain ⟨a₁, _a₂, hinc₁, _hinc₂, hi₁, _hi₂, _hslash⟩ := h
  obtain ⟨carrier, _hdesc, hincluded⟩ := hinc₁
  exact (S.includedAttestations.evidence hincluded).attesters_in_registry i hi₁

@[simp] theorem mem_slashableOnChain
    (S : ChainFFGState cfg E anchor) (tip : Root) (i : ValidatorIndex) :
    i ∈ S.slashableOnChain cfg tip ↔
      S.HasSlashablePairOnChain cfg tip i := by
  classical
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
          (S.hasSlashablePairOnChain_in_registry (cfg := cfg) h), h⟩

/-- AU evidence is monotone down the descendant relation. -/
theorem AU.mono (S : ChainFFGState cfg E anchor)
    {old new : Root} {c : Checkpoint Root}
    (hdesc : E.RootDescends new old) (hAU : S.AU cfg old c) :
    S.AU cfg new c := by
  obtain ⟨carrier, holdCarrier, hformed⟩ := hAU
  exact ⟨carrier, Execution.RootDescends.trans E hdesc holdCarrier, hformed⟩

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

/-- The realized selector is available at its own block. -/
theorem gj_AU (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    S.AU cfg r (S.GJ r) :=
  S.gj_mem r hr

/-- The unrealized selector is available at its own block. -/
theorem gu_AU (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    S.AU cfg r (S.GU r) :=
  S.gu_mem r hr

/-- The realized finalized selector is available/unrealized justified on its
own block chain. -/
theorem gf_AU (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    S.AU cfg r (S.GF r) :=
  S.gf_mem r hr

/-- The eagerly pulled-up finalized selector is available/unrealized
justified on its own block chain. -/
theorem guf_AU (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    S.AU cfg r (S.GUF r) :=
  S.guf_mem r hr

/-- At a fixed block, greatest-unrealized justification is no older than
greatest-realized justification. -/
theorem gj_epoch_le_gu (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    (S.GJ r).epoch ≤ (S.GU r).epoch :=
  S.gu_max hr (S.gj_mem r hr)

end ChainFFGState
namespace AcceptedChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
theorem hasSlashablePairOnChain_in_registry
    (S : AcceptedChainFFGState cfg ext E anchor)
    {tip : Root} {i : ValidatorIndex}
    (h : S.HasSlashablePairOnChain cfg ext tip i) :
    i < E.registry.length := by
  obtain ⟨a₁, _a₂, hinc₁, _hinc₂, hi₁, _hi₂, _hslash⟩ := h
  obtain ⟨carrier, _hdesc, hincluded⟩ := hinc₁
  exact (S.includedAttestations.evidence hincluded).attesters_in_registry i hi₁

@[simp] theorem mem_slashableOnChain
    (S : AcceptedChainFFGState cfg ext E anchor)
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

theorem AU.mono (S : AcceptedChainFFGState cfg ext E anchor)
    {old new : Root} {c : Checkpoint Root}
    (hdesc : E.RootDescends new old) (hAU : S.AU cfg ext old c) :
    S.AU cfg ext new c := by
  obtain ⟨carrier, holdCarrier, hformed⟩ := hAU
  exact ⟨carrier, Execution.RootDescends.trans E hdesc holdCarrier, hformed⟩

theorem AU.evidence (S : AcceptedChainFFGState cfg ext E anchor)
    {tip : Root} {c : Checkpoint Root} (hAU : S.AU cfg ext tip c) :
    ∃ carrier, E.RootDescends tip carrier ∧
      AcceptedFormedCheckpointEvidence cfg ext E
        S.includedAttestations.Included anchor carrier c := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact ⟨carrier, hdesc, S.formed_evidence hformed⟩

theorem gj_AU (S : AcceptedChainFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GJ r) :=
  S.gj_mem r hr

theorem gu_AU (S : AcceptedChainFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GU r) :=
  S.gu_mem r hr

theorem gf_AU (S : AcceptedChainFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GF r) :=
  S.gf_mem r hr

theorem guf_AU (S : AcceptedChainFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    S.AU cfg ext r (S.GUF r) :=
  S.guf_mem r hr

theorem gj_epoch_le_gu (S : AcceptedChainFFGState cfg ext E anchor)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    (S.GJ r).epoch ≤ (S.GU r).epoch :=
  S.gu_max hr (S.gj_mem r hr)

end AcceptedChainFFGState
/-- Same-root accepted transitions expose identical post-state selectors.
There is no freshness premise, so this theorem explicitly includes duplicate
accepted deliveries at different compatible prefixes. -/
theorem accepted_post_selectors_unique
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    (t₁ t₂ : E.AcceptedBlockTransition cfg ext)
    (hroot : t₁.signedBlock.root = t₂.signedBlock.root) :
    (t₁.postStore.block_states t₁.signedBlock.root).current_justified_checkpoint =
        (t₂.postStore.block_states t₂.signedBlock.root).current_justified_checkpoint ∧
    (t₁.postStore.block_states t₁.signedBlock.root).finalized_checkpoint =
        (t₂.postStore.block_states t₂.signedBlock.root).finalized_checkpoint ∧
    (ext.process_justification_and_finalization
      (t₁.postStore.block_states t₁.signedBlock.root)
    ).current_justified_checkpoint =
        (ext.process_justification_and_finalization
          (t₂.postStore.block_states t₂.signedBlock.root)
        ).current_justified_checkpoint ∧
    (ext.process_justification_and_finalization
      (t₁.postStore.block_states t₁.signedBlock.root)
    ).finalized_checkpoint =
        (ext.process_justification_and_finalization
          (t₂.postStore.block_states t₂.signedBlock.root)
        ).finalized_checkpoint := by
  constructor
  · rw [hcoh.transition_gj t₁, hcoh.transition_gj t₂, hroot]
  constructor
  · rw [hcoh.transition_gf t₁, hcoh.transition_gf t₂, hroot]
  constructor
  · rw [hcoh.transition_gu t₁, hcoh.transition_gu t₂, hroot]
  · rw [hcoh.transition_guf t₁, hcoh.transition_guf t₂, hroot]

/-- The same already-selected state interprets accepted roots in two
compatible exact prefixes. -/
theorem one_state_interprets_compatible_prefixes
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSelectors cfg ext E)
    (p q : E.ScheduledEventPrefix) (hcompat : p.Compatible q)
    {r s : Root}
    (hr : r ∈ (p.store cfg ext).block_roots)
    (hs : s ∈ (q.store cfg ext).block_roots) :
    B.state.AU cfg ext r (B.state.GJ r) ∧
      B.state.AU cfg ext s (B.state.GJ s) := by
  have _ := hcompat
  constructor
  · exact B.state.gj_AU cfg ext
      (E.acceptedRoot_of_causal_known cfg ext (.scheduledPrefix p) hr)
  · exact B.state.gj_AU cfg ext
      (E.acceptedRoot_of_causal_known cfg ext (.scheduledPrefix q) hs)

namespace PaperA32StateView
variable {E : Execution Root}
end PaperA32StateView
namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
end ChainFFGState
namespace AcceptedChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
end AcceptedChainFFGState
end FastConfirmation.Spec

end
