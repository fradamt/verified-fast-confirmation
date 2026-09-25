module
public import FastConfirmationProofs.Handlers.ResetAdoption
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_includedAttestationSlot_lt_acceptedCarrierBlock
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {v : ValidatorIndex} {q : ℕ} {carrier : Root}
    (hcarrier : carrier ∈
      (E.store cfg ext v q).block_roots)
    {a : Attestation Root}
    (hchain : AttestationIncludedOnChain E
      B.state.includedAttestations.Included carrier a) :
    a.data.slot < ((E.store cfg ext v q).blocks carrier).slot := by
  obtain ⟨containing, hcarrierContaining, hincluded⟩ := hchain
  have hevidence := B.state.includedAttestations.evidence hincluded
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hcontainingRoot : E.ExecutionRoot containing :=
    ⟨hevidence.carrier_message, hevidence.carrier_at⟩
  have hreflection :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hT.wellFormed hT.externals_coherence
      hgenEq hslot hparent hcarrier hcontainingRoot
      hcarrierContaining
  have hcontainingKnown := hreflection.1
  have hancestor := hreflection.2
  have hparentSlots : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled v q
  have hwalkK : ∀ target ∈ (E.store cfg ext v q).block_roots,
      ∀ r ∈ (E.store cfg ext v q).block_roots,
        WalkKnown (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks target).slot r :=
    E.store_walkKnownK cfg ext hT.wellFormed
      hT.externals_coherence ⟨ast, ablk, hgenEq, hslot, hparent⟩ v q
  have hslotLe : ((E.store cfg ext v q).blocks containing).slot ≤
      ((E.store cfg ext v q).blocks carrier).slot :=
    ancestor_slot_le hparentSlots
      (hwalkK containing hcontainingKnown carrier hcarrier) hancestor
  have hcontainingBlock : (E.store cfg ext v q).blocks containing =
      hevidence.carrier_message :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed (E.store_causal cfg ext v q) hcontainingKnown).mp
        hevidence.carrier_accepted
  calc
    a.data.slot < hevidence.carrier_message.slot :=
      hevidence.slot_before_carrier
    _ = ((E.store cfg ext v q).blocks containing).slot :=
      (congrArg BeaconBlock.slot hcontainingBlock).symm
    _ ≤ ((E.store cfg ext v q).blocks carrier).slot := hslotLe

end Execution
end FastConfirmation.Spec
end
