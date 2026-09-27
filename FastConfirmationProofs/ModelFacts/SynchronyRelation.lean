module
public import FastConfirmationInternal.Network.SynchronyConversion

@[expose] public section

/-! The full synchrony bundle and the next-slot bundle differ only by the envelope boundary
prefix. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- Full synchrony plus the envelope boundary prefix is exactly the accepted
next-slot synchrony bundle. -/
theorem synchrony_and_delivery_iff_nextSlot
    (E : Execution Root) :
    (Synchrony cfg ext E ∧ HorizonVoteDeliveryLookahead cfg E ∧
      DeadlineBoundaryEnvelopePrefix cfg ext E) ↔
    NextSlotSynchronyPremises cfg ext E := by
  constructor
  · rintro ⟨hs, hl, hp⟩
    exact Synchrony.toPaperSafetySynchrony cfg ext hs hl hp
  · intro hn
    exact ⟨{
      delta := hn.delta
      attestation_delivery := hn.attestation_delivery
      deadline_block_relay := hn.deadline_block_relay
      boundary_block_prefix := hn.boundary_block_prefix
      attester_slashing_relay := hn.attester_slashing_relay
    }, hn.delivery_lookahead, hn.boundary_envelope_prefix⟩

end FastConfirmation.Spec

end
