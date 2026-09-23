module
public import FastConfirmationInternal.Network.SynchronyConversion

@[expose] public section

/-! The full synchrony bundle is the next-slot bundle plus latest-message relay. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The latest-message relay law, with the exact type of
`Synchrony.latest_message_relay`. -/
def LatestMessageRelay (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n i (msg : LatestMessage Root),
    E.WithinHorizon cfg n →
    (E.store cfg ext v n).latest_messages i = some msg →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
      ∃ msg', (E.store cfg ext w m).latest_messages i = some msg' ∧
        get_latest_message_epoch cfg msg ≤ get_latest_message_epoch cfg msg'

/-- Full synchrony plus payload delivery is exactly the accepted next-slot
synchrony bundle plus latest-message relay. -/
theorem synchrony_and_delivery_iff_nextSlot_and_latestMessageRelay
    (E : Execution Root) :
    (Synchrony cfg ext E ∧ EnvelopeDelivery cfg ext E ∧
      DataAvailabilityRelay cfg ext E) ↔
    (NextSlotSynchronyPremises cfg ext E ∧ LatestMessageRelay cfg ext E) := by
  constructor
  · rintro ⟨hs, he, hd⟩
    exact ⟨Synchrony.toPaperSafetySynchrony cfg ext hs he hd,
      hs.latest_message_relay⟩
  · rintro ⟨hn, hl⟩
    exact ⟨{
      attestation_delivery := hn.attestation_delivery
      block_relay := hn.block_relay
      latest_message_relay := hl
      attester_slashing_relay := hn.attester_slashing_relay
    }, hn.envelope_delivery, hn.data_availability_relay⟩

end FastConfirmation.Spec

end
