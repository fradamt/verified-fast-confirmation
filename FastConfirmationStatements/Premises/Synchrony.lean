module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Behavior

@[expose] public section

/-! Synchrony declarations from FastConfirmation.Spec.Model.Assumptions. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution
/-- Network synchrony — the FCR intro's assumption ("starting from the
current slot, attestations created by honest validators in any slot are
received by the end of that slot"), made operational, plus the block/message
propagation the spec leaves implicit (explicit in the paper's `Synchrony`
bundle). The fork choice's own `current_slot ≥ slot + 1` gate makes the first
second of slot `s+1` the earliest applicable processing time for a slot-`s`
attestation. -/
structure Synchrony (E : Execution Root) : Prop where
  /-- honest attestations of slot `s` are processed by every honest node at
      the first second of slot `s+1`.

      The *vote* is horizon-scoped — its slot and its creation second both lie
      inside the public verification horizon — but the mandated receipt second
      is not gated: it is named in the (infinite) execution schedule. For a
      vote cast in the horizon's last slot that receipt is the first second of
      the following epoch, just past the exclusive cutoff, which no
      receipt-gated phrasing can name; the cutoff cannot be asked to contain
      its own next epoch boundary.

      **This one field is exactly the old pair.** It is the conjunction of the
      previous receipt-gated clause (recovered verbatim by
      `Synchrony.toHorizonScopedDelivery`) and the previous separate boundary
      record `HorizonVoteDeliveryLookahead` (recovered verbatim by
      `Synchrony.toDeliveryLookahead`); `attestation_delivery_pair_iff` proves
      that conjunction and this field are the same proposition, so merging the
      two assumptions added no content. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  /-- blocks known to an honest node propagate by the **end of the same
      slot**: anything in `v`'s block set at a second of slot `s` is in every
      honest node's block set from the last second of slot `s` on — in
      particular *before* the first second of slot `s+1`, so that second's
      attestation fold finds the referenced blocks already known
      (`validate_on_attestation`'s known-block asserts). The `m+1` clock read is
      only the arithmetic characterization of "last second of the slot"; no
      execution-state assumption is made at `m+1`, so the endpoint itself (not
      its successor) is the horizon-scoped state. -/
  block_relay : ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    r ∈ (E.store cfg ext v n).block_roots →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      r ∈ (E.store cfg ext w m).block_roots
  /-- LMD messages relay: a latest message recorded by an honest node is,
      from the next slot on, recorded (or dominated by a newer one) at every
      honest node. -/
  latest_message_relay : ∀ v ∈ E.honest, ∀ n i (msg : LatestMessage Root),
    E.WithinHorizon cfg n →
    (E.store cfg ext v n).latest_messages i = some msg →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
      ∃ msg', (E.store cfg ext w m).latest_messages i = some msg' ∧
        get_latest_message_epoch cfg msg ≤ get_latest_message_epoch cfg msg'
  /-- Equivocation evidence known to an honest node is known to every honest
      node from the next slot onward. Attester slashings gossip and may be
      carried in blocks through `on_attester_slashing`; the safety argument
      requires all honest nodes to exclude the same detected equivocators. -/
  attester_slashing_relay : ∀ v ∈ E.honest, ∀ n (i : ValidatorIndex),
    E.WithinHorizon cfg n →
    i ∈ (E.store cfg ext v n).equivocating_indices →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
    E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
    i ∈ (E.store cfg ext w m).equivocating_indices

/-- A verified envelope received by an honest node is scheduled at every
honest receiver by the block-relay deadline. The receiver processes preceding
events first: its block must be known at the envelope's position, since the
handler rejects an envelope for an unknown block. -/
def EnvelopeDelivery (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    is_payload_verified (E.store cfg ext v n) r = true →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      ∃ (d k : ℕ) (signed : SignedExecutionPayloadEnvelope Root)
        (sourceObservation receiverObservation : EnvelopeObservation Root)
        (before after : List (Event Root)),
        0 < d ∧ d ≤ m ∧
        E.slot_at cfg n + 1 ≤ E.slot_at cfg (d + 1) ∧ k ≤ n ∧
        Event.execution_payload_envelope signed sourceObservation ∈ E.schedule v k ∧
        signed.message.beacon_block_root = r ∧
        r ∈ (E.store cfg ext v n).block_roots ∧
        ext.is_data_available r sourceObservation = true ∧
        ext.verify_execution_payload_envelope
          ((E.store cfg ext v n).block_states r) signed sourceObservation = true ∧
        E.schedule w d = before ++
          Event.execution_payload_envelope signed receiverObservation :: after ∧
        r ∈ (before.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w (d - 1)) (E.time_at d))).block_roots

/-- Data available at an honest node's envelope observation is available at
every honest receiver's corresponding observation by the relay deadline. -/
def DataAvailabilityRelay (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ k n (signed : SignedExecutionPayloadEnvelope Root)
      (sourceObservation : EnvelopeObservation Root),
    k ≤ n → E.WithinHorizon cfg n →
    Event.execution_payload_envelope signed sourceObservation ∈ E.schedule v k →
    ext.is_data_available signed.message.beacon_block_root sourceObservation = true →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      ∀ receiverSigned receiverObservation,
        receiverSigned.message.beacon_block_root = signed.message.beacon_block_root →
        Event.execution_payload_envelope receiverSigned receiverObservation ∈ E.schedule w m →
        ext.is_data_available signed.message.beacon_block_root receiverObservation = true

/-- The synchrony fragment used by the accepted spec next-slot proof.

The accepted next-slot argument needs honest-attestation delivery, block relay,
envelope delivery, data-availability relay, and equivocation-evidence relay. It does not use the additional
`latest_message_relay` field of the full `Synchrony` bundle. -/
structure NextSlotSynchronyPremises (E : Execution Root) : Prop where
  /-- Same single delivery clause as `Synchrony.attestation_delivery`: the
      vote is horizon-scoped, its mandated receipt second is named in the
      execution schedule without a horizon gate, and the field is exactly the
      old receipt-gated clause together with the old
      `HorizonVoteDeliveryLookahead`. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  block_relay : ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    r ∈ (E.store cfg ext v n).block_roots →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      r ∈ (E.store cfg ext w m).block_roots
  envelope_delivery : EnvelopeDelivery cfg ext E
  data_availability_relay : DataAvailabilityRelay cfg ext E
  attester_slashing_relay : ∀ v ∈ E.honest, ∀ n (i : ValidatorIndex),
    E.WithinHorizon cfg n →
    i ∈ (E.store cfg ext v n).equivocating_indices →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
    E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
    i ∈ (E.store cfg ext w m).equivocating_indices

/-- The legacy synchrony bundle supplies the beacon and attestation fields.
Gloas also needs envelope delivery and data-availability relay. -/
def Synchrony.toPaperSafetySynchrony
    (h : Synchrony cfg ext E)
    (henvelope : EnvelopeDelivery cfg ext E)
    (hdata : DataAvailabilityRelay cfg ext E) :
    NextSlotSynchronyPremises cfg ext E where
  attestation_delivery := h.attestation_delivery
  block_relay := h.block_relay
  envelope_delivery := henvelope
  data_availability_relay := hdata
  attester_slashing_relay := h.attester_slashing_relay


end FastConfirmation.Spec

end
