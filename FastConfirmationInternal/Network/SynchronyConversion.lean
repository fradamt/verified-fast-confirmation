module
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Conversion from full synchrony and Gloas delivery laws to next-slot synchrony. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
end Execution
/-- Network synchrony — the FCR intro's assumption ("starting from the
current slot, attestations created by honest validators in any slot are
received by the end of that slot"), made operational, plus the block/message
propagation the spec leaves implicit (explicit in the paper's `Synchrony`
bundle). The fork choice's own `current_slot ≥ slot + 1` gate makes the first
second of slot `s+1` the earliest applicable processing time for a slot-`s`
attestation. The exact relation to `NextSlotSynchronyPremises` is proved by
`synchrony_and_delivery_iff_nextSlot`. -/
structure Synchrony (E : Execution Root) : Prop where
  /-- An honest vote sent by its deadline is at every honest node at the
      first second of the next slot. Motivation: the paper's `A + Δ < S`
      gives receipt before the next slot; honest clients retain early votes
      and process them at the first applicable slot start. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 →
    E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  /-- Deadline gossip with the pre-tick finalized-guard exemption. -/
  deadline_block_relay : DeadlineBlockRelay cfg ext E
  /-- A root stored by a cutoff observation is in the store read by each
      boundary vote handler; exclusion is tested before the tick. -/
  boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext E
  /-- Evidence held by a cutoff observation is held by every honest node
      from the next boundary on, with no exclusion. This is a premise:
      the literal justified-state check in `on_attester_slashing` can reject
      a signer that head-state clients accept (module note above). -/
  attester_slashing_relay : DeadlineAttesterSlashingRelay cfg ext E

/-- The lookahead vote law supplies next-slot delivery within the horizon. -/
theorem NextSlotSynchronyPremises.attestation_delivery
    {cfg : Config} {ext : BeaconFunctionInterface Root}
    {E : Execution Root} (h : NextSlotSynchronyPremises cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest)
    (s n : ℕ) (a : Attestation Root)
    (hs : E.SlotWithinHorizon cfg s)
    (hn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some (n, a))
    (hdeadline : n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000)
    (_hdelivery : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  h.delivery_lookahead.attestation_delivery v hv s n a hs hn hvote hdeadline w hw

/-- The synchrony bundle supplies the beacon and attestation fields.
Gloas also needs the envelope boundary prefix. -/
def Synchrony.toPaperSafetySynchrony
    (h : Synchrony cfg ext E)
    (hlookahead : HorizonVoteDeliveryLookahead cfg E)
    (henvelopePrefix : DeadlineBoundaryEnvelopePrefix cfg ext E) :
    NextSlotSynchronyPremises cfg ext E where
  delivery_lookahead := hlookahead
  deadline_block_relay := h.deadline_block_relay
  boundary_block_prefix := h.boundary_block_prefix
  boundary_envelope_prefix := henvelopePrefix
  attester_slashing_relay := h.attester_slashing_relay

end FastConfirmation.Spec

end
