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
  /-- The paper's timing parameter: a positive gossip delay `Δ` in
      milliseconds that fits after the attestation deadline, `A + Δ < S`.
      The delivery fields below state the network content at slot level. -/
  delta : ∃ delay_ms : ℕ,
    0 < delay_ms ∧
      get_attestation_due_ms cfg + delay_ms < cfg.slot_duration_ms
  /-- The honest vote deadline and positive Δ with strict `A + Δ < S`
      give receipt before the next slot. Honest clients retain early votes
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
  /-- Strict `A + Δ < S` and honest ready-message service put cutoff blocks
      before the next-slot vote handler; exclusion is tested before the tick. -/
  boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext E
  /-- Positive-Δ gossip and strict deadline fit give evidence by the next
      boundary from a cutoff holding time, with no exclusion. This is a premise:
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
Gloas also needs envelope delivery and data-availability relay. -/
def Synchrony.toPaperSafetySynchrony
    (h : Synchrony cfg ext E)
    (hlookahead : HorizonVoteDeliveryLookahead cfg E)
    (henvelope : DeadlineEnvelopeDelivery cfg ext E)
    (hdata : DeadlineDataAvailabilityRelay cfg ext E) :
    NextSlotSynchronyPremises cfg ext E where
  delta := h.delta
  delivery_lookahead := hlookahead
  deadline_block_relay := h.deadline_block_relay
  boundary_block_prefix := h.boundary_block_prefix
  envelope_delivery := henvelope
  data_availability_relay := hdata
  attester_slashing_relay := h.attester_slashing_relay

section DelayFacts
variable {cfg : Config} {ext : BeaconFunctionInterface Root} {E : Execution Root}

/-- The delay chosen from `Synchrony.delta` is strictly positive. -/
theorem Synchrony.delta_pos (h : Synchrony cfg ext E) :
    0 < Classical.choose h.delta :=
  (Classical.choose_spec h.delta).1

/-- The vote deadline plus the chosen delay precedes the next slot start. -/
theorem Synchrony.deadline_fits (h : Synchrony cfg ext E) :
    get_attestation_due_ms cfg + Classical.choose h.delta <
      cfg.slot_duration_ms :=
  (Classical.choose_spec h.delta).2

/-- The delay chosen from `NextSlotSynchronyPremises.delta` is strictly
positive. -/
theorem NextSlotSynchronyPremises.delta_pos
    (h : NextSlotSynchronyPremises cfg ext E) :
    0 < Classical.choose h.delta :=
  (Classical.choose_spec h.delta).1

/-- The honest vote deadline plus the chosen delay precedes the next slot
start. -/
theorem NextSlotSynchronyPremises.deadline_fits
    (h : NextSlotSynchronyPremises cfg ext E) :
    get_attestation_due_ms cfg + Classical.choose h.delta <
      cfg.slot_duration_ms :=
  (Classical.choose_spec h.delta).2

end DelayFacts

end FastConfirmation.Spec

end
