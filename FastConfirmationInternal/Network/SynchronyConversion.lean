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
/-- The legacy synchrony bundle supplies the beacon and attestation fields.
Gloas also needs envelope delivery and data-availability relay. -/
def Synchrony.toPaperSafetySynchrony
    (h : Synchrony cfg ext E)
    (henvelope : DeadlineEnvelopeDelivery cfg ext E)
    (hdata : DeadlineDataAvailabilityRelay cfg ext E) :
    NextSlotSynchronyPremises cfg ext E where
  delta := h.delta
  attestation_delivery := h.attestation_delivery
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
