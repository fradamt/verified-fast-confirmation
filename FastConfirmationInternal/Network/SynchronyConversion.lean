module
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Conversion from full synchrony and Gloas delivery laws to next-slot synchrony. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
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


end FastConfirmation.Spec

end
