module
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Defines legacy proof vocabulary outside the public review claims. -/

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
