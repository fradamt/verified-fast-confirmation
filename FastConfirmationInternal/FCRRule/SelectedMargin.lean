module
public import FastConfirmationStatements.Premises.SelectedMargin

@[expose] public section

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Compatibility name for the two operational payload premises used with
the legacy `Synchrony` bundle. -/
def PayloadEnvelopeRelay (E : Execution Root) : Prop :=
  EnvelopeDelivery cfg ext E ∧ DataAvailabilityRelay cfg ext E

end FastConfirmation.Spec

end
