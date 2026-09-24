module
public import FastConfirmationStatements.Premises.FFGState

/-! Accepted carrier evidence can name an explicit trusted validation domain.
The existing evidence record and headline types retain their honest domain.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root) (E : Execution Root)

variable {cfg ext E}

/-- The old evidence is the honest-store instance of the trusted domain. -/
def CausalCarrierAttestationEvidence.toTrusted {validity carrier a}
    (h : CausalCarrierAttestationEvidence cfg ext E validity carrier a) :
    TrustedCarrierAttestationEvidence cfg ext E validity
      (E.HonestCausalStore cfg ext) carrier a where
  toIncludedAttestationEvidence := h.toIncludedAttestationEvidence
  carrier_accepted := h.carrier_accepted
  validation_store := h.validation_store
  validation_store_trusted := h.validation_store_honest
  validation_target_known := h.validation_target_known
  validation_state_from_target := h.validation_state_from_target

/-- Specializing the trusted predicate to honesty recovers the old record. -/
def TrustedCarrierAttestationEvidence.toHonest {validity carrier a}
    (h : TrustedCarrierAttestationEvidence cfg ext E validity
      (E.HonestCausalStore cfg ext) carrier a) :
    CausalCarrierAttestationEvidence cfg ext E validity carrier a where
  toIncludedAttestationEvidence := h.toIncludedAttestationEvidence
  carrier_accepted := h.carrier_accepted
  validation_store := h.validation_store
  validation_store_honest := h.validation_store_trusted
  validation_target_known := h.validation_target_known
  validation_state_from_target := h.validation_state_from_target


end Execution
end FastConfirmation.Spec
end
