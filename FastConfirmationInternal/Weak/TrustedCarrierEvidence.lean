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

/-- The validation store is checked by an explicit predicate. Body membership,
accepted occurrence, and the exact prepared-state equation are retained. -/
structure TrustedCarrierAttestationEvidence
    (validity : BeaconState Root → Attestation Root → Bool)
    (trusted : Store Root → Prop) (carrier : Root) (a : Attestation Root)
    extends IncludedAttestationEvidence cfg E validity carrier a where
  carrier_accepted : E.AcceptedBlockAt cfg ext carrier carrier_message
  validation_store : Store Root
  validation_store_trusted : trusted validation_store
  validation_target_known : a.data.target.root ∈ validation_store.block_roots
  validation_state_from_target : validation_state =
    let base := validation_store.block_states a.data.target.root
    let start := compute_start_slot_at_epoch cfg a.data.target.epoch
    if base.slot < start then ext.process_slots base start else base

/-- Positive inclusion with the same explicit validation domain. -/
structure TrustedCarrierAttestationRelation
    (validity : BeaconState Root → Attestation Root → Bool)
    (trusted : Store Root → Prop) where
  Included : Root → Attestation Root → Prop
  evidence : ∀ {carrier a}, Included carrier a →
    TrustedCarrierAttestationEvidence cfg ext E validity trusted carrier a

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

/-- Ordinary certificate consumers do not read the validation domain. -/
def TrustedCarrierAttestationRelation.relation {validity trusted}
    (I : TrustedCarrierAttestationRelation cfg ext E validity trusted) :
    IncludedAttestationRelation cfg E validity where
  Included := I.Included
  evidence := fun h => (I.evidence h).toIncludedAttestationEvidence

end Execution
end FastConfirmation.Spec
end
