module
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-!
# Premises/InterpretationFidelity

Interpretation fidelity of the supplied FFG state. These records state the
intended meaning of included votes: real, valid attestations in the bodies of
accepted blocks, validated on the state that `on_attestation` reads. The
safety proof does not need them, and `NextSlotSafetyPremises` does not contain
them. Each full-bundle witness proves them for its interpretation.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution
variable (E : Execution Root)

/-- The intended interpretation of one included attestation: it is a real,
valid body member of an accepted block, and it is validated on the target
state that `on_attestation` prepares. The safety proof does not need these
facts. It uses `IncludedAttestationEvidence` and `HonestBehavior.no_forgery`
instead.

Block roots are injective labels (`WellFormedExecution`), so
`carrier_message` is the same message as in the inclusion evidence. -/
structure IncludedAttestationFidelity
    (carrier : Root) (a : Attestation Root) where
  carrier_message : BeaconBlock Root
  carrier_accepted : E.BlockKnownInScheduledPrefix cfg ext carrier carrier_message
  in_carrier_body : a ∈ carrier_message.attestations
  /-- The attested LMD head may fork from the including block after the target
  boundary; validity requires the head to descend the target, not to descend
  the carrier. -/
  head_descends_target :
    E.RootDescends a.data.beacon_block_root a.data.target.root
  target_on_chain : E.RootDescends carrier a.data.target.root
  target_descends_source :
    E.RootDescends a.data.target.root a.data.source.root
  attesters_in_registry : ∀ i ∈ a.attesting_indices,
    i < E.registry.length
  validation_state : BeaconState Root
  validation_registry : validation_state.validators = E.registry
  valid : ext.is_valid_indexed_attestation validation_state a = true
  /-- An honest in-horizon store with the target block state keyed. -/
  validation_store : Store Root
  validation_store_honest : E.HonestPrefixStoreWithinHorizon cfg ext validation_store
  validation_target_known : a.data.target.root ∈ validation_store.block_roots
  /-- The state read by `on_attestation` after target checkpoint preparation.
  The prepared state need not itself be keyed. -/
  validation_state_from_target :
    validation_state =
      let base := validation_store.block_states a.data.target.root
      let start := compute_start_slot_at_epoch cfg a.data.target.epoch
      if base.slot < start then ext.process_slots base start else base

end Execution

/-- The intended interpretation of an accepted-prefix FFG interpretation:
included votes are real, valid body members of accepted blocks; the validity
check is the external indexed-attestation function; and realized finality does
not pass unrealized finality. This record is not needed by the safety proof
and is not a hypothesis of `confirmed_root_safe_from_next_slot`. -/
structure FFGInterpretationFidelity (E : Execution Root)
    (I : ScheduledFFGInterpretation cfg ext E) : Prop where
  included_fidelity : ∀ {carrier : Root} {a : Attestation Root},
    I.state.includedAttestations.Included carrier a →
      Nonempty (E.IncludedAttestationFidelity cfg ext
        carrier a)
  realized_finalized_epoch_le_unrealized_finalized : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    (I.state.realized_finalized r).epoch ≤ (I.state.unrealized_finalized r).epoch

end FastConfirmation.Spec

end
