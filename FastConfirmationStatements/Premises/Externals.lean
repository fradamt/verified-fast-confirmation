module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Externals declarations from FastConfirmation.Spec.Model.Assumptions. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution
/-- Contracts for the abstract `Externals` under the static-registry model.
The three indexed-attestation laws apply only to keyed states in honest,
in-horizon causal stores. Default-state rejection and validity preservation
under Phase0 slot processing are separate contracts. The other fields state
slot/registry behavior and committee agreement; this record is not a proof
that the external interpretation refines the full beacon-chain functions. -/
structure BeaconExternalsPremises (E : Execution Root) : Prop where
  /-- `process_slots` targets its slot.  Verbatim from the pinned loop
      `while state.slot < slot: … state.slot = Slot(state.slot + 1)`
      (beacon-chain.md:1396). -/
  process_slots_slot : ∀ st (s : Slot), st.slot < s → (ext.process_slots st s).slot = s
  /-- `process_slots` preserves the validator registry.

      **DISCLOSURE (`docs/plumbing-spec-citations.md` P-7): this is the
      static-validator-set idealization at the function level, not a
      transcription.**  It is *false* of the pinned `process_slots` across an
      epoch boundary: the loop calls `process_epoch` on the last slot of each
      epoch, and `process_epoch` calls `process_registry_updates`,
      `process_slashings` and `process_effective_balance_updates`, all three of
      which write `state.validators`.  Within a single epoch the boundary test
      never fires and `process_slot` (beacon-chain.md:1407) touches only
      `state_roots` / `block_roots` / `latest_block_header`, so the field is
      exactly right there; across boundaries it asserts that no activation,
      exit, slashing or effective-balance change lands inside the verified
      window.  That is the same idealization as `StaticValidatorSet` ([S],
      paper Assumption 1) and as this record's own `state_transition_registry`,
      which already discloses it — this field is its `process_slots` half and is
      licensed by the same assumption, no more. -/
  process_slots_registry : ∀ st s, (ext.process_slots st s).validators = st.validators
  /-- a valid state transition lands on the block's slot and preserves the
      registry (no deposits/exits in the window — the static-set idealization,
      spec's own balance-source design note). -/
  state_transition_slot : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st'.slot = b.message.slot
  state_transition_registry : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st'.validators = st.validators
  /-- a valid state transition requires the pre-state to precede the block's
      slot (the real `process_slots` assert inside `state_transition`) —
      gives Layer 0 the parent-slot ordering `WellFormedStore` preservation
      needs. -/
  state_transition_pre_slot_lt : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st.slot < b.message.slot
  /-- checkpoint-chain coherence of the abstract state transition: the
      checkpoints a post-state carries have epochs at most the block's
      epoch (the real epoch processing justifies only past-epoch targets;
      full chain-position coherence — roots on the block's ancestor chain —
      is added when the proof consumes it). -/
  state_transition_checkpoint_epoch : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' →
      st'.current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg b.message.slot ∧
      st'.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot
  /-- Epoch processing adopts no future checkpoint: the new justified
      checkpoint's epoch is at most the state's epoch. This is the pull-up
      counterpart of `state_transition_checkpoint_epoch`; the concrete epoch
      processing considers only current- and previous-epoch targets. -/
  pjf_checkpoint_epoch : ∀ st : BeaconState Root,
    (ext.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg st.slot
  /-- the store-computed slot committees agree with the ground-truth
      assignment on every honest store (the spec's committee-consistency
      window, idealized to the verified execution prefix).

      **DISCLOSURE (`docs/plumbing-spec-citations.md` P-8): the agreement
      window asserted here EXCEEDS the spec's own bound.**  The pinned
      requirement on `get_slot_committee` is
      fast-confirmation.md:230 — *"This function returns the committee for a
      specific slot. It MUST support committees of epochs starting from
      `current_epoch - 2`."* — i.e. a two-epoch lookback over
      `shuffling_source = store.block_states[head]`, matching validator.md:257's
      `MAX_SEED_LOOKAHEAD` and validator.md:325's "Lookahead".  This field
      instead asserts exact agreement with the ground-truth committee for
      **every** in-horizon slot, with no window and no `MAX_SEED_LOOKAHEAD`
      qualification.  It is a strengthening of the quoted MUST, licensed by the
      same static-validator-set idealization as `process_slots_registry` /
      `state_transition_registry` ([S] `StaticValidatorSet`, paper Assumption
      1): with the active set constant below the horizon the shuffling is a
      function of the (fixed) registry, so `current_epoch - 2` stops binding.
      Under a mutating registry the extra window would not be available. -/
  committees_agree : ∀ v ∈ E.honest, ∀ n (s : Slot),
    E.WithinHorizon cfg n → E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s
  /-- honestly *cast* singleton attestations pass the abstract
      index/signature validity check on keyed states of honest, in-horizon
      causal stores (restricted to data the validator
      actually signed — an unrestricted version would force fabricated data
      naming honest validators to validate, handing forged slashings to the
      adversary). -/
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ReachableValidationState cfg ext state →
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      ext.is_valid_indexed_attestation state a = true
  /-- BLS soundness on the same reachable-state domain: a validating attestation naming an honest
      validator carries data that validator actually signed — no forged
      slashings against honest validators. -/
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ReachableValidationState cfg ext state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  /-- Committee confinement on the same reachable-state domain: validating attestations carry only indices from
      the slot's committee (in the real pipeline `get_indexed_attestation`
      derives indices from the committee and aggregation bits — absorbed into
      the wire object, so the constraint is restored here; confines LMD
      supporters to the spans `ByzantineWeightPremises` budgets). -/
  valid_attestation_committee : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ReachableValidationState cfg ext state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot
  /-- the beacon chain assigns each validator to exactly one slot per epoch
      (`get_committee_assignment` uniqueness — a structural fact of the
      shuffling): two assigned slots in the same epoch coincide. -/
  committee_assignment_unique : ∀ (i : ValidatorIndex) (s s' : Slot),
    i ∈ E.committee s → i ∈ E.committee s' →
    compute_epoch_at_slot cfg s = compute_epoch_at_slot cfg s' → s = s'
  /-- Every active validator has a committee assignment in each in-horizon
      epoch. Together with `committee_assignment_unique`, this states that
      `get_beacon_committee` partitions the epoch's active validators across
      its slots. -/
  committee_coverage : ∀ (i : ValidatorIndex) (e : Epoch),
    e < E.verification_horizon →
    is_active_validator (E.registry.getD i default) e = true →
      ∃ s : Slot, E.SlotWithinHorizon cfg s ∧
        compute_epoch_at_slot cfg s = e ∧ i ∈ E.committee s
  /-- Committee members are active validators. The beacon-chain shuffling
      draws committees from the epoch's active set; cross-epoch stability is
      supplied by `StaticValidatorSet.activity_constant`. -/
  committee_members_active : ∀ (i : ValidatorIndex) (s : Slot),
    E.SlotWithinHorizon cfg s →
    i ∈ E.committee s →
      is_active_validator (E.registry.getD i default)
        (compute_epoch_at_slot cfg s) = true
  /-- The default state has no validator public keys. Empty or noncanonical
      indices fail the Python check; a nonempty canonical list fails its
      validator lookup. This contract represents either rejection as `false`
      in the total Boolean primitive. It also rules out successful reads
      outside a state map's keyed domain. -/
  valid_attestation_default : ∀ a : Attestation Root,
    ext.is_valid_indexed_attestation (default : BeaconState Root) a = false
  /-- Successful Phase0 empty-slot processing preserves validator public keys
      and the fork/genesis inputs of the signing domain. The attestation fixes
      the target epoch. On a reachable base state the abstract primitive must
      preserve indexed validity; this contract covers the prepared checkpoint
      state before a handler commits it. It is an explicit contract of the
      total abstraction, not a theorem about Python exceptions. -/
  process_slots_attestation_valid : ∀ (state : BeaconState Root) (slot : Slot)
      (a : Attestation Root), E.ReachableValidationState cfg ext state →
    state.slot < slot →
    ext.is_valid_indexed_attestation (ext.process_slots state slot) a =
      ext.is_valid_indexed_attestation state a
  /-- Execution-envelope validation depends on the state and signed envelope,
      not on which honest node observed the available data. -/
  verify_envelope_deterministic : ∀ state signed o o',
    ext.verify_execution_payload_envelope state signed o =
      ext.verify_execution_payload_envelope state signed o'

end FastConfirmation.Spec

end
