module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Defines coherence conditions for abstract state transitions, committees, signatures, and payload observations. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- A state held in an honest, in-horizon causal store, or a state obtained by
`process_slots` at an in-horizon slot from one of its keyed validation states. Successful scheduled
imports at honest nodes enter the first case through their successor prefix.
The second case includes the checkpoint and pulled-up head states computed by
handlers. -/
def RegistryStateInHorizon (E : Execution Root) (state : BeaconState Root) : Prop :=
  E.ReachableValidationState cfg ext state ∨
    ∃ base slot, E.ReachableValidationState cfg ext base ∧
      E.SlotWithinHorizon cfg slot ∧
      ext.process_slots base slot = state

/-- Contracts for the abstract `BeaconFunctionInterface` and the execution.
The three indexed-attestation laws apply only to keyed states in honest,
in-horizon causal stores. Default-state rejection and validity preservation
under slot processing are separate contracts. The other fields state
slot behavior and committee agreement; this record is not a proof
that the external interpretation refines the full beacon-chain functions. -/
structure BeaconExternalsPremises (E : Execution Root) : Prop where
  /-- `process_slots` targets its slot. -/
  process_slots_slot : ∀ st (s : Slot), st.slot < s → (ext.process_slots st s).slot = s
  /-- The execution-scope static-registry condition. Every keyed state in an
      honest in-horizon causal store and every in-horizon `process_slots`
      result computed from one has the anchor registry. This includes successful scheduled
      imports at honest nodes. Real runs with included slashings or deposits,
      or activations, exits, or effective-balance changes taking effect in the
      horizon do not satisfy this condition. -/
  registry_static_in_horizon : ∀ state,
    RegistryStateInHorizon cfg ext E state → state.validators = E.registry
  /-- A valid state transition lands on the block's slot. -/
  state_transition_slot : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st'.slot = b.message.slot
  /-- A valid state transition requires the pre-state slot to precede the
      block slot, as `process_slots` asserts in `state_transition`. -/
  state_transition_pre_slot_lt : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st.slot < b.message.slot
  /-- A post-state checkpoint has an epoch at most the block epoch, if the
      pre-state's checkpoints are not in a future epoch of the pre-state.
      Epoch processing in `process_slots` sets the justified checkpoint only
      to the previous or current epoch, and finalizes only a checkpoint whose
      epoch the weighing rules fix below the current epoch
      (`weigh_justification_and_finalization`); `process_block` does not
      write either checkpoint. Every keyed state of a store satisfies the
      antecedent (`anchor_state_checkpoint_epoch` and this law). Without the
      antecedent the law is false: a state at slot 0 with justified epoch 5
      keeps it through a block at slot 1. This field does not constrain the
      checkpoint root. -/
  state_transition_checkpoint_epoch : ∀ st (b : SignedBeaconBlock Root) st',
    st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot →
    st.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot →
    ext.state_transition st b = some st' →
      st'.current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg b.message.slot ∧
      st'.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot
  /-- Epoch processing adopts no future checkpoint, if the state's justified
      checkpoint is not in a future epoch: the new justified checkpoint's
      epoch is at most the state's epoch. This is the pull-up counterpart of
      `state_transition_checkpoint_epoch`. `process_justification_and_finalization`
      returns early at epochs up to `GENESIS_EPOCH + 1` and otherwise
      justifies only the previous or current epoch. Without the antecedent the
      law is false: the early return keeps a justified epoch 5 at slot 0. -/
  pjf_checkpoint_epoch : ∀ st : BeaconState Root,
    st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg st.slot →
    (ext.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg st.slot
  /-- The anchor state's checkpoints are not in a future epoch of the anchor
      state. A genesis state (both checkpoints at `GENESIS_EPOCH`) and every
      state that the beacon chain reaches satisfy it. It is the base case of
      the store invariant that gives the antecedents of
      `state_transition_checkpoint_epoch` and `pjf_checkpoint_epoch` for
      every keyed state. -/
  anchor_state_checkpoint_epoch :
    E.anchor_state.current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg E.anchor_state.slot ∧
      E.anchor_state.finalized_checkpoint.epoch ≤
        compute_epoch_at_slot cfg E.anchor_state.slot
  /-- the store-computed slot committees agree with the ground-truth
      assignment on every honest store (the spec's committee-consistency
      window, idealized to the verified execution prefix). This is an
      idealization: committees are modeled as one fixed ground-truth
      assignment, and the RANDAO-seeded, fork-dependent committees of the
      real protocol are not modeled. -/
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
  /-- Committee confinement only for a successful `on_attestation` delivery
      in an honest in-horizon causal prefix. Python obtains these indices from
      committee bits before this handler. The Lean wire object is already
      indexed, so this premise supplies the committee. It uses the fixed
      ground-truth assignment `E.committee`; the RANDAO-seeded,
      fork-dependent committees of the real protocol are not modeled.
      Attester-slashing evidence is checked by the same indexed Boolean but
      does not enter this handler and need not have committee indices. -/
  on_attestation_committee : ∀ (store store' : Store Root) (a : Attestation Root)
      (is_from_block : Bool),
    E.HonestPrefixStoreWithinHorizon cfg ext store' →
    on_attestation cfg ext store a is_from_block = some store' →
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
  /-- Successful empty-slot processing to an in-horizon slot preserves
      indexed validity when it keeps the validator registry. Slot processing
      does not change validator public keys or the fork and genesis inputs of
      the signing domain, and the attestation fixes the target epoch. The
      registry hypothesis is where `registry_static_in_horizon` enters: the
      reachable base state and its in-horizon slot-processed state are both
      `RegistryStateInHorizon` states. Epoch processing that applies a pending
      deposit appends a validator and can make an invalid attestation valid;
      such a run is outside `registry_static_in_horizon`. This contract covers
      the prepared checkpoint state before a handler commits it. It is an
      explicit contract of the total abstraction, not a theorem about Python
      exceptions. -/
  process_slots_attestation_valid : ∀ (state : BeaconState Root) (slot : Slot)
      (a : Attestation Root), E.ReachableValidationState cfg ext state →
    state.slot < slot → E.SlotWithinHorizon cfg slot →
    (ext.process_slots state slot).validators = state.validators →
    ext.is_valid_indexed_attestation (ext.process_slots state slot) a =
      ext.is_valid_indexed_attestation state a
  /-- Execution-envelope validation depends on the state and signed envelope,
      not on which honest node observed the available data. -/
  verify_envelope_deterministic : ∀ state signed o o',
    ext.verify_execution_payload_envelope state signed o =
      ext.verify_execution_payload_envelope state signed o'

end FastConfirmation.Spec

end
