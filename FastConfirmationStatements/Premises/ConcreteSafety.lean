module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.Behavior
public import FastConfirmationStatements.Premises.Economics
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Defines the safety premise of a run with the concrete bridge. The bridge
fixes the configuration, the state functions, the FFG selectors, and the
inclusion relation. The premise states the execution scope, the network and
honest behavior, the stake bounds, and paper Assumption 3.2 over the view of
the bridge. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The paper A3.2 view of a run with the concrete bridge. The carrier domain
is the accepted blocks. `D_b` is computed from the attestations in the bodies
of the accepted blocks on the chain of `b`. A checkpoint is formed at a block
when the block carries it as its realized or unrealized justified or
finalized checkpoint. `C(r, e)` is the checkpoint selector of the bridge, and
`GJ` and `GU` are the realized and unrealized justified checkpoints. -/
noncomputable def checkpointInclusionView (E : Execution Root) :
    CheckpointInclusionView B.setup.cfg E where
  BlockAt := E.BlockKnownInScheduledPrefix B.setup.cfg B.interface
  Included := B.BodyIncludedAt E
  formed := B.Carried E
  C := B.checkpointAt
  GJ := B.realizedJustified
  GU := B.unrealizedJustified
  checkpoint_epoch := fun _ _ => rfl

/-- The external contracts of a run with the concrete bridge that the bridge
does not prove. They relate the fixed committee schedule to the ground-truth
committee assignment of the execution (class I: RANDAO-seeded,
fork-dependent committees are not modeled), and they state the behavior of
the opaque signature and envelope checks of `base`. The bridge proves the
other contracts of the internal record `BeaconExternalsPremises` (slot and
checkpoint-epoch laws, anchor checkpoint epochs, default-state rejection,
and the static registry) and the static validator set. -/
structure ConcreteExternalsPremises (E : Execution Root) : Prop where
  /-- The store-computed slot committees agree with the ground-truth
      assignment on every honest store in the horizon. This is an
      idealization: committees are one fixed ground-truth assignment. -/
  committees_agree : ∀ v ∈ E.honest, ∀ n (s : Slot),
    E.WithinHorizon B.setup.cfg n → E.SlotWithinHorizon B.setup.cfg s →
    get_slot_committee B.setup.cfg B.interface (E.store B.setup.cfg B.interface v n) s =
      E.committee s
  /-- Honestly cast singleton attestations pass the indexed validity check on
      keyed states of honest, in-horizon causal stores, for data that the
      validator signed. -/
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ReachableValidationState B.setup.cfg B.interface state →
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      B.interface.is_valid_indexed_attestation state a = true
  /-- BLS soundness on the same domain: a validating attestation that names an
      honest validator carries data that the validator signed. -/
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ReachableValidationState B.setup.cfg B.interface state →
    B.interface.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  /-- Committee confinement for every successful `on_attestation` call whose
      result is an honest in-horizon prefix store. The pre-store is
      arbitrary, so the validity check must reject, on the states of such
      stores, an indexed attestation with an index outside its slot
      committee. Python obtains the indices from committee bits before this
      handler; the Lean wire object is already indexed. -/
  on_attestation_committee : ∀ (store store' : Store Root) (a : Attestation Root)
      (is_from_block : Bool),
    E.HonestPrefixStoreWithinHorizon B.setup.cfg B.interface store' →
    on_attestation B.setup.cfg B.interface store a is_from_block = some store' →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot
  /-- Each validator has at most one assigned slot per epoch. -/
  committee_assignment_unique : ∀ (i : ValidatorIndex) (s s' : Slot),
    i ∈ E.committee s → i ∈ E.committee s' →
    compute_epoch_at_slot B.setup.cfg s = compute_epoch_at_slot B.setup.cfg s' → s = s'
  /-- Every active validator has a committee assignment in each in-horizon
      epoch. -/
  committee_coverage : ∀ (i : ValidatorIndex) (e : Epoch),
    e < E.verification_horizon →
    is_active_validator (E.registry.getD i default) e = true →
      ∃ s : Slot, E.SlotWithinHorizon B.setup.cfg s ∧
        compute_epoch_at_slot B.setup.cfg s = e ∧ i ∈ E.committee s
  /-- Committee members are active validators. -/
  committee_members_active : ∀ (i : ValidatorIndex) (s : Slot),
    E.SlotWithinHorizon B.setup.cfg s →
    i ∈ E.committee s →
      is_active_validator (E.registry.getD i default)
        (compute_epoch_at_slot B.setup.cfg s) = true
  /-- Successful empty-slot processing to an in-horizon slot preserves
      indexed validity when it keeps the validator registry. -/
  process_slots_attestation_valid : ∀ (state : BeaconState Root) (slot : Slot)
      (a : Attestation Root), E.ReachableValidationState B.setup.cfg B.interface state →
    state.slot < slot → E.SlotWithinHorizon B.setup.cfg slot →
    (B.interface.process_slots state slot).validators = state.validators →
    B.interface.is_valid_indexed_attestation (B.interface.process_slots state slot) a =
      B.interface.is_valid_indexed_attestation state a
  /-- Execution-envelope validation depends on the state and signed envelope,
      not on which honest node observed the available data. -/
  verify_envelope_deterministic : ∀ state signed o o',
    B.interface.verify_execution_payload_envelope state signed o =
      B.interface.verify_execution_payload_envelope state signed o'

/-- The safety premise of a run `E` with the concrete bridge `B`. The state
functions of the run are `B.interface`, and the configuration is
`B.setup.cfg`. -/
structure SafetyPremises (E : Execution Root) : Prop where
  admissible : B.Admissible
  genesis : B.ConcreteGenesis E
  horizon_scope : E.verification_horizon = B.setup.scope.last_epoch + 1
  whole_seconds : 1000 ∣ B.setup.cfg.slot_duration_ms
  wellFormed : WellFormedExecution E
  externals_coherence : B.ConcreteExternalsPremises E
  honest_behavior : HonestBehavior B.setup.cfg B.interface E
  body_attestations_delivered : B.BodyAttestationsDelivered E
  synchrony : NextSlotSynchronyPremises B.setup.cfg B.interface E
  byzantine_bound : ByzantineWeightPremises B.setup.cfg E
  epoch_ends_fit : EpochEndsFitUint64 B.setup.cfg
  slots_per_epoch_gt_one : 1 < B.setup.cfg.slots_per_epoch
  epoch_one_finalization_scope : B.EpochOneFinalizationScope E
  checkpoint_inclusion :
    EventualCheckpointInclusion B.setup.cfg B.interface (B.checkpointInclusionView E)

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
