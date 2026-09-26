module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.Behavior
public import FastConfirmationStatements.Premises.Economics
public import FastConfirmationStatements.Premises.Externals
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

/-- The safety premise of a run `E` with the concrete bridge `B`. The state
functions of the run are `B.interface`, and the configuration is
`B.setup.cfg`. -/
structure SafetyPremises (E : Execution Root) : Prop where
  admissible : B.Admissible
  genesis : B.ConcreteGenesis E
  horizon_scope : E.verification_horizon = B.setup.scope.last_epoch + 1
  whole_seconds : 1000 ∣ B.setup.cfg.slot_duration_ms
  wellFormed : WellFormedExecution E
  externals_coherence : BeaconExternalsPremises B.setup.cfg B.interface E
  honest_behavior : HonestBehavior B.setup.cfg B.interface E
  body_attestations_delivered : B.BodyAttestationsDelivered E
  synchrony : NextSlotSynchronyPremises B.setup.cfg B.interface E
  static_validators : StaticValidatorSet B.setup.cfg E
  byzantine_bound : ByzantineWeightPremises B.setup.cfg E
  epoch_ends_fit : EpochEndsFitUint64 B.setup.cfg
  slots_per_epoch_gt_one : 1 < B.setup.cfg.slots_per_epoch
  epoch_one_finalization_scope : B.EpochOneFinalizationScope E
  checkpoint_inclusion :
    EventualCheckpointInclusion B.setup.cfg B.interface (B.checkpointInclusionView E)

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
