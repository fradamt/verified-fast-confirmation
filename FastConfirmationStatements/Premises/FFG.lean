module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-!
Defines Phase0 voting-source coherence at FFG epoch boundaries.
These premises constrain the abstract beacon-state functions.
-/

section

/-! ## Epoch-boundary source coherence -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- The remaining phase0 fact hidden by the reduced model's opaque state
functions.

After at least one epoch boundary, empty-slot processing exposes exactly the
eager `process_justification_and_finalization` value of the starting state.
The same value is installed by a block transition whose block crosses an
epoch boundary from its pre-state.  Additional empty epochs cannot create a
new justified checkpoint: without a new block there are no newly included
attestations.

This is deliberately a state-function contract only.  It mentions no
execution, fork-choice target, certificate, ancestry, or safety conclusion.
Together with `Phase0SourceCoherence`, it is the exact phase0 distinction in
paper Definition 7: a head in the voting epoch reads `GJ`, while a head from
an earlier epoch reads the eager `GU` value. -/
structure Phase0BoundarySourceCoherence
    (cfg : Config) (ext : BeaconFunctionInterface Root) : Prop where
  process_slots_current_justified :
    ∀ (st : BeaconState Root) (target : Slot),
      st.slot < target →
      compute_epoch_at_slot cfg st.slot <
        compute_epoch_at_slot cfg target →
      (ext.process_slots st target).current_justified_checkpoint =
        (ext.process_justification_and_finalization st).current_justified_checkpoint
  state_transition_current_justified :
    ∀ (pre : BeaconState Root) (sb : SignedBeaconBlock Root)
      (post : BeaconState Root),
      ext.state_transition pre sb = some post →
      compute_epoch_at_slot cfg pre.slot <
        compute_epoch_at_slot cfg sb.message.slot →
      post.current_justified_checkpoint =
        (ext.process_justification_and_finalization pre).current_justified_checkpoint

end FastConfirmation.Spec

end

section

/-! ## Same-epoch source coherence -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : BeaconFunctionInterface Root}
/-- The narrow phase0 fact hidden by the two opaque state functions.

`process_slots` invokes epoch processing only when it crosses an epoch
boundary.  Likewise, the state transition's block-processing phase does not
alter `current_justified_checkpoint`; that field can change only in the
empty-slot/epoch processing preceding the block.  Consequently both
operations preserve the checkpoint when their input and target slots are in
the same epoch.

This record is intentionally independent of an `Execution` and of all FCR
selection/safety statements. -/
structure Phase0SourceCoherence (cfg : Config) (ext : BeaconFunctionInterface Root) : Prop where
  process_slots_current_justified :
    ∀ (st : BeaconState Root) (target : Slot),
      st.slot < target →
      compute_epoch_at_slot cfg st.slot = compute_epoch_at_slot cfg target →
      (ext.process_slots st target).current_justified_checkpoint =
        st.current_justified_checkpoint
  state_transition_current_justified :
    ∀ (pre : BeaconState Root) (sb : SignedBeaconBlock Root)
      (post : BeaconState Root),
      ext.state_transition pre sb = some post →
      compute_epoch_at_slot cfg pre.slot =
        compute_epoch_at_slot cfg sb.message.slot →
      post.current_justified_checkpoint =
        pre.current_justified_checkpoint

end FastConfirmation.Spec

end

end
