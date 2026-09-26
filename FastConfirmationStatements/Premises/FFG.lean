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
/-- An unconditional cross-boundary equality used by the current proof.

This contract is stronger than the real Phase0 state functions. In
`specs/phase0/beacon-chain.md:1893-1898` and
`specs/altair/beacon-chain.md:728-733`, PJF returns early in epochs 0 and 1.
Starting in epoch 1, slot processing across two boundaries can justify epoch
1 from votes already included in the state, while eager PJF is a no-op.
The equality below therefore does not cover that real execution.

A repair needs a guarded equality and a separate initial-epoch case in its
consumers. The contract is retained here until that proof repair is complete;
it must not be read as an exact Phase0 law. It mentions only state functions,
not execution ancestry or a safety conclusion. -/
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
