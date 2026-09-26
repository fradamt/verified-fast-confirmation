module
public import FastConfirmationProofs.Checkpoints.GlobalResetCheckpointRealization
public import FastConfirmationProofs.FFG.State.ScheduledFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.Certificates.FFGAccountability
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks
public import FastConfirmationProofs.FFG.SelectedSource.SelectedTraceFFGRealization
public import FastConfirmationProofs.ModelFacts
public import FastConfirmationProofs.ForkChoice.Head.Descent

@[expose] public section

/-!
# Genesis and observed-reset safety without the legacy justification interface

The public trajectory fold used to demand `SafeFrom` for the rotated observed
checkpoint on every slot update, even though `get_latest_confirmed` reads that
checkpoint as a reset input only when its epoch-start restart guard fires.  This
file makes the executable branch condition explicit and scopes the reset
obligation to that condition.

The local half of the restart is fully concrete: the guard says that the
observed checkpoint is the unrealized justification of the query head.  The
common `ChainFFGState` therefore identifies it with `GU(head)`, supplies AU
evidence, and realizes it as the corresponding checkpoint on the head chain.

The cross-view half has two protocol-native ways to finish:

* the endpoint justified checkpoint has a concrete justification chain whose
  trusted anchor is the observed checkpoint; or
* while the endpoint still lags that checkpoint, the filtered LMD-GHOST tree
  has an explicit weight-dominant descent from its justified root to the
  observed root.

The first case is turned into concrete store ancestry by execution-parent
reflection.  The second is consumed directly by the ordinary GHOST descent
theorem.  Neither branch assumes a head/ancestry/`SafeFrom` conclusion.

The trusted genesis anchor needs neither branch: every concretely certified
global justified checkpoint descends from it, so the filter root and hence the
head do as well.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-! ## The exact restart core -/

/-- The three safety-relevant conjuncts of the executable observed restart.

The fourth executable conjunct only says that the restart moves the candidate
strictly forward.  It is irrelevant to placement of the restart checkpoint and
is deliberately omitted here. -/
structure ObservedRestartCompatible
    (fcrStore : FastConfirmationStore Root) : Prop where
  epoch_start :
    is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true
  root_previous_epoch :
    get_block_epoch cfg fcrStore.store
        fcrStore.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg fcrStore.store
  observed_eq_head_unrealized :
    fcrStore.current_epoch_observed_justified_checkpoint =
      fcrStore.store.unrealized_justifications
        (get_head cfg fcrStore.store).root



namespace Execution

variable (E : Execution Root)



/-! ## Cross-view certificate-or-filter takeover -/






/-! ## Genesis certificate continuation -/



/-! ## Restart-scoped public fold -/





end Execution

end FastConfirmation.Spec

end
