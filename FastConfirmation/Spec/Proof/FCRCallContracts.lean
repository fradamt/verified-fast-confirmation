module
public import FastConfirmation.Spec.Model.FFGCertificates

@[expose] public section

/-!
# Low-level contracts for concrete fast-confirmation calls

This module contains only executable call-state definitions and certificate
payloads over the existing `Execution.fcr` trajectory.  In particular, it
does not mention safety, canonicality, filter viability, source availability,
tip placement, takeover, or honest-head conclusions.

Keeping these names below both the historical trajectory proof and its reset
producer avoids making either producer import a downstream semantic consumer
merely to share the type of the reset payload.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Exact executable call state -/

/-- `update_fast_confirmation_variables` never writes `confirmed_root` (it
rotates only the slot-head and observed-checkpoint fields). -/
theorem update_fcv_confirmed_root (fcrStore : FastConfirmationStore Root) :
    (update_fast_confirmation_variables cfg fcrStore).confirmed_root =
      fcrStore.confirmed_root := by
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- The variable-updated FCR store at a slot boundary: `E.fcr v n` re-seated
on the current store and run through `update_fast_confirmation_variables`,
before `get_latest_confirmed` is evaluated. -/
def fcrStep (v : ValidatorIndex) (n : ℕ) : FastConfirmationStore Root :=
  update_fast_confirmation_variables cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- `fcrStep`'s confirmed-root input is the previous `E.confirmed`. -/
theorem fcrStep_confirmed_root (v : ValidatorIndex) (n : ℕ) :
    (E.fcrStep cfg ext v n).confirmed_root = E.confirmed cfg ext v n := by
  rw [Execution.fcrStep, update_fcv_confirmed_root]
  rfl

/-- `fcrStep`'s store is the current-second store. -/
theorem fcrStep_store (v : ValidatorIndex) (n : ℕ) :
    (E.fcrStep cfg ext v n).store = E.store cfg ext v (n + 1) := by
  rw [Execution.fcrStep]
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- The actual call from `n` to `n+1` advanced a slot. -/
def IsFCRCallAt (v : ValidatorIndex) (n : ℕ) : Prop :=
  get_current_slot cfg (E.store cfg ext v (n + 1)) >
    get_current_slot cfg (E.store cfg ext v n)

/-! ## Safety-free reset payload -/

/-- Concrete certificate evidence for the two non-carried reset candidates of
an actual FCR invocation.  Global FFG origins construct this interface.  It
contains only root knownness and a conditional certificate for the reset
block's epoch checkpoint; it contains no FCR ancestry, safety, canonicality,
filter, source, placement, takeover, or historical conclusion. -/
def ActualResetInputCheckpointRealization
    (anchor : Checkpoint Root) (v : ValidatorIndex) : Prop :=
  ∀ n : ℕ, E.WithinHorizon cfg (n + 1) → ∀ input : Root,
    (input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
      input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
    input ∈ (E.fcrStep cfg ext v n).store.block_roots ∧
      (get_block_epoch cfg (E.fcrStep cfg ext v n).store input =
          get_current_store_epoch cfg (E.fcrStep cfg ext v n).store →
        Nonempty (CertifiedJustified cfg E anchor
          (get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store input
            (get_block_epoch cfg (E.fcrStep cfg ext v n).store input))))

end Execution

end FastConfirmation.Spec

end
