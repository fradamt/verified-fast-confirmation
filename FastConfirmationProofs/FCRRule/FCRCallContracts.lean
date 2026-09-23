module
public import FastConfirmationStatements.Premises.FFGCertificates

public import FastConfirmationStatements.Traces
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

/-! ## Safety-free reset payload -/


end Execution

end FastConfirmation.Spec

end
