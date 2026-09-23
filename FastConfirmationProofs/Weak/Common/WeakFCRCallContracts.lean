module
public import FastConfirmationModel.Weak.Execution
public import FastConfirmationProofs.FCRRule.FCRCallContracts

@[expose] public section

/-!
# Spec / Proof / WeakFCRCallContracts

Weak-model actual-call scaffolding. Mirrors `FCRCallContracts.lean`'s
`Execution.fcr` / `Execution.fcrStoreAtCall` / `Execution.confirmed` over the weak
bookkeeping functions (`Weak.on_fast_confirmation`,
`Weak.update_fast_confirmation_variables`, rule delta 5 —
`Spec/Model/WeakSynchrony.lean`).

`Execution.IsScheduledFCRCallAt` is a pure clock predicate over `E.store` — it names
only "the store's slot advanced from `n` to `n+1`" and mentions no
bookkeeping function at all — so it is reused verbatim for the weak
trajectory; no `weakIsFCRCallAt` twin is defined here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- `weakFcrStep`'s confirmed-root input is the previous `E.weakConfirmed`
(mirrors `Execution.fcrStep_confirmed_root`). -/
theorem weakFcrStep_confirmed_root (v : ValidatorIndex) (n : ℕ) :
    (E.weakFcrStep cfg ext v n).confirmed_root = E.weakConfirmed cfg ext v n := by
  rw [Execution.weakFcrStep]
  simp only [Weak.update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- `weakFcrStep`'s store is the current-second store (mirrors
`Execution.fcrStep_store`). -/
theorem weakFcrStep_store (v : ValidatorIndex) (n : ℕ) :
    (E.weakFcrStep cfg ext v n).store = E.store cfg ext v (n + 1) := by
  rw [Execution.weakFcrStep]
  simp only [Weak.update_fast_confirmation_variables]
  split_ifs <;> rfl

end Execution

end FastConfirmation.Spec

end
