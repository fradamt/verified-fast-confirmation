import FastConfirmation.Spec.Model.WeakSynchrony
import FastConfirmation.Spec.Proof.FCRCallContracts

/-!
# Spec / Proof / WeakFCRCallContracts

Weak-model actual-call scaffolding. Mirrors `FCRCallContracts.lean`'s
`Execution.fcr` / `Execution.fcrStep` / `Execution.confirmed` over the weak
bookkeeping functions (`Weak.on_fast_confirmation`,
`Weak.update_fast_confirmation_variables`, rule delta 5 —
`Spec/Model/WeakSynchrony.lean`).

`Execution.IsFCRCallAt` is a pure clock predicate over `E.store` — it names
only "the store's slot advanced from `n` to `n+1`" and mentions no
bookkeeping function at all — so it is reused verbatim for the weak
trajectory; no `weakIsFCRCallAt` twin is defined here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Node `v`'s weak fast-confirmation store at relative second `n`: as
`Execution.fcr`, but running `Weak.on_fast_confirmation` (rule delta 5)
instead of the strong handler at each slot advance. The read-only `store`
snapshot still tracks `E.store v n`; `on_fast_confirmation` still fires
exactly at the first second of each slot (detected as the slot advancing),
after that second's events. -/
def weakFcr (v : ValidatorIndex) : ℕ → FastConfirmationStore Root
  | 0 => get_fast_confirmation_store (E.store cfg ext v 0)
  | n + 1 =>
    let fcr_store := { weakFcr v n with store := E.store cfg ext v (n + 1) }
    if get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n) then
      Weak.on_fast_confirmation cfg ext fcr_store
    else fcr_store

/-- Node `v`'s weak confirmed block root at relative second `n`. -/
def weakConfirmed (v : ValidatorIndex) (n : ℕ) : Root :=
  (E.weakFcr cfg ext v n).confirmed_root

/-- The weak variable-updated FCR store at a slot boundary: `E.weakFcr v n`
re-seated on the current store and run through
`Weak.update_fast_confirmation_variables` (rule delta 5), before
`Weak.get_latest_confirmed` is evaluated. Mirrors `Execution.fcrStep` with the
weak bookkeeping function substituted (hfilter architecture correction: the
two are not the same function — `Weak.update_fast_confirmation_variables`
also needs `ext`, for the certificate gate). -/
def weakFcrStep (v : ValidatorIndex) (n : ℕ) : FastConfirmationStore Root :=
  Weak.update_fast_confirmation_variables cfg ext
    { E.weakFcr cfg ext v n with store := E.store cfg ext v (n + 1) }

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
