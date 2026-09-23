module
public import FastConfirmationModel.Weak.WeakSynchrony

@[expose] public section

/-! Execution of the weak rule at scheduled calls. -/

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

end Execution
end FastConfirmation.Spec

end
