import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import FastConfirmation.Paper.Core.Model.Time

/-!
# Core / Model / Validators

Validators, rational weights, balance sources (anchors), per-slot committees,
and the fault model (the adversarial-weight *bound*, not the adversary's
identity). The paper allows an infinite validator set; we use `Fin n` plus
finite per-slot committees, which is all the §3.1 weights read.
-/

namespace FastConfirmation

/-- A validator is an index in `Fin n`. -/
abbrev Validator (n : ℕ) := Fin n

/-- Weights/balances are exact rationals. -/
abbrev Weight := ℚ

/-- A balance source: an effective-balance assignment. In the paper this is the
    balance assignment anchored at a checkpoint `C`; here it is abstract. -/
structure Stakes (n : ℕ) where
  bal : Validator n → Weight
  hpos : ∀ i, 0 < bal i

/-- An **anchor** `C` is a balance source. §3.1 uses it only as such; the
    checkpoint/justification structure behind it lives in the HFC layer. -/
abbrev Anchor (n : ℕ) := Stakes n

/-- Total weight of a validator set under an anchor. -/
def totalWeight {n : ℕ} (A : Anchor n) (X : Finset (Validator n)) : Weight :=
  ∑ i ∈ X, A.bal i

/-- Per-slot committee assignment. -/
structure Committees (n : ℕ) where
  member : Slot → Finset (Validator n)

/-- The fault model carries the honest validator set and the adversarial-weight
    *bound* `β < 1/3`. It deliberately does **not** carry the adversary's identity or a
    weight bound on it:

    * the **adversary is the complement** `Finset.univ \ honest` — the proofs always read
      it as `univ.filter (· ∉ honest)`, never as a stored set; and
    * the actual **adversary-weight bound is anchor-relative** — `totalWeight C` depends on
      the balance anchor `C`, which a `FaultModel` does not carry — so it cannot live here.

    The β↔weight bridge is therefore supplied where an anchor is in scope, as an explicit
    theorem premise: `CommitteeHonestMajority` (Assumption 2, committee-level: honest weight
    `≥ (1−β)·`total) for §3.1, and the global Byzantine bound
    `totalWeight C (univ \ honest) ≤ β · totalWeight C univ` for §4. So `hβ` is only the bare
    bound (`hβ0` its nonnegativity); `β` constrains the adversary *only* through those
    premises. Monotonicity additionally needs Assumption 4 (`β < (1 − pb)/4`). -/
structure FaultModel (n : ℕ) where
  honest : Finset (Validator n)
  β : Weight
  hβ0 : 0 ≤ β
  hβ : β < 1 / 3

/-- **The global Byzantine bound** (anchor-relative): the total weight of non-honest
    validators is at most `β` of the total, measured at anchor `C`. The §4 statement of
    "the adversary controls less than `β` of stake"; it lives as a premise (not a
    `FaultModel` field) because it depends on the balance anchor `C` — see `FaultModel`. -/
def GlobalByzantineBound {n : ℕ} (C : Anchor n) (fm : FaultModel n) : Prop :=
  totalWeight C (Finset.univ.filter (fun i => i ∉ fm.honest)) ≤ fm.β * totalWeight C Finset.univ

end FastConfirmation
