module
public import FastConfirmationStatements.Premises.NextSlotSafety

@[expose] public section

/-! Defines the confirmed support package and the future honest head invariant. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The confirmation-time support package for `b` at confirming slot `s`:
the honest supporters `HS₀`, each with a **newest pre-`s` vote** whose block
descends from `b` — stated on the execution's own vote record (`E.vote`),
hence node-independent — and the frozen old-window majority inequality
(`Wold`/`D`/`discount` are the confirmation-time quantities; `boost` the
registry-constant proposer score). -/
structure ConfirmedSupport (E : Execution Root) (b : Root) (s : Slot)
    (v₀ : ValidatorIndex) (n₀ : ℕ)
    (HS₀ : Finset ValidatorIndex) (Wold D discount boost : ℕ) : Prop where
  /-- supporters are honest. -/
  honest : ∀ i ∈ HS₀, i ∈ E.honest
  /-- each supporter's newest pre-`s` vote supports `b`: a vote at slot
      `t < s`, no later vote before `s`, and the vote block descends from
      `b` at the confirming store (`v₀`/`n₀`) — the store-indexed support
      fact, transported to later stores via cross-store block agreement. -/
  votes : ∀ i ∈ HS₀, ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t < s ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' < s → E.vote i t' = none) ∧
    is_ancestor (E.store cfg ext v₀ n₀)
      (get_node_for_root a.data.beacon_block_root)
      (get_node_for_root b) = true
  /-- the frozen ledger inequality (`honest_support_majority` at the
      confirming node, `H₀ := E.weight HS₀`). -/
  majority : Wold + boost + 1 ≤ 2 * E.weight HS₀ + discount
  /-- the discount is covered by the stuck-set weight. -/
  discount_le : discount ≤ D

/-- The engine invariant: through slot `k`, every honest node's head descends
from `b` at every second from `n₀` on inside the modeled finite execution
segment. This retains the pinned executable spec's current-moment target. -/
def EngineInv (E : Execution Root) (b : Root) (n₀ : ℕ) (k : Slot) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m → E.slot_at cfg m ≤ k →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root b) = true

end FastConfirmation.Spec

end
