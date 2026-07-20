import FastConfirmation.Spec.Proof.EngineWindows
import FastConfirmation.Spec.Proof.EngineSupport

/-!
# Spec / Proof / EngineInduction: the input package and invariant

The head-safety engine's induction vocabulary. `ConfirmedSupport` is the
confirmation-time package the L4 layer extracts from `is_one_confirmed` +
`honest_support_majority` at the confirming node: the honest supporter set
`HS₀` with per-member newest-vote facts (node-independent objects — a
validator's newest pre-`s` vote is the same at every honest node once
delivered, which is what makes the majority transportable), plus the frozen
old-window ledger inequality. `EngineInv` is the strong-induction invariant:
heads descend from `b` at every honest node through slot `k`.
-/

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

/-- The invariant is monotone downward in the slot bound. -/
theorem EngineInv.mono {E : Execution Root} {b : Root} {n₀ : ℕ} {k k' : Slot}
    (h : EngineInv cfg ext E b n₀ k) (hk : k' ≤ k) :
    EngineInv cfg ext E b n₀ k' :=
  fun w hw m hm hsl hH => h w hw m hm (le_trans hsl hk) hH

end FastConfirmation.Spec
