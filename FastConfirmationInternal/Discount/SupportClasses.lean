module
public import FastConfirmationInternal.Discount.CommitteeWeight
public import FastConfirmationInternal.Discount.HeadSafetyInvariant

@[expose] public section

/-! Defines honest vote classes, their weights, and the first ledger invariant. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- `i`'s newest vote by `σ` **supports `subtree(b′)`**: there is a vote at some
slot `t ≤ σ` with no later vote through `σ`, whose block descends from `b′` at the
confirming store (`b′` is an ancestor of the vote block). Mirrors
`ConfirmedSupport.votes`, parameterized by the window end `σ`. -/
def SupportsDesc (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ : Slot)
    (i : ValidatorIndex) : Prop :=
  ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t ≤ σ ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' ≤ σ → E.vote i t' = none) ∧
    is_ancestor (E.store cfg ext v₀ n₀)
      (get_node_for_root a.data.beacon_block_root) (get_node_for_root b') = true

/-- `i` **backs no sibling** of `b′` by `σ`: either it has cast no vote through
`σ` (voteless), or its newest vote's block is an **ancestor of** `b′` (`b′`
descends from the vote block — the reversed `is_ancestor` orientation). -/
def AncestorOrVoteless (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (σ : Slot)
    (i : ValidatorIndex) : Prop :=
  (∀ t' : Slot, t' ≤ σ → E.vote i t' = none) ∨
  (∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t ≤ σ ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' ≤ σ → E.vote i t' = none) ∧
    is_ancestor (E.store cfg ext v₀ n₀)
      (get_node_for_root b') (get_node_for_root a.data.beacon_block_root) = true)

open Classical in
/-- `Sclass σ` — honest window members whose newest vote by `σ` supports
`subtree(b′)`; weight `s(σ)`. -/
noncomputable def Sclass (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => E.SupportsDesc cfg ext v₀ n₀ b' σ i)

open Classical in
/-- `Aclass σ` — honest window members that are **not** `Sclass` and back no
sibling of `b′` (voteless or ancestor-voting); weight `a(σ)`. The `¬S` guard
keeps `Sclass`/`Aclass` disjoint. -/
noncomputable def Aclass (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => ¬ E.SupportsDesc cfg ext v₀ n₀ b' σ i ∧
      E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i)

open Classical in
/-- `Xclass σ` — the remaining honest window members (`¬S ∧ ¬A`; sibling-stuck);
weight `x(σ)`. -/
noncomputable def Xclass (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => ¬ E.SupportsDesc cfg ext v₀ n₀ b' σ i ∧
      ¬ E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i)

/-- `Bwin σ` — the window's non-honest members (the enemy set; weight `B(σ)`). -/
def Bwin (lo σ : Slot) : Finset ValidatorIndex :=
  (E.span_committee lo σ).filter (fun i => i ∉ E.honest)

open Classical in
/-- `Unrec σ` — the not-yet-recurred **base** supporters: `Sclass es` members with
no committee assignment in `(es, σ]`; weight `U(σ)`. Their future recurrence
slots are the only pay-go-free byz-arrival opportunities. -/
noncomputable def Unrec (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) :
    Finset ValidatorIndex :=
  (E.Sclass cfg ext v₀ n₀ b' lo es).filter
    (fun i => ∀ t : Slot, es < t → t ≤ σ → i ∉ E.committee t)

/-- `s(σ)` — `Sclass` weight. -/
noncomputable def Sval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) : Gwei :=
  E.weight (E.Sclass cfg ext v₀ n₀ b' lo σ)

/-- `a(σ)` — `Aclass` weight. -/
noncomputable def Aval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) : Gwei :=
  E.weight (E.Aclass cfg ext v₀ n₀ b' lo σ)

/-- `x(σ)` — `Xclass` weight. -/
noncomputable def Xval (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot) : Gwei :=
  E.weight (E.Xclass cfg ext v₀ n₀ b' lo σ)

/-- `B(σ)` — enemy (non-honest window) weight. -/
noncomputable def Bval (lo σ : Slot) : Gwei :=
  E.weight (E.Bwin lo σ)



end Execution

end FastConfirmation.Spec

end
