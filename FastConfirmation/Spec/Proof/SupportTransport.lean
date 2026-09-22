module
public import FastConfirmation.Spec.Proof.Forks

@[expose] public section

/-!
# Spec / Proof / SupportTransport

Layer 0, the head-safety engine's step **E2**: *support transports down a
known chain*. Built on `Proof/AncestryRoots.lean`'s `is_ancestor_trans` and
`Proof/Forks.lean`'s `siblings_incompatible`.

`get_attestation_score store node state` counts the weight of the unslashed,
active, non-equivocating validators whose latest-message root is an ancestor of
`node` (a *supporter* of `node`). The single behavioral fact here is that
support is downward-closed on a known ancestry chain: an index that supports a
block `b` also supports every chain-ancestor `c` of `b` (`is_ancestor_trans`),
so the supporter set of `c` contains that of `b`, and — the map to effective
balances being nonnegative — the score is monotone: `score c ≥ score b`.

The disjointness corollary reads off `Forks.siblings_incompatible`: a single
validator's latest message cannot support two distinct siblings.

Every lemma carries the `parent_slot_lt`-shaped `hwf` (exactly
`WellFormedStore.parent_slot_lt`) plus `WalkKnown` witnesses pinning the walks
down to the ancestor's slot — the same domain discipline as `Proof/Forks.lean`.
No new behavioral assumptions enter.
-/

namespace FastConfirmation.Spec

/-- Sum monotonicity under sublist for `ℕ`-valued lists (dropping elements can
only shrink the sum). A small local helper standing in for the multiplicative
`List.Sublist.prod_le_prod'` on the additive `ℕ` side. -/
private theorem sum_le_sum_of_sublist {l₁ l₂ : List ℕ} (h : List.Sublist l₁ l₂) :
    l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => exact le_refl _
  | cons a _ ih => rw [List.sum_cons]; exact ih.trans (Nat.le_add_left _ _)
  | cons_cons a _ ih => rw [List.sum_cons, List.sum_cons]; exact Nat.add_le_add_left ih a

variable {Root : Type*} [LinearOrder Root]

/-! ## Single-supporter transport -/

/-- **Support transports down a chain (one supporter).** If a validator's
latest-message root `mroot` supports `b` (`is_ancestor store (mk mroot) (mk b)`)
and `c` is a chain-ancestor of `b` (`is_ancestor store (mk b) (mk c)`), then that
root also supports `c`. A thin frame over `is_ancestor_trans`; the `WalkKnown`
witnesses pin both parent-walks down to `c`'s slot. -/
theorem supporter_of_ancestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {mroot b c : Root}
    (hwa : WalkKnown store (store.blocks c).slot mroot)
    (hwb : WalkKnown store (store.blocks c).slot b)
    (hsupp : is_ancestor store (ForkChoiceNode.mk mroot) (ForkChoiceNode.mk b) = true)
    (hbc : is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true) :
    is_ancestor store (ForkChoiceNode.mk mroot) (ForkChoiceNode.mk c) = true :=
  is_ancestor_trans hwf hwa hwb hsupp hbc

/-! ## Score monotonicity along a known chain -/

variable (cfg : Config)

/-- **The attestation score is monotone down a known chain.** With `c` a
chain-ancestor of `b` (`hbc`), every supporter of `b` is a supporter of `c`
(`supporter_of_ancestor`), so the supporter list of `c` is a superlist of that
of `b`; the map to effective balances being into `ℕ`, the summed score can only
grow: `score c ≥ score b`. The `hwalk` domain condition supplies, for each
supporter of `b`, the `WalkKnown` witness that `is_ancestor_trans` needs. -/
theorem attestation_score_mono_of_ancestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {b c : Root} (state : BeaconState Root)
    (hwb : WalkKnown store (store.blocks c).slot b)
    (hbc : is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      is_ancestor store (ForkChoiceNode.mk lm.root) (ForkChoiceNode.mk b) = true →
      WalkKnown store (store.blocks c).slot lm.root) :
    get_attestation_score cfg store (ForkChoiceNode.mk b) state ≤
      get_attestation_score cfg store (ForkChoiceNode.mk c) state := by
  simp only [get_attestation_score, get_supported_node]
  refine sum_le_sum_of_sublist ?_
  refine List.Sublist.map _ ?_
  refine List.monotone_filter_right _ ?_
  intro i hib
  cases hlm : store.latest_messages i with
  | none => simp [hlm] at hib
  | some lm =>
    simp only [hlm, Bool.and_eq_true] at hib ⊢
    exact ⟨hib.1, is_ancestor_trans hwf (hwalk i lm hlm hib.2) hwb hib.2 hbc⟩

/-! ## Sibling disjointness -/

/-- **No validator supports two distinct siblings.** A single latest message
`lm` cannot support both `c` and `c'` when these are distinct children of one
parent `p`: `Forks.siblings_incompatible` rules out a common descendant, and
`lm.root` (the supported node) would be a common ancestor of both. The
`WalkKnown` witnesses pin `lm.root`'s parent-walk down to each sibling's slot,
exactly as `siblings_incompatible` requires. -/
theorem no_index_supports_both_siblings {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {p c c' : Root} {lm : LatestMessage Root}
    (hc : c ∈ store.block_roots) (hc' : c' ∈ store.block_roots)
    (hp : p ∈ store.block_roots)
    (hpc : (store.blocks c).parent_root = p)
    (hpc' : (store.blocks c').parent_root = p)
    (hne : c ≠ c')
    (hwc : WalkKnown store (store.blocks c).slot lm.root)
    (hwc' : WalkKnown store (store.blocks c').slot lm.root)
    (hsc : is_ancestor store (get_supported_node store lm) (ForkChoiceNode.mk c) = true)
    (hsc' : is_ancestor store (get_supported_node store lm) (ForkChoiceNode.mk c') = true) :
    False := by
  simp only [get_supported_node] at hsc hsc'
  exact siblings_incompatible hwf hc hc' hp hpc hpc' hne hwc hwc' hsc hsc'

end FastConfirmation.Spec

end
