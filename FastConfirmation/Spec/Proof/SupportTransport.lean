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
    (hsupp : is_ancestor store (ForkChoiceNode.mk mroot .pending) (ForkChoiceNode.mk b .pending) = true)
    (hbc : is_ancestor store (ForkChoiceNode.mk b .pending) (ForkChoiceNode.mk c .pending) = true) :
    is_ancestor store (ForkChoiceNode.mk mroot .pending) (ForkChoiceNode.mk c .pending) = true :=
  is_ancestor_trans hwf hwa hwb hsupp hbc

/-! ## Score monotonicity along a known chain -/

variable (cfg : Config)


/-! ## Sibling disjointness -/


end FastConfirmation.Spec

end
