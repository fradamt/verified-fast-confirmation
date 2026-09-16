import FastConfirmation.Spec.Proof.EngineStore
import FastConfirmation.Spec.Proof.HeadReroot

/-!
# Spec / Proof / HeadRerootChain: the mid-walk `DescendStep`-chain adapter

This is the mid-walk analogue of `Endpoint.head_descends_of_ledger` and
`EngineStore.is_ancestor_get_head_of_chain`: those fold a `DescendStep` chain
rooted at the store's **own** `justified_checkpoint.root`;
`head_ge_of_intermediate_ledger` folds one rooted at an arbitrary mid-chain node `x` that the head
already descends from (`head ⪰ x`) and that itself descends from the justified root (`x ⪰ jc.root`).

It converts the chain to a `DescendsTo` path (`EngineStore.descendsTo_of_chain`) and closes with
`HeadReroot.head_ge_of_intermediate_chain`. `AnchorClose`'s advance leg supplies `head ⪰ r₀` from
the anchor's own threaded `SafeFrom` witness, `r₀ ⪰ jc.root` from chain comparability on `b`'s
chain, and the `r₀`-rooted `DescendStep` chain from the `r₀`-scoped supply — exactly this lemma's
inputs.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-- **Mid-walk `DescendStep`-chain fold.** The re-rooted `head_descends_of_ledger`: a `DescendStep`
chain from `x` down to `b` (each fork's `x`-side child dominating every sibling), together with
`head ⪰ x` and `x ⪰ jc.root`, forces `head ⪰ b`. Composes `descendsTo_of_chain` with
`head_ge_of_intermediate_chain`. This is the adapter used by case (iii) of the covering fold. -/
theorem head_ge_of_intermediate_ledger {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {x b : Root} {ds : List Root} (hx : x ∈ store.block_roots)
    (hxj : is_ancestor store (get_node_for_root x)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hhx : is_ancestor store (get_head cfg store) (get_node_for_root x) = true)
    (hb : b ∈ store.block_roots)
    (hchain : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store)) (x :: ds))
    (hlast : (x :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
  head_ge_of_intermediate_chain cfg hwf hsub hwalk hjust hx hxj hhx
    (descendsTo_of_chain cfg hb ds x hchain hlast)

end FastConfirmation.Spec
