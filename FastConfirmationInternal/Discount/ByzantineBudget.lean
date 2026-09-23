module
public import FastConfirmationInternal.Discount.SupportClasses

@[expose] public section

/-! Defines recorded Byzantine enemy sets and the second ledger invariant. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

open Classical in
/-- `BbadSet` — the base enemy in **recorded** form (`recorded-base reduction` reshape): non-honest,
`(v₀, n₀)`-non-equivocating members of the window `[lo, es]` whose **recorded** latest
message at `(v₀, n₀)` is **sibling-ward** — recorded neither `b′`-supporting
(`¬ lm.root ⪰ b′`) nor a `b′`-ancestor (`¬ b′ ⪰ lm.root`). Byzantine enemies are only
knowable through the store's recorded latest message (there is no
`HonestBehavior.no_forgery` for byz, so the ground `E.vote` and the recorded message
diverge); this is the recorded analog of `Xclass es`, definitionally equal to
`ByzVpre.RecByzSibBase cfg ext v₀ n₀ b′ lo es`. It still excludes `Bsup`, `Bpar` and
the relayed equivocators, and sits inside the window byz set `Bwin lo es` (only the
`span_committee`/`∉ honest` prefix is read by the accounting). -/
noncomputable def BbadSet (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo es).filter (fun i => i ∉ E.honest)).filter
    (fun i => i ∉ (E.store cfg ext v₀ n₀).equivocating_indices ∧
      ∀ lm : LatestMessage Root, (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        ¬ is_ancestor (E.store cfg ext v₀ n₀)
            (get_node_for_root lm.root) (get_node_for_root b') = true ∧
        ¬ is_ancestor (E.store cfg ext v₀ n₀)
            (get_node_for_root b') (get_node_for_root lm.root) = true)

/-- `SpentSet σ` — the byz of the tail window `(es, σ]`; their per-slot votes pay
`span_fraction` capacity. -/
def SpentSet (es σ : Slot) : Finset ValidatorIndex :=
  (E.span_committee (es + 1) σ).filter (fun i => i ∉ E.honest)

/-- `Bbad` — base-enemy weight. -/
noncomputable def BbadVal (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) : Gwei :=
  E.weight (E.BbadSet cfg ext v₀ n₀ b' lo es)



end Execution

end FastConfirmation.Spec

end
