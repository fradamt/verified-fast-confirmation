module
public import FastConfirmation.Spec.Proof.EngineTransport
public import FastConfirmation.Spec.Proof.Engine

@[expose] public section

/-!
# Spec / Proof / EngineStore (per-store head descent)

At a single honest store `(w, m)` in slot `k`, the transported engine facts and
the window ledger `EngineWindows.fork_majority_of_windows` provide a `b`-side dominant child
at every fork on `b`'s chain, and (via `FilterViability`) that every chain root
survives `get_filtered_block_tree`. This module wires those per-fork facts into a
`Descent.DescendsTo` path from the justified root down to `b` and concludes, via
`Descent.is_ancestor_get_head`, that the fork-choice head descends from `b`.

The per-fork data is packaged as one relation, `DescendStep`, between a node and
its chosen child: the child is a `get_node_children` member drawn from the
filtered tree, and it strictly dominates every sibling in `get_weight` — exactly
the pair (`hchild`, `hdom`) `Descent.DescendsTo.step` consumes, and exactly what
`EngineWindows.fork_majority_of_windows` produces per fork. A `List.Chain` of
`DescendStep` from the justified root down to `b` is the parent-linked dominant
path (`AncestryRoots`' `get_ancestor_roots` characterization supplies its
shape).

Contents:

* `DescendStep` — the per-fork child-choice relation (membership + domination).
* `descendsTo_of_chain` — a `List.Chain DescendStep` from `h` down to `b` builds a
  `DescendsTo … b … h` path (structural recursion over the chain).
* `chain_descendStep_mem` — every node on the chain is in the filtered tree (each
  is a `get_node_children` member): the subset feeding the fuel bound.
* `is_ancestor_get_head_of_chain` — the headline: under the descent chain (plus
  `Nodup` for the path-length/fuel discharge and the usual `parent_slot_lt` /
  filtered-containment domain conditions) the head descends from `b`.

Every transported fact — the per-fork dominance, the filtered-tree containment,
the `parent_slot_lt` well-formedness — enters in its delivered shape as a
hypothesis; this module is the pure wiring. No Model / TheoremStatements edits.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## The per-fork child-choice relation -/

/-- `DescendStep cfg store blocks h c`: `c` is the fork-choice-dominant child of
`h` in the candidate list `blocks`. It is a `get_node_children` member (drawn from
`blocks`, parent-linked to `h`) and it strictly dominates every other child of `h`
in `get_weight` — the exact `(hchild, hdom)` pair `Descent.DescendsTo.step`
consumes and `EngineWindows.fork_majority_of_windows` produces per fork. -/
def DescendStep (store : Store Root) (blocks : List Root) (h c : Root) : Prop :=
  ForkChoiceNode.mk c ∈ get_node_children store blocks (ForkChoiceNode.mk h) ∧
    ∀ c' ∈ get_node_children store blocks (ForkChoiceNode.mk h),
      c' ≠ ForkChoiceNode.mk c →
        get_weight cfg store c' < get_weight cfg store (ForkChoiceNode.mk c)

/-- **Assemble a `DescendStep` from per-sibling domination.** The `hdom` clause is
reindexed from sibling *roots* — the form `EngineWindows.fork_majority_of_windows`
delivers per fork (`get_weight (mk c') < get_weight (mk c)` for each competing root
`c'`) — to the `ForkChoiceNode` children `DescendStep` records. -/
theorem descendStep_of_dom {store : Store Root} {blocks : List Root} {h c : Root}
    (hchild : ForkChoiceNode.mk c ∈ get_node_children store blocks (ForkChoiceNode.mk h))
    (hdom : ∀ c' : Root,
      ForkChoiceNode.mk c' ∈ get_node_children store blocks (ForkChoiceNode.mk h) →
        c' ≠ c →
          get_weight cfg store (ForkChoiceNode.mk c') <
            get_weight cfg store (ForkChoiceNode.mk c)) :
    DescendStep cfg store blocks h c := by
  refine ⟨hchild, ?_⟩
  rintro ⟨cr⟩ hc'' hne
  exact hdom cr hc'' (fun heq => hne (by rw [heq]))

/-! ## The descent chain builds a `DescendsTo` path -/

/-- A `List.IsChain DescendStep` over `h :: ds` ending at `b` (the last node of
`h :: ds`) is a `Descent.DescendsTo … b ds.length h` path. Structural recursion on
`ds`, `h` general: the `nil` base forces `h = b` (`DescendsTo.here`); each `cons`
peels one dominant child (`DescendsTo.step`) and recurses. -/
theorem descendsTo_of_chain {store : Store Root} {blocks : List Root} {b : Root}
    (hb : b ∈ store.block_roots) :
    ∀ (ds : List Root) (h : Root),
      List.IsChain (DescendStep cfg store blocks) (h :: ds) →
      (h :: ds).getLast (List.cons_ne_nil h ds) = b →
      DescendsTo cfg store blocks b ds.length h := by
  intro ds
  induction ds with
  | nil =>
    intro h _ hlast
    have hhb : h = b := hlast
    subst hhb
    exact DescendsTo.here hb
  | cons a rest ih =>
    intro h hchain hlast
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hstep, hchain'⟩ := hchain
    have hlast' : (a :: rest).getLast (List.cons_ne_nil a rest) = b :=
      (List.getLast_cons (List.cons_ne_nil a rest)).symm.trans hlast
    exact DescendsTo.step hstep.1 hstep.2 (ih a hchain' hlast')

/-! ## The descent nodes live in the filtered tree -/

/-- Every non-root node on a `DescendStep` chain sits in the candidate list
`blocks`: each is a chosen `get_node_children` member, whose root is drawn from
`blocks` (`mem_get_node_children`). This is the subset feeding the path-length /
fuel bound. -/
theorem chain_descendStep_mem {store : Store Root} {blocks : List Root} :
    ∀ (ds : List Root) (h : Root),
      List.IsChain (DescendStep cfg store blocks) (h :: ds) →
      ∀ c ∈ ds, c ∈ blocks := by
  intro ds
  induction ds with
  | nil => intro _ _ c hc; exact absurd hc List.not_mem_nil
  | cons a rest ih =>
    intro h hchain c hc
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hstep, hchain'⟩ := hchain
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact (mem_get_node_children.mp hstep.1).1
    · exact ih a hchain' c hc

omit [Inhabited Root] in
/-- A `Nodup` list injects into any list it is a subset of, so its length is
bounded (`toFinset` card comparison). The path-length discharge for the fuel
hypothesis of `Descent.is_ancestor_get_head`. -/
private theorem length_le_of_nodup_subset {l₁ l₂ : List Root}
    (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) : l₁.length ≤ l₂.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  have hfs : l₁.toFinset ⊆ l₂.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact hsub hx
  exact le_trans (Finset.card_le_card hfs) (List.toFinset_card_le (l := l₂))

/-! ## The headline: the head descends from `b` -/

/-- **Per-store head descent.** At an honest store, a `DescendStep` chain from the
justified checkpoint root down to `b` (each fork's `b`-side child dominating every
sibling — `EngineWindows.fork_majority_of_windows` per fork — over roots in the
filtered tree) forces the fork-choice head to descend from `b`. The path's `Nodup`
discharges the fuel bound (its nodes are distinct filtered roots); `hwf`
(`parent_slot_lt`) and `hsub` (filtered-tree containment) are the usual domain
conditions, ``Preservation``/``FilterViability`` establish them. Composes `descendsTo_of_chain` with
`Descent.is_ancestor_get_head`. -/
theorem is_ancestor_get_head_of_chain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  have hdesc := descendsTo_of_chain cfg hb ds store.justified_checkpoint.root hchain hlast
  have hmem := chain_descendStep_mem cfg ds store.justified_checkpoint.root hchain
  have hfuel : ds.length ≤ (get_filtered_block_tree cfg store).length + 1 :=
    Nat.le_succ_of_le (length_le_of_nodup_subset hnd (fun c hc => hmem c hc))
  change is_ancestor store (get_head cfg store) (ForkChoiceNode.mk b) = true
  exact is_ancestor_get_head cfg hwf hsub hdesc hfuel

/-! ## The filter complement: filtered roots descend from the justified root

The FFG branch uses the filter rather than the LMD margin. Once the justified checkpoint's block is
on `b`'s chain in an honest store, every filtered branch descends from the
justified root, so the head — itself a filtered root — descends from `b`, with
no weight accounting.

The walk-known plumbing enters as one blanket hypothesis `hwalk`: the store is
ancestor-closed, so every known root's parent-walk down to any terminal slot
stays known (the `WalkKnown` ∀-form the toolkit sanctions). -/

omit [Inhabited Root] in
/-- One parent step of `is_ancestor`: a known block whose `parent_root` is a
known block `base` descends from `base`. The walk from the child down to
`base`'s slot steps once (to `base`) and stops; the strict slot drop
`base.slot < child.slot` comes from `hwf` (`parent_slot_lt`). -/
theorem is_ancestor_of_parent {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {child base : Root}
    (hchild : child ∈ store.block_roots) (hbase : base ∈ store.block_roots)
    (hp : (store.blocks child).parent_root = base) :
    is_ancestor store (ForkChoiceNode.mk child) (ForkChoiceNode.mk base) = true := by
  simp only [is_ancestor, decide_eq_true_eq]
  show get_ancestor store (ForkChoiceNode.mk child) (store.blocks base).slot
      = ForkChoiceNode.mk base
  have hlt : (store.blocks base).slot < (store.blocks child).slot := by
    have h := hwf child hchild (by rw [hp]; exact hbase)
    rwa [hp] at h
  rw [get_ancestor_step hwf hchild hlt
    (by rw [hp]; exact WalkKnown.stop hbase (le_refl _))]
  rw [hp]
  exact get_ancestor_stop (le_refl _)

omit [Inhabited Root] in
/-- Inductive step of `filter_block_tree_aux_output_descends`: a root `r` in a
child subtree's output descends from that child (`ih`), the child descends from
`base` (`is_ancestor_of_parent`), so `r` descends from `base` by transitivity.
The `WalkKnown` witnesses come from the blanket `hwalk`. -/
private theorem output_descends_step {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ store.block_roots →
      WalkKnown store (store.blocks t).slot r)
    {base : Root} (hbase : base ∈ store.block_roots) {fuel : ℕ}
    (ih : ∀ b' : Root, b' ∈ store.block_roots → ∀ r,
      r ∈ (filter_block_tree_aux cfg store fuel b').2 →
        is_ancestor store (ForkChoiceNode.mk r) (ForkChoiceNode.mk b') = true)
    {child r : Root}
    (hchild : child ∈ store.block_roots.filter
      (fun root => (store.blocks root).parent_root = base))
    (hrl : r ∈ (filter_block_tree_aux cfg store fuel child).2) :
    is_ancestor store (ForkChoiceNode.mk r) (ForkChoiceNode.mk base) = true := by
  have hchild_mem : child ∈ store.block_roots := (List.mem_filter.mp hchild).1
  have hp : (store.blocks child).parent_root = base := by
    have h := (List.mem_filter.mp hchild).2
    simpa using h
  have hac := ih child hchild_mem r hrl
  have hcb := is_ancestor_of_parent hwf hchild_mem hbase hp
  have hr_mem : r ∈ store.block_roots := by
    rcases filter_block_tree_aux_output_mem cfg _ _ _ hrl with h | h
    · exact h
    · rw [h]; exact hchild_mem
  exact is_ancestor_trans hwf (hwalk base r hr_mem) (hwalk base child hchild_mem) hac hcb

omit [Inhabited Root] in
/-- **Filter-output descent.** Every root the `filter_block_tree` worker emits
from `base` descends from `base`: outputs are `base` itself (`is_ancestor_refl`)
or outputs of a child subtree, which descend from their child and hence from
`base` (`output_descends_step`). Mirrors `Engine.filter_block_tree_aux_output_mem`,
tracking descent instead of membership. -/
theorem filter_block_tree_aux_output_descends {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ store.block_roots →
      WalkKnown store (store.blocks t).slot r) :
    ∀ (fuel : ℕ) (base : Root), base ∈ store.block_roots →
      ∀ r, r ∈ (filter_block_tree_aux cfg store fuel base).2 →
        is_ancestor store (ForkChoiceNode.mk r) (ForkChoiceNode.mk base) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro base _ r hr
    simp only [filter_block_tree_aux] at hr
    exact absurd hr List.not_mem_nil
  | succ fuel ih =>
    intro base hbase r hr
    by_cases hne :
      store.block_roots.filter (fun x => (store.blocks x).parent_root = base) ≠ []
    · rw [filter_block_tree_aux_internal cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr
      · rcases List.mem_append.mp hr with hr' | hr'
        · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr'
          obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
          exact output_descends_step cfg hwf hwalk hbase ih hchild hrl
        · rw [List.mem_singleton] at hr'
          subst hr'
          exact is_ancestor_refl store _
      · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr
        obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
        exact output_descends_step cfg hwf hwalk hbase ih hchild hrl
    · rw [not_not] at hne
      rw [filter_block_tree_aux_leaf cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr
      · rw [List.mem_singleton] at hr
        subst hr
        exact is_ancestor_refl store _
      · exact absurd hr List.not_mem_nil

omit [Inhabited Root] in
/-- **Every filtered root descends from the justified root.**
`filter_block_tree_aux_output_descends` at `base := justified_checkpoint.root`,
which `get_filtered_block_tree` uses as the tree root. This is the filter-side
complement to the per-fork LMD argument. -/
theorem filtered_through_justified {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ store.block_roots →
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {r : Root} (hr : r ∈ get_filtered_block_tree cfg store) :
    is_ancestor store (get_node_for_root r)
      (get_node_for_root store.justified_checkpoint.root) = true := by
  simp only [get_node_for_root]
  have hr' : r ∈ (filter_block_tree_aux cfg store (store.block_roots.length + 1)
      store.justified_checkpoint.root).2 := hr
  exact filter_block_tree_aux_output_descends cfg hwf hwalk _ _ hjust r hr'

/-- **FFG takeover head lemma.** Once the justified checkpoint's block descends
from `b`, so does the fork-choice head, with no LMD weight margin. The head is a
filtered root (`Engine.get_head_aux_root_mem_or`) descending from the justified
root (`filtered_through_justified`), which descends from `b` (`hjb`) — transitivity;
or the head degenerately stays at the justified root, where `hjb` applies directly.
THE punchline of `EngineStore`: once the justified block is on `b`'s chain, the filter alone
forces every head above `b`. -/
theorem head_ge_of_justified_ge {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ store.block_roots →
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {b : Root}
    (hjb : is_ancestor store (get_node_for_root store.justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  simp only [get_node_for_root] at hjb ⊢
  have hmem : (get_head cfg store).root ∈ get_filtered_block_tree cfg store ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg ((get_filtered_block_tree cfg store).length + 1)
      (ForkChoiceNode.mk store.justified_checkpoint.root)
  rcases hmem with hin | heq
  · have hgt := filtered_through_justified cfg hwf hwalk hjust hin
    simp only [get_node_for_root] at hgt
    have hqr_mem : (get_head cfg store).root ∈ store.block_roots := by
      have hin' : (get_head cfg store).root ∈
          (filter_block_tree_aux cfg store (store.block_roots.length + 1)
            store.justified_checkpoint.root).2 := hin
      rcases filter_block_tree_aux_output_mem cfg _ _ _ hin' with h | h
      · exact h
      · rw [h]; exact hjust
    exact is_ancestor_trans hwf (hwalk b _ hqr_mem) (hwalk b _ hjust) hgt hjb
  · change is_ancestor store (ForkChoiceNode.mk (get_head cfg store).root)
      (ForkChoiceNode.mk b) = true
    rw [heq]
    exact hjb

end FastConfirmation.Spec

end
