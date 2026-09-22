module
public import FastConfirmation.Spec.Proof.AncestryRoots

@[expose] public section

/-!
# Spec / Proof / FilterFuel

Layer 0, the head-stack fuel toolkit: fuel elimination for the two remaining
fuel-bounded fork-choice workers, `filter_block_tree_aux` and `get_head_aux`,
mirroring `Proof/Ancestry.lean`'s pattern for `get_ancestor_aux`.

Both workers descend the block tree toward the leaves (each recursive call
moves to a *child* of the current node). The recursion domain is captured by
`TreeBounded store L n r`: the subtree rooted at `r`, taking children from the
candidate list `L`, has height at most `n` — an `Acc`-shaped inductive whose
`n` index is the decreasing measure the fuel-independence induction runs on.
Instantiating `L := store.block_roots` gives the `filter_block_tree` domain;
`L := blocks` (the filtered tree) gives the `get_head` descent domain.

Contents:

* `TreeBounded` and its monotonicity in the height index.
* `mem_get_node_children` — membership characterization of the descent step.
* `filter_block_tree_aux_succ` / `_fuel_eq` — python-shaped unfold and fuel
  independence on the `TreeBounded store store.block_roots` domain.
* `get_head_aux_succ` / `_fuel_eq` — the same for the `get_head` descent, plus
  `get_head_argmax_dominant`: a child whose weight strictly dominates every
  other child is the `argmax` (the lexicographic root tie-break is irrelevant
  under strict weight domination).

No behavioral assumptions enter — the only premises are the domain predicate
and, for the unfold corollaries, the branch conditions.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## The tree-descent domain -/

/-- Height bound for the child-descent recursion shared by `filter_block_tree`
and `get_head`: `TreeBounded store L n r` holds when the subtree rooted at `r`,
drawing children from the candidate list `L` (those `c ∈ L` with
`(store.blocks c).parent_root = r`), terminates within `n` levels. `Acc`-shaped:
a leaf (no children in `L`) is bounded at every positive height; the `n` index
is the well-founded measure the fuel inductions descend on. -/
inductive TreeBounded (store : Store Root) (L : List Root) : ℕ → Root → Prop
  | mk {n : ℕ} {r : Root}
      (h : ∀ c ∈ L.filter (fun x => (store.blocks x).parent_root = r),
          TreeBounded store L n c) :
      TreeBounded store L (n + 1) r

omit [Inhabited Root] in
/-- The height bound is an upper bound: a subtree bounded at height `n` is also
bounded at any larger height. -/
theorem TreeBounded.mono {store : Store Root} {L : List Root} {n : ℕ} {r : Root}
    (h : TreeBounded store L n r) : TreeBounded store L (n + 1) r := by
  induction h with
  | @mk n r hchild ih => exact TreeBounded.mk (fun c hc => ih c hc)

/-! ## `filter_block_tree_aux` fuel elimination -/

omit [Inhabited Root] in
/-- Python-shaped one-step unfold of `filter_block_tree_aux` at positive fuel:
recurse into the children if any, else run the justified/finalized viability
test on the leaf (both branches transcribed exactly from the def). -/
theorem filter_block_tree_aux_succ (store : Store Root) (fuel : ℕ) (block_root : Root) :
    filter_block_tree_aux cfg store (fuel + 1) block_root =
      let children :=
        store.block_roots.filter (fun root => (store.blocks root).parent_root = block_root)
      if children ≠ [] then
        let filter_block_tree_result :=
          children.map (fun child => filter_block_tree_aux cfg store fuel child)
        let child_blocks : List Root :=
          (filter_block_tree_result.map Prod.snd).flatten
        if filter_block_tree_result.any Prod.fst then
          (true, child_blocks ++ [block_root])
        else
          (false, child_blocks)
      else
        let current_epoch := get_current_store_epoch cfg store
        let voting_source := get_voting_source cfg store block_root
        let correct_justified :=
          decide (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
            voting_source.epoch = store.justified_checkpoint.epoch ∨
            voting_source.epoch + 2 ≥ current_epoch)
        let finalized_checkpoint_block :=
          get_checkpoint_block cfg store block_root store.finalized_checkpoint.epoch
        let correct_finalized :=
          decide (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
            store.finalized_checkpoint.root = finalized_checkpoint_block)
        if correct_justified && correct_finalized then
          (true, [block_root])
        else
          (false, []) := rfl

omit [Inhabited Root] in
/-- Internal unfold: with at least one child, `filter_block_tree_aux` recurses
into every child and reports viability iff some child branch is viable. -/
theorem filter_block_tree_aux_internal (store : Store Root) (fuel : ℕ) (block_root : Root)
    (hne : store.block_roots.filter (fun root => (store.blocks root).parent_root = block_root)
        ≠ []) :
    filter_block_tree_aux cfg store (fuel + 1) block_root =
      (let children :=
        store.block_roots.filter (fun root => (store.blocks root).parent_root = block_root)
      let res := children.map (fun child => filter_block_tree_aux cfg store fuel child)
      if res.any Prod.fst then (true, (res.map Prod.snd).flatten ++ [block_root])
      else (false, (res.map Prod.snd).flatten)) := by
  simp only [filter_block_tree_aux]
  rw [if_pos hne]

omit [Inhabited Root] in
/-- Leaf unfold: with no children, `filter_block_tree_aux` runs the
justified/finalized viability test on the block itself. -/
theorem filter_block_tree_aux_leaf (store : Store Root) (fuel : ℕ) (block_root : Root)
    (hnil : store.block_roots.filter (fun root => (store.blocks root).parent_root = block_root)
        = []) :
    filter_block_tree_aux cfg store (fuel + 1) block_root =
      (let voting_source := get_voting_source cfg store block_root
      let correct_justified :=
        decide (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
          voting_source.epoch = store.justified_checkpoint.epoch ∨
          voting_source.epoch + 2 ≥ get_current_store_epoch cfg store)
      let correct_finalized :=
        decide (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
          store.finalized_checkpoint.root =
            get_checkpoint_block cfg store block_root store.finalized_checkpoint.epoch)
      if correct_justified && correct_finalized then (true, [block_root]) else (false, [])) := by
  simp only [filter_block_tree_aux]
  rw [if_neg (not_not.mpr hnil)]

omit [Inhabited Root] in
/-- Fuel independence for `filter_block_tree_aux` on the `TreeBounded` domain:
any two fuels at least the subtree height compute the same viability flag and
root list (induction on the height, the child maps aligned by the IH — mirrors
`get_ancestor_aux_fuel_eq`, descending toward the leaves instead of the root). -/
theorem filter_block_tree_aux_fuel_eq {store : Store Root} {n : ℕ} {r : Root}
    (hk : TreeBounded store store.block_roots n r) :
    ∀ fuel fuel' : ℕ, n ≤ fuel → n ≤ fuel' →
      filter_block_tree_aux cfg store fuel r = filter_block_tree_aux cfg store fuel' r := by
  induction hk with
  | @mk n r _ ih =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => omega
    | succ f => cases fuel' with
      | zero => omega
      | succ f' =>
        simp only [filter_block_tree_aux]
        have hmap :
            (store.block_roots.filter (fun x => (store.blocks x).parent_root = r)).map
                (fun c => filter_block_tree_aux cfg store f c) =
              (store.block_roots.filter (fun x => (store.blocks x).parent_root = r)).map
                (fun c => filter_block_tree_aux cfg store f' c) := by
          apply List.map_congr_left
          intro c hc
          exact ih c hc f f' (by omega) (by omega)
        rw [hmap]

/-! ## `get_node_children` membership -/

omit [Inhabited Root] in
/-- A node is a `get_node_children` child exactly when its root is drawn from
the candidate list and points at the parent — the descent step's membership
characterization. -/
theorem mem_get_node_children {store : Store Root} {blocks : List Root}
    {node child : ForkChoiceNode Root} :
    child ∈ get_node_children store blocks node ↔
      child.root ∈ blocks ∧ (store.blocks child.root).parent_root = node.root := by
  simp only [get_node_children, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨hr, hp⟩, rfl⟩; exact ⟨hr, hp⟩
  · rintro ⟨hr, hp⟩; exact ⟨child.root, ⟨hr, hp⟩, rfl⟩

/-! ## `get_head_aux` fuel elimination -/

/-- Python-shaped one-step unfold of `get_head_aux` at positive fuel: pick the
`argmax` child by lexicographic `(weight, root)` and descend, or return `head`
when there are no children. -/
theorem get_head_aux_succ (store : Store Root) (blocks : List Root) (fuel : ℕ)
    (head : ForkChoiceNode Root) :
    get_head_aux cfg store blocks (fuel + 1) head =
      match (get_node_children store blocks head).argmax
          (fun child => toLex (get_weight cfg store child, child.root)) with
      | none => head
      | some best => get_head_aux cfg store blocks fuel best := rfl

/-- Leaf unfold: with no children the `get_head` descent stops at `head`
(`argmax [] = none`). -/
theorem get_head_aux_leaf (store : Store Root) (blocks : List Root) (fuel : ℕ)
    (head : ForkChoiceNode Root)
    (hnil : get_node_children store blocks head = []) :
    get_head_aux cfg store blocks (fuel + 1) head = head := by
  rw [get_head_aux_succ, hnil, List.argmax_nil]

/-- Internal unfold: when the `argmax` child exists the descent moves to it. -/
theorem get_head_aux_step (store : Store Root) (blocks : List Root) (fuel : ℕ)
    (head best : ForkChoiceNode Root)
    (hbest : (get_node_children store blocks head).argmax
        (fun child => toLex (get_weight cfg store child, child.root)) = some best) :
    get_head_aux cfg store blocks (fuel + 1) head =
      get_head_aux cfg store blocks fuel best := by
  rw [get_head_aux_succ, hbest]

/-- Fuel independence for `get_head_aux` on the `TreeBounded store blocks`
domain: any two fuels at least the descent height compute the same head. The
`argmax` child is a `get_node_children` member, hence lies in the `TreeBounded`
child set, so the IH aligns the two recursive descents. -/
theorem get_head_aux_fuel_eq {store : Store Root} {blocks : List Root} {n : ℕ} {r : Root}
    (hk : TreeBounded store blocks n r) :
    ∀ fuel fuel' : ℕ, n ≤ fuel → n ≤ fuel' →
      get_head_aux cfg store blocks fuel (ForkChoiceNode.mk r) =
        get_head_aux cfg store blocks fuel' (ForkChoiceNode.mk r) := by
  induction hk with
  | @mk n r _ ih =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => omega
    | succ f => cases fuel' with
      | zero => omega
      | succ f' =>
        rw [get_head_aux_succ, get_head_aux_succ]
        rcases hbest : (get_node_children store blocks (ForkChoiceNode.mk r)).argmax
            (fun child => toLex (get_weight cfg store child, child.root)) with _ | best
        · rfl
        · obtain ⟨br⟩ := best
          have hmem : ForkChoiceNode.mk br ∈
              get_node_children store blocks (ForkChoiceNode.mk r) := List.argmax_mem hbest
          rw [mem_get_node_children] at hmem
          have hfilt : br ∈ blocks.filter (fun x => (store.blocks x).parent_root = r) :=
            List.mem_filter.mpr ⟨hmem.1, by simpa using hmem.2⟩
          exact ih br hfilt f f' (by omega) (by omega)

/-- Strict weight domination selects the `argmax`: if `best` is a child whose
weight strictly exceeds every other child's, then it is the lexicographic
`argmax` regardless of the root tie-break (strictness in the first Lex
coordinate makes the second coordinate irrelevant). This is the descent-step
determinism `get_head` relies on. -/
theorem get_head_argmax_dominant {store : Store Root} {blocks : List Root}
    {head best : ForkChoiceNode Root}
    (hbest : best ∈ get_node_children store blocks head)
    (hdom : ∀ c ∈ get_node_children store blocks head, c ≠ best →
        get_weight cfg store c < get_weight cfg store best) :
    (get_node_children store blocks head).argmax
        (fun child => toLex (get_weight cfg store child, child.root)) = some best := by
  have key : ∀ a : ForkChoiceNode Root,
      get_weight cfg store a < get_weight cfg store best →
        (toLex (get_weight cfg store a, a.root) : Gwei ×ₗ Root) <
          toLex (get_weight cfg store best, best.root) := by
    intro a hlt
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hlt
  rw [List.argmax_eq_some_iff]
  refine ⟨hbest, fun a ha => ?_, fun a ha hle => ?_⟩
  · by_cases hab : a = best
    · subst hab; exact le_refl _
    · exact le_of_lt (key a (hdom a ha hab))
  · by_cases hab : a = best
    · subst hab; exact le_refl _
    · exact absurd (lt_of_lt_of_le (key a (hdom a ha hab)) hle) (lt_irrefl _)

end FastConfirmation.Spec

end
