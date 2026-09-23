module
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestryRoots

@[expose] public section

/-!
# Spec / Proof / FilterFuel

Proves the bounded recursion and tree facts of the block-tree filter.

This module contains `TreeBounded`, `TreeBounded.mono`, `filter_block_tree_aux_internal` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## The tree-descent domain -/

/-- Beacon-tree height bound for `filter_block_tree`: `TreeBounded store L n r` holds when the subtree rooted at `r`,
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


/-! ## `get_node_children` membership -/

omit [Inhabited Root] in
/-- A pending node has same-root EMPTY and, when verified, FULL children. -/
theorem mem_get_node_children_pending {store : Store Root} {blocks : List Root}
    {node child : ForkChoiceNode Root} (hpending : node.payload_status = .pending) :
    child ∈ get_node_children store blocks node ↔
      child.root = node.root ∧
        (child.payload_status = .empty ∨
          (child.payload_status = .full ∧ is_payload_verified store node.root = true)) := by
  cases child with
  | mk root status =>
    by_cases hv : is_payload_verified store node.root = true
    · simp [get_node_children, hpending, hv, and_or_left]
    · simp [get_node_children, hpending, hv]

omit [Inhabited Root] in
/-- A resolved node has pending beacon children that select its payload status. -/
theorem mem_get_node_children_resolved {store : Store Root} {blocks : List Root}
    {node child : ForkChoiceNode Root} (hresolved : node.payload_status ≠ .pending) :
    child ∈ get_node_children store blocks node ↔
      child.payload_status = .pending ∧ child.root ∈ blocks ∧
        (store.blocks child.root).parent_root = node.root ∧
        node.payload_status = get_parent_payload_status store (store.blocks child.root) := by
  rw [get_node_children, if_neg hresolved]
  constructor
  · rintro hchild
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hchild
    simp only [List.mem_filter, decide_eq_true_eq] at hr
    exact ⟨rfl, hr.1, hr.2.1, hr.2.2⟩
  · rintro ⟨hpending, hmem, hparent, hstatus⟩
    apply List.mem_map.mpr
    refine ⟨child.root, List.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
    · simpa only [decide_eq_true_eq] using And.intro hparent hstatus
    · cases child with
      | mk root status =>
        change status = .pending at hpending
        subst status
        rfl

omit [Inhabited Root] in
/-- Gloas child membership has two cases: payload resolution at one root,
or a pending beacon child of a resolved node. -/
theorem mem_get_node_children {store : Store Root} {blocks : List Root}
    {node child : ForkChoiceNode Root} :
    child ∈ get_node_children store blocks node ↔
      (node.payload_status = .pending ∧ child.root = node.root ∧
        (child.payload_status = .empty ∨
          (child.payload_status = .full ∧ is_payload_verified store node.root = true))) ∨
      (node.payload_status ≠ .pending ∧ child.payload_status = .pending ∧
        child.root ∈ blocks ∧ (store.blocks child.root).parent_root = node.root ∧
        node.payload_status = get_parent_payload_status store (store.blocks child.root)) := by
  by_cases hpending : node.payload_status = .pending
  · constructor
    · intro hc
      exact Or.inl ⟨hpending, (mem_get_node_children_pending hpending).mp hc⟩
    · rintro (⟨_, hc⟩ | ⟨hresolved, _⟩)
      · exact (mem_get_node_children_pending hpending).mpr hc
      · exact False.elim (hresolved hpending)
  · constructor
    · intro hc
      exact Or.inr ⟨hpending, (mem_get_node_children_resolved hpending).mp hc⟩
    · rintro (⟨hresolved, _⟩ | ⟨_, hc⟩)
      · exact False.elim (hpending hresolved)
      · exact (mem_get_node_children_resolved hpending).mpr hc

omit [Inhabited Root] in
/-- A child either uses a candidate beacon root or preserves its parent's root. -/
theorem get_node_children_root_mem_or {store : Store Root} {blocks : List Root}
    {node child : ForkChoiceNode Root}
    (hchild : child ∈ get_node_children store blocks node) :
    child.root ∈ blocks ∨ child.root = node.root := by
  rcases mem_get_node_children.mp hchild with hpending | hresolved
  · exact Or.inr hpending.2.1
  · exact Or.inl hresolved.2.2.1

/-! ## The payload-aware node-descent domain -/

/-- Height of the actual Gloas node graph, including payload resolution steps. -/
inductive NodeTreeBounded (store : Store Root) (blocks : List Root) :
    ℕ → ForkChoiceNode Root → Prop
  | mk {n : ℕ} {node : ForkChoiceNode Root}
      (h : ∀ child ∈ get_node_children store blocks node,
        NodeTreeBounded store blocks n child) :
      NodeTreeBounded store blocks (n + 1) node

omit [Inhabited Root] in
/-- A node height bound remains valid with one more level. -/
theorem NodeTreeBounded.mono {store : Store Root} {blocks : List Root}
    {n : ℕ} {node : ForkChoiceNode Root} (h : NodeTreeBounded store blocks n node) :
    NodeTreeBounded store blocks (n + 1) node := by
  induction h with
  | @mk n node hchild ih => exact NodeTreeBounded.mk (fun child hc => ih child hc)



/-! ## `get_head_aux` fuel elimination -/

/-- Gloas head-loop unfolding uses the full weight/root/status key. -/
theorem get_head_aux_succ (store : Store Root) (blocks : List Root) (fuel : ℕ)
    (head : ForkChoiceNode Root) :
    get_head_aux cfg store blocks (fuel + 1) head =
      match (get_node_children store blocks head).argmax
          (fun child => toLex (get_weight cfg store child,
            toLex (child.root, get_payload_status_tiebreaker cfg store child))) with
      | none => head
      | some best => get_head_aux cfg store blocks fuel best := rfl

/-- With no children, the Gloas descent returns its current node. -/
theorem get_head_aux_leaf (store : Store Root) (blocks : List Root) (fuel : ℕ)
    (head : ForkChoiceNode Root)
    (hnil : get_node_children store blocks head = []) :
    get_head_aux cfg store blocks (fuel + 1) head = head := by
  rw [get_head_aux_succ, hnil, List.argmax_nil]

/-- The head loop follows the maximum child under the full Gloas key. -/
theorem get_head_aux_step (store : Store Root) (blocks : List Root) (fuel : ℕ)
    (head best : ForkChoiceNode Root)
    (hbest : (get_node_children store blocks head).argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) = some best) :
    get_head_aux cfg store blocks (fuel + 1) head =
      get_head_aux cfg store blocks fuel best := by
  rw [get_head_aux_succ, hbest]



/-- Strict weight domination selects a child under the Gloas key. Root and
payload priority cannot override a strict first-coordinate inequality. -/
theorem get_head_argmax_dominant {store : Store Root} {blocks : List Root}
    {head best : ForkChoiceNode Root}
    (hbest : best ∈ get_node_children store blocks head)
    (hdom : ∀ c ∈ get_node_children store blocks head, c ≠ best →
        get_weight cfg store c < get_weight cfg store best) :
    (get_node_children store blocks head).argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) = some best := by
  have key : ∀ a : ForkChoiceNode Root,
      get_weight cfg store a < get_weight cfg store best →
        (toLex (get_weight cfg store a,
          toLex (a.root, get_payload_status_tiebreaker cfg store a)) : Gwei ×ₗ (Root ×ₗ ℕ)) <
          toLex (get_weight cfg store best,
            toLex (best.root, get_payload_status_tiebreaker cfg store best)) := by
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
