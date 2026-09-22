module
public import FastConfirmation.Spec.Proof.AncestryRoots

@[expose] public section

/-!
# Spec / Proof / FilterFuel

Layer 0, the head-stack fuel toolkit: fuel elimination for the two remaining
fuel-bounded fork-choice workers, `filter_block_tree_aux` and `get_head_aux`,
mirroring `Proof/Ancestry.lean`'s pattern for `get_ancestor_aux`.

The filter descends the beacon tree. The head loop also resolves payload status
at each root. `TreeBounded store L n r` records beacon height, and
`NodeTreeBounded` records height in the full Gloas graph. The beacon bound is: the subtree rooted at `r`, taking children from the
candidate list `L`, has height at most `n` — an `Acc`-shaped inductive whose
`n` index is the decreasing measure the fuel-independence induction runs on.
Instantiating `L := store.block_roots` gives the `filter_block_tree` domain;
`L := blocks` gives twice that height as a bound for the Gloas head descent.

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

omit [Inhabited Root] in
/-- Each beacon-tree level needs at most two Gloas node levels: one pending
node and one resolved node. -/
theorem TreeBounded.nodeBounded {store : Store Root} {blocks : List Root}
    {n : ℕ} {r : Root} (h : TreeBounded store blocks n r) :
    ∀ status : PayloadStatus,
      NodeTreeBounded store blocks (2 * n) (ForkChoiceNode.mk r status) := by
  induction h with
  | @mk n r hchild ih =>
    have resolved : ∀ status : PayloadStatus, status ≠ .pending →
        NodeTreeBounded store blocks (2 * n + 1) (ForkChoiceNode.mk r status) := by
      intro status hstatus
      apply NodeTreeBounded.mk
      intro child hc
      obtain ⟨hpending, hmem, hparent, _⟩ :=
        (mem_get_node_children_resolved hstatus).mp hc
      have hfilt : child.root ∈ blocks.filter (fun x => (store.blocks x).parent_root = r) :=
        List.mem_filter.mpr ⟨hmem, by simpa using hparent⟩
      have hb := ih child.root hfilt child.payload_status
      exact hb
    intro status
    by_cases hpending : status = .pending
    · subst status
      have hb : NodeTreeBounded store blocks (2 * n + 2)
          (ForkChoiceNode.mk r .pending) := by
        apply NodeTreeBounded.mk
        intro child hc
        obtain ⟨hroot, hstatus⟩ := (mem_get_node_children_pending rfl).mp hc
        have hresolved : child.payload_status ≠ .pending := by
          rcases hstatus with hempty | ⟨hfull, _⟩
          · simp [hempty]
          · simp [hfull]
        have hb := resolved child.payload_status hresolved
        cases child with
        | mk childRoot childStatus =>
          change childRoot = r at hroot
          subst childRoot
          exact hb
      convert hb using 1 <;> omega
    · have hb := (resolved status hpending).mono
      convert hb using 1 <;> omega

omit [Inhabited Root] in
/-- Starting from a resolved node saves the first payload-resolution level. -/
theorem TreeBounded.nodeBounded_resolved {store : Store Root} {blocks : List Root}
    {n : ℕ} {r : Root} (h : TreeBounded store blocks n r)
    {status : PayloadStatus} (hstatus : status ≠ .pending) :
    NodeTreeBounded store blocks (2 * n - 1) (ForkChoiceNode.mk r status) := by
  cases h with
  | @mk n r hchild =>
    have hb : NodeTreeBounded store blocks (2 * n + 1) (ForkChoiceNode.mk r status) := by
      apply NodeTreeBounded.mk
      intro child hc
      obtain ⟨_, hmem, hparent, _⟩ := (mem_get_node_children_resolved hstatus).mp hc
      have hfilt : child.root ∈ blocks.filter (fun x => (store.blocks x).parent_root = r) :=
        List.mem_filter.mpr ⟨hmem, by simpa using hparent⟩
      exact (hchild child.root hfilt).nodeBounded child.payload_status
    convert hb using 1 <;> omega

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

/-- Fuel independence on the actual Gloas node graph. -/
theorem get_head_aux_fuel_eq_node {store : Store Root} {blocks : List Root}
    {n : ℕ} {node : ForkChoiceNode Root} (hk : NodeTreeBounded store blocks n node) :
    ∀ fuel fuel' : ℕ, n ≤ fuel → n ≤ fuel' →
      get_head_aux cfg store blocks fuel node = get_head_aux cfg store blocks fuel' node := by
  induction hk with
  | @mk n node hchild ih =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => omega
    | succ f =>
      cases fuel' with
      | zero => omega
      | succ f' =>
        rw [get_head_aux_succ, get_head_aux_succ]
        cases hbest : (get_node_children store blocks node).argmax
            (fun child => toLex (get_weight cfg store child,
              toLex (child.root, get_payload_status_tiebreaker cfg store child))) with
        | none => rfl
        | some best =>
          exact ih best (List.argmax_mem hbest) f f' (by omega) (by omega)

/-- A beacon height of `n` requires `2 * n` head-loop fuel in Gloas. -/
theorem get_head_aux_fuel_eq {store : Store Root} {blocks : List Root} {n : ℕ} {r : Root}
    (hk : TreeBounded store blocks n r) :
    ∀ fuel fuel' : ℕ, 2 * n ≤ fuel → 2 * n ≤ fuel' →
      get_head_aux cfg store blocks fuel (ForkChoiceNode.mk r .pending) =
        get_head_aux cfg store blocks fuel' (ForkChoiceNode.mk r .pending) :=
  get_head_aux_fuel_eq_node cfg (hk.nodeBounded .pending)

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
