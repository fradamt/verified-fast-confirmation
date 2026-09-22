module
public import FastConfirmation.Spec.Proof.Engine

@[expose] public section

/-!
# Spec / Proof / HeadReroot: the mid-walk head-descent lemma

The existing head-descent lemmas (`Descent.is_ancestor_get_head`,
`EngineStore.is_ancestor_get_head_of_chain`) are formulated for a
`DescendsTo`/`DescendStep` chain that **starts at the store's own `justified_checkpoint.root`**
— where `get_head`'s argmax descent begins. The strict FFG branch of the covering fold, however,
already knows `head ⪰ r₀` for a mid-chain anchor `r₀` (via the `justified_descends` export) and only
needs to continue the argmax descent from `r₀` down to `b` along a `DescendStep` chain.

This module supplies exactly that continuation. The **walk-path characterization** is
`head_aux_reroot`: if the argmax walk from `start` produces a head that descends from a node `x`
which itself descends from `start`, then the walk **passes through** `x` — the head is the head of
the argmax walk re-rooted at `x` (`∃ N, get_head_aux fuel (mk start) = get_head_aux N (mk x)`). The
lemma `head_leaf` shows that the actual `get_head` walk terminates at a childless node
(fuel `blocks.length + 1` exceeds the pairwise-distinct descent length), so the re-rooted walk has
fuel to spare for the remaining `DescendStep` chain. Composing the two gives
`head_ge_of_intermediate_chain`.

Domain hypotheses are the usual `parent_slot_lt` (`hwf`), filtered-containment (`hsub`), and the
blanket walk-knownness `hwalk` (`∀ t r, r ∈ block_roots → WalkKnown store (blocks t).slot r`),
as also used by `EngineStore`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Comparability of two ancestors of a common node -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Two ancestors of a common node `y` are ancestry-comparable, by
`get_ancestor_comp`. -/
theorem reroot_comparable {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {y a b : Root}
    (hwa : WalkKnown store (store.blocks a).slot y)
    (hwb : WalkKnown store (store.blocks b).slot y)
    (ha : get_ancestor store (ForkChoiceNode.mk y) (store.blocks a).slot = ForkChoiceNode.mk a)
    (hb : get_ancestor store (ForkChoiceNode.mk y) (store.blocks b).slot = ForkChoiceNode.mk b) :
    get_ancestor store (ForkChoiceNode.mk b) (store.blocks a).slot = ForkChoiceNode.mk a ∨
      get_ancestor store (ForkChoiceNode.mk a) (store.blocks b).slot = ForkChoiceNode.mk b := by
  rcases le_total (store.blocks a).slot (store.blocks b).slot with hle | hle
  · left
    have hcomp := get_ancestor_comp hwf hle hwa
    rw [hb, ha] at hcomp
    exact hcomp
  · right
    have hcomp := get_ancestor_comp hwf hle hwb
    rw [ha, hb] at hcomp
    exact hcomp

omit [LinearOrder Root] [Inhabited Root] in
/-- Mutual descent forces equality: if `x ⪰ start` and `start ⪰ x` then `x = start`. -/
theorem reroot_eq_of_mutual {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x start : Root} (hx : x ∈ store.block_roots) (hstart : start ∈ store.block_roots)
    (hxs : get_ancestor store (ForkChoiceNode.mk x) (store.blocks start).slot =
        ForkChoiceNode.mk start)
    (hsx : get_ancestor store (ForkChoiceNode.mk start) (store.blocks x).slot =
        ForkChoiceNode.mk x) :
    x = start := by
  have hle1 : (store.blocks start).slot ≤ (store.blocks x).slot := by
    have h := get_ancestor_slot_le hwf (hwalk start hstart x hx)
    rw [hxs] at h; simpa using h
  have hle2 : (store.blocks x).slot ≤ (store.blocks start).slot := by
    have h := get_ancestor_slot_le hwf (hwalk x hx start hstart)
    rw [hsx] at h; simpa using h
  have heq : (store.blocks x).slot ≤ (store.blocks start).slot := hle2
  have hstop : get_ancestor store (ForkChoiceNode.mk x) (store.blocks start).slot =
      ForkChoiceNode.mk x := get_ancestor_stop heq
  rw [hstop] at hxs
  exact ForkChoiceNode.mk.injEq x start |>.mp hxs

omit [LinearOrder Root] [Inhabited Root] in
/-- Direct-child squeeze: if `x ⪰ start`, `br ⪰ x`, and `br`'s parent is `start`, then `x` is
`start` or `br` — nothing sits strictly between a node and its parent. -/
theorem reroot_child_squeeze {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x start br : Root} (hx : x ∈ store.block_roots) (hstart : start ∈ store.block_roots)
    (hbr : br ∈ store.block_roots) (hbr_par : (store.blocks br).parent_root = start)
    (hxs : get_ancestor store (ForkChoiceNode.mk x) (store.blocks start).slot =
        ForkChoiceNode.mk start)
    (hbrx : get_ancestor store (ForkChoiceNode.mk br) (store.blocks x).slot =
        ForkChoiceNode.mk x) :
    x = start ∨ x = br := by
  have hstart_lt_br : (store.blocks start).slot < (store.blocks br).slot := by
    have h := hwf br hbr (by rw [hbr_par]; exact hstart)
    rwa [hbr_par] at h
  -- `slot start ≤ slot x`
  have hle_sx : (store.blocks start).slot ≤ (store.blocks x).slot := by
    have h := get_ancestor_slot_le hwf (hwalk start hstart x hx)
    rw [hxs] at h; simpa using h
  rcases eq_or_lt_of_le hle_sx with heq | hlt
  · -- `slot x = slot start` ⟹ `x = start`
    left
    have hstop : get_ancestor store (ForkChoiceNode.mk x) (store.blocks start).slot =
        ForkChoiceNode.mk x := get_ancestor_stop (le_of_eq heq.symm)
    rw [hstop] at hxs
    exact ForkChoiceNode.mk.injEq x start |>.mp hxs
  · -- `slot start < slot x`; show `x = br`
    right
    rcases le_or_gt (store.blocks br).slot (store.blocks x).slot with hle | hgt
    · -- `slot br ≤ slot x`; `get_ancestor br (slot x)` stops at `br`
      have hstop : get_ancestor store (ForkChoiceNode.mk br) (store.blocks x).slot =
          ForkChoiceNode.mk br := get_ancestor_stop hle
      rw [hstop] at hbrx
      exact (ForkChoiceNode.mk.injEq br x |>.mp hbrx).symm
    · -- `slot x < slot br`; the walk steps to `start`, landing at `start` ⟹ `x = start`, absurd
      exfalso
      have hpw : WalkKnown store (store.blocks x).slot (store.blocks br).parent_root := by
        rw [hbr_par]; exact WalkKnown.stop hstart (le_of_lt hlt)
      rw [get_ancestor_step hwf hbr hgt hpw, hbr_par,
        get_ancestor_stop (le_of_lt hlt)] at hbrx
      have : start = x := ForkChoiceNode.mk.injEq start x |>.mp hbrx
      exact absurd (this ▸ hlt) (lt_irrefl _)

/-! ## The walk-path characterization: the argmax walk passes through `x` -/

/-- **Reroot.** If the argmax walk from `start` produces a head that descends from `x`, and `x`
descends from `start`, then the walk **passes through** `x`: the head is the head of the argmax
walk re-rooted at `x`, at some remaining fuel `N`. Induction on `fuel`; at each descent step the
head is comparable to both the chosen child `br` and to `x` (`reroot_comparable`), and the
direct-child squeeze (`reroot_child_squeeze`) resolves which subtree `x` lies in. -/
theorem head_aux_reroot {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x : Root} (hx : x ∈ store.block_roots) :
    ∀ (fuel : ℕ) (start : Root), start ∈ store.block_roots →
      get_ancestor store (ForkChoiceNode.mk x) (store.blocks start).slot =
        ForkChoiceNode.mk start →
      get_ancestor store (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk start))
          (store.blocks x).slot = ForkChoiceNode.mk x →
      ∃ N, get_head_aux cfg store blocks fuel (ForkChoiceNode.mk start) =
        get_head_aux cfg store blocks N (ForkChoiceNode.mk x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro start hstart hxs hhx
    have hleaf : get_head_aux cfg store blocks 0 (ForkChoiceNode.mk start) =
        ForkChoiceNode.mk start := rfl
    rw [hleaf] at hhx
    have hxeq : x = start := reroot_eq_of_mutual hwf hwalk hx hstart hxs hhx
    exact ⟨0, by rw [hxeq]⟩
  | succ f ih =>
    intro start hstart hxs hhx
    rcases hbest : (get_node_children store blocks (ForkChoiceNode.mk start)).argmax
        (fun child => toLex (get_weight cfg store child, child.root)) with _ | best
    · -- leaf: the walk stops at `start`, so `start ⪰ x`; with `x ⪰ start`, `x = start`
      have hnil : get_node_children store blocks (ForkChoiceNode.mk start) = [] :=
        List.argmax_eq_none.mp hbest
      rw [get_head_aux_leaf cfg store blocks f (ForkChoiceNode.mk start) hnil] at hhx
      have hxeq : x = start := reroot_eq_of_mutual hwf hwalk hx hstart hxs hhx
      exact ⟨f + 1, by rw [hxeq, get_head_aux_leaf cfg store blocks f _ hnil]⟩
    · -- descent step to `br`
      obtain ⟨br⟩ := best
      have hmem : ForkChoiceNode.mk br ∈
          get_node_children store blocks (ForkChoiceNode.mk start) := List.argmax_mem hbest
      have hbr_par : (store.blocks br).parent_root = start := (mem_get_node_children.mp hmem).2
      have hbr_mem : br ∈ store.block_roots := hsub br (mem_get_node_children.mp hmem).1
      rw [get_head_aux_step cfg store blocks f (ForkChoiceNode.mk start) (ForkChoiceNode.mk br)
        hbest] at hhx ⊢
      -- `H ⪰ br`
      have hHbr : get_ancestor store (get_head_aux cfg store blocks f (ForkChoiceNode.mk br))
          (store.blocks br).slot = ForkChoiceNode.mk br :=
        get_head_aux_stays_below cfg hwf hsub f
          (WalkKnown.stop hbr_mem (le_refl _)) (get_ancestor_stop (le_refl _))
      -- the head as `mk H0`
      set H0 : Root := (get_head_aux cfg store blocks f (ForkChoiceNode.mk br)).root with hH0def
      have hHeq : get_head_aux cfg store blocks f (ForkChoiceNode.mk br) = ForkChoiceNode.mk H0 :=
        rfl
      have hH0mem : H0 ∈ store.block_roots := by
        rcases get_head_aux_root_mem_or cfg (blocks := blocks) f (ForkChoiceNode.mk br) with h | h
        · exact hsub _ h
        · rw [hH0def, h]; exact hbr_mem
      rw [hHeq] at hHbr hhx
      rcases reroot_comparable hwf (hwalk br hbr_mem H0 hH0mem) (hwalk x hx H0 hH0mem) hHbr hhx with
        hxbr | hbrx
      · -- `x ⪰ br`: recurse
        exact ih br hbr_mem hxbr (by rw [hHeq]; exact hhx)
      · -- `br ⪰ x`: `x = start` or `x = br`
        rcases reroot_child_squeeze hwf hwalk hx hstart hbr_mem hbr_par hxs hbrx with hxst | hxbr
        · exact ⟨f + 1, by rw [hxst,
            get_head_aux_step cfg store blocks f (ForkChoiceNode.mk start)
              (ForkChoiceNode.mk br) hbest]⟩
        · exact ⟨f, by rw [hxbr]⟩

/-! ## Finiteness: the argmax walk terminates at a leaf when fuel exceeds the descent length -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Budget decrease: the `blocks`-count of strictly-higher-slot roots strictly drops from a node to
any child (the child is such a root, and every higher-slot root of the child is one of the parent).
The strictly-decreasing measure driving `walk_reaches_leaf`. -/
private theorem budget_lt_of_child {store : Store Root} {blocks : List Root}
    {start br : Root} (hbr : br ∈ blocks)
    (hlt : (store.blocks start).slot < (store.blocks br).slot) :
    (blocks.filter (fun r => decide ((store.blocks br).slot < (store.blocks r).slot))).length <
      (blocks.filter (fun r => decide ((store.blocks start).slot <
        (store.blocks r).slot))).length := by
  set p : Root → Bool := fun r => decide ((store.blocks br).slot < (store.blocks r).slot) with hp
  set q : Root → Bool := fun r => decide ((store.blocks start).slot < (store.blocks r).slot) with hq
  have hfe : blocks.filter p = (blocks.filter q).filter p := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    simp only [hp, hq]
    by_cases hb : (store.blocks br).slot < (store.blocks a).slot
    · simp [hb, lt_trans hlt hb]
    · simp [hb]
  have hsl : (blocks.filter p).Sublist (blocks.filter q) := by
    rw [hfe]; exact List.filter_sublist
  have hbrq : br ∈ blocks.filter q := by
    rw [List.mem_filter]; exact ⟨hbr, by simp only [hq, decide_eq_true_eq]; exact hlt⟩
  have hbrp : br ∉ blocks.filter p := by
    rw [List.mem_filter]; rintro ⟨_, hbp⟩
    simp only [hp, decide_eq_true_eq] at hbp; exact lt_irrefl _ hbp
  rcases lt_or_eq_of_le hsl.length_le with h | h
  · exact h
  · exact absurd ((hsl.eq_of_length h).symm ▸ hbrq) hbrp

/-- **The argmax walk reaches a leaf.** If the `blocks`-count of roots strictly above `start`'s slot
is below `fuel`, the descent from `start` lands on a childless node. Strong induction on `fuel`:
each step moves to a child `br` of strictly higher slot, dropping the budget (`budget_lt_of_child`),
so the fuel outlasts the strictly-shrinking budget. -/
theorem walk_reaches_leaf {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) :
    ∀ (fuel : ℕ) (start : Root), start ∈ store.block_roots →
      (blocks.filter (fun r => decide ((store.blocks start).slot <
        (store.blocks r).slot))).length < fuel →
      get_node_children store blocks
        (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk start)) = [] := by
  intro fuel
  induction fuel with
  | zero => intro start _ hbud; exact absurd hbud (Nat.not_lt_zero _)
  | succ f ih =>
    intro start hstart hbud
    rcases hbest : (get_node_children store blocks (ForkChoiceNode.mk start)).argmax
        (fun child => toLex (get_weight cfg store child, child.root)) with _ | best
    · have hnil : get_node_children store blocks (ForkChoiceNode.mk start) = [] :=
        List.argmax_eq_none.mp hbest
      rw [get_head_aux_leaf cfg store blocks f (ForkChoiceNode.mk start) hnil]; exact hnil
    · obtain ⟨br⟩ := best
      have hmem : ForkChoiceNode.mk br ∈
          get_node_children store blocks (ForkChoiceNode.mk start) := List.argmax_mem hbest
      have hbr_par : (store.blocks br).parent_root = start := (mem_get_node_children.mp hmem).2
      have hbr_blocks : br ∈ blocks := (mem_get_node_children.mp hmem).1
      have hbr_mem : br ∈ store.block_roots := hsub br hbr_blocks
      have hlt : (store.blocks start).slot < (store.blocks br).slot := by
        have h := hwf br hbr_mem (by rw [hbr_par]; exact hstart)
        rwa [hbr_par] at h
      rw [get_head_aux_step cfg store blocks f (ForkChoiceNode.mk start) (ForkChoiceNode.mk br)
        hbest]
      refine ih br hbr_mem ?_
      exact lt_of_lt_of_le (budget_lt_of_child hbr_blocks hlt) (Nat.lt_succ_iff.mp hbud)

/-- **The fork-choice head is a leaf of the filtered tree.** `get_head`'s fuel
`(filtered tree).length + 1` exceeds the strictly-shrinking descent budget
(`walk_reaches_leaf`), so the argmax descent stops at a childless node. -/
theorem head_leaf {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots) :
    get_node_children store (get_filtered_block_tree cfg store) (get_head cfg store) = [] := by
  simp only [get_head]
  refine walk_reaches_leaf cfg hwf hsub _ store.justified_checkpoint.root hjust ?_
  exact lt_of_le_of_lt (List.filter_sublist.length_le) (Nat.lt_succ_self _)

/-! ## Phase 2: descend the `DescendsTo` chain from a leaf head -/

/-- **Leaf descent.** Once the head is known to be the leaf of the argmax walk re-rooted at `x`
(`∃ N, head = get_head_aux N (mk x)`) and to descend from `x`, following any `DescendsTo` chain
`x → b` shows the head descends from `b`. Induction on the chain: at each step the head is not `x`
itself (`x` has the dominant child, but the head is a leaf), so the re-rooted walk had fuel to take
that dominant step, and the head descends from the child. -/
theorem head_ge_of_reroot_leaf {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hleaf : get_node_children store (get_filtered_block_tree cfg store) (get_head cfg store) = [])
    {b : Root} :
    ∀ {n : ℕ} {x : Root},
      DescendsTo cfg store (get_filtered_block_tree cfg store) b n x →
      (∃ N, get_head cfg store =
        get_head_aux cfg store (get_filtered_block_tree cfg store) N (ForkChoiceNode.mk x)) →
      get_ancestor store (get_head cfg store) (store.blocks x).slot = ForkChoiceNode.mk x →
      get_ancestor store (get_head cfg store) (store.blocks b).slot = ForkChoiceNode.mk b := by
  intro n x hdesc
  induction hdesc with
  | here hb => intro _ hhx; exact hhx
  | @step n h c hchild hdom hrec ih =>
    intro hex hhx
    obtain ⟨N, hN⟩ := hex
    cases N with
    | zero =>
      have hGx : get_head cfg store = ForkChoiceNode.mk h := hN
      rw [hGx] at hleaf
      rw [hleaf] at hchild
      exact absurd hchild List.not_mem_nil
    | succ f' =>
      have harg : (get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h)).argmax
            (fun child => toLex (get_weight cfg store child, child.root)) =
          some (ForkChoiceNode.mk c) := get_head_argmax_dominant cfg hchild hdom
      have hGc : get_head cfg store =
          get_head_aux cfg store (get_filtered_block_tree cfg store) f' (ForkChoiceNode.mk c) := by
        rw [hN, get_head_aux_step cfg store (get_filtered_block_tree cfg store) f'
          (ForkChoiceNode.mk h) (ForkChoiceNode.mk c) harg]
      have hc_mem : c ∈ store.block_roots := hsub c (mem_get_node_children.mp hchild).1
      have hGgec : get_ancestor store (get_head cfg store) (store.blocks c).slot =
          ForkChoiceNode.mk c := by
        rw [hGc]
        exact get_head_aux_stays_below cfg hwf hsub f'
          (WalkKnown.stop hc_mem (le_refl _)) (get_ancestor_stop (le_refl _))
      exact ih ⟨f', hGc⟩ hGgec

/-! ## The headline: mid-walk head descent -/

/-- **Mid-walk head descent.** If `head ⪰ x` for a node `x` that descends
from the store's justified root, and there is a `DescendsTo` chain from `x` down to `b` in the
filtered tree, then `head ⪰ b`. Composes the walk-path characterization (`head_aux_reroot`, so the
argmax walk passes through `x`) with the leaf-descent (`head_ge_of_reroot_leaf`, so the remaining
argmax steps follow the dominant chain to `b`). This is the strict-FFG-branch continuation the
covering fold needs: `justified_descends` supplies `head ⪰ r₀` for a mid-chain `r₀`, and this lemma
carries the descent the rest of the way to the confirmed block. -/
theorem head_ge_of_intermediate_chain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {x b : Root} {n : ℕ} (hx : x ∈ store.block_roots)
    (hxj : is_ancestor store (get_node_for_root x)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hhx : is_ancestor store (get_head cfg store) (get_node_for_root x) = true)
    (hdesc : DescendsTo cfg store (get_filtered_block_tree cfg store) b n x) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  simp only [is_ancestor, get_node_for_root, decide_eq_true_eq] at hxj hhx ⊢
  have hgd : get_head cfg store =
      get_head_aux cfg store (get_filtered_block_tree cfg store)
        ((get_filtered_block_tree cfg store).length + 1)
        (ForkChoiceNode.mk store.justified_checkpoint.root) := rfl
  have hleaf := head_leaf cfg hwf hsub hjust
  have hreroot : ∃ N, get_head cfg store =
      get_head_aux cfg store (get_filtered_block_tree cfg store) N (ForkChoiceNode.mk x) := by
    rw [hgd]
    exact head_aux_reroot cfg hwf hsub hwalk hx _ store.justified_checkpoint.root hjust hxj
      (by rw [← hgd]; exact hhx)
  exact head_ge_of_reroot_leaf cfg hwf hsub hleaf hdesc hreroot hhx

end FastConfirmation.Spec

end
