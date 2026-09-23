module
public import FastConfirmation.Spec.Proof.Engine

@[expose] public section

/-!
# Spec / Proof / HeadReroot


A Gloas head walk alternates payload resolution and beacon-child selection.
This module proves that a head walk passes through each pending beacon
ancestor between its start and its result. A walk that starts at a resolved
node needs an explicit pending-status premise when that node is the target.
Root ancestry alone does not imply equality of complete fork-choice nodes.


The leaf bound counts both kinds of node step. The final continuation theorem
follows the actual selections recorded by `NodeDescendsTo`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Beacon-root geometry -/

/-- Two beacon ancestors of a common root are comparable. The result records
root equality, since the parent walk can resolve a payload status. -/
theorem reroot_comparable {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {y a b : Root}
    (hwa : WalkKnown store (store.blocks a).slot y)
    (hwb : WalkKnown store (store.blocks b).slot y)
    (ha : (get_ancestor store (ForkChoiceNode.mk y .pending) (store.blocks a).slot).root = a)
    (hb : (get_ancestor store (ForkChoiceNode.mk y .pending) (store.blocks b).slot).root = b) :
    (get_ancestor store (ForkChoiceNode.mk b .pending) (store.blocks a).slot).root = a ∨
      (get_ancestor store (ForkChoiceNode.mk a .pending) (store.blocks b).slot).root = b := by
  rcases le_total (store.blocks a).slot (store.blocks b).slot with hle | hle
  · left
    have hcomp := congrArg ForkChoiceNode.root (get_ancestor_comp hwf hle hwa)
    have hroot := get_ancestor_root_eq_of_root_eq (store := store)
      (a := get_ancestor store (ForkChoiceNode.mk y .pending) (store.blocks b).slot)
      (b := ForkChoiceNode.mk b .pending) hb (store.blocks a).slot
    exact hroot.symm.trans (hcomp.trans ha)
  · right
    have hcomp := congrArg ForkChoiceNode.root (get_ancestor_comp hwf hle hwb)
    have hroot := get_ancestor_root_eq_of_root_eq (store := store)
      (a := get_ancestor store (ForkChoiceNode.mk y .pending) (store.blocks a).slot)
      (b := ForkChoiceNode.mk a .pending) ha (store.blocks b).slot
    exact hroot.symm.trans (hcomp.trans hb)

/-- Mutual beacon-root ancestry forces root equality. -/
theorem reroot_eq_of_mutual {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x start : Root} (hx : x ∈ store.block_roots) (hstart : start ∈ store.block_roots)
    (hxs : (get_ancestor store (ForkChoiceNode.mk x .pending) (store.blocks start).slot).root = start)
    (hsx : (get_ancestor store (ForkChoiceNode.mk start .pending) (store.blocks x).slot).root = x) :
    x = start := by
  have hle : (store.blocks x).slot ≤ (store.blocks start).slot := by
    have h := get_ancestor_slot_le hwf (hwalk x hx start hstart)
    rwa [hsx] at h
  rwa [get_ancestor_stop hle] at hxs

/-- A beacon ancestor between a parent and its direct child is one of those
roots. Payload nodes at the parent root do not introduce a third root. -/
theorem reroot_child_squeeze {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x start br : Root} (hx : x ∈ store.block_roots) (hstart : start ∈ store.block_roots)
    (hbr : br ∈ store.block_roots) (hbr_par : (store.blocks br).parent_root = start)
    (hxs : (get_ancestor store (ForkChoiceNode.mk x .pending) (store.blocks start).slot).root = start)
    (hbrx : (get_ancestor store (ForkChoiceNode.mk br .pending) (store.blocks x).slot).root = x) :
    x = start ∨ x = br := by
  have hle_sx : (store.blocks start).slot ≤ (store.blocks x).slot := by
    have h := get_ancestor_slot_le hwf (hwalk start hstart x hx)
    rwa [hxs] at h
  rcases eq_or_lt_of_le hle_sx with heq | hlt
  · left
    rwa [get_ancestor_stop (le_of_eq heq.symm)] at hxs
  · right
    rcases le_or_gt (store.blocks br).slot (store.blocks x).slot with hle | hgt
    · rw [get_ancestor_stop hle] at hbrx
      exact hbrx.symm
    · exfalso
      have hpw : WalkKnown store (store.blocks x).slot (store.blocks br).parent_root := by
        rw [hbr_par]
        exact WalkKnown.stop hstart (le_of_lt hlt)
      rw [get_ancestor_step hwf hbr hgt hpw, hbr_par,
        get_ancestor_stop (le_of_lt hlt)] at hbrx
      have : start = x := hbrx
      exact absurd (this ▸ hlt) (lt_irrefl _)

/-! ## The actual head path passes through the pending target -/

/-- Complete node equality uses both the beacon root and the payload status. -/
private theorem node_eq_pending {node : ForkChoiceNode Root} {r : Root}
    (hroot : node.root = r) (hstatus : node.payload_status = .pending) :
    node = ForkChoiceNode.mk r .pending := by
  cases node with
  | mk root status =>
    change root = r at hroot
    change status = .pending at hstatus
    rw [hroot, hstatus]

/-- Reroot an arbitrary-status head walk at a pending beacon ancestor.
If the target is already the start root, the start must itself be pending.
For a strict beacon descendant, the walk reaches its pending node through
an actual beacon-child edge. -/
theorem head_aux_reroot_node {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x : Root} (hx : x ∈ store.block_roots) :
    ∀ (fuel : ℕ) (start : ForkChoiceNode Root), start.root ∈ store.block_roots →
      (get_ancestor store (ForkChoiceNode.mk x .pending) (store.blocks start.root).slot).root =
        start.root →
      (get_ancestor store (get_head_aux cfg store blocks fuel start)
        (store.blocks x).slot).root = x →
      (x = start.root → start.payload_status = .pending) →
      ∃ N, get_head_aux cfg store blocks fuel start =
        get_head_aux cfg store blocks N (ForkChoiceNode.mk x .pending) := by
  intro fuel
  induction fuel with
  | zero =>
    intro start hstart hxs hhx hstatus
    change (get_ancestor store start (store.blocks x).slot).root = x at hhx
    have hsx : (get_ancestor store (ForkChoiceNode.mk start.root .pending)
        (store.blocks x).slot).root = x :=
      (get_ancestor_root_eq_of_root_eq (store := store)
        (a := start) (b := ForkChoiceNode.mk start.root .pending) rfl _).symm.trans hhx
    have hxeq := reroot_eq_of_mutual hwf hwalk hx hstart hxs hsx
    have hnode : start = ForkChoiceNode.mk x .pending :=
      node_eq_pending hxeq.symm (hstatus hxeq)
    exact ⟨0, by rw [hnode]⟩
  | succ fuel ih =>
    intro start hstart hxs hhx hstatus
    by_cases hxeq : x = start.root
    · have hnode : start = ForkChoiceNode.mk x .pending :=
        node_eq_pending hxeq.symm (hstatus hxeq)
      exact ⟨fuel + 1, by rw [hnode]⟩
    · cases hbest : (get_node_children store blocks start).argmax
          (fun child => toLex (get_weight cfg store child,
            toLex (child.root, get_payload_status_tiebreaker cfg store child))) with
      | none =>
        have hnil := List.argmax_eq_none.mp hbest
        rw [get_head_aux_leaf cfg store blocks fuel start hnil] at hhx
        have hsx : (get_ancestor store (ForkChoiceNode.mk start.root .pending)
            (store.blocks x).slot).root = x :=
          (get_ancestor_root_eq_of_root_eq (store := store)
            (a := start) (b := ForkChoiceNode.mk start.root .pending) rfl _).symm.trans hhx
        exact False.elim (hxeq (reroot_eq_of_mutual hwf hwalk hx hstart hxs hsx))
      | some best =>
        have hmem : best ∈ get_node_children store blocks start := List.argmax_mem hbest
        rw [get_head_aux_step cfg store blocks fuel start best hbest] at hhx ⊢
        rcases mem_get_node_children.mp hmem with hpending | hresolved
        · have hroot : best.root = start.root := hpending.2.1
          apply ih best
          · rwa [hroot]
          · simpa only [hroot] using hxs
          · exact hhx
          · intro heq
            exact False.elim (hxeq (heq.trans hroot))
        · obtain ⟨_, hbeststatus, hbestblocks, hparent, _⟩ := hresolved
          have hbestknown : best.root ∈ store.block_roots := hsub _ hbestblocks
          have hHbest : (get_ancestor store (get_head_aux cfg store blocks fuel best)
              (store.blocks best.root).slot).root = best.root := by
            apply get_head_aux_stays_below cfg hwf hsub fuel
              (WalkKnown.stop hbestknown (le_refl _))
            rw [get_ancestor_stop_status (le_refl _)]
          let H := get_head_aux cfg store blocks fuel best
          have hHknown : H.root ∈ store.block_roots := by
            rcases get_head_aux_root_mem_or cfg (store := store) (blocks := blocks) fuel best with h | h
            · exact hsub _ h
            · change H.root = best.root at h
              rwa [h]
          have hHbest' : (get_ancestor store (ForkChoiceNode.mk H.root .pending)
              (store.blocks best.root).slot).root = best.root :=
            (get_ancestor_root_eq_of_root_eq (store := store)
              (a := H) (b := ForkChoiceNode.mk H.root .pending) rfl _).symm.trans hHbest
          have hHx' : (get_ancestor store (ForkChoiceNode.mk H.root .pending)
              (store.blocks x).slot).root = x :=
            (get_ancestor_root_eq_of_root_eq (store := store)
              (a := H) (b := ForkChoiceNode.mk H.root .pending) rfl _).symm.trans hhx
          rcases reroot_comparable hwf
              (hwalk best.root hbestknown H.root hHknown)
              (hwalk x hx H.root hHknown) hHbest' hHx' with hxbest | hbestx
          · exact ih best hbestknown hxbest hhx (fun _ => hbeststatus)
          · rcases reroot_child_squeeze hwf hwalk hx hstart hbestknown
                hparent hxs hbestx with hxstart | hxbest
            · exact False.elim (hxeq hxstart)
            · have hnode : best = ForkChoiceNode.mk x .pending :=
                node_eq_pending hxbest.symm hbeststatus
              exact ⟨fuel, by rw [hnode]⟩

/-- Root-facing rerooting starts at a pending node. The local status premise
of `head_aux_reroot_node` therefore holds without an extra assumption. -/
theorem head_aux_reroot {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x : Root} (hx : x ∈ store.block_roots) :
    ∀ (fuel : ℕ) (start : Root), start ∈ store.block_roots →
      (get_ancestor store (ForkChoiceNode.mk x .pending) (store.blocks start).slot).root = start →
      (get_ancestor store (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk start .pending))
        (store.blocks x).slot).root = x →
      ∃ N, get_head_aux cfg store blocks fuel (ForkChoiceNode.mk start .pending) =
        get_head_aux cfg store blocks N (ForkChoiceNode.mk x .pending) := by
  intro fuel start hstart hxs hhx
  exact head_aux_reroot_node cfg hwf hsub hwalk hx fuel
    (ForkChoiceNode.mk start .pending) hstart hxs hhx (fun _ => rfl)

/-! ## Both kinds of node edge consume the finite walk budget -/

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

/-- A pending node needs one more node step than a resolved node at the
same root. Each strictly higher beacon root supplies two possible steps. -/
def head_walk_budget (store : Store Root) (blocks : List Root)
    (node : ForkChoiceNode Root) : ℕ :=
  2 * (blocks.filter (fun r => decide ((store.blocks node.root).slot <
    (store.blocks r).slot))).length + if node.payload_status = .pending then 1 else 0

/-- Every actual node edge strictly decreases the two-step beacon budget. -/
private theorem head_walk_budget_lt_of_child {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots)
    {start best : ForkChoiceNode Root} (hstart : start.root ∈ store.block_roots)
    (hmem : best ∈ get_node_children store blocks start) :
    head_walk_budget store blocks best < head_walk_budget store blocks start := by
  rcases mem_get_node_children.mp hmem with hpending | hresolved
  · obtain ⟨hstatus, hroot, hbeststatus⟩ := hpending
    have hresolved : best.payload_status ≠ .pending := by
      rcases hbeststatus with hempty | ⟨hfull, _⟩
      · simp [hempty]
      · simp [hfull]
    simp only [head_walk_budget, hroot, if_pos hstatus, if_neg hresolved]
    omega
  · obtain ⟨hstatus, hbeststatus, hbestblocks, hparent, _⟩ := hresolved
    have hbestknown := hsub _ hbestblocks
    have hlt : (store.blocks start.root).slot < (store.blocks best.root).slot := by
      have h := hwf best.root hbestknown (by rw [hparent]; exact hstart)
      rwa [hparent] at h
    have hcount := budget_lt_of_child hbestblocks hlt
    simp only [head_walk_budget, if_neg hstatus, if_pos hbeststatus]
    omega

/-- An arbitrary-status head walk reaches a childless node when its fuel
exceeds the budget for payload and beacon edges. -/
theorem walk_reaches_leaf_node {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) :
    ∀ (fuel : ℕ) (start : ForkChoiceNode Root), start.root ∈ store.block_roots →
      head_walk_budget store blocks start < fuel →
      get_node_children store blocks (get_head_aux cfg store blocks fuel start) = [] := by
  intro fuel
  induction fuel with
  | zero => intro start _ hbud; exact absurd hbud (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro start hstart hbud
    cases hbest : (get_node_children store blocks start).argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) with
    | none =>
      have hnil := List.argmax_eq_none.mp hbest
      rw [get_head_aux_leaf cfg store blocks fuel start hnil]
      exact hnil
    | some best =>
      have hmem : best ∈ get_node_children store blocks start := List.argmax_mem hbest
      have hbestknown : best.root ∈ store.block_roots := by
        rcases get_node_children_root_mem_or hmem with h | h
        · exact hsub _ h
        · rwa [h]
      have hdecrease := head_walk_budget_lt_of_child hwf hsub hstart hmem
      rw [get_head_aux_step cfg store blocks fuel start best hbest]
      exact ih best hbestknown (by omega)

/-- Pending-root form of the leaf bound. Each possible beacon descendant
requires two node steps, and the start root needs its payload resolution. -/
theorem walk_reaches_leaf {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) :
    ∀ (fuel : ℕ) (start : Root), start ∈ store.block_roots →
      2 * (blocks.filter (fun r => decide ((store.blocks start).slot <
        (store.blocks r).slot))).length + 1 < fuel →
      get_node_children store blocks
        (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk start .pending)) = [] := by
  intro fuel start hstart hbud
  apply walk_reaches_leaf_node cfg hwf hsub fuel (ForkChoiceNode.mk start .pending) hstart
  simpa [head_walk_budget] using hbud

/-- The Gloas head fuel `2 * blocks.length + 2` exceeds the budget for every
payload-resolution and beacon-child edge. Thus the head is childless. -/
theorem head_leaf {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots) :
    get_node_children store (get_filtered_block_tree cfg store) (get_head cfg store) = [] := by
  simp only [get_head]
  refine walk_reaches_leaf cfg hwf hsub _ store.justified_checkpoint.root hjust ?_
  have hcount : ((get_filtered_block_tree cfg store).filter (fun r =>
      decide ((store.blocks store.justified_checkpoint.root).slot <
        (store.blocks r).slot))).length ≤ (get_filtered_block_tree cfg store).length :=
    List.filter_sublist.length_le
  omega

/-! ## Continue actual selections from a head that is already a leaf -/

/-- A leaf reached from any node also follows every certified selection
from that node. A positive path cannot finish with zero remaining fuel,
since its current node has the selected child. -/
theorem head_ge_of_reroot_leaf_node {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots)
    {H : ForkChoiceNode Root} (hleaf : get_node_children store blocks H = [])
    {b : Root} {n : ℕ} {start : ForkChoiceNode Root}
    (hdesc : NodeDescendsTo cfg store blocks b n start) :
    (∃ fuel, H = get_head_aux cfg store blocks fuel start) →
      (get_ancestor store H (store.blocks b).slot).root = b := by
  induction hdesc with
  | here status hb =>
    rintro ⟨fuel, hH⟩
    rw [hH]
    apply get_head_aux_stays_below cfg hwf hsub fuel (WalkKnown.stop hb (le_refl _))
    rw [get_ancestor_stop_status (le_refl _)]
  | @step n head best hbest hrec ih =>
    rintro ⟨fuel, hH⟩
    cases fuel with
    | zero =>
      change H = head at hH
      have hchild := List.argmax_mem hbest
      rw [← hH, hleaf] at hchild
      exact absurd hchild List.not_mem_nil
    | succ fuel =>
      apply ih
      refine ⟨fuel, ?_⟩
      rw [hH, get_head_aux_step cfg store blocks fuel head best hbest]

/-- Root-facing continuation at a pending beacon node. The conclusion is
beacon-root ancestry and permits any final payload status. -/
theorem head_ge_of_reroot_leaf {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hleaf : get_node_children store (get_filtered_block_tree cfg store) (get_head cfg store) = [])
    {b : Root} {n : ℕ} {x : Root}
    (hdesc : DescendsTo cfg store (get_filtered_block_tree cfg store) b n x)
    (hex : ∃ N, get_head cfg store =
      get_head_aux cfg store (get_filtered_block_tree cfg store) N (ForkChoiceNode.mk x .pending))
    (_hhx : (get_ancestor store (get_head cfg store) (store.blocks x).slot).root = x) :
    (get_ancestor store (get_head cfg store) (store.blocks b).slot).root = b :=
  head_ge_of_reroot_leaf_node cfg hwf hsub hleaf hdesc hex


/-- If the head descends from an intermediate pending root and an actual
Gloas descent path continues from that root to `b`, the head descends from
`b`. This statement retains its root-facing public interface. -/

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
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hxj hhx ⊢
  have hgd : get_head cfg store =
      get_head_aux cfg store (get_filtered_block_tree cfg store)
        (2 * (get_filtered_block_tree cfg store).length + 2)
        (ForkChoiceNode.mk store.justified_checkpoint.root .pending) := rfl
  have hleaf := head_leaf cfg hwf hsub hjust
  have hreroot : ∃ N, get_head cfg store =
      get_head_aux cfg store (get_filtered_block_tree cfg store) N (ForkChoiceNode.mk x .pending) := by
    rw [hgd]
    exact head_aux_reroot cfg hwf hsub hwalk hx _ store.justified_checkpoint.root hjust hxj
      (by rw [← hgd]; exact hhx)
  exact head_ge_of_reroot_leaf cfg hwf hsub hleaf hdesc hreroot hhx

end FastConfirmation.Spec

end
