import FastConfirmation.Spec.Proof.FilterFuel
import FastConfirmation.Spec.Proof.AncestryRoots

/-!
# Spec / Proof / Descent

Layer 0, the E1 GHOST-descent mechanics: `get_head`'s child-descent follows a
weight-dominant chain down to a target block `b`, so `b` ends up an ancestor of
the computed head.

The fork condition the descent needs at every step — the `b`-side child strictly
dominates every sibling in `get_weight` — is packaged as the explicit predicate
`DescendsTo`, a parent-linked path of dominant argmax children from a start root
down to `b`, indexed by its length. The L3 engine supplies a `DescendsTo`
witness from E2 + E3 + L2; this module is purely the descent bookkeeping.

Contents:

* `DescendsTo` — the dominant-descent path predicate.
* `get_head_aux_stays_below` — once the descent has reached a descendant of `b`,
  every further `get_head_aux` step stays a descendant of `b` (the invariant
  `get_ancestor · (slot b) = b`, preserved down the tree).
* `get_head_descends` — following a `DescendsTo` path with enough fuel lands
  `get_head_aux` on a descendant of `b`.
* `is_ancestor_get_head` — the headline: under a `DescendsTo` path from the
  justified root to `b`, `is_ancestor store (get_head store) b = true`.

Domain hypotheses are the usual `WellFormedStore.parent_slot_lt` shape (`hwf`)
and `blocks ⊆ store.block_roots` (`hsub`) — the filtered-tree containment
`FilterViability` establishes; here it stays a plain hypothesis.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## The dominant-descent path predicate -/

/-- `DescendsTo cfg store blocks b n h`: from root `h` there is a length-`n`
parent-linked path of weight-dominant argmax children ending at `b`. At each
step the chosen child is a `get_node_children` member whose `get_weight`
strictly exceeds every sibling's, so `get_head_aux`'s argmax picks it. -/
inductive DescendsTo (cfg : Config) (store : Store Root) (blocks : List Root) (b : Root) :
    ℕ → Root → Prop
  | here (hb : b ∈ store.block_roots) : DescendsTo cfg store blocks b 0 b
  | step {n : ℕ} {h c : Root}
      (hchild : ForkChoiceNode.mk c ∈ get_node_children store blocks (ForkChoiceNode.mk h))
      (hdom : ∀ c' ∈ get_node_children store blocks (ForkChoiceNode.mk h),
          c' ≠ ForkChoiceNode.mk c →
            get_weight cfg store c' < get_weight cfg store (ForkChoiceNode.mk c))
      (hrec : DescendsTo cfg store blocks b n c) :
      DescendsTo cfg store blocks b (n + 1) h

/-! ## The descent stays below the target -/

/-- Descent invariant: if `h` is already a descendant of `b`
(`get_ancestor · (slot b) = b`) on the known walk domain, every further
`get_head_aux` step keeps the result a descendant of `b`. Each argmax child sits
one `parent_slot_lt` step below `h`, so the walk down to `b`'s slot factors
through `h` and still lands on `b`. -/
theorem get_head_aux_stays_below {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) {b : Root} :
    ∀ (fuel : ℕ) {h : Root},
      WalkKnown store (store.blocks b).slot h →
      get_ancestor store (ForkChoiceNode.mk h) (store.blocks b).slot = ForkChoiceNode.mk b →
      get_ancestor store (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk h))
        (store.blocks b).slot = ForkChoiceNode.mk b := by
  intro fuel
  induction fuel with
  | zero => intro h _ hanc; simpa [get_head_aux] using hanc
  | succ f ih =>
    intro h hwalk hanc
    rw [get_head_aux_succ]
    rcases hbest : (get_node_children store blocks (ForkChoiceNode.mk h)).argmax
        (fun child => toLex (get_weight cfg store child, child.root)) with _ | best
    · exact hanc
    · obtain ⟨br⟩ := best
      have hmem : ForkChoiceNode.mk br ∈ get_node_children store blocks (ForkChoiceNode.mk h) :=
        List.argmax_mem hbest
      rw [mem_get_node_children] at hmem
      obtain ⟨hbr_blocks, hbr_par⟩ := hmem
      have hbr_mem : br ∈ store.block_roots := hsub br hbr_blocks
      have hh_mem : h ∈ store.block_roots := hwalk.root_mem
      have hpar_lt :
          (store.blocks (store.blocks br).parent_root).slot < (store.blocks br).slot :=
        hwf br hbr_mem (by rw [hbr_par]; exact hh_mem)
      rw [hbr_par] at hpar_lt
      have hb_le_h : (store.blocks b).slot ≤ (store.blocks h).slot := by
        have h1 := get_ancestor_slot_le hwf hwalk
        rw [hanc] at h1; simpa using h1
      have hgt : (store.blocks b).slot < (store.blocks br).slot :=
        lt_of_le_of_lt hb_le_h hpar_lt
      have hwalk_br : WalkKnown store (store.blocks b).slot br :=
        WalkKnown.step hbr_mem hgt (by rw [hbr_par]; exact hwalk)
      have hanc_br : get_ancestor store (ForkChoiceNode.mk br) (store.blocks b).slot =
          ForkChoiceNode.mk b := by
        rw [get_ancestor_step hwf hbr_mem hgt (by rw [hbr_par]; exact hwalk), hbr_par]
        exact hanc
      exact ih hwalk_br hanc_br

/-! ## Following the descent path -/

/-- Following a `DescendsTo` path from `h` to `b` with fuel at least the path
length lands `get_head_aux` on a descendant of `b`. Induction on the path: each
`step` peels one dominant argmax child (`get_head_argmax_dominant`); the `here`
base falls to `get_head_aux_stays_below`. -/
theorem get_head_descends {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) {b : Root} {n : ℕ} {h : Root}
    (hdesc : DescendsTo cfg store blocks b n h) :
    ∀ fuel, n ≤ fuel →
      get_ancestor store (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk h))
        (store.blocks b).slot = ForkChoiceNode.mk b := by
  induction hdesc with
  | here hb =>
      intro fuel _
      exact get_head_aux_stays_below cfg hwf hsub fuel
        (WalkKnown.stop hb (le_refl _)) (get_ancestor_stop (le_refl _))
  | @step n h c hchild hdom _ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ f =>
          rw [get_head_aux_step cfg store blocks f (ForkChoiceNode.mk h) (ForkChoiceNode.mk c)
                (get_head_argmax_dominant cfg hchild hdom)]
          exact ih f (by omega)

/-- E1 headline: if there is a dominant-descent path from the justified root to
`b` within the filtered block tree, then the fork-choice head is a descendant of
`b`. `hfuel` (path length ≤ tree size) is discharged by path distinctness at L3;
`hsub` is the filtered-tree containment `FilterViability` establishes. -/
theorem is_ancestor_get_head {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {n : ℕ}
    (hdesc : DescendsTo cfg store (get_filtered_block_tree cfg store) b n
      store.justified_checkpoint.root)
    (hfuel : n ≤ (get_filtered_block_tree cfg store).length + 1) :
    is_ancestor store (get_head cfg store) (ForkChoiceNode.mk b) = true := by
  simp only [is_ancestor, get_head, decide_eq_true_eq]
  exact get_head_descends cfg hwf hsub hdesc
    ((get_filtered_block_tree cfg store).length + 1) hfuel

end FastConfirmation.Spec
