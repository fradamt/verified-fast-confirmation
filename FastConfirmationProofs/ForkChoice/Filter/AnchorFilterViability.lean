module
public import FastConfirmationProofs.FFG.SourceHistory.StoreDynamicsInputs
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.Execution.Trajectory.StoreDynamicsInputs

@[expose] public section

/-!
# Spec / Proof / E5Filter

Proves that the trusted anchor remains a viable filtered fork-choice candidate.

This module contains `walkClosure_of_anchorSlot`, `walkKnown_of_anchorSlot`, `output_descends_step_K` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the filter-route head lemma

The head of an honest store dominates every `JustifiedIn` checkpoint whose root is
known. The store's own realized justified checkpoint `jc` is `JustifiedIn`
(`Or.inl rfl`), and every filtered root — hence the head — descends from `jc`
(`EngineStore.filtered_through_justified`). For a `JustifiedIn` `c` at-or-below `jc`'s
epoch, `justified_ancestry` puts `c` on `jc`'s chain, so the head descends past `c`. -/










end Execution



omit [LinearOrder Root] [Inhabited Root] in
/-- **`WalkClosure` at target `sl ≥ anchorSlot` from the sound anchor-min fact.** The
reshaped producer: instead of the `∀ sl` guard `parent = P → slot ≤ sl` (false at
`sl < anchorSlot`), it needs only the fixed-slot anchor-min fact `parent = P → slot ≤
anchorSlot` (sound — the only `P`-parented block is the anchor, at `anchorSlot`) together
with `anchorSlot ≤ sl`. `walkClosure_of_min` then closes `WalkClosure store sl`. -/
theorem walkClosure_of_anchorSlot {store : Store Root} {P : Root} {anchorSlot sl : Slot}
    (hQ : ParentInRootsOr P store)
    (hanc : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root = P → (store.blocks r).slot ≤ anchorSlot)
    (hsl : anchorSlot ≤ sl) :
    WalkClosure store sl :=
  walkClosure_of_min hQ (fun r hr hP => le_trans (hanc r hr hP) hsl)

omit [LinearOrder Root] [Inhabited Root] in
/-- **`WalkKnown` at every target `sl ≥ anchorSlot`.** Composes `walkClosure_of_anchorSlot`
with `walkKnown_of_closure` (the `ParentSlotLt` + closure → `WalkKnown` builder): for
`sl ≥ anchorSlot`, every known root's walk down to `sl` stays known, with no `anchor_guard`
— only the sound fixed-slot anchor-min fact. -/
theorem walkKnown_of_anchorSlot {store : Store Root} {P : Root} {anchorSlot sl : Slot}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hQ : ParentInRootsOr P store)
    (hanc : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root = P → (store.blocks r).slot ≤ anchorSlot)
    (hsl : anchorSlot ≤ sl) :
    ∀ r ∈ store.block_roots, WalkKnown store sl r :=
  walkKnown_of_closure sl hwf (walkClosure_of_anchorSlot hQ hanc hsl)

/-! ### The descent chain with a target-known walk domain (`_K`)

Re-proofs of `EngineStore`'s filter-output descent lemmas with the walk domain
`hwalkK : ∀ t ∈ block_roots, ∀ r ∈ block_roots, WalkKnown store (blocks t).slot r`
(targets restricted to known blocks) in place of the committed blanket `hwalk`. The
proofs are the committed bodies verbatim, threading the extra `t ∈ block_roots` witness at
each `hwalk` call (always available — `base`/`b`/`justified-root` are known). This makes the
FFG-takeover head lemma consume only walks to known-block slots. -/

omit [Inhabited Root] in
/-- Inductive step of `filter_block_tree_aux_output_descends_K` — `EngineStore`'s
`output_descends_step` with the target-known walk `hwalkK` (base is known: `hbase`). -/
private theorem output_descends_step_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {base : Root} (hbase : base ∈ store.block_roots) {fuel : ℕ}
    (ih : ∀ b' : Root, b' ∈ store.block_roots → ∀ r,
      r ∈ (filter_block_tree_aux cfg store fuel b').2 →
        is_ancestor store (ForkChoiceNode.mk r .pending) (ForkChoiceNode.mk b' .pending) = true)
    {child r : Root}
    (hchild : child ∈ store.block_roots.filter
      (fun root => (store.blocks root).parent_root = base))
    (hrl : r ∈ (filter_block_tree_aux cfg store fuel child).2) :
    is_ancestor store (ForkChoiceNode.mk r .pending) (ForkChoiceNode.mk base .pending) = true := by
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
  exact is_ancestor_trans hwf (hwalkK base hbase r hr_mem) (hwalkK base hbase child hchild_mem)
    hac hcb

omit [Inhabited Root] in
/-- **Filter-output descent with a target-known walk** — `EngineStore`'s
`filter_block_tree_aux_output_descends` re-proved with `hwalkK`. Every root the worker
emits from `base` (known) descends from `base`. -/
theorem filter_block_tree_aux_output_descends_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    ∀ (fuel : ℕ) (base : Root), base ∈ store.block_roots →
      ∀ r, r ∈ (filter_block_tree_aux cfg store fuel base).2 →
        is_ancestor store (ForkChoiceNode.mk r .pending) (ForkChoiceNode.mk base .pending) = true := by
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
          exact output_descends_step_K cfg hwf hwalkK hbase ih hchild hrl
        · rw [List.mem_singleton] at hr'
          subst hr'
          exact is_ancestor_refl store _
      · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr
        obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
        exact output_descends_step_K cfg hwf hwalkK hbase ih hchild hrl
    · rw [not_not] at hne
      rw [filter_block_tree_aux_leaf cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr
      · rw [List.mem_singleton] at hr
        subst hr
        exact is_ancestor_refl store _
      · exact absurd hr List.not_mem_nil

omit [Inhabited Root] in
/-- **Every filtered root descends from the justified root, target-known walk.**
`EngineStore.filtered_through_justified` re-proved with `hwalkK`. -/
theorem filtered_through_justified_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {r : Root} (hr : r ∈ get_filtered_block_tree cfg store) :
    is_ancestor store (get_node_for_root r)
      (get_node_for_root store.justified_checkpoint.root) = true := by
  simp only [get_node_for_root]
  have hr' : r ∈ (filter_block_tree_aux cfg store (store.block_roots.length + 1)
      store.justified_checkpoint.root).2 := hr
  exact filter_block_tree_aux_output_descends_K cfg hwf hwalkK _ _ hjust r hr'

/-- **FFG-takeover head lemma with a target-known walk** — `EngineStore.head_ge_of_justified_ge`
re-proved with `hwalkK`. Adds `hb : b ∈ block_roots` (the target block is known — always
so at the genuine call sites), which lets the final `is_ancestor_trans` use walks to the
known slot `(blocks b).slot`. No `anchor_guard`: `hwalkK` is dischargeable from
`walkKnown_of_anchorSlot` at every needed (known-block) target. -/
theorem head_ge_of_justified_ge_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {b : Root} (hb : b ∈ store.block_roots)
    (hjb : is_ancestor store (get_node_for_root store.justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  rw [is_ancestor_node_root]
  simp only [get_node_for_root] at hjb ⊢
  have hmem : (get_head cfg store).root ∈ get_filtered_block_tree cfg store ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg (2 * (get_filtered_block_tree cfg store).length + 2)
      (ForkChoiceNode.mk store.justified_checkpoint.root .pending)
  rcases hmem with hin | heq
  · have hgt := filtered_through_justified_K cfg hwf hwalkK hjust hin
    simp only [get_node_for_root] at hgt
    have hqr_mem : (get_head cfg store).root ∈ store.block_roots := by
      have hin' : (get_head cfg store).root ∈
          (filter_block_tree_aux cfg store (store.block_roots.length + 1)
            store.justified_checkpoint.root).2 := hin
      rcases filter_block_tree_aux_output_mem cfg _ _ _ hin' with h | h
      · exact h
      · rw [h]; exact hjust
    exact is_ancestor_trans hwf (hwalkK b hb _ hqr_mem) (hwalkK b hb _ hjust) hgt hjb
  · change is_ancestor store (ForkChoiceNode.mk (get_head cfg store).root .pending)
      (ForkChoiceNode.mk b .pending) = true
    rw [heq]
    exact hjb

namespace Execution

variable (E : Execution Root)


end Execution

/-! ## Section 2 — `Spec_Safety` via the observed-anchor filter route -/


end FastConfirmation.Spec

end
