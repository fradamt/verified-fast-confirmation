module
public import FastConfirmation.Spec.Proof.AncestryRoots

@[expose] public section

/-!
# Spec / Proof / Forks

Layer 0, the fork toolkit built on the `Proof/AncestryRoots.lean` ancestry
order facts. The headline fact is `siblings_incompatible`: two *distinct*
children of one parent have no common descendant. It is the disjointness input
the head-safety engine's sibling bound (design plan L3, step E3) needs — a
supporter of one sibling can never also support another.

Everything reuses `WalkKnown`, `get_ancestor_comp`, `get_ancestor_step` /
`get_ancestor_stop` from `Proof/Ancestry.lean` / `Proof/AncestryRoots.lean`; the
only behavioral premise is the `parent_slot_lt`-shaped `hwf`, exactly the
`WellFormedStore.parent_slot_lt` field, plus a `WalkKnown` witness for the
common-descendant walk (without it `is_ancestor` could be a fuel-exhaustion
artifact on an ill-formed store).

The fork-point existence direction of `Forks` is not delivered: the L3 design's
step E3 consumes only `siblings_incompatible`, so scope is kept tight per the
package spec.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root]

/-! ## Ancestor determinism at a fixed slot -/

/-- Two ancestors of the same node sitting at the same slot coincide — a purely
definitional consequence of `get_ancestor` being a function (needs no
well-formedness). If `a` and `b` are both ancestors of `x` and
`(blocks a).slot = (blocks b).slot`, then `a = b`. -/
theorem ancestor_unique_at_slot {store : Store Root} {x a b : Root}
    (hsl : (store.blocks a).slot = (store.blocks b).slot)
    (ha : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk a .pending) = true)
    (hb : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk b .pending) = true) :
    a = b := by
  simp only [is_ancestor_pending, decide_eq_true_eq] at ha hb
  rw [hsl] at ha
  simpa using ha.symm.trans hb

/-! ## Siblings share no descendant -/

/-- Asymmetric core: with `c`'s slot at or below `c'`'s, distinct siblings `c`,
`c'` (both children of `p`) have no common descendant `x`. The walk from `x`
down to `c`'s slot factors through `c'` (via `get_ancestor_comp` + `hac'`), but
that walk continues past `c'` to its parent `p` (one step, since `c`'s slot is
strictly below `c'`'s) and stops there — so it would have to equal `c`, forcing
`p = c`, contradicting `parent_slot_lt`. The equal-slot case collapses directly
by `get_ancestor` determinism. -/
theorem no_common_descendant_of_slot_le {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {p c c' x : Root}
    (hc : c ∈ store.block_roots) (hc' : c' ∈ store.block_roots)
    (hp : p ∈ store.block_roots)
    (hpc : (store.blocks c).parent_root = p)
    (hpc' : (store.blocks c').parent_root = p)
    (hne : c ≠ c')
    (hle : (store.blocks c).slot ≤ (store.blocks c').slot)
    (hwx : WalkKnown store (store.blocks c).slot x)
    (hac : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk c .pending) = true)
    (hac' : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk c' .pending) = true) :
    False := by
  simp only [is_ancestor_pending, decide_eq_true_eq] at hac hac'
  have hpslt : (store.blocks p).slot < (store.blocks c).slot := by
    have := hwf c hc (by rw [hpc]; exact hp)
    rwa [hpc] at this
  rcases hle.lt_or_eq with hlt | heq
  · have hcomp := get_ancestor_comp_root hwf hle hwx
    rw [hac', hac] at hcomp
    have hwp : WalkKnown store (store.blocks c).slot (store.blocks c').parent_root := by
      rw [hpc']; exact WalkKnown.stop hp hpslt.le
    rw [get_ancestor_step hwf hc' hlt hwp, hpc', get_ancestor_stop hpslt.le] at hcomp
    have hpc_eq : p = c := by simpa using hcomp
    rw [hpc_eq] at hpslt
    exact absurd hpslt (lt_irrefl _)
  · rw [heq] at hac
    exact hne (by simpa using hac.symm.trans hac')

/-- **Siblings are incompatible.** Two distinct children `c ≠ c'` of one parent
`p` (all three known blocks) have no common descendant: no known-walk node `x`
is an ancestor-descendant of both. Symmetric wrapper over
`no_common_descendant_of_slot_le`, dispatching on which sibling sits lower.
The `WalkKnown` witnesses pin `x`'s parent-walk down to each sibling's slot,
ruling out a fuel-exhaustion `is_ancestor` on an ill-formed store. -/
theorem siblings_incompatible {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {p c c' x : Root}
    (hc : c ∈ store.block_roots) (hc' : c' ∈ store.block_roots)
    (hp : p ∈ store.block_roots)
    (hpc : (store.blocks c).parent_root = p)
    (hpc' : (store.blocks c').parent_root = p)
    (hne : c ≠ c')
    (hwc : WalkKnown store (store.blocks c).slot x)
    (hwc' : WalkKnown store (store.blocks c').slot x)
    (hac : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk c .pending) = true)
    (hac' : is_ancestor store (ForkChoiceNode.mk x .pending) (ForkChoiceNode.mk c' .pending) = true) :
    False := by
  rcases le_total (store.blocks c).slot (store.blocks c').slot with hle | hle
  · exact no_common_descendant_of_slot_le hwf hc hc' hp hpc hpc' hne hle hwc hac hac'
  · exact no_common_descendant_of_slot_le hwf hc' hc hp hpc' hpc hne.symm hle hwc' hac' hac

end FastConfirmation.Spec

end
