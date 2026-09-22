module
public import FastConfirmation.Spec.Proof.Genesis

@[expose] public section

/-!
# Spec / Proof / Ancestry

Layer 0, the ancestry toolkit: fuel elimination for `get_ancestor`. The
python recursion is defined exactly on walks that stay inside the store's
known blocks; `WalkKnown` captures that domain, and on it the fuel-bounded
`get_ancestor_aux` is fuel-independent (any fuel above the walked block's
slot computes the same value), unlocking the python-shaped unfold equations
(`get_ancestor_stop`/`get_ancestor_step`) the later layers rewrite with.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- The parent-walk from `r` down to `slot` stays inside the store's known
blocks — the domain on which python's `get_ancestor` recursion is defined.
Uses the store's own `parent_slot_lt` discipline implicitly: derivations are
finite by construction. -/
inductive WalkKnown (store : Store Root) (slot : Slot) : Root → Prop
  | stop {r : Root} (hr : r ∈ store.block_roots)
      (hle : (store.blocks r).slot ≤ slot) : WalkKnown store slot r
  | step {r : Root} (hr : r ∈ store.block_roots)
      (hgt : slot < (store.blocks r).slot)
      (hp : WalkKnown store slot (store.blocks r).parent_root) :
      WalkKnown store slot r

namespace WalkKnown

theorem root_mem {store : Store Root} {slot : Slot} {r : Root}
    (h : WalkKnown store slot r) : r ∈ store.block_roots := by
  cases h with
  | stop hr _ => exact hr
  | step hr _ _ => exact hr

end WalkKnown

variable [LinearOrder Root] [Inhabited Root]

omit [LinearOrder Root] [Inhabited Root] in
/-- Fuel independence on the known domain: any fuel above the walked block's
slot computes the same ancestor (strong induction on the walk, slots
strictly decreasing by `parent_slot_lt`). -/
theorem get_ancestor_aux_fuel_eq {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    ∀ fuel fuel' : ℕ, (store.blocks r).slot < fuel → (store.blocks r).slot < fuel' →
      get_ancestor_aux store slot fuel (ForkChoiceNode.mk r) =
        get_ancestor_aux store slot fuel' (ForkChoiceNode.mk r) := by
  induction hw with
  | stop hr hle =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      cases fuel' with
      | zero => exact absurd hf' (Nat.not_lt_zero _)
      | succ f' =>
        rw [get_ancestor_aux, get_ancestor_aux]
        rw [if_neg (by simpa using hle), if_neg (by simpa using hle)]
  | step hr hgt hp ih =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      cases fuel' with
      | zero => exact absurd hf' (Nat.not_lt_zero _)
      | succ f' =>
        rw [get_ancestor_aux, get_ancestor_aux]
        rw [if_pos (by simpa using hgt), if_pos (by simpa using hgt)]
        have hparent_lt := hwf _ hr hp.root_mem
        exact ih f f'
          (Nat.lt_of_lt_of_le hparent_lt (Nat.lt_succ_iff.mp hf))
          (Nat.lt_of_lt_of_le hparent_lt (Nat.lt_succ_iff.mp hf'))

omit [LinearOrder Root] [Inhabited Root] in
/-- Python-shaped stop equation: at or below the requested slot the walk
returns the node itself (no domain condition needed — the wrapper's first
unfold suffices). -/
theorem get_ancestor_stop {store : Store Root} {slot : Slot} {r : Root}
    (hle : (store.blocks r).slot ≤ slot) :
    get_ancestor store (ForkChoiceNode.mk r) slot = ForkChoiceNode.mk r := by
  rw [get_ancestor, get_ancestor_aux, if_neg (by simpa using hle)]

omit [LinearOrder Root] [Inhabited Root] in
/-- Python-shaped step equation on the known domain: above the requested slot
the walk continues from the parent. -/
theorem get_ancestor_step {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hr : r ∈ store.block_roots)
    (hgt : slot < (store.blocks r).slot)
    (hp : WalkKnown store slot (store.blocks r).parent_root) :
    get_ancestor store (ForkChoiceNode.mk r) slot =
      get_ancestor store (ForkChoiceNode.mk (store.blocks r).parent_root) slot := by
  rw [get_ancestor, get_ancestor_aux, if_pos (by simpa using hgt)]
  rw [get_ancestor]
  exact get_ancestor_aux_fuel_eq hwf hp _ _ (hwf _ hr hp.root_mem)
    (Nat.lt_succ_self _)

omit [LinearOrder Root] [Inhabited Root] in
/-- On the known domain the walk lands on a known block at or below the
requested slot — python's postcondition. -/
theorem get_ancestor_spec {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    (get_ancestor store (ForkChoiceNode.mk r) slot).root ∈ store.block_roots ∧
      (store.blocks (get_ancestor store (ForkChoiceNode.mk r) slot).root).slot ≤
        slot := by
  induction hw with
  | stop hr hle =>
    rw [get_ancestor_stop hle]
    exact ⟨hr, hle⟩
  | step hr hgt hp ih =>
    rw [get_ancestor_step hwf hr hgt hp]
    exact ih

end FastConfirmation.Spec

end
