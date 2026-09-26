module
public import FastConfirmationProofs.FFG.Concrete.TransitionFrames

@[expose] public section

/-! Proves the accepted-chain history facts of the concrete FFG model: chain
roots at earlier slots are stable when a later block is appended, parent links
compose, and one slot step keeps the block-root ring equal to the chain roots. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

theorem chainRootAt_of_forall_le {genesisRoot : Root} {blocks : List (FFGWireBlock Root)}
    {slot : Slot} (h : ∀ b ∈ blocks, b.slot ≤ slot) :
    chainRootAt genesisRoot blocks slot = tipRoot genesisRoot blocks := by
  unfold chainRootAt tipRoot
  rw [List.filter_eq_self.mpr (fun b hb => by simpa using h b hb)]

theorem chainRootAt_append_of_lt {genesisRoot : Root} {blocks : List (FFGWireBlock Root)}
    {block : FFGWireBlock Root} {slot : Slot} (h : slot < block.slot) :
    chainRootAt genesisRoot (blocks ++ [block]) slot = chainRootAt genesisRoot blocks slot := by
  unfold chainRootAt
  rw [List.filter_append]
  have : [block].filter (fun b => decide (b.slot ≤ slot)) = [] := by
    simp [Nat.not_le.mpr h]
  rw [this, List.append_nil]

theorem tipRoot_append {genesisRoot : Root} {blocks : List (FFGWireBlock Root)}
    {block : FFGWireBlock Root} : tipRoot genesisRoot (blocks ++ [block]) = block.root := by
  simp [tipRoot]

theorem tipSlot_append {blocks : List (FFGWireBlock Root)} {block : FFGWireBlock Root} :
    tipSlot (blocks ++ [block]) = block.slot := by
  simp [tipSlot]

theorem tipRoot_cons {genesisRoot : Root} {block : FFGWireBlock Root}
    {blocks : List (FFGWireBlock Root)} :
    tipRoot genesisRoot (block :: blocks) = tipRoot block.root blocks := by
  cases h : blocks.getLast? <;> simp [tipRoot, List.getLast?_cons, h]

theorem parentLinked_append {genesisRoot : Root} {blocks : List (FFGWireBlock Root)}
    {block : FFGWireBlock Root} :
    ParentLinked genesisRoot (blocks ++ [block]) ↔
      ParentLinked genesisRoot blocks ∧ block.parent_root = tipRoot genesisRoot blocks := by
  induction blocks generalizing genesisRoot with
  | nil => simp [ParentLinked, tipRoot]
  | cons a blocks ih =>
    simp only [List.cons_append, ParentLinked, ih, tipRoot_cons]
    tauto

theorem mod_ne_of_lt_of_lt_add {x y n : ℕ} (hyx : y < x) (hxy : x < y + n) :
    x % n ≠ y % n := by
  intro h
  have hx := Nat.mod_add_div x n
  have hy := Nat.mod_add_div y n
  rcases Nat.lt_or_ge (x / n) (y / n + 1) with hq | hq
  · have : n * (x / n) ≤ n * (y / n) := Nat.mul_le_mul_left n (by omega)
    omega
  · have : n * (y / n + 1) ≤ n * (x / n) := Nat.mul_le_mul_left n hq
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-- After `process_slot` writes the chain root of the current slot and the
slot increments, every ring cell in range holds the chain root of its slot. -/
theorem ring_after_slot {roots : List Root} {n x : ℕ} {chain : Slot → Root}
    (hlen : roots.length = n) (hn : 0 < n)
    (hring : ∀ y, y < x → x ≤ y + n → roots[y % n]? = some (chain y)) :
    ∀ y, y < x + 1 → x + 1 ≤ y + n → (roots.set (x % n) (chain x))[y % n]? = some (chain y) := by
  intro y hy1 hy2
  by_cases hyx : y = x
  · subst hyx
    rw [List.getElem?_set_self (by rw [hlen]; exact Nat.mod_lt _ hn)]
  · rw [List.getElem?_set_ne (mod_ne_of_lt_of_lt_add (by omega) (by omega))]
    exact hring y (by omega) (by omega)

end FastConfirmation.Spec.ConcreteFFG

end
