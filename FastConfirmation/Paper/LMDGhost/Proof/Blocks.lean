import Mathlib.Tactic
import FastConfirmation.Paper.Core.Model.View

/-!
# LMDGhost / Proof / Blocks

Pure `Block` / `Ancestor` combinatorics used by the GHOST canonicality argument:
transitivity of ancestry, genesis is a global ancestor, and slot/well-formedness
monotonicity along ancestry.
-/

namespace FastConfirmation

open scoped Block

variable {n : ℕ}

/-- Ancestry is transitive. -/
theorem Block.Ancestor.trans {a b c : Block n} (h1 : a ≼ b) (h2 : b ≼ c) : a ≼ c := by
  induction h2 with
  | refl => exact h1
  | step _ ih => exact Block.Ancestor.step ih
  | stepWithVotes _ ih => exact Block.Ancestor.stepWithVotes ih

/-- Genesis is an ancestor of every block. -/
theorem genesis_ancestor (x : Block n) : Block.genesis ≼ x := by
  induction x with
  | genesis => exact Block.Ancestor.refl _
  | mk _ _ _ ih => exact Block.Ancestor.step ih
  | mkWithVotes _ _ _ _ ih => exact Block.Ancestor.stepWithVotes ih

/-- Well-formedness is inherited by ancestors. -/
theorem WellFormed_of_ancestor {a b : Block n} (h : a ≼ b) : b.WellFormed → a.WellFormed := by
  induction h with
  | refl => intro hWF; exact hWF
  | step _ ih => intro hWF; simp only [Block.WellFormed] at hWF; exact ih hWF.2
  | stepWithVotes _ ih => intro hWF; simp only [Block.WellFormed] at hWF; exact ih hWF.2

/-- In a well-formed block, ancestors have not-greater slots. -/
theorem slot_le_of_ancestor {a b : Block n} (h : a ≼ b) : b.WellFormed → a.slot ≤ b.slot := by
  induction h with
  | refl => intro _; exact le_refl _
  | step _ ih =>
    intro hWF
    simp only [Block.WellFormed] at hWF
    exact le_trans (ih hWF.2) (le_of_lt hWF.1)
  | stepWithVotes _ ih =>
    intro hWF
    simp only [Block.WellFormed] at hWF
    exact le_trans (ih hWF.2) (le_of_lt hWF.1)

/-- Two ancestors of a common block are comparable (parent-pointer linearity). -/
theorem ancestor_comparable {x : Block n} :
    ∀ {a b : Block n}, a ≼ x → b ≼ x → a ~ b := by
  induction x with
  | genesis => intro a b ha hb; cases ha; cases hb; exact Or.inl (Block.Ancestor.refl _)
  | mk bid p s ih =>
    intro a b ha hb
    cases ha with
    | refl => exact Or.inr hb
    | step ha' =>
      cases hb with
      | refl => exact Or.inl (Block.Ancestor.step ha')
      | step hb' => exact ih ha' hb'
  | mkWithVotes bid p s votes ih =>
    intro a b ha hb
    cases ha with
    | refl => exact Or.inr hb
    | stepWithVotes ha' =>
      cases hb with
      | refl => exact Or.inl (Block.Ancestor.stepWithVotes ha')
      | stepWithVotes hb' => exact ih ha' hb'

/-- The `Ancestor` relation implies the executable ancestry test. -/
theorem isAncestorOf_of_ancestor {B C : Block n} (h : B ≼ C) : B.isAncestorOf C = true := by
  induction h with
  | refl => cases B <;> simp [Block.isAncestorOf]
  | step _ ih => simp [Block.isAncestorOf, ih]
  | stepWithVotes _ ih => simp [Block.isAncestorOf, ih]

/-- The executable ancestry test implies the `Ancestor` relation. -/
theorem isAncestorOf_imp {B : Block n} : ∀ {C : Block n}, B.isAncestorOf C = true → B ≼ C := by
  intro C
  induction C with
  | genesis =>
    intro h
    simp only [Block.isAncestorOf, decide_eq_true_eq] at h
    exact h ▸ Block.Ancestor.refl _
  | mk bid p s ih =>
    intro h
    simp only [Block.isAncestorOf, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h1 | h2
    · exact h1 ▸ Block.Ancestor.refl _
    · exact Block.Ancestor.step (ih h2)
  | mkWithVotes bid p s votes ih =>
    intro h
    simp only [Block.isAncestorOf, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h1 | h2
    · exact h1 ▸ Block.Ancestor.refl _
    · exact Block.Ancestor.stepWithVotes (ih h2)

/-- The child of `a` on the path to a strict descendant `b` exists. -/
theorem chain_child {a b : Block n} (hab : a ≼ b) (hne : a ≠ b) :
    ∃ c, c.parent? = some a ∧ a ≼ c ∧ c ≼ b := by
  induction hab with
  | refl => exact absurd rfl hne
  | @step C bid s h ih =>
    by_cases hac : a = C
    · refine ⟨Block.mk bid C s, ?_, ?_, Block.Ancestor.refl _⟩
      · exact congrArg some hac.symm
      · rw [hac]; exact Block.Ancestor.step (Block.Ancestor.refl C)
    · obtain ⟨c, hpar, hac', hcb⟩ := ih hac
      exact ⟨c, hpar, hac', Block.Ancestor.step hcb⟩
  | @stepWithVotes C bid s votes h ih =>
    by_cases hac : a = C
    · refine ⟨Block.mkWithVotes bid C s votes, ?_, ?_, Block.Ancestor.refl _⟩
      · exact congrArg some hac.symm
      · rw [hac]; exact Block.Ancestor.stepWithVotes (Block.Ancestor.refl C)
    · obtain ⟨c, hpar, hac', hcb⟩ := ih hac
      exact ⟨c, hpar, hac', Block.Ancestor.stepWithVotes hcb⟩

/-- A block with `parent? = some x` is a vote-free or vote-carrying child of `x`. -/
theorem child_cases_of_parent {c x : Block n} (h : c.parent? = some x) :
    (∃ bid s, c = Block.mk bid x s) ∨
      ∃ bid s votes, c = Block.mkWithVotes bid x s votes := by
  cases c with
  | genesis => simp [Block.parent?] at h
  | mk bid p s =>
    simp only [Block.parent?, Option.some.injEq] at h
    exact Or.inl ⟨bid, s, by rw [h]⟩
  | mkWithVotes bid p s votes =>
    simp only [Block.parent?, Option.some.injEq] at h
    exact Or.inr ⟨bid, s, votes, by rw [h]⟩

/-- An ancestor with the same slot (in a well-formed block) is equal. -/
theorem eq_of_ancestor_slot {x b : Block n} (h : x ≼ b) (hbwf : b.WellFormed)
    (hs : x.slot = b.slot) : x = b := by
  cases h with
  | refl => rfl
  | @step C bid s h' =>
    exfalso
    simp only [Block.WellFormed] at hbwf
    have hlt : x.slot < s := lt_of_le_of_lt (slot_le_of_ancestor h' hbwf.2) hbwf.1
    simp only [Block.slot] at hs
    exact Nat.ne_of_lt hlt hs
  | @stepWithVotes C bid s votes h' =>
    exfalso
    simp only [Block.WellFormed] at hbwf
    have hlt : x.slot < s := lt_of_le_of_lt (slot_le_of_ancestor h' hbwf.2) hbwf.1
    simp only [Block.slot] at hs
    exact Nat.ne_of_lt hlt hs

/-- A child has strictly greater slot than its parent (well-formed). -/
theorem parent_slot_lt {c x : Block n} (h : c.parent? = some x) (hwf : c.WellFormed) :
    x.slot < c.slot := by
  rcases child_cases_of_parent h with ⟨bid, s, rfl⟩ | ⟨bid, s, votes, rfl⟩
  · exact hwf.1
  · exact hwf.1

/-- A child of a well-formed block has a well-formed parent. -/
theorem parent_wellFormed {c x : Block n} (h : c.parent? = some x) (hwf : c.WellFormed) :
    x.WellFormed := by
  rcases child_cases_of_parent h with ⟨bid, s, rfl⟩ | ⟨bid, s, votes, rfl⟩
  · exact hwf.2
  · exact hwf.2

/-- `psPlus1` of a child equals its parent's slot plus one. -/
theorem psPlus1_eq_of_parent {c x : Block n} (h : c.parent? = some x) :
    c.psPlus1 = x.slot + 1 := by
  rcases child_cases_of_parent h with ⟨bid, s, rfl⟩ | ⟨bid, s, votes, rfl⟩
  · rfl
  · rfl

/-- A parent is an ancestor of its child. -/
theorem parent_ancestor {c x : Block n} (h : c.parent? = some x) : x ≼ c := by
  rcases child_cases_of_parent h with ⟨bid, s, rfl⟩ | ⟨bid, s, votes, rfl⟩
  · exact Block.Ancestor.step (Block.Ancestor.refl x)
  · exact Block.Ancestor.stepWithVotes (Block.Ancestor.refl x)

/-- Case split on ancestry into `mk`. -/
theorem ancestor_mk_cases {a : Block n} {bid : BlockId} {p : Block n} {s : Slot}
    (h : a ≼ Block.mk bid p s) : a = Block.mk bid p s ∨ a ≼ p := by
  cases h with
  | refl => exact Or.inl rfl
  | step h' => exact Or.inr h'

/-- Case split on ancestry into `mkWithVotes`. -/
theorem ancestor_mkWithVotes_cases {a : Block n} {bid : BlockId} {p : Block n} {s : Slot}
    {votes : Finset (ContainedFFGVote n)}
    (h : a ≼ Block.mkWithVotes bid p s votes) :
    a = Block.mkWithVotes bid p s votes ∨ a ≼ p := by
  cases h with
  | refl => exact Or.inl rfl
  | stepWithVotes h' => exact Or.inr h'

/-- Case split on ancestry into an arbitrary non-genesis child. -/
theorem ancestor_child_cases {a c x : Block n} (hpar : c.parent? = some x)
    (h : a ≼ c) : a = c ∨ a ≼ x := by
  rcases child_cases_of_parent hpar with ⟨bid, s, rfl⟩ | ⟨bid, s, votes, rfl⟩
  · exact ancestor_mk_cases h
  · exact ancestor_mkWithVotes_cases h

/-- Two distinct children of the same block are incompatible. -/
theorem siblings_incompatible {x c c' : Block n} (hcwf : c.WellFormed) (hc'wf : c'.WellFormed)
    (hc : c.parent? = some x) (hc' : c'.parent? = some x) (hne : c ≠ c') : ¬ c ~ c' := by
  rintro (h | h)
  · rcases ancestor_child_cases hc' h with heq | hax
    · exact hne heq
    · exact absurd (parent_slot_lt hc hcwf)
        (not_lt.mpr (slot_le_of_ancestor hax (parent_wellFormed hc' hc'wf)))
  · rcases ancestor_child_cases hc h with heq | hax
    · exact hne heq.symm
    · exact absurd (parent_slot_lt hc' hc'wf)
        (not_lt.mpr (slot_le_of_ancestor hax (parent_wellFormed hc hcwf)))

variable {P : Type}

/-- An honest validator's single effective vote cannot support two incompatible blocks. -/
theorem honest_supports_at_most_one_sibling {c d : Block n} (V : View n P) (i : Validator n)
    (s : Slot) (hincomp : ¬ c ~ d) :
    ¬ (V.supportsLMD c i s = true ∧ V.supportsLMD d i s = true) := by
  rintro ⟨hc, hd⟩
  cases hev : V.effectiveVote i s with
  | none => simp [View.supportsLMD, hev] at hc
  | some gv =>
    simp only [View.supportsLMD, hev] at hc hd
    exact hincomp (ancestor_comparable (isAncestorOf_imp hc) (isAncestorOf_imp hd))

end FastConfirmation
