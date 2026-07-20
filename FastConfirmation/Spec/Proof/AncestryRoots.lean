import FastConfirmation.Spec.Proof.Ancestry

/-!
# Spec / Proof / AncestryRoots

Layer 0, the `get_ancestor_roots` / `is_ancestor` toolkit built on top of
`Proof/Ancestry.lean`. Two independent halves:

* **`is_ancestor` order facts** on the known walk domain — reflexivity, the
  walk-composition law `get_ancestor_comp` (walking to a lower slot factors
  through any intermediate stop), a slot-monotonicity fact, and hence
  transitivity of `is_ancestor`.
* **`get_ancestor_roots` fuel elimination and characterization** — the worker
  is fuel-independent on the `WalkKnown` domain, giving python-shaped unfold
  equations for the wrapper and a structural description of the returned chain
  segment (all roots known, parent-linked, ending at `block_root`).

Everything reuses `WalkKnown` and `get_ancestor_stop`/`get_ancestor_step`/
`get_ancestor_spec` from `Proof/Ancestry.lean`; no behavioral assumptions
enter here — the only premise is the `parent_slot_lt`-shaped `hwf`, exactly the
`WellFormedStore.parent_slot_lt` field.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Monotonicity of the walk domain -/

/-- The walk domain grows as the target slot rises: a walk that stays known
down to `s` also stays known down to any `s' ≥ s` (it terminates no later). -/
theorem WalkKnown.mono {store : Store Root} {s s' : Slot} (hs : s ≤ s') {r : Root}
    (h : WalkKnown store s r) : WalkKnown store s' r := by
  induction h with
  | stop hr hle => exact WalkKnown.stop hr (hle.trans hs)
  | @step r hr hgt hp ih =>
    rcases le_or_gt (store.blocks r).slot s' with hle | hgt'
    · exact WalkKnown.stop hr hle
    · exact WalkKnown.step hr hgt' ih

/-! ## `get_ancestor` order facts -/

/-- The walked ancestor never sits at a higher slot than the start block
(each `parent_slot_lt` step strictly lowers the slot). -/
theorem get_ancestor_slot_le {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    (store.blocks (get_ancestor store (ForkChoiceNode.mk r) slot).root).slot ≤
      (store.blocks r).slot := by
  induction hw with
  | stop hr hle => simp [get_ancestor_stop hle]
  | step hr hgt hp ih =>
    rw [get_ancestor_step hwf hr hgt hp]
    exact ih.trans (le_of_lt (hwf _ hr hp.root_mem))

/-- Walk-composition on the known domain: walking down to `slot` and then to a
still-lower `slot'` lands where a single walk down to `slot'` would. -/
theorem get_ancestor_comp {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot slot' : Slot} (hss : slot' ≤ slot) {r : Root}
    (hw : WalkKnown store slot' r) :
    get_ancestor store (get_ancestor store (ForkChoiceNode.mk r) slot) slot' =
      get_ancestor store (ForkChoiceNode.mk r) slot' := by
  induction hw with
  | stop hr hle => rw [get_ancestor_stop (hle.trans hss)]
  | @step r hr hgt hp ih =>
    rcases le_or_gt (store.blocks r).slot slot with hle | hlt
    · rw [get_ancestor_stop hle]
    · rw [get_ancestor_step hwf hr hlt (hp.mono hss),
        get_ancestor_step hwf hr hgt hp]
      exact ih

/-! ## `get_ancestor_roots` fuel elimination -/

variable [LinearOrder Root]

/-- Python-shaped one-step unfold of the worker at positive fuel (the `let next`
of the def zeta-reduced away). -/
theorem get_ancestor_roots_aux_succ (store : Store Root) (terminal_root : Root)
    (fuel : ℕ) (root : Root) :
    get_ancestor_roots_aux store terminal_root (fuel + 1) root =
      if (store.blocks root).slot > (store.blocks terminal_root).slot then
        (if (store.blocks root).parent_root = terminal_root then some [root]
         else (get_ancestor_roots_aux store terminal_root fuel
           (store.blocks root).parent_root).map (· ++ [root]))
      else none := rfl

/-- Fuel independence for `get_ancestor_roots_aux` on the known domain: any two
fuels exceeding the walked block's slot compute the same value (mirrors
`get_ancestor_aux_fuel_eq`; the walk descends toward `terminal_root`'s slot). -/
theorem get_ancestor_roots_aux_fuel_eq {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {terminal_root : Root} {r : Root}
    (hw : WalkKnown store (store.blocks terminal_root).slot r) :
    ∀ fuel fuel' : ℕ, (store.blocks r).slot < fuel → (store.blocks r).slot < fuel' →
      get_ancestor_roots_aux store terminal_root fuel r =
        get_ancestor_roots_aux store terminal_root fuel' r := by
  induction hw with
  | stop hr hle =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f => cases fuel' with
      | zero => exact absurd hf' (Nat.not_lt_zero _)
      | succ f' =>
        rw [get_ancestor_roots_aux_succ, get_ancestor_roots_aux_succ,
          if_neg (by simpa using hle), if_neg (by simpa using hle)]
  | @step r hr hgt hp ih =>
    intro fuel fuel' hf hf'
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f => cases fuel' with
      | zero => exact absurd hf' (Nat.not_lt_zero _)
      | succ f' =>
        have hCpos : (store.blocks r).slot > (store.blocks terminal_root).slot := hgt
        rw [get_ancestor_roots_aux_succ, get_ancestor_roots_aux_succ,
          if_pos hCpos, if_pos hCpos]
        by_cases hD : (store.blocks r).parent_root = terminal_root
        · rw [if_pos hD, if_pos hD]
        · rw [if_neg hD, if_neg hD, ih f f'
            (Nat.lt_of_lt_of_le (hwf _ hr hp.root_mem) (Nat.lt_succ_iff.mp hf))
            (Nat.lt_of_lt_of_le (hwf _ hr hp.root_mem) (Nat.lt_succ_iff.mp hf'))]

/-- Wrapper stop equation: at or below `terminal_root`'s slot the ancestor list
is empty (the walk's first test fails, worker returns `none`). -/
theorem get_ancestor_roots_stop {store : Store Root} {block_root terminal_root : Root}
    (hle : (store.blocks block_root).slot ≤ (store.blocks terminal_root).slot) :
    get_ancestor_roots store block_root terminal_root = [] := by
  rw [get_ancestor_roots, get_ancestor_roots_aux_succ, if_neg (by simpa using hle)]
  rfl

/-- Wrapper hit equation: one step above `terminal_root` whose parent is
`terminal_root` yields the singleton chain `[block_root]`. -/
theorem get_ancestor_roots_hit {store : Store Root} {block_root terminal_root : Root}
    (hgt : (store.blocks terminal_root).slot < (store.blocks block_root).slot)
    (hpar : (store.blocks block_root).parent_root = terminal_root) :
    get_ancestor_roots store block_root terminal_root = [block_root] := by
  rw [get_ancestor_roots, get_ancestor_roots_aux_succ, if_pos (by simpa using hgt),
    if_pos hpar]
  rfl

/-! ## `get_ancestor_roots` characterization -/

/-- Structural description of the worker output on the known domain: whenever it
returns `some l`, that list is a nonempty, all-known, oldest→newest chain whose
newest element is the start block `r` and whose oldest element's parent is
`terminal_root`. The single induction the wrapper corollaries below draw on. -/
theorem get_ancestor_roots_aux_chain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {terminal_root : Root} {r : Root}
    (hw : WalkKnown store (store.blocks terminal_root).slot r) :
    ∀ (fuel : ℕ), (store.blocks r).slot < fuel → ∀ (l : List Root),
      get_ancestor_roots_aux store terminal_root fuel r = some l →
        l ≠ [] ∧ (∀ x ∈ l, x ∈ store.block_roots) ∧
          List.IsChain (fun a b => (store.blocks b).parent_root = a) l ∧
          l.getLast? = some r ∧
          (∀ x ∈ l.head?, (store.blocks x).parent_root = terminal_root) := by
  induction hw with
  | stop hr hle =>
    intro fuel hfuel l hl
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ f =>
      rw [get_ancestor_roots_aux_succ, if_neg (by simpa using hle)] at hl
      simp at hl
  | @step r hr hgt hp ih =>
    intro fuel hfuel l hl
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ f =>
      have hCpos : (store.blocks r).slot > (store.blocks terminal_root).slot := hgt
      rw [get_ancestor_roots_aux_succ, if_pos hCpos] at hl
      by_cases hD : (store.blocks r).parent_root = terminal_root
      · rw [if_pos hD, Option.some_inj] at hl
        subst hl
        refine ⟨by simp, ?_, List.isChain_singleton _, by simp, ?_⟩
        · simp only [List.mem_singleton]; rintro x rfl; exact hr
        · simp only [List.head?_cons, Option.mem_some_iff]; rintro x rfl; exact hD
      · rw [if_neg hD] at hl
        obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp hl
        have hbound : (store.blocks (store.blocks r).parent_root).slot < f :=
          Nat.lt_of_lt_of_le (hwf _ hr hp.root_mem) (Nat.lt_succ_iff.mp hfuel)
        obtain ⟨hne', hmem', hchain', hlast', hhead'⟩ := ih f hbound l' hl'
        refine ⟨by simp, ?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hmem' x hx
          · exact hr
        · refine hchain'.append (List.isChain_singleton r) ?_
          intro x hx y hy
          rw [hlast', Option.mem_some_iff] at hx
          rw [List.head?_cons, Option.mem_some_iff] at hy
          subst hx; subst hy; rfl
        · rw [List.getLast?_append_cons]; simp
        · intro x hx
          rw [List.head?_append_of_ne_nil _ hne'] at hx
          exact hhead' x hx

/-- Every root of the returned ancestor list is a known block (wrapper form). -/
theorem get_ancestor_roots_mem {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {block_root terminal_root : Root}
    (hw : WalkKnown store (store.blocks terminal_root).slot block_root)
    {x : Root} (hx : x ∈ get_ancestor_roots store block_root terminal_root) :
    x ∈ store.block_roots := by
  have hx' : x ∈ (get_ancestor_roots_aux store terminal_root
      ((store.blocks block_root).slot + 1) block_root).getD [] := hx
  cases hworker : get_ancestor_roots_aux store terminal_root
      ((store.blocks block_root).slot + 1) block_root with
  | none => rw [hworker] at hx'; simp at hx'
  | some l =>
    rw [hworker, Option.getD_some] at hx'
    exact (get_ancestor_roots_aux_chain hwf hw _ (Nat.lt_succ_self _) l hworker).2.1 x hx'

/-- The returned ancestor list is parent-linked oldest→newest (wrapper form;
holds vacuously for the empty list). -/
theorem get_ancestor_roots_isChain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {block_root terminal_root : Root}
    (hw : WalkKnown store (store.blocks terminal_root).slot block_root) :
    List.IsChain (fun a b => (store.blocks b).parent_root = a)
      (get_ancestor_roots store block_root terminal_root) := by
  change List.IsChain _ ((get_ancestor_roots_aux store terminal_root
    ((store.blocks block_root).slot + 1) block_root).getD [])
  cases hworker : get_ancestor_roots_aux store terminal_root
      ((store.blocks block_root).slot + 1) block_root with
  | none => exact List.isChain_nil
  | some l =>
    rw [Option.getD_some]
    exact (get_ancestor_roots_aux_chain hwf hw _ (Nat.lt_succ_self _) l hworker).2.2.1

/-- When nonempty, the newest (last) root of the ancestor list is the start
block `block_root` (wrapper form). -/
theorem get_ancestor_roots_getLast? {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {block_root terminal_root : Root}
    (hw : WalkKnown store (store.blocks terminal_root).slot block_root)
    (hne : get_ancestor_roots store block_root terminal_root ≠ []) :
    (get_ancestor_roots store block_root terminal_root).getLast? = some block_root := by
  have he : get_ancestor_roots store block_root terminal_root =
      (get_ancestor_roots_aux store terminal_root
        ((store.blocks block_root).slot + 1) block_root).getD [] := rfl
  cases hworker : get_ancestor_roots_aux store terminal_root
      ((store.blocks block_root).slot + 1) block_root with
  | none => rw [he, hworker] at hne; simp at hne
  | some l =>
    rw [he, hworker, Option.getD_some]
    exact (get_ancestor_roots_aux_chain hwf hw _ (Nat.lt_succ_self _) l hworker).2.2.2.1

/-- The oldest (first) root of the ancestor list has `terminal_root` as its
parent — the segment is `terminal_root`-exclusive at its base (wrapper form). -/
theorem get_ancestor_roots_head? {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {block_root terminal_root : Root}
    (hw : WalkKnown store (store.blocks terminal_root).slot block_root)
    {x : Root} (hx : (get_ancestor_roots store block_root terminal_root).head? = some x) :
    (store.blocks x).parent_root = terminal_root := by
  have hx' : ((get_ancestor_roots_aux store terminal_root
      ((store.blocks block_root).slot + 1) block_root).getD []).head? = some x := hx
  cases hworker : get_ancestor_roots_aux store terminal_root
      ((store.blocks block_root).slot + 1) block_root with
  | none => rw [hworker] at hx'; simp at hx'
  | some l =>
    rw [hworker, Option.getD_some] at hx'
    exact (get_ancestor_roots_aux_chain hwf hw _ (Nat.lt_succ_self _) l hworker).2.2.2.2 x hx'

/-! ## `is_ancestor` order facts -/

/-- `is_ancestor` is reflexive: the walk down to a block's own slot stops
immediately at that block (needs no domain hypothesis). -/
theorem is_ancestor_refl (store : Store Root) (n : ForkChoiceNode Root) :
    is_ancestor store n n = true := by
  obtain ⟨r⟩ := n
  simp only [is_ancestor, decide_eq_true_eq]
  exact get_ancestor_stop (le_refl _)

/-- `is_ancestor` is transitive on the known domain: if `a`'s walk down to
`c`'s slot is known and `b`'s walk down to `c`'s slot is known, `a ⪰ b ⪰ c`
gives `a ⪰ c`. Composition through `b` uses `get_ancestor_comp`; the slot
ordering `c ≤ b` comes from `get_ancestor_slot_le`. -/
theorem is_ancestor_trans {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {a b c : ForkChoiceNode Root}
    (hwa : WalkKnown store (store.blocks c.root).slot a.root)
    (hwb : WalkKnown store (store.blocks c.root).slot b.root)
    (hab : is_ancestor store a b = true) (hbc : is_ancestor store b c = true) :
    is_ancestor store a c = true := by
  obtain ⟨ar⟩ := a; obtain ⟨br⟩ := b; obtain ⟨cr⟩ := c
  simp only [is_ancestor, decide_eq_true_eq] at hab hbc ⊢
  have hSc_le_Sb : (store.blocks cr).slot ≤ (store.blocks br).slot := by
    have h := get_ancestor_slot_le hwf hwb
    rwa [hbc] at h
  have hcomp := get_ancestor_comp hwf hSc_le_Sb hwa
  rw [hab, hbc] at hcomp
  exact hcomp.symm

end FastConfirmation.Spec
