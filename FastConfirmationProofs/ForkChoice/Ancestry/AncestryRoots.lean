module
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestorWalk

@[expose] public section

/-!
# Spec / Proof / AncestryRoots

base proof layer, the `get_ancestor_roots` / `is_ancestor` toolkit built on top of
`FastConfirmationProofs/ForkChoice/Ancestry/AncestorWalk.lean`. Two independent halves:

* **`is_ancestor` order facts** on the known walk domain — reflexivity, the
  walk-composition law `get_ancestor_comp` (walking to a lower slot factors
  through any intermediate stop), a slot-monotonicity fact, and hence
  transitivity of `is_ancestor`.
* **`get_ancestor_roots` fuel elimination and characterization** — the worker
  is fuel-independent on the `WalkKnown` domain, giving python-shaped unfold
  equations for the wrapper and a structural description of the returned chain
  segment (all roots known, parent-linked, ending at `block_root`).

Everything reuses `WalkKnown` and `get_ancestor_stop`/`get_ancestor_step`/
`get_ancestor_spec` from `FastConfirmationProofs/ForkChoice/Ancestry/AncestorWalk.lean`; no behavioral assumptions
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

variable [LinearOrder Root]

/-! ## `get_ancestor` order facts -/

/-- Every parent step lowers the slot, for every starting payload status. -/
theorem get_ancestor_slot_le_status {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    ∀ status : PayloadStatus,
      (store.blocks (get_ancestor store (ForkChoiceNode.mk r status) slot).root).slot ≤
        (store.blocks r).slot := by
  induction hw with
  | stop hr hle =>
    intro status
    rw [get_ancestor_stop_status hle]
  | step hr hgt hp ih =>
    intro status
    rw [get_ancestor_step_status hwf hr hgt hp]
    exact (ih _).trans (le_of_lt (hwf _ hr hp.root_mem))

/-- Pending-node slot bound. -/
theorem get_ancestor_slot_le {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    (store.blocks (get_ancestor store (ForkChoiceNode.mk r .pending) slot).root).slot ≤
      (store.blocks r).slot :=
  get_ancestor_slot_le_status hwf hw .pending

/-- Exact walk composition, with the complete Gloas node at the intermediate
stop. Parent recursion resolves statuses in the same way in both walks. -/
theorem get_ancestor_comp_status {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot slot' : Slot} (hss : slot' ≤ slot) {r : Root}
    (hw : WalkKnown store slot' r) :
    ∀ status : PayloadStatus,
      get_ancestor store (get_ancestor store (ForkChoiceNode.mk r status) slot) slot' =
        get_ancestor store (ForkChoiceNode.mk r status) slot' := by
  induction hw with
  | @stop r hr hle =>
    intro status
    rw [get_ancestor_stop_status (node := ForkChoiceNode.mk r status)
      (slot := slot) (hle.trans hss)]
  | @step r hr hgt hp ih =>
    intro status
    rcases le_or_gt (store.blocks r).slot slot with hle | hlt
    · rw [get_ancestor_stop_status (node := ForkChoiceNode.mk r status)
        (slot := slot) hle]
    · rw [get_ancestor_step_status (node := ForkChoiceNode.mk r status)
        (slot := slot) hwf hr hlt (hp.mono hss),
        get_ancestor_step_status (node := ForkChoiceNode.mk r status)
          (slot := slot') hwf hr hgt hp]
      exact ih _

/-- Pending-node form of exact walk composition. -/
theorem get_ancestor_comp {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot slot' : Slot} (hss : slot' ≤ slot) {r : Root}
    (hw : WalkKnown store slot' r) :
    get_ancestor store (get_ancestor store (ForkChoiceNode.mk r .pending) slot) slot' =
      get_ancestor store (ForkChoiceNode.mk r .pending) slot' :=
  get_ancestor_comp_status hwf hss hw .pending

/-- Root-only composition can restart from a pending intermediate root.
The starting status does not affect the root reached by an ancestor walk. -/
theorem get_ancestor_comp_root {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot slot' : Slot} (hss : slot' ≤ slot) {r : Root}
    (hw : WalkKnown store slot' r) :
    (get_ancestor store
      (ForkChoiceNode.mk (get_ancestor store (ForkChoiceNode.mk r .pending) slot).root .pending)
      slot').root = (get_ancestor store (ForkChoiceNode.mk r .pending) slot').root := by
  calc
    _ = (get_ancestor store (get_ancestor store (ForkChoiceNode.mk r .pending) slot)
        slot').root :=
      get_ancestor_root_eq_status store slot'
        (get_ancestor store (ForkChoiceNode.mk r .pending) slot).root .pending
        (get_ancestor store (ForkChoiceNode.mk r .pending) slot).payload_status
    _ = _ := congrArg ForkChoiceNode.root (get_ancestor_comp hwf hss hw)

/-! ## `get_ancestor_roots` fuel elimination -/

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


/-- Wrapper stop equation: at or below `terminal_root`'s slot the ancestor list
is empty (the walk's first test fails, worker returns `none`). -/
theorem get_ancestor_roots_stop {store : Store Root} {block_root terminal_root : Root}
    (hle : (store.blocks block_root).slot ≤ (store.blocks terminal_root).slot) :
    get_ancestor_roots store block_root terminal_root = [] := by
  rw [get_ancestor_roots, get_ancestor_roots_aux_succ, if_neg (by simpa using hle)]
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

/-- `is_ancestor` is reflexive for every payload status. -/
theorem is_ancestor_refl (store : Store Root) (n : ForkChoiceNode Root) :
    is_ancestor store n n = true := by
  simp only [is_ancestor]
  rw [get_ancestor_stop_status (le_refl _)]
  simp

/-- Gloas ancestry is transitive on the known walk domain. At a lower slot,
the first parent step discards the intermediate start status. At the same
slot, payload-status equality or a pending ancestor composes directly. -/
theorem is_ancestor_trans {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {a b c : ForkChoiceNode Root}
    (hwa : WalkKnown store (store.blocks c.root).slot a.root)
    (hwb : WalkKnown store (store.blocks c.root).slot b.root)
    (hab : is_ancestor store a b = true) (hbc : is_ancestor store b c = true) :
    is_ancestor store a c = true := by
  simp only [is_ancestor, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
  have hSc_le_Sb : (store.blocks c.root).slot ≤ (store.blocks b.root).slot := by
    have h := get_ancestor_slot_le_status hwf hwb b.payload_status
    change (store.blocks (get_ancestor store b (store.blocks c.root).slot).root).slot ≤
      (store.blocks b.root).slot at h
    rwa [hbc.1] at h
  have hcomp :
      get_ancestor store (get_ancestor store a (store.blocks b.root).slot)
          (store.blocks c.root).slot =
        get_ancestor store a (store.blocks c.root).slot :=
    get_ancestor_comp_status hwf hSc_le_Sb hwa a.payload_status
  rcases hSc_le_Sb.lt_or_eq with hlt | heq
  · have hsame :
        get_ancestor store (get_ancestor store a (store.blocks b.root).slot)
            (store.blocks c.root).slot =
          get_ancestor store b (store.blocks c.root).slot :=
      get_ancestor_eq_of_root_eq_of_lt hab.1 (by rw [hab.1]; exact hlt)
    have hresult : get_ancestor store a (store.blocks c.root).slot =
        get_ancestor store b (store.blocks c.root).slot := hcomp.symm.trans hsame
    rw [hresult]
    exact hbc
  · have hstop : get_ancestor store b (store.blocks c.root).slot = b :=
      get_ancestor_stop_status (node := b) (Nat.le_of_eq heq.symm)
    rw [hstop] at hbc
    constructor
    · rw [heq]
      exact hab.1.trans hbc.1
    · rcases hbc.2 with hbcstatus | hcPending
      · rcases hab.2 with habstatus | hbPending
        · left
          rw [heq]
          exact habstatus.trans hbcstatus
        · exact Or.inr (hbcstatus.symm.trans hbPending)
      · exact Or.inr hcPending

end FastConfirmation.Spec

end
