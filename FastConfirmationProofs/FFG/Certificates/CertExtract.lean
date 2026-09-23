module
public import FastConfirmationProofs.Checkpoints.AnchorChainSafety

@[expose] public section

/-!
# Spec / Proof / CertExtract

Extracts comparable checkpoint ancestry and certificate facts from accepted stores.

This module contains `is_ancestor_antisymm`, `is_ancestor_comparable`, `between_parent_child` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-! ## Section 0 — `is_ancestor` order helpers -/

omit [Inhabited Root] in
/-- **Antisymmetry of `is_ancestor`.** Mutual descent forces equality: from `b ⪰ a`
(`a.slot ≤ b.slot` by `get_ancestor_slot_le`) the walk of `a` down to `b`'s slot stops at `a`
(`get_ancestor_stop`), yet `a ⪰ b` says it lands on `b`. -/
theorem is_ancestor_antisymm {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {a b : Root}
    (hwb : WalkKnown store (store.blocks a).slot b)
    (hab : is_ancestor store (get_node_for_root a) (get_node_for_root b) = true)
    (hba : is_ancestor store (get_node_for_root b) (get_node_for_root a) = true) :
    a = b := by
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hab hba
  have h2 := get_ancestor_slot_le hwf hwb
  rw [hba] at h2
  have hstop : (get_ancestor store (ForkChoiceNode.mk a .pending) (store.blocks b).slot).root
      = a := by rw [get_ancestor_stop h2]
  exact hstop.symm.trans hab

/-- **Comparability of two ancestors** — the `is_ancestor` wrapper of
`HeadReroot.reroot_comparable`. If `a` and `b` are both ancestors of a common `y`, then they are
ancestry-comparable. -/
theorem is_ancestor_comparable {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {y a b : Root}
    (hwa : WalkKnown store (store.blocks a).slot y)
    (hwb : WalkKnown store (store.blocks b).slot y)
    (hya : is_ancestor store (get_node_for_root y) (get_node_for_root a) = true)
    (hyb : is_ancestor store (get_node_for_root y) (get_node_for_root b) = true) :
    is_ancestor store (get_node_for_root b) (get_node_for_root a) = true ∨
      is_ancestor store (get_node_for_root a) (get_node_for_root b) = true := by
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hya hyb ⊢
  exact reroot_comparable hwf hwa hwb hya hyb

omit [Inhabited Root] in
/-- **Nothing strictly between a block and its parent.** If `b ⪰ c ⪰ a` with `a = parent(b)`,
then `c` is `a` or `b`: either `c.slot = b.slot` (`get_ancestor_stop` ⟹ `c = b`) or the walk of
`b` down to `c.slot` steps once to `a` and stops (`a.slot ≤ c.slot`), forcing `c = a`. -/
theorem between_parent_child {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {a b c : Root}
    (hbmem : b ∈ store.block_roots) (hamem : a ∈ store.block_roots)
    (hwcb : WalkKnown store (store.blocks c).slot b)
    (hwac : WalkKnown store (store.blocks a).slot c)
    (hpar : (store.blocks b).parent_root = a)
    (hbc : is_ancestor store (get_node_for_root b) (get_node_for_root c) = true)
    (hca : is_ancestor store (get_node_for_root c) (get_node_for_root a) = true) :
    c = a ∨ c = b := by
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hbc hca
  have hc_le_b : (store.blocks c).slot ≤ (store.blocks b).slot := by
    have h := get_ancestor_slot_le hwf hwcb; rw [hbc] at h; exact h
  have ha_le_c : (store.blocks a).slot ≤ (store.blocks c).slot := by
    have h := get_ancestor_slot_le hwf hwac; rw [hca] at h; exact h
  rcases eq_or_lt_of_le hc_le_b with heq | hlt
  · right
    have hstop : (get_ancestor store (ForkChoiceNode.mk b .pending) (store.blocks c).slot).root
        = b := by rw [get_ancestor_stop (le_of_eq heq.symm)]
    exact hbc.symm.trans hstop
  · left
    have hstep : (get_ancestor store (ForkChoiceNode.mk b .pending) (store.blocks c).slot).root
        = a := by
      rw [get_ancestor_step hwf hbmem hlt (by rw [hpar]; exact WalkKnown.stop hamem ha_le_c),
        hpar, get_ancestor_stop ha_le_c]
    exact hbc.symm.trans hstep

/-! ## Section 1 — the strengthened loop invariant (task 1) -/

variable (cfg : Config) (ext : Externals Root)

/-- **The strengthened per-block confirmation predicate** relative to a reset anchor `lcr`. A
loop accumulator `r` is `Pstr` when `r` descends from `lcr`, is known, and **every** block `c`
strictly between `lcr` and `r` on the canonical chain is `lcr` or passed `is_one_confirmed` at
the querying store. The existing `L4Fold.{prev,tentative}_loop_spec` only certify the final
returned block; this predicate is preserved across every advance step, so it certifies the whole
walk. -/
def PstrConfirmed (fcr_store : FastConfirmationStore Root) (lcr r : Root) : Prop :=
  is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root lcr) = true ∧
  r ∈ fcr_store.store.block_roots ∧
  ∀ c, c ∈ fcr_store.store.block_roots →
    is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root c) = true →
    is_ancestor fcr_store.store (get_node_for_root c) (get_node_for_root lcr) = true →
    c = lcr ∨
      is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) c = true

/-- Cons-case unfold of the prev-epoch loop (`rfl`; the private `L4Fold` copy re-derived here). -/
private theorem prev_loop_cons (fcr_store : FastConfirmationStore Root) (ce : Epoch)
    (b : Root) (rest : List Root) (acc : Root) :
    find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b = ce then acc
       else if ¬ is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
              (get_node_for_root b) then acc
       else if ¬ is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) b
         then acc
       else find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce rest b) :=
  rfl

/-- Cons-case unfold of the tentative loop (`rfl`). -/
private theorem tent_loop_cons (fcr_store : FastConfirmationStore Root)
    (b : Root) (rest : List Root) (acc : Root) :
    find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b > get_block_epoch cfg fcr_store.store acc ∧
            ¬ will_current_target_be_justified cfg ext fcr_store.store then acc
       else if ¬ is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) b
         then acc
       else find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store rest b) :=
  rfl

/-- **The advance step preserves `Pstr`.** When the loop advances the accumulator `acc` to a
direct child `b` (`parent(b) = acc`) whose `is_one_confirmed` gate passed, `Pstr acc ⟹ Pstr b`:
`b` descends from `lcr` (via `acc`), and an arbitrary block `c` between `lcr` and `b` is either
between `lcr` and `acc` (the IH `Pstr acc`) or between `acc` and `b` — where
`between_parent_child` forces `c ∈ {acc, b}`, both `lcr`-or-confirmed. -/
theorem pstr_advance (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    {acc b : Root} (hb_mem : b ∈ fcr_store.store.block_roots)
    (hb_par : (fcr_store.store.blocks b).parent_root = acc)
    (hg3 : is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) b = true)
    (hacc : PstrConfirmed cfg ext fcr_store lcr acc) :
    PstrConfirmed cfg ext fcr_store lcr b := by
  obtain ⟨hacc_lcr, hacc_mem, hacc_between⟩ := hacc
  have hb_acc : is_ancestor fcr_store.store (get_node_for_root b) (get_node_for_root acc) = true :=
    is_ancestor_of_parent hwf hb_mem hacc_mem hb_par
  refine ⟨is_ancestor_trans (a := get_node_for_root b) (b := get_node_for_root acc)
      (c := get_node_for_root lcr) hwf (hwalk lcr hlcr b hb_mem) (hwalk lcr hlcr acc hacc_mem)
      hb_acc hacc_lcr, hb_mem, ?_⟩
  intro c hc_mem hbc_c hc_lcr
  rcases is_ancestor_comparable hwf (hwalk c hc_mem b hb_mem) (hwalk acc hacc_mem b hb_mem)
      hbc_c hb_acc with hacc_c | hc_acc
  · exact hacc_between c hc_mem hacc_c hc_lcr
  · rcases between_parent_child hwf hb_mem hacc_mem (hwalk c hc_mem b hb_mem)
        (hwalk acc hacc_mem c hc_mem) hb_par hbc_c hc_acc with heq | heq
    · rw [heq]; exact hacc_between acc hacc_mem (is_ancestor_refl _ _) hacc_lcr
    · rw [heq]; exact Or.inr hg3

/-- **Prev-epoch loop preserves `Pstr`** (task 1, first loop). List induction over `roots` (a
parent-linked, all-known chain whose head's parent is `acc` — exactly `get_ancestor_roots`'s
shape): each break returns `acc` (IH `Pstr acc`), each advance goes through `pstr_advance` then
the tail IH. -/
theorem prev_epoch_loop_between (fcr_store : FastConfirmationStore Root) (ce : Epoch)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    ∀ (roots : List Root) (acc : Root),
      (∀ x ∈ roots, x ∈ fcr_store.store.block_roots) →
      List.IsChain (fun a c => (fcr_store.store.blocks c).parent_root = a) roots →
      (∀ x, roots.head? = some x → (fcr_store.store.blocks x).parent_root = acc) →
      PstrConfirmed cfg ext fcr_store lcr acc →
      PstrConfirmed cfg ext fcr_store lcr
        (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc) := by
  intro roots
  induction roots with
  | nil => intro acc _ _ _ hacc; exact hacc
  | cons b rest ih =>
    intro acc hmem hchain hhead hacc
    rw [prev_loop_cons]
    by_cases hg1 : get_block_epoch cfg fcr_store.store b = ce
    · rw [if_pos hg1]; exact hacc
    · rw [if_neg hg1]
      by_cases hg2 : is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
          (get_node_for_root b) = true
      · rw [if_neg (not_not_intro hg2)]
        by_cases hg3 : is_one_confirmed cfg ext fcr_store.store
            (get_current_balance_source fcr_store) b = true
        · rw [if_neg (not_not_intro hg3)]
          have hb_mem : b ∈ fcr_store.store.block_roots := hmem b List.mem_cons_self
          have hb_par : (fcr_store.store.blocks b).parent_root = acc := hhead b rfl
          exact ih b (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
            (List.isChain_cons.mp hchain).2
            (fun x hx => (List.isChain_cons.mp hchain).1 x (Option.mem_def.mpr hx))
            (pstr_advance cfg ext fcr_store hwf hwalk lcr hlcr hb_mem hb_par hg3 hacc)
        · rw [if_pos hg3]; exact hacc
      · rw [if_pos hg2]; exact hacc

/-- **Tentative loop preserves `Pstr`** (task 1, second loop). Identical structure to
`prev_epoch_loop_between`; the extra `will_current_target_be_justified` gate only *blocks* an
advance (returns `acc`), never manufactures one, so the `is_one_confirmed` advance step is the
same `pstr_advance`. -/
theorem tentative_loop_between (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    ∀ (roots : List Root) (acc : Root),
      (∀ x ∈ roots, x ∈ fcr_store.store.block_roots) →
      List.IsChain (fun a c => (fcr_store.store.blocks c).parent_root = a) roots →
      (∀ x, roots.head? = some x → (fcr_store.store.blocks x).parent_root = acc) →
      PstrConfirmed cfg ext fcr_store lcr acc →
      PstrConfirmed cfg ext fcr_store lcr
        (find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc) := by
  intro roots
  induction roots with
  | nil => intro acc _ _ _ hacc; exact hacc
  | cons b rest ih =>
    intro acc hmem hchain hhead hacc
    rw [tent_loop_cons]
    by_cases hg1 : get_block_epoch cfg fcr_store.store b > get_block_epoch cfg fcr_store.store acc ∧
        ¬ will_current_target_be_justified cfg ext fcr_store.store
    · rw [if_pos hg1]; exact hacc
    · rw [if_neg hg1]
      by_cases hg3 : is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) b = true
      · rw [if_neg (not_not_intro hg3)]
        have hb_mem : b ∈ fcr_store.store.block_roots := hmem b List.mem_cons_self
        have hb_par : (fcr_store.store.blocks b).parent_root = acc := hhead b rfl
        exact ih b (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
          (List.isChain_cons.mp hchain).2
          (fun x hx => (List.isChain_cons.mp hchain).1 x (Option.mem_def.mpr hx))
          (pstr_advance cfg ext fcr_store hwf hwalk lcr hlcr hb_mem hb_par hg3 hacc)
      · rw [if_pos hg3]; exact hacc

/-! ## Section 2 — composition + the fcrStoreAtCall reconciliation (tasks 2+3) -/

/-- **The strengthened `find_latest_confirmed_descendant` invariant** (task 2). Folding the two
loop preservers through the `find_latest_confirmed_descendant` structure (the `Anchoring`
`P`-motive skeleton, with `Pstr` in place of the descent-only predicate): the result descends
from `lcr`, is known, and **every** block on the walk segment `[lcr, glc]` is `lcr` or
`is_one_confirmed`. Each loop consumes `get_ancestor_roots`'s parent-linked chain, so the chain
preconditions are `get_ancestor_roots_{mem,isChain,head?}`. -/
theorem find_latest_confirmed_descendant_between (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    PstrConfirmed cfg ext fcr_store lcr
      (find_latest_confirmed_descendant cfg ext fcr_store lcr) := by
  set P : Root → Prop := fun r => PstrConfirmed cfg ext fcr_store lcr r with hP
  have base : P lcr := by
    refine ⟨is_ancestor_refl _ _, hlcr, ?_⟩
    intro c hc_mem hlcr_c hc_lcr
    exact Or.inl (is_ancestor_antisymm hwf (hwalk c hc_mem lcr hlcr) hc_lcr hlcr_c)
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc) := by
    intro ce acc hacc
    have hw : WalkKnown fcr_store.store (fcr_store.store.blocks acc).slot
        (get_head cfg fcr_store.store).root := hwalk acc hacc.2.1 _ hhead
    exact prev_epoch_loop_between cfg ext fcr_store ce hwf hwalk lcr hlcr _ acc
      (fun x hx => get_ancestor_roots_mem hwf hw hx) (get_ancestor_roots_isChain hwf hw)
      (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc
  have htent : ∀ (acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc) := by
    intro acc hacc
    have hw : WalkKnown fcr_store.store (fcr_store.store.blocks acc).slot
        (get_head cfg fcr_store.store).root := hwalk acc hacc.2.1 _ hhead
    exact tentative_loop_between cfg ext fcr_store hwf hwalk lcr hlcr _ acc
      (fun x hx => get_ancestor_roots_mem hwf hw hx) (get_ancestor_roots_isChain hwf hw)
      (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc
  change P (find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [find_latest_confirmed_descendant] at hX
  simp only at hX
  split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
    subst hX <;>
      first
      | exact base
      | (apply htent; first | exact base | exact hprev _ _ base)
      | exact hprev _ _ base

/-- **`get_latest_confirmed` per-block charge** (task 2) — `Anchoring.get_latest_confirmed_ge`
strengthened with the per-block confirmation charge. The block `get_latest_confirmed` returns
descends from one of the three reset anchors `r₀`, and **every** block on the segment `[r₀, glc]`
is `r₀` or `is_one_confirmed` at the querying store. The reset branches (`glc = r₀`) give the
charge by antisymmetry; the advance branch (`glc = find_latest_confirmed_descendant r₀`) by the
loop invariant `find_latest_confirmed_descendant_between`. -/
theorem get_latest_confirmed_between (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (h0 : fcr_store.confirmed_root ∈ fcr_store.store.block_roots)
    (h1 : fcr_store.store.finalized_checkpoint.root ∈ fcr_store.store.block_roots)
    (h2 : fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      fcr_store.store.block_roots) :
    ∃ r₀ : Root,
      (r₀ = fcr_store.confirmed_root ∨ r₀ = fcr_store.store.finalized_checkpoint.root ∨
        r₀ = fcr_store.current_epoch_observed_justified_checkpoint.root) ∧
      r₀ ∈ fcr_store.store.block_roots ∧
      is_ancestor fcr_store.store
        (get_node_for_root (get_latest_confirmed cfg ext fcr_store)) (get_node_for_root r₀) = true ∧
      ∀ c : Root, c ∈ fcr_store.store.block_roots →
        is_ancestor fcr_store.store (get_node_for_root (get_latest_confirmed cfg ext fcr_store))
          (get_node_for_root c) = true →
        is_ancestor fcr_store.store (get_node_for_root c) (get_node_for_root r₀) = true →
        c = r₀ ∨ is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) c = true := by
  generalize hX : get_latest_confirmed cfg ext fcr_store = X
  simp only [get_latest_confirmed] at hX
  split_ifs at hX <;>
    subst hX <;>
      first
      | exact ⟨_, Or.inl rfl, h0, is_ancestor_refl _ _,
          fun c hc hXc hc0 => Or.inl (is_ancestor_antisymm hwf (hwalk c hc _ h0) hc0 hXc)⟩
      | exact ⟨_, Or.inr (Or.inl rfl), h1, is_ancestor_refl _ _,
          fun c hc hXc hc1 => Or.inl (is_ancestor_antisymm hwf (hwalk c hc _ h1) hc1 hXc)⟩
      | exact ⟨_, Or.inr (Or.inr rfl), h2, is_ancestor_refl _ _,
          fun c hc hXc hc2 => Or.inl (is_ancestor_antisymm hwf (hwalk c hc _ h2) hc2 hXc)⟩
      | exact ⟨_, Or.inl rfl, h0,
          (find_latest_confirmed_descendant_between cfg ext fcr_store hwf hwalk hhead _ h0).1,
          (find_latest_confirmed_descendant_between cfg ext fcr_store hwf hwalk hhead _ h0).2.2⟩
      | exact ⟨_, Or.inr (Or.inl rfl), h1,
          (find_latest_confirmed_descendant_between cfg ext fcr_store hwf hwalk hhead _ h1).1,
          (find_latest_confirmed_descendant_between cfg ext fcr_store hwf hwalk hhead _ h1).2.2⟩
      | exact ⟨_, Or.inr (Or.inr rfl), h2,
          (find_latest_confirmed_descendant_between cfg ext fcr_store hwf hwalk hhead _ h2).1,
          (find_latest_confirmed_descendant_between cfg ext fcr_store hwf hwalk hhead _ h2).2.2⟩

namespace Execution

variable (E : Execution Root)


end Execution

end FastConfirmation.Spec

end
