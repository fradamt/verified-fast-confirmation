module
public import FastConfirmation.Spec.Proof.WeakCertifiedHead
public import FastConfirmation.Spec.Proof.CertExtract
public import FastConfirmation.Spec.Model.WeakSynchrony

@[expose] public section

/-!
# Spec / Proof / WeakSelectorBetween

Margin-discharge wave, Stage J-b: the weak twin of `CertExtract.lean`'s
strengthened per-block confirmation invariant, over `Weak.is_one_confirmed`
and the weak selector loops (`Weak.find_latest_confirmed_descendant_prev_epoch_loop`
/ `_tentative_loop` / `find_latest_confirmed_descendant`).

The weak loop bodies are verbatim copies of the strong ones over the weak
predicates (`WeakSelectorInversion.lean`'s module docstring), so the
inductions below are line-for-line clones of `CertExtract.prev_epoch_loop_between`
/ `tentative_loop_between` / `find_latest_confirmed_descendant_between`. The
pure `is_ancestor`-order helpers (`is_ancestor_antisymm`, `is_ancestor_comparable`,
`between_parent_child`) carry no `is_one_confirmed` dependence at all and are
reused verbatim from `CertExtract.lean`.

`Weak.find_latest_confirmed_descendant`'s certificate-gated guards (rule
delta 4, `docs/weak-synchrony.md`) add extra conjuncts to the three top-level
`if`s the selector case-splits on, but do not change how many `if`s there
are or their nesting — `split_ifs` treats each (possibly larger) guard as one
opaque atom, so the case dispatch is structurally identical to the strong
proof. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-- **The strengthened per-block confirmation predicate**, weak twin of
`CertExtract.PstrConfirmed`: verbatim, with `is_one_confirmed` replaced by
`Weak.is_one_confirmed`. -/
def PstrConfirmed (fcr_store : FastConfirmationStore Root) (lcr r : Root) : Prop :=
  is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root lcr) = true ∧
  r ∈ fcr_store.store.block_roots ∧
  ∀ c, c ∈ fcr_store.store.block_roots →
    is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root c) = true →
    is_ancestor fcr_store.store (get_node_for_root c) (get_node_for_root lcr) = true →
    c = lcr ∨
      Weak.is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) c = true

/-- Cons-case unfold of the weak prev-epoch loop (`rfl`). -/
private theorem prev_loop_cons (fcr_store : FastConfirmationStore Root) (ce : Epoch)
    (b : Root) (rest : List Root) (acc : Root) :
    Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b = ce then acc
       else if ¬ is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
              (get_node_for_root b) then acc
       else if ¬ Weak.is_one_confirmed cfg ext fcr_store.store
              (get_current_balance_source fcr_store) b then acc
       else Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce rest b) :=
  rfl

/-- Cons-case unfold of the weak tentative loop (`rfl`). -/
private theorem tent_loop_cons (fcr_store : FastConfirmationStore Root)
    (b : Root) (rest : List Root) (acc : Root) :
    Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b > get_block_epoch cfg fcr_store.store acc ∧
            ¬ Weak.will_current_target_be_justified cfg ext fcr_store.store then acc
       else if ¬ Weak.is_one_confirmed cfg ext fcr_store.store
              (get_current_balance_source fcr_store) b then acc
       else Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store rest b) :=
  rfl

/-- **The advance step preserves `Pstr`**, weak twin of `CertExtract.pstr_advance`.
When the loop advances the accumulator `acc` to a direct child `b`
(`parent(b) = acc`) whose `Weak.is_one_confirmed` gate passed,
`Weak.PstrConfirmed acc ⟹ Weak.PstrConfirmed b`. -/
theorem pstrConfirmed_step (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    {acc b : Root} (hb_mem : b ∈ fcr_store.store.block_roots)
    (hb_par : (fcr_store.store.blocks b).parent_root = acc)
    (hg3 : Weak.is_one_confirmed cfg ext fcr_store.store
      (get_current_balance_source fcr_store) b = true)
    (hacc : Weak.PstrConfirmed cfg ext fcr_store lcr acc) :
    Weak.PstrConfirmed cfg ext fcr_store lcr b := by
  obtain ⟨hacc_lcr, hacc_mem, hacc_between⟩ := hacc
  have hb_acc : is_ancestor fcr_store.store (get_node_for_root b) (get_node_for_root acc) = true :=
    is_ancestor_of_parent hwf hb_mem hacc_mem hb_par
  refine ⟨is_ancestor_trans hwf (hwalk lcr hlcr b hb_mem) (hwalk lcr hlcr acc hacc_mem)
      hb_acc hacc_lcr, hb_mem, ?_⟩
  intro c hc_mem hbc_c hc_lcr
  rcases is_ancestor_comparable hwf (hwalk c hc_mem b hb_mem) (hwalk acc hacc_mem b hb_mem)
      hbc_c hb_acc with hacc_c | hc_acc
  · exact hacc_between c hc_mem hacc_c hc_lcr
  · rcases between_parent_child hwf hb_mem hacc_mem (hwalk c hc_mem b hb_mem)
        (hwalk acc hacc_mem c hc_mem) hb_par hbc_c hc_acc with heq | heq
    · rw [heq]; exact hacc_between acc hacc_mem (is_ancestor_refl _ _) hacc_lcr
    · rw [heq]; exact Or.inr hg3

/-- **Prev-epoch loop preserves `Pstr`**, weak twin of
`CertExtract.prev_epoch_loop_between`. -/
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
      Weak.PstrConfirmed cfg ext fcr_store lcr acc →
      Weak.PstrConfirmed cfg ext fcr_store lcr
        (Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc) := by
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
        by_cases hg3 : Weak.is_one_confirmed cfg ext fcr_store.store
            (get_current_balance_source fcr_store) b = true
        · rw [if_neg (not_not_intro hg3)]
          have hb_mem : b ∈ fcr_store.store.block_roots := hmem b List.mem_cons_self
          have hb_par : (fcr_store.store.blocks b).parent_root = acc := hhead b rfl
          exact ih b (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
            (List.isChain_cons.mp hchain).2
            (fun x hx => (List.isChain_cons.mp hchain).1 x (Option.mem_def.mpr hx))
            (pstrConfirmed_step cfg ext fcr_store hwf hwalk lcr hlcr hb_mem hb_par hg3 hacc)
        · rw [if_pos hg3]; exact hacc
      · rw [if_pos hg2]; exact hacc

/-- **Tentative loop preserves `Pstr`**, weak twin of
`CertExtract.tentative_loop_between`. -/
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
      Weak.PstrConfirmed cfg ext fcr_store lcr acc →
      Weak.PstrConfirmed cfg ext fcr_store lcr
        (Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc) := by
  intro roots
  induction roots with
  | nil => intro acc _ _ _ hacc; exact hacc
  | cons b rest ih =>
    intro acc hmem hchain hhead hacc
    rw [tent_loop_cons]
    by_cases hg1 : get_block_epoch cfg fcr_store.store b > get_block_epoch cfg fcr_store.store acc ∧
        ¬ Weak.will_current_target_be_justified cfg ext fcr_store.store
    · rw [if_pos hg1]; exact hacc
    · rw [if_neg hg1]
      by_cases hg3 : Weak.is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) b = true
      · rw [if_neg (not_not_intro hg3)]
        have hb_mem : b ∈ fcr_store.store.block_roots := hmem b List.mem_cons_self
        have hb_par : (fcr_store.store.blocks b).parent_root = acc := hhead b rfl
        exact ih b (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
          (List.isChain_cons.mp hchain).2
          (fun x hx => (List.isChain_cons.mp hchain).1 x (Option.mem_def.mpr hx))
          (pstrConfirmed_step cfg ext fcr_store hwf hwalk lcr hlcr hb_mem hb_par hg3 hacc)
      · rw [if_pos hg3]; exact hacc

/-- **The strengthened `Weak.find_latest_confirmed_descendant` invariant**,
weak twin of `CertExtract.find_latest_confirmed_descendant_between`: the
result descends from `lcr`, is known, and every block on the walk segment
`[lcr, glc]` is `lcr` or `Weak.is_one_confirmed`. The certificate-gated extra
conjuncts in the wrapper's top-level guards (rule delta 4) do not change the
number or nesting of the `if`s the selector case-splits on, so the same
three-way `split_ifs` dispatch closes every branch. -/
theorem find_latest_confirmed_descendant_between (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    Weak.PstrConfirmed cfg ext fcr_store lcr
      (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) := by
  have hhead := Weak.get_certified_head_known cfg ext fcr_store.store
    (get_current_balance_source fcr_store) hhead
  set P : Root → Prop := fun r => Weak.PstrConfirmed cfg ext fcr_store lcr r with hP
  have base : P lcr := by
    refine ⟨is_ancestor_refl _ _, hlcr, ?_⟩
    intro c hc_mem hlcr_c hc_lcr
    exact Or.inl (is_ancestor_antisymm hwf (hwalk c hc_mem lcr hlcr) hc_lcr hlcr_c)
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) acc) acc) := by
    intro ce acc hacc
    have hw : WalkKnown fcr_store.store (fcr_store.store.blocks acc).slot
        (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) := hwalk acc hacc.2.1 _ hhead
    exact prev_epoch_loop_between cfg ext fcr_store ce hwf hwalk lcr hlcr _ acc
      (fun x hx => get_ancestor_roots_mem hwf hw hx) (get_ancestor_roots_isChain hwf hw)
      (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc
  have htent : ∀ (acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) acc) acc) := by
    intro acc hacc
    have hw : WalkKnown fcr_store.store (fcr_store.store.blocks acc).slot
        (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) := hwalk acc hacc.2.1 _ hhead
    exact tentative_loop_between cfg ext fcr_store hwf hwalk lcr hlcr _ acc
      (fun x hx => get_ancestor_roots_mem hwf hw hx) (get_ancestor_roots_isChain hwf hw)
      (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc
  change P (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [Weak.find_latest_confirmed_descendant] at hX
  simp only at hX
  split_ifs at hX <;>
    subst hX <;>
      first
      | exact base
      | (apply htent; first | exact base | exact hprev _ _ base)
      | exact hprev _ _ base

end Weak

end FastConfirmation.Spec

end
