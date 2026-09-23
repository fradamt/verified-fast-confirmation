module
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.Discount.Confinement
public import FastConfirmationProofs.FFG.SourceHistory.MarginInvariant

@[expose] public section

/-!
# Spec / Proof / Anchoring

Connects ancestor walks and confirmed descendants to the trusted chain terminal.

This module contains `chain_descends_terminal`, `get_ancestor_roots_descends`, `find_latest_confirmed_descendant_ge` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-! ## Section 1 — the additive anchoring lemma -/

omit [Inhabited Root] in
/-- **Chain members descend from the terminal.** Along a parent-linked chain `L` of known
roots whose oldest element's parent is `t` (`L.head? = some x → (blocks x).parent_root = t`),
every member `x` is a descendant of `t` (`is_ancestor store x t`): the oldest element steps
once to `t` (`is_ancestor_of_parent`), and each later element descends from the previous by the
chain relation, composed by `is_ancestor_trans` (walk domains from the blanket `hwalk`). The
`t`-generalised dual of `INVstarTrack.mem_isAncestor_of_parentChain` (which walks toward the
*last* element). -/
theorem chain_descends_terminal {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    ∀ {L : List Root}, List.IsChain (fun a c => (store.blocks c).parent_root = a) L →
      (∀ x ∈ L, x ∈ store.block_roots) →
      ∀ {t : Root}, t ∈ store.block_roots →
      (∀ x, L.head? = some x → (store.blocks x).parent_root = t) →
      ∀ x ∈ L, is_ancestor store (get_node_for_root x) (get_node_for_root t) = true := by
  intro L hchain
  induction hchain with
  | nil => intro _ t _ _ x hx; simp at hx
  | singleton a =>
    intro hmem t ht hhd x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact is_ancestor_of_parent hwf (hmem a (by simp)) ht (hhd a rfl)
  | @cons_cons a d rest hr _ ih =>
    intro hmem t ht hhd x hx
    have hamem : a ∈ store.block_roots := hmem a (by simp)
    have hpar_a : (store.blocks a).parent_root = t := hhd a rfl
    have ha_t : is_ancestor store (get_node_for_root a) (get_node_for_root t) = true :=
      is_ancestor_of_parent hwf hamem ht hpar_a
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha_t
    · have hmem' : ∀ y ∈ d :: rest, y ∈ store.block_roots :=
        fun y hy => hmem y (List.mem_cons_of_mem _ hy)
      have hhd' : ∀ y, (d :: rest).head? = some y → (store.blocks y).parent_root = a := by
        intro y hy; rw [List.head?_cons, Option.some_inj] at hy; subst hy; exact hr
      have hx_a := ih hmem' hamem hhd' x hx'
      exact is_ancestor_trans (a := get_node_for_root x) (b := get_node_for_root a)
        (c := get_node_for_root t) hwf (hwalk t ht x (hmem x (List.mem_cons_of_mem _ hx')))
        (hwalk t ht a hamem) hx_a ha_t

omit [Inhabited Root] in
/-- **`get_ancestor_roots` members descend from the terminal.** Every root of
`get_ancestor_roots store head t` is a descendant of `t` at the store: the list is the
parent-linked known chain from `t` toward `head`, so `chain_descends_terminal` applies. -/
theorem get_ancestor_roots_descends {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {t head : Root} (ht : t ∈ store.block_roots) (hhead : head ∈ store.block_roots)
    {x : Root} (hx : x ∈ get_ancestor_roots store head t) :
    is_ancestor store (get_node_for_root x) (get_node_for_root t) = true := by
  have hw : WalkKnown store (store.blocks t).slot head := hwalk t ht head hhead
  exact chain_descends_terminal hwf hwalk (get_ancestor_roots_isChain hwf hw)
    (fun y hy => get_ancestor_roots_mem hwf hw hy) ht
    (fun y hy => get_ancestor_roots_head? hwf hw hy) x hx

variable (cfg : Config) (ext : Externals Root)

/-- **The additive anchoring lemma.** At the querying store, the block
`find_latest_confirmed_descendant` returns descends from the input `lcr`
(`is_ancestor store result lcr`) and is a known block. Both advancement stages advance the
accumulator only through `get_ancestor_roots store head acc` (`get_ancestor_roots_descends` ⟹
each advance is a descendant), so the "descends from `lcr` and is known" predicate is preserved
from the reflexive base `P lcr` through the two loops (`L4Fold.prev_epoch_loop_spec` /
`tentative_loop_spec` return `r ∈ roots`). Needs `lcr` and the head known + the fork-choice
domain conditions (`hwf` the `parent_slot_lt` shape, `hwalk` the blanket walk domain). -/
theorem find_latest_confirmed_descendant_ge (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    is_ancestor fcr_store.store
        (get_node_for_root (find_latest_confirmed_descendant cfg ext fcr_store lcr))
        (get_node_for_root lcr) = true ∧
      find_latest_confirmed_descendant cfg ext fcr_store lcr ∈ fcr_store.store.block_roots := by
  set P : Root → Prop := fun r =>
    is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root lcr) = true ∧
      r ∈ fcr_store.store.block_roots with hP
  have base : P lcr := ⟨is_ancestor_refl _ _, hlcr⟩
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc) := by
    intro ce acc hacc
    obtain ⟨hacc_anc, hacc_mem⟩ := hacc
    rcases prev_epoch_loop_spec cfg ext fcr_store ce
        (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc with
      h | ⟨r, hr, heq, _hc⟩
    · rw [h]; exact ⟨hacc_anc, hacc_mem⟩
    · rw [heq]
      have hr_anc := get_ancestor_roots_descends hwf hwalk hacc_mem hhead hr
      have hr_mem := get_ancestor_roots_mem hwf (hwalk acc hacc_mem _ hhead) hr
      exact ⟨is_ancestor_trans (a := get_node_for_root r) (b := get_node_for_root acc)
        (c := get_node_for_root lcr) hwf (hwalk lcr hlcr r hr_mem)
        (hwalk lcr hlcr acc hacc_mem) hr_anc hacc_anc, hr_mem⟩
  have htent : ∀ (acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc) := by
    intro acc hacc
    obtain ⟨hacc_anc, hacc_mem⟩ := hacc
    rcases tentative_loop_spec cfg ext fcr_store
        (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc with
      h | ⟨r, hr, heq, _hc⟩
    · rw [h]; exact ⟨hacc_anc, hacc_mem⟩
    · rw [heq]
      have hr_anc := get_ancestor_roots_descends hwf hwalk hacc_mem hhead hr
      have hr_mem := get_ancestor_roots_mem hwf (hwalk acc hacc_mem _ hhead) hr
      exact ⟨is_ancestor_trans (a := get_node_for_root r) (b := get_node_for_root acc)
        (c := get_node_for_root lcr) hwf (hwalk lcr hlcr r hr_mem)
        (hwalk lcr hlcr acc hacc_mem) hr_anc hacc_anc, hr_mem⟩
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




namespace Execution

variable (E : Execution Root)



end Execution

end FastConfirmation.Spec

end
