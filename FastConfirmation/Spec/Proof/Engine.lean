module
public import FastConfirmation.Spec.Proof.MajorityPersists
public import FastConfirmation.Spec.Proof.Descent
public import FastConfirmation.Spec.Proof.FilterViability

@[expose] public section

/-!
# Spec / Proof / Engine: head membership and boost congruence

This module establishes two structural facts used by the head-safety engine:

- **Head membership** (`get_head_root_mem_or`): `get_head` lands on a known
  block or degenerately stays at the justified root — the filtered list only
  carries known roots plus possibly the descent base itself, and every
  descent step moves into the filtered list. This settles `Delivery`'s
  `hhead_known` residue by case split, with **no** `justified_known`
  assumption: the degenerate case is threaded, not assumed away.
- **Boost congruence** (`compute_proposer_score_congr`): registry-constant
  balance sources agree on the proposer score, so the confirmation-time
  boost equals the later store's (reconciliation (a), boost half).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

omit [Inhabited Root] in
/-- Filter-output confinement: every root the `filter_block_tree` worker emits
is a known block or the call's own base root (children are drawn from
`block_roots`; only the base can be foreign). -/
theorem filter_block_tree_aux_output_mem {store : Store Root} :
    ∀ (fuel : ℕ) (base r : Root),
      r ∈ (filter_block_tree_aux cfg store fuel base).2 →
        r ∈ store.block_roots ∨ r = base := by
  intro fuel
  induction fuel with
  | zero =>
    intro base r hr
    simp only [filter_block_tree_aux] at hr
    exact absurd hr (List.not_mem_nil)
  | succ fuel ih =>
    intro base r hr
    by_cases hne :
      store.block_roots.filter (fun x => (store.blocks x).parent_root = base) ≠ []
    · rw [filter_block_tree_aux_internal cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr <;>
        [skip; skip] <;>
        first
          | · rcases List.mem_append.mp hr with hr | hr
              · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr
                obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
                obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
                rcases ih child r hrl with h | rfl
                · exact Or.inl h
                · exact Or.inl (List.mem_filter.mp hchild).1
              · exact Or.inr (List.mem_singleton.mp hr)
          | · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr
              obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
              obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
              rcases ih child r hrl with h | rfl
              · exact Or.inl h
              · exact Or.inl (List.mem_filter.mp hchild).1
    · rw [not_not] at hne
      rw [filter_block_tree_aux_leaf cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr
      · exact Or.inr (List.mem_singleton.mp hr)
      · exact absurd hr (List.not_mem_nil)

/-- Descent confinement: `get_head_aux` returns its start node or a member of
the candidate list (each step's `argmax` picks a child from the list). -/
theorem get_head_aux_root_mem_or {store : Store Root} {blocks : List Root} :
    ∀ (fuel : ℕ) (h : ForkChoiceNode Root),
      (get_head_aux cfg store blocks fuel h).root ∈ blocks ∨
        (get_head_aux cfg store blocks fuel h).root = h.root := by
  intro fuel
  induction fuel with
  | zero => intro h; exact Or.inr rfl
  | succ fuel ih =>
    intro h
    cases hbest : (get_node_children store blocks h).argmax
        (fun child => toLex (get_weight cfg store child, child.root)) with
    | none =>
      rw [get_head_aux_succ, hbest]
      exact Or.inr rfl
    | some best =>
      rw [get_head_aux_step cfg store blocks fuel h best hbest]
      have hmem : best ∈ get_node_children store blocks h := List.argmax_mem hbest
      have hbb : best.root ∈ blocks := (mem_get_node_children.mp hmem).1
      rcases ih best with hin | heq
      · exact Or.inl hin
      · exact Or.inl (heq ▸ hbb)

/-- **Head membership**: `get_head` lands on a known block, or degenerately at
the justified checkpoint root (empty filtered descent) — the case split that
replaces any `justified_known` assumption. -/
theorem get_head_root_mem_or (store : Store Root) :
    (get_head cfg store).root ∈ store.block_roots ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
  simp only [get_head]
  rcases get_head_aux_root_mem_or cfg
      (blocks := get_filtered_block_tree cfg store)
      (get_filtered_block_tree cfg store).length.succ
      (ForkChoiceNode.mk store.justified_checkpoint.root) with hin | heq
  · rcases filter_block_tree_aux_output_mem cfg _ _ _ hin with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inr heq

omit [LinearOrder Root] [Inhabited Root] in
/-- **Boost congruence**: registry-constant, activity-constant balance sources
agree on `compute_proposer_score` (reconciliation (a), boost half — the
confirmation-time proposer score equals the later store's). -/
theorem compute_proposer_score_congr {st st' : BeaconState Root}
    (hval : st.validators = st'.validators)
    (hact : ∀ i : ValidatorIndex,
      is_active_validator (st.validators.getD i default) (get_current_epoch cfg st) =
        is_active_validator (st'.validators.getD i default) (get_current_epoch cfg st')) :
    compute_proposer_score cfg st = compute_proposer_score cfg st' := by
  simp only [compute_proposer_score]
  rw [get_total_active_balance_congr cfg hval hact]

end FastConfirmation.Spec

end
