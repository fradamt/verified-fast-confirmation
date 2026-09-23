module
public import FastConfirmation.Spec.Proof.SelectedFilterBridge
public import FastConfirmation.Spec.Proof.AnchorClose

@[expose] public section

/-!
# Selected filter-tip chain geometry

The opaque FFG boundary only needs to identify a known leaf which lies below
both the endpoint justified root and the selected child, plus the walk domain
at the finalized epoch boundary (which does not follow from the ordinary
known-root-slot walk in the totalized model).  This module turns that placement
into the concrete `get_ancestor_roots`/`ChainDown` skeleton consumed by the
executable filter.

The nontrivial list fact is converse path membership: a block strictly
between the walk start and terminal occurs in `get_ancestor_roots`.  It is
proved directly from the worker recursion, rather than postulated as part of
the FFG contract.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-- The residual selected-branch placement around a source-fresh tip.  Unlike
`FilterTipSkeleton`, it contains no ancestor list, `ChainDown` witness, or
selected-child list membership. -/
structure RetainedFilterTipPlacement (store : Store Root) (c : Root) where
  tip : Root
  tip_known : tip ∈ store.block_roots
  tip_descends_justified : is_ancestor store (get_node_for_root tip)
    (get_node_for_root store.justified_checkpoint.root) = true
  tip_descends_child : is_ancestor store (get_node_for_root tip)
    (get_node_for_root c) = true
  tip_is_leaf : store.block_roots.filter
    (fun x => (store.blocks x).parent_root = tip) = []
  finalized_walk_known : WalkKnown store
    (compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch) tip

namespace SelectedFilterChainGeometry

omit [Inhabited Root] in
/-- An ancestry walk makes the ancestor-list worker return a list, unless the
start already equals the terminal. -/
private theorem roots_isSome_of_ancestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {t r : Root} (hw : WalkKnown store (store.blocks t).slot r) :
    (get_ancestor store (ForkChoiceNode.mk r .pending) (store.blocks t).slot).root = t →
    ∀ fuel : ℕ, (store.blocks r).slot < fuel →
      (get_ancestor_roots_aux store t fuel r).isSome = true ∨ r = t := by
  induction hw with
  | stop hr hle =>
    intro hanc _ _
    rw [get_ancestor_stop hle] at hanc
    exact Or.inr (by simpa using hanc)
  | @step r hr hgt hp ih =>
    intro hanc fuel hfuel
    rw [get_ancestor_step hwf hr hgt hp] at hanc
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ f =>
      rw [get_ancestor_roots_aux_succ, if_pos hgt]
      by_cases hD : (store.blocks r).parent_root = t
      · rw [if_pos hD]
        exact Or.inl rfl
      · rw [if_neg hD]
        have hbound : (store.blocks (store.blocks r).parent_root).slot < f :=
          Nat.lt_of_lt_of_le (hwf r hr hp.root_mem) (Nat.lt_succ_iff.mp hfuel)
        rcases ih hanc f hbound with hsome | hpeq
        · left
          obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hsome
          rw [hl]
          rfl
        · exact absurd hpeq hD

omit [Inhabited Root] in
/-- Executable ancestor-list case split for a known ancestry walk. -/
private theorem hcase_of_ancestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {b jc : Root} (hwalk : WalkKnown store (store.blocks jc).slot b)
    (hanc : is_ancestor store (ForkChoiceNode.mk b .pending) (ForkChoiceNode.mk jc .pending) = true) :
    get_ancestor_roots store b jc ≠ [] ∨ b = jc := by
  simp only [is_ancestor_pending, decide_eq_true_eq] at hanc
  rcases roots_isSome_of_ancestor hwf hwalk hanc
      ((store.blocks b).slot + 1) (Nat.lt_succ_self _) with hsome | heq
  · left
    rw [get_ancestor_roots]
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hsome
    rw [hl]
    change l ≠ []
    exact (get_ancestor_roots_aux_chain hwf hwalk _
      (Nat.lt_succ_self _) l hl).1
  · exact Or.inr heq

omit [Inhabited Root] [LinearOrder Root] in
/-- A known parent-linked list is a `ChainDown` run. -/
theorem chainDown_of_parentChain {store : Store Root} :
    ∀ (L : List Root) (top : Root),
      (∀ r ∈ top :: L, r ∈ store.block_roots) →
      List.IsChain (fun a c => (store.blocks c).parent_root = a) (top :: L) →
      ChainDown store top L
  | [], _, _, _ => trivial
  | c :: rest, top, hmem, hchain => by
      rw [List.isChain_cons_cons] at hchain
      refine ⟨⟨hmem c (by simp), hchain.1⟩, ?_⟩
      exact chainDown_of_parentChain rest c
        (fun r hr => hmem r (List.mem_cons_of_mem _ hr)) hchain.2

omit [Inhabited Root] in
/-- Decompose a strict ancestry walk into the exact list used by
`get_ancestor_roots`, retaining the equality needed for intermediate
membership. -/
theorem chainDown_of_isAncestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {top t : Root} (htop : top ∈ store.block_roots) (ht : t ∈ store.block_roots)
    (hanc : is_ancestor store (get_node_for_root t) (get_node_for_root top) = true) :
    t = top ∨ ∃ mids : List Root,
      ChainDown store top (mids ++ [t]) ∧
      (∀ r ∈ mids ++ [t], r ∈ store.block_roots) ∧
      mids ++ [t] = get_ancestor_roots store t top := by
  have hanc' : is_ancestor store (ForkChoiceNode.mk t .pending) (ForkChoiceNode.mk top .pending) = true := by
    simpa only [get_node_for_root] using hanc
  have hcase := hcase_of_ancestor hwf (hwalkK top htop t ht) hanc'
  rcases hcase with hne | heq
  · refine Or.inr ?_
    obtain ⟨hmem, hchainPL, hlast⟩ := parentChain_at hwf hwalkK htop ht (Or.inl hne)
    set L := get_ancestor_roots store t top with hLdef
    have hLne : L ≠ [] := hne
    have hgetLast : L.getLast hLne = t := by
      have := hlast
      rwa [List.getLast_cons hLne] at this
    have hsplit : L.dropLast ++ [t] = L := by
      conv_rhs => rw [← List.dropLast_append_getLast hLne, hgetLast]
    refine ⟨L.dropLast, ?_, ?_, hsplit⟩
    · rw [hsplit]
      exact chainDown_of_parentChain _ top hmem hchainPL
    · rw [hsplit]
      exact fun r hr => hmem r (List.mem_cons_of_mem _ hr)
  · exact Or.inl heq

omit [Inhabited Root] in
/-- Root form of converse ancestor-list membership. Parent recursion may
resolve a payload status; list membership depends only on the beacon root. -/
private theorem mem_get_ancestor_roots_aux_of_between_root {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {top : Root} {r : Root} (hw : WalkKnown store (store.blocks top).slot r) :
    ∀ (fuel : ℕ), (store.blocks r).slot < fuel → ∀ (l : List Root),
      get_ancestor_roots_aux store top fuel r = some l →
      ∀ c : Root, (store.blocks top).slot < (store.blocks c).slot →
        (get_ancestor store (ForkChoiceNode.mk r .pending) (store.blocks c).slot).root = c →
        c ∈ l := by
  induction hw with
  | stop hr hle =>
    intro fuel hfuel l hl
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ f =>
      rw [get_ancestor_roots_aux_succ, if_neg (by simpa using hle)] at hl
      simp at hl
  | @step r hr hgt hp ih =>
    intro fuel hfuel l hl c hcslot hget
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ f =>
      have hCpos : (store.blocks r).slot > (store.blocks top).slot := hgt
      rw [get_ancestor_roots_aux_succ, if_pos hCpos] at hl
      by_cases hceq : c = r
      · subst hceq
        by_cases hD : (store.blocks c).parent_root = top
        · rw [if_pos hD, Option.some_inj] at hl
          subst hl
          simp
        · rw [if_neg hD] at hl
          obtain ⟨l', _hl', rfl⟩ := Option.map_eq_some_iff.mp hl
          simp
      · have hcr : (store.blocks c).slot < (store.blocks r).slot := by
          rcases Nat.lt_or_ge (store.blocks c).slot (store.blocks r).slot with h | h
          · exact h
          · rw [get_ancestor_stop h] at hget
            exact absurd hget.symm hceq
        have hp' : WalkKnown store (store.blocks c).slot
            (store.blocks r).parent_root := hp.mono (le_of_lt hcslot)
        have hget' : (get_ancestor store
            (ForkChoiceNode.mk (store.blocks r).parent_root .pending)
            (store.blocks c).slot).root = c := by
          rw [← get_ancestor_step hwf hr hcr hp']
          exact hget
        by_cases hD : (store.blocks r).parent_root = top
        · rw [hD] at hget'
          rw [get_ancestor_stop (le_of_lt hcslot)] at hget'
          have : top = c := hget'
          exact absurd (this ▸ hcslot) (lt_irrefl _)
        · rw [if_neg hD] at hl
          obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp hl
          have hbound : (store.blocks (store.blocks r).parent_root).slot < f :=
            Nat.lt_of_lt_of_le (hwf _ hr hp.root_mem) (Nat.lt_succ_iff.mp hfuel)
          exact List.mem_append.mpr (Or.inl (ih f hbound l' hl' c hcslot hget'))


omit [Inhabited Root] in
/-- A block strictly between the terminal and start of an ancestry walk occurs
in the executable ancestor list. -/
theorem mem_get_ancestor_roots_of_between {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {top t c : Root} (htop : top ∈ store.block_roots) (ht : t ∈ store.block_roots)
    (hc : c ∈ store.block_roots)
    (htc : is_ancestor store (get_node_for_root t) (get_node_for_root c) = true)
    (hctop : is_ancestor store (get_node_for_root c) (get_node_for_root top) = true)
    (hne : c ≠ top) :
    c ∈ get_ancestor_roots store t top := by
  have hctop' : (get_ancestor store (ForkChoiceNode.mk c .pending) (store.blocks top).slot).root =
      top := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hctop
  have htc' : (get_ancestor store (ForkChoiceNode.mk t .pending) (store.blocks c).slot).root =
      c := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using htc
  have hcslot : (store.blocks top).slot < (store.blocks c).slot := by
    rcases Nat.lt_or_ge (store.blocks top).slot (store.blocks c).slot with h | h
    · exact h
    · rw [get_ancestor_stop h] at hctop'
      exact absurd hctop' hne
  have hct : (store.blocks c).slot ≤ (store.blocks t).slot := by
    have h := get_ancestor_slot_le hwf (hwalkK c hc t ht)
    rw [htc'] at h
    exact h
  have htne : t ≠ top := by
    intro heq
    rw [heq] at hct
    exact absurd (lt_of_lt_of_le hcslot hct) (lt_irrefl _)
  have httop : is_ancestor store (ForkChoiceNode.mk t .pending) (ForkChoiceNode.mk top .pending) = true := by
    have h := is_ancestor_trans hwf (hwalkK top htop t ht)
      (hwalkK top htop c hc) htc hctop
    simpa only [get_node_for_root] using h
  rcases hcase_of_ancestor hwf (hwalkK top htop t ht) httop with hnil | heq
  · rw [get_ancestor_roots] at hnil ⊢
    cases haux : get_ancestor_roots_aux store top ((store.blocks t).slot + 1) t with
    | none =>
      rw [haux] at hnil
      simp at hnil
    | some l =>
      rw [Option.getD_some]
      exact mem_get_ancestor_roots_aux_of_between_root hwf (hwalkK top htop t ht)
        _ (Nat.lt_succ_self _) l haux c hcslot htc'
  · exact absurd heq htne

/-- Construct the entire filter skeleton from a common-descendant leaf.  All
ancestor-list fields are derived; only the separately indexed finalized-slot
walk is copied from the narrow placement boundary. -/
theorem exists_filterTipSkeleton_of_placement {store : Store Root} {c : Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    (hc : c ∈ store.block_roots)
    (hnotCovered : is_ancestor store
      (get_node_for_root store.justified_checkpoint.root)
      (get_node_for_root c) ≠ true)
    (hplace : RetainedFilterTipPlacement cfg store c) :
    ∃ hskel : FilterTipSkeleton cfg store c, hskel.tip = hplace.tip := by
  have hcJust : is_ancestor store (get_node_for_root c)
      (get_node_for_root store.justified_checkpoint.root) = true := by
    rcases is_ancestor_comparable hwf
        (hwalkK c hc hplace.tip hplace.tip_known)
        (hwalkK store.justified_checkpoint.root hjust hplace.tip hplace.tip_known)
        hplace.tip_descends_child hplace.tip_descends_justified with hreverse | hforward
    · exact False.elim (hnotCovered hreverse)
    · exact hforward
  rcases chainDown_of_isAncestor hwf hwalkK hjust hplace.tip_known
      hplace.tip_descends_justified with htipEq | ⟨mids, hchain, _hall, hroots⟩
  · have hreverse : is_ancestor store
        (get_node_for_root store.justified_checkpoint.root)
        (get_node_for_root c) = true := by
      simpa only [htipEq] using hplace.tip_descends_child
    exact False.elim (hnotCovered hreverse)
  · have hchild : c ∈ mids ∨ c = hplace.tip ∨
        c = store.justified_checkpoint.root := by
      by_cases hcJustEq : c = store.justified_checkpoint.root
      · exact Or.inr (Or.inr hcJustEq)
      by_cases hcTip : c = hplace.tip
      · exact Or.inr (Or.inl hcTip)
      have hmem := mem_get_ancestor_roots_of_between hwf hwalkK hjust
        hplace.tip_known hc hplace.tip_descends_child hcJust hcJustEq
      rw [← hroots, List.mem_append, List.mem_singleton] at hmem
      exact hmem.elim Or.inl (fun heq => False.elim (hcTip heq))
    refine ⟨
      { mids := mids
        tip := hplace.tip
        chain := hchain
        child_on_chain := hchild
        tip_is_leaf := hplace.tip_is_leaf
        parent_slot_lt := hwf
        walk_known := hwalkK
        finalized_walk_known := hplace.finalized_walk_known }, rfl⟩

end SelectedFilterChainGeometry

end FastConfirmation.Spec

end
