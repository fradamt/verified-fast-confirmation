module
public import FastConfirmationProofs.ForkChoice.Filter.SelectedFilterVisibility

@[expose] public section

/-!
# Complete selected-loop edge coverage

The result-only inversions for `find_latest_confirmed_descendant` identify the
last accepted block but erase the accepted prefix.  The executable ghost trace
retains that prefix.  This module proves that the retained lists are complete:
every strict direct parent edge between the wrapper input and its returned
result occurs in one of the two lists.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- A list of direct parent transitions from `start` to `result`.  Knownness is
stored at every node so completeness uses only ordinary well-formed tree
geometry. -/
inductive SelectedParentTrace (store : Store Root) :
    Root → Root → List (Root × Root) → Prop where
  | nil {r : Root} (hr : r ∈ store.block_roots) :
      SelectedParentTrace store r r []
  | cons {start next result : Root} {rest : List (Root × Root)}
      (hstart : start ∈ store.block_roots)
      (hnext : next ∈ store.block_roots)
      (hparent : (store.blocks next).parent_root = start)
      (tail : SelectedParentTrace store next result rest) :
      SelectedParentTrace store start result ((start, next) :: rest)

namespace SelectedParentTrace


omit [LinearOrder Root] [Inhabited Root] in
theorem result_known {store : Store Root} {start result : Root}
    {edges : List (Root × Root)}
    (h : SelectedParentTrace store start result edges) :
    result ∈ store.block_roots := by
  induction h with
  | nil hr => exact hr
  | cons _ _ _ _ ih => exact ih


omit [LinearOrder Root] [Inhabited Root] in
/-- The child of every listed edge is strictly later than the trace start. -/
theorem edge_child_slot_gt_start {store : Store Root}
    (hwf : ParentSlotLt store)
    {start result : Root} {edges : List (Root × Root)}
    (h : SelectedParentTrace store start result edges)
    {a c : Root} (hm : (a, c) ∈ edges) :
    (store.blocks start).slot < (store.blocks c).slot := by
  induction h with
  | nil hr => simp at hm
  | @cons start next result rest hs hn hp tail ih =>
      have hstartNext : (store.blocks start).slot <
          (store.blocks next).slot := by
        have hlt := hwf next hn (by rw [hp]; exact hs)
        rwa [hp] at hlt
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact hstartNext
      · exact hstartNext.trans (ih hm)

omit [LinearOrder Root] [Inhabited Root] in
theorem append {store : Store Root} {start mid result : Root}
    {left right : List (Root × Root)}
    (hleft : SelectedParentTrace store start mid left)
    (hright : SelectedParentTrace store mid result right) :
    SelectedParentTrace store start result (left ++ right) := by
  induction hleft with
  | nil _ => simpa using hright
  | cons hs hn hp _ ih =>
      simpa using SelectedParentTrace.cons hs hn hp (ih hright)

omit [Inhabited Root] in
/-- The result of a parent trace descends from its start. -/
theorem result_descends_start {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {start result : Root} {edges : List (Root × Root)}
    (h : SelectedParentTrace store start result edges) :
    is_ancestor store (get_node_for_root result)
      (get_node_for_root start) = true := by
  induction h with
  | nil hr => exact is_ancestor_refl _ _
  | @cons start next result rest hs hn hp tail ih =>
      have hnextStart : is_ancestor store (get_node_for_root next)
          (get_node_for_root start) = true :=
        is_ancestor_of_parent hwf hn hs hp
      exact is_ancestor_trans (a := get_node_for_root result) (b := get_node_for_root next)
          (c := get_node_for_root start) hwf
        (hwalk start hs result tail.result_known)
        (hwalk start hs next hn) ih hnextStart

/-- Every strict direct parent edge on the ancestry interval represented by a
parent trace occurs in its edge list. -/
theorem edge_mem {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {start result : Root} {edges : List (Root × Root)}
    (htrace : SelectedParentTrace store start result edges)
    {a c : Root} (ha : a ∈ store.block_roots) (hc : c ∈ store.block_roots)
    (hparent : (store.blocks c).parent_root = a)
    (hresultC : is_ancestor store (get_node_for_root result)
      (get_node_for_root c) = true)
    (hcStart : is_ancestor store (get_node_for_root c)
      (get_node_for_root start) = true)
    (hcne : c ≠ start) :
    (a, c) ∈ edges := by
  induction htrace generalizing a c with
  | @nil r hr =>
      have heq : c = r := is_ancestor_antisymm hwf
        (hwalk c hc r hr) hcStart hresultC
      exact False.elim (hcne heq)
  | @cons start next result rest hstart hnext hnextParent tail ih =>
      have hresultNext := tail.result_descends_start hwf hwalk
      rcases is_ancestor_comparable hwf
          (hwalk c hc result tail.result_known)
          (hwalk next hnext result tail.result_known)
          hresultC hresultNext with hnextC | hcNext
      · rcases between_parent_child hwf hnext hstart
            (hwalk c hc next hnext) (hwalk start hstart c hc)
            hnextParent hnextC hcStart with rfl | rfl
        · exact False.elim (hcne rfl)
        · have haeq : a = start := by
            rw [← hparent, hnextParent]
          simp [haeq]
      · by_cases hceq : c = next
        · subst c
          have haeq : a = start := by
            rw [← hparent, hnextParent]
          simp [haeq]
        · exact List.mem_cons_of_mem _
            (ih ha hc hparent hresultC hcNext hceq)

end SelectedParentTrace

/-! ## The two loop traces are complete parent traces -/

theorem prevEpochLoopTrace_parentTrace
    (fcrStore : FastConfirmationStore Root) (currentEpoch : Epoch) :
    ∀ (roots : List Root) (acc : Root),
      (∀ x ∈ roots, x ∈ fcrStore.store.block_roots) →
      List.IsChain
        (fun a c => (fcrStore.store.blocks c).parent_root = a) roots →
      (∀ x, roots.head? = some x →
        (fcrStore.store.blocks x).parent_root = acc) →
      acc ∈ fcrStore.store.block_roots →
      SelectedParentTrace fcrStore.store acc
        (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).1
        (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).2 := by
  intro roots
  induction roots with
  | nil =>
      intro acc _ _ _ hacc
      exact .nil hacc
  | cons b rest ih =>
      intro acc hmem hchain hhead hacc
      simp only [prevEpochLoopTrace]
      by_cases hEpoch : get_block_epoch cfg fcrStore.store b = currentEpoch
      · rw [if_pos hEpoch]
        exact .nil hacc
      · rw [if_neg hEpoch]
        by_cases hAncestor : is_ancestor fcrStore.store
            (get_node_for_root fcrStore.previous_slot_head)
            (get_node_for_root b) = true
        · rw [if_neg (not_not_intro hAncestor)]
          by_cases hConfirmed : is_one_confirmed cfg ext fcrStore.store
              (get_current_balance_source fcrStore) b = true
          · rw [if_neg (not_not_intro hConfirmed)]
            apply SelectedParentTrace.cons hacc
              (hmem b List.mem_cons_self) (hhead b rfl)
            exact ih b
              (fun x hx => hmem x (List.mem_cons_of_mem b hx))
              (List.isChain_cons.mp hchain).2
              (fun x hx => (List.isChain_cons.mp hchain).1 x
                (Option.mem_def.mpr hx))
              (hmem b List.mem_cons_self)
          · rw [if_pos hConfirmed]
            exact .nil hacc
        · rw [if_pos hAncestor]
          exact .nil hacc

theorem tentativeLoopTrace_parentTrace
    (fcrStore : FastConfirmationStore Root) :
    ∀ (roots : List Root) (acc : Root),
      (∀ x ∈ roots, x ∈ fcrStore.store.block_roots) →
      List.IsChain
        (fun a c => (fcrStore.store.blocks c).parent_root = a) roots →
      (∀ x, roots.head? = some x →
        (fcrStore.store.blocks x).parent_root = acc) →
      acc ∈ fcrStore.store.block_roots →
      SelectedParentTrace fcrStore.store acc
        (tentativeLoopTrace cfg ext fcrStore roots acc).1
        (tentativeLoopTrace cfg ext fcrStore roots acc).2 := by
  intro roots
  induction roots with
  | nil =>
      intro acc _ _ _ hacc
      exact .nil hacc
  | cons b rest ih =>
      intro acc hmem hchain hhead hacc
      simp only [tentativeLoopTrace]
      by_cases hGate : get_block_epoch cfg fcrStore.store b >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ will_current_target_be_justified cfg ext fcrStore.store
      · rw [if_pos hGate]
        exact .nil hacc
      · rw [if_neg hGate]
        by_cases hConfirmed : is_one_confirmed cfg ext fcrStore.store
            (get_current_balance_source fcrStore) b = true
        · rw [if_neg (not_not_intro hConfirmed)]
          apply SelectedParentTrace.cons hacc
            (hmem b List.mem_cons_self) (hhead b rfl)
          exact ih b
            (fun x hx => hmem x (List.mem_cons_of_mem b hx))
            (List.isChain_cons.mp hchain).2
            (fun x hx => (List.isChain_cons.mp hchain).1 x
              (Option.mem_def.mpr hx))
            (hmem b List.mem_cons_self)
        · rw [if_pos hConfirmed]
          exact .nil hacc

theorem prevEpochCanonicalTrace_parentTrace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (currentEpoch : Epoch) (acc : Root)
    (hacc : acc ∈ fcrStore.store.block_roots) :
    SelectedParentTrace fcrStore.store acc
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).1
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).2 := by
  have hw := hwalk acc hacc _ hhead
  exact prevEpochLoopTrace_parentTrace cfg ext fcrStore currentEpoch _ acc
    (fun x hx => get_ancestor_roots_mem hwf hw hx)
    (get_ancestor_roots_isChain hwf hw)
    (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc

theorem tentativeCanonicalTrace_parentTrace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (acc : Root) (hacc : acc ∈ fcrStore.store.block_roots) :
    SelectedParentTrace fcrStore.store acc
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).1
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).2 := by
  have hw := hwalk acc hacc _ hhead
  exact tentativeLoopTrace_parentTrace cfg ext fcrStore _ acc
    (fun x hx => get_ancestor_roots_mem hwf hw hx)
    (get_ancestor_roots_isChain hwf hw)
    (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc

/-! ## Complete wrapper trace -/

/-- The two retained lists form a complete parent trace from the wrapper input
to its executable result. -/
theorem findLatestSelectedTrace_parentTrace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (latestConfirmedRoot : Root)
    (hlcr : latestConfirmedRoot ∈ fcrStore.store.block_roots) :
    SelectedParentTrace fcrStore.store latestConfirmedRoot
      (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).1
      ((findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.1 ++
        (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) := by
  let store := fcrStore.store
  let head := (get_head cfg store).root
  let currentEpoch := get_current_store_epoch cfg store
  let pRoots := get_ancestor_roots store head latestConfirmedRoot
  let pExec := find_latest_confirmed_descendant_prev_epoch_loop cfg ext
    fcrStore currentEpoch pRoots latestConfirmedRoot
  let pTrace := prevEpochLoopTrace cfg ext fcrStore currentEpoch pRoots
    latestConfirmedRoot
  let pGuard :=
    get_block_epoch cfg store latestConfirmedRoot + 1 = currentEpoch ∧
      (get_voting_source cfg store fcrStore.previous_slot_head).epoch + 2 ≥
        currentEpoch ∧
      (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
        (will_no_conflicting_checkpoint_be_justified cfg ext store = true ∧
          ((store.unrealized_justifications fcrStore.previous_slot_head).epoch + 1 ≥
              currentEpoch ∨
            (store.unrealized_justifications head).epoch + 1 ≥ currentEpoch)))
  let previousRoot := if pGuard then pExec else latestConfirmedRoot
  let previousEdges := if pGuard then pTrace.2 else []
  have hpRaw := prevEpochCanonicalTrace_parentTrace cfg ext fcrStore hwf
    hwalk hhead currentEpoch latestConfirmedRoot hlcr
  have hpExec : SelectedParentTrace store latestConfirmedRoot pExec pTrace.2 := by
    simpa only [store, head, currentEpoch, pRoots, pExec, pTrace,
      prevEpochLoopTrace_fst] using hpRaw
  have hp : SelectedParentTrace store latestConfirmedRoot
      previousRoot previousEdges := by
    by_cases hpg : pGuard
    · simpa only [previousRoot, previousEdges, if_pos hpg] using hpExec
    · simpa only [previousRoot, previousEdges, if_neg hpg] using
        (SelectedParentTrace.nil hlcr)
  let tRoots := get_ancestor_roots store head previousRoot
  let tExec := find_latest_confirmed_descendant_tentative_loop cfg ext
    fcrStore tRoots previousRoot
  let tTrace := tentativeLoopTrace cfg ext fcrStore tRoots previousRoot
  have htRaw := tentativeCanonicalTrace_parentTrace cfg ext fcrStore hwf
    hwalk hhead previousRoot hp.result_known
  have htExec : SelectedParentTrace store previousRoot tExec tTrace.2 := by
    simpa only [store, head, tRoots, tExec, tTrace,
      tentativeLoopTrace_fst] using htRaw
  let tGuard := is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
    (store.unrealized_justifications head).epoch + 1 ≥ currentEpoch
  let finalGuard :=
    get_block_epoch cfg store tExec = currentEpoch ∨
      ((get_voting_source cfg store tExec).epoch + 2 ≥ currentEpoch ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
          will_no_conflicting_checkpoint_be_justified cfg ext store = true))
  by_cases htg : tGuard
  · by_cases hfg : finalGuard
    · have hall := hp.append htExec
      simpa [findLatestSelectedTrace, find_latest_confirmed_descendant,
        store, head, currentEpoch, pRoots, pExec, pTrace, pGuard,
        previousRoot, previousEdges, tRoots, tExec, tTrace, tGuard,
        finalGuard, htg, hfg] using hall
    · simpa [findLatestSelectedTrace, find_latest_confirmed_descendant,
        store, head, currentEpoch, pRoots, pExec, pTrace, pGuard,
        previousRoot, previousEdges, tRoots, tExec, tTrace, tGuard,
        finalGuard, htg, hfg] using hp
  · simpa [findLatestSelectedTrace, find_latest_confirmed_descendant,
      store, head, currentEpoch, pRoots, pExec, pTrace, pGuard,
      previousRoot, previousEdges, tRoots, tExec, tTrace, tGuard,
      finalGuard, htg] using hp

/-- Every strict direct parent edge between the wrapper input and its selected
result occurs in one of the two retained executable traces.  This is the
coverage statement needed to apply the corresponding accepted-edge filter
facts to an arbitrary edge of the selected chain. -/
theorem strict_selected_edge_mem_trace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (latestConfirmedRoot : Root)
    (hlcr : latestConfirmedRoot ∈ fcrStore.store.block_roots)
    {a c : Root}
    (ha : a ∈ fcrStore.store.block_roots)
    (hc : c ∈ fcrStore.store.block_roots)
    (hparent : (fcrStore.store.blocks c).parent_root = a)
    (hresultC : is_ancestor fcrStore.store
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot))
      (get_node_for_root c) = true)
    (hcLcr : is_ancestor fcrStore.store (get_node_for_root c)
      (get_node_for_root latestConfirmedRoot) = true)
    (hcne : c ≠ latestConfirmedRoot) :
    PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c ∨
      (a, c) ∈
        (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2 := by
  have htrace := findLatestSelectedTrace_parentTrace cfg ext fcrStore hwf
    hwalk hhead latestConfirmedRoot hlcr
  have hresultC' : is_ancestor fcrStore.store
      (get_node_for_root
        (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).1)
      (get_node_for_root c) = true := by
    simpa only [findLatestSelectedTrace_fst] using hresultC
  have hm := htrace.edge_mem hwf hwalk ha hc hparent hresultC' hcLcr hcne
  rcases List.mem_append.mp hm with hprev | htent
  · exact Or.inl hprev
  · exact Or.inr htent



end FastConfirmation.Spec

end
