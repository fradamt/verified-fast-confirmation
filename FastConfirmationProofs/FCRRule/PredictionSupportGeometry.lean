module
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant
public import FastConfirmationProofs.FCRRule.SelectedTraceCoverage

/-!
A retained epoch-crossing edge has a known current-epoch child on the query
head chain. This is the geometric part of the prediction-support reduction.
It follows from the selected parent trace and the selector's recency guard.
No future vote support or head-safety conclusion is an input.
-/

@[expose] public section

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

private theorem selectedParentTrace_descendsStart
    {store : Store Root} (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {start result : Root} {edges : List (Root × Root)}
    (h : SelectedParentTrace store start result edges) :
    is_ancestor store (get_node_for_root result) (get_node_for_root start) = true := by
  induction h with
  | nil hr => exact is_ancestor_refl _ _
  | @cons start next result rest hs hn hp tail ih =>
      exact is_ancestor_trans (a := get_node_for_root result)
        (b := get_node_for_root next) (c := get_node_for_root start) hwf
        (hwalk start hs result tail.result_known) (hwalk start hs next hn)
        ih (is_ancestor_of_parent hwf hn hs hp)

private theorem selectedParentTrace_edge_geometry
    {store : Store Root} (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {start result : Root} {edges : List (Root × Root)}
    (h : SelectedParentTrace store start result edges)
    {a c : Root} (hedge : (a, c) ∈ edges) :
    a ∈ store.block_roots ∧ c ∈ store.block_roots ∧
      (store.blocks start).slot ≤ (store.blocks a).slot ∧
      is_ancestor store (get_node_for_root result) (get_node_for_root c) = true := by
  induction h with
  | nil hr => simp at hedge
  | @cons start next result rest hs hn hp tail ih =>
      rw [List.mem_cons] at hedge
      rcases hedge with hedge | hedge
      · simp only [Prod.mk.injEq] at hedge
        obtain ⟨rfl, rfl⟩ := hedge
        exact ⟨hs, hn, Nat.le_refl _, selectedParentTrace_descendsStart hwf hwalk tail⟩
      · obtain ⟨ha, hc, hslot, hdesc⟩ := ih hedge
        have hstep := hwf next hn (by rw [hp]; exact hs)
        rw [hp] at hstep
        exact ⟨ha, hc, hstep.le.trans hslot, hdesc⟩

private theorem tentativeLoopTrace_child_mem
    (query : FastConfirmationStore Root) :
    ∀ roots acc a c, (a, c) ∈ (tentativeLoopTrace cfg ext query roots acc).2 →
      c ∈ roots := by
  intro roots
  induction roots with
  | nil => simp [tentativeLoopTrace]
  | cons b rest ih =>
      intro acc a c h
      simp only [tentativeLoopTrace] at h
      split_ifs at h <;> try simp at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ _ _ h)

/-- A retained crossing child is a known current-epoch block below the query
head. The selected result descends from it. The recency guard rules out an
older crossing, and the store clock rules out a future-epoch child. -/
theorem CurrentTargetSelectedEdge.geometry
    {query : FastConfirmationStore Root} {input a c : Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots, ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : input ∈ query.store.block_roots)
    (hslots : ∀ r ∈ query.store.block_roots,
      (query.store.blocks r).slot ≤ get_current_slot cfg query.store)
    (hguard : getLatestSelectorGuard cfg query input)
    (hedge : CurrentTargetSelectedEdge cfg ext query input a c) :
    c ∈ query.store.block_roots ∧
      get_block_epoch cfg query.store c = get_current_store_epoch cfg query.store ∧
      is_ancestor query.store (get_head cfg query.store) (get_node_for_root c) = true ∧
      is_ancestor query.store
        (get_node_for_root (find_latest_confirmed_descendant cfg ext query input))
        (get_node_for_root c) = true := by
  have htrace := findLatestSelectedTrace_parentTrace cfg ext query
    hwf hwalk hhead input hinput
  obtain ⟨_ha, hc, hslot, hdesc⟩ := selectedParentTrace_edge_geometry hwf hwalk htrace
    (List.mem_append.mpr (Or.inr hedge.1))
  have hinputA : get_block_epoch cfg query.store input ≤
      get_block_epoch cfg query.store a := ce_mono cfg hslot
  have hcUpper : get_block_epoch cfg query.store c ≤
      get_current_store_epoch cfg query.store := ce_mono cfg (hslots c hc)
  have hcurrentC : get_current_store_epoch cfg query.store ≤
      get_block_epoch cfg query.store c :=
    hguard.trans ((Nat.add_le_add_right hinputA 1).trans (Nat.succ_le_of_lt hedge.2))
  refine ⟨hc, Nat.le_antisymm hcUpper hcurrentC, ?_, hdesc⟩
  have hprevKnown : ∀ ce acc, acc ∈ query.store.block_roots →
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext query ce
        (get_ancestor_roots query.store (get_head cfg query.store).root acc) acc ∈
        query.store.block_roots := by
    intro ce acc hacc
    rcases prev_epoch_loop_spec cfg ext query ce
        (get_ancestor_roots query.store (get_head cfg query.store).root acc) acc with
      heq | ⟨r, hr, heq, _⟩
    · rwa [heq]
    · rw [heq]
      exact get_ancestor_roots_mem hwf (hwalk acc hacc _ hhead) hr
  have hbelow : ∀ acc, acc ∈ query.store.block_roots →
      (a, c) ∈ (tentativeLoopTrace cfg ext query
        (get_ancestor_roots query.store (get_head cfg query.store).root acc) acc).2 →
      is_ancestor query.store (get_head cfg query.store) (get_node_for_root c) = true := by
    intro acc hacc hmem
    have hcList := tentativeLoopTrace_child_mem cfg ext query _ _ _ _ hmem
    rw [is_ancestor_node_root]
    exact Execution.ancestorRoots_member_below_head hwf hwalk hhead hacc hcList
  have hmem := hedge.1
  simp only [findLatestSelectedTrace] at hmem
  split_ifs at hmem <;> try simp at hmem
  all_goals
    apply hbelow _ ?_ hmem
    first | exact hinput | exact hprevKnown _ _ hinput

namespace Execution

variable (E : Execution Root)

/-- The crossing geometry at a guarded execution call. The only inputs are
the accepted trajectory and its store domain; no helper proviso is used. -/
theorem currentTargetSelectedEdge_geometry_of_accepted
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hguard : getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved)
    {a c : Root}
    (hedge : CurrentTargetSelectedEdge cfg ext (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved a c) :
    c ∈ (E.store cfg ext v (n + 1)).block_roots ∧
      get_block_epoch cfg (E.store cfg ext v (n + 1)) c =
        get_current_store_epoch cfg (E.store cfg ext v (n + 1)) ∧
      is_ancestor (E.store cfg ext v (n + 1))
        (get_head cfg (E.store cfg ext v (n + 1))) (get_node_for_root c) = true ∧
      is_ancestor (E.store cfg ext v (n + 1))
        (get_node_for_root (find_latest_confirmed_descendant cfg ext
          (E.fcrStoreAtCall cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved))
        (get_node_for_root c) = true := by
  have hknown := E.confirmed_known_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hv n (E.withinHorizon_mono cfg (Nat.le_succ n) hH)
  have hinput := E.getLatestConfirmedTraceAt_input_known cfg ext B hT hanchor hboundary hknown
  obtain ⟨hwf, hwalk, _⟩ := E.store_domainK_of_selectedMarginDomain cfg ext
    hT.wellFormed hT.externals_coherence hT.genesis_structure hdomain v hv (n + 1) hH
  have hhead := E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv (n + 1) hH
  obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis_structure
  have hgeometry := hedge.geometry cfg ext
    (by simpa only [E.fcrStep_store] using hwf)
    (by simpa only [E.fcrStep_store] using hwalk)
    (by simpa only [E.fcrStep_store] using hhead) hinput
    (by
      intro r hr
      rw [E.fcrStep_store] at hr ⊢
      exact E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hslot⟩ v (n + 1) r hr) hguard
  simpa only [E.fcrStep_store] using hgeometry

end Execution

end FastConfirmation.Spec

end
