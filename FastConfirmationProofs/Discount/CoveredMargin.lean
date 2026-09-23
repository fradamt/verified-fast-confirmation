module
public import FastConfirmationProofs.Discount.ArbitraryQueryMargin

@[expose] public section

/-!
# Justified coverage or a selected margin

Shows that covered selected roots retain enough score to dominate competing heads.

This module contains `covered_roots_isSome_of_ancestor`, `covered_hcase_of_ancestor`, `head_ge_of_covered_or_descend_chain` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
private theorem covered_roots_isSome_of_ancestor {store : Store Root}
    (hwf : ParentSlotLt store)
    {t r : Root} (hw : WalkKnown store (store.blocks t).slot r) :
    (get_ancestor store (ForkChoiceNode.mk r .pending) (store.blocks t).slot).root = t →
    ∀ fuel : ℕ, (store.blocks r).slot < fuel →
      (get_ancestor_roots_aux store t fuel r).isSome = true ∨ r = t := by
  induction hw with
  | stop _hr hle =>
      intro hanc _fuel _hbound
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
              Nat.lt_of_lt_of_le (hwf r hr hp.root_mem)
                (Nat.lt_succ_iff.mp hfuel)
            rcases ih hanc f hbound with hsome | hpeq
            · left
              obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hsome
              rw [hl]
              rfl
            · exact absurd hpeq hD

omit [Inhabited Root] in
private theorem covered_hcase_of_ancestor {store : Store Root}
    (hwf : ParentSlotLt store)
    {b terminal : Root}
    (hwalk : WalkKnown store (store.blocks terminal).slot b)
    (hanc : is_ancestor store (ForkChoiceNode.mk b .pending)
      (ForkChoiceNode.mk terminal .pending) = true) :
    get_ancestor_roots store b terminal ≠ [] ∨ b = terminal := by
  simp only [is_ancestor_pending, decide_eq_true_eq] at hanc
  rcases covered_roots_isSome_of_ancestor hwf hwalk hanc
      ((store.blocks b).slot + 1) (Nat.lt_succ_self _) with hsome | heq
  · left
    rw [get_ancestor_roots]
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hsome
    rw [hl]
    change l ≠ []
    exact (get_ancestor_roots_aux_chain hwf hwalk _
      (Nat.lt_succ_self _) l hl).1
  · exact Or.inr heq

/-- Fold a parent-linked chain when every edge is either already below the
justified checkpoint or is the fork-choice-dominant filtered child. -/
theorem head_ge_of_covered_or_descend_chain {store : Store Root}
    (hwf : ParentSlotLt store)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {b : Root} (hb : b ∈ store.block_roots) :
    ∀ (ds : List Root) (a : Root),
      (∀ r ∈ a :: ds, r ∈ store.block_roots) →
      List.IsChain (fun x y => (store.blocks y).parent_root = x) (a :: ds) →
      List.IsChain (fun _x y =>
        is_ancestor store
            (get_node_for_root store.justified_checkpoint.root)
            (get_node_for_root y) = true ∨
          DescendStep cfg store (get_filtered_block_tree cfg store) _x y)
        (a :: ds) →
      (a :: ds).getLast (List.cons_ne_nil a ds) = b →
      is_ancestor store (get_head cfg store) (get_node_for_root a) = true →
      is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  intro ds
  induction ds with
  | nil =>
      intro a _hmem _hparent _hsteps hlast hhead
      have hab : a = b := hlast
      simpa only [hab] using hhead
  | cons c rest ih =>
      intro a hmem hparent hsteps hlast hheadA
      rw [List.isChain_cons_cons] at hparent hsteps
      obtain ⟨hparentAC, hparentTail⟩ := hparent
      obtain ⟨hcoveredOrStep, hstepsTail⟩ := hsteps
      have ha : a ∈ store.block_roots := hmem a (by simp)
      have hc : c ∈ store.block_roots := hmem c (by simp)
      have hheadC : is_ancestor store (get_head cfg store)
          (get_node_for_root c) = true := by
        by_cases hcovered : is_ancestor store
            (get_node_for_root store.justified_checkpoint.root)
            (get_node_for_root c) = true
        · exact head_ge_of_justified_ge_K cfg hwf hwalk hjust hc hcovered
        · have hstep : DescendStep cfg store
              (get_filtered_block_tree cfg store) a c := by
            rcases hcoveredOrStep with hcov | hstep
            · exact False.elim (hcovered hcov)
            · exact hstep
          have hcFiltered : c ∈ get_filtered_block_tree cfg store :=
            hstep.child_mem
          have hcJ : is_ancestor store (get_node_for_root c)
              (get_node_for_root store.justified_checkpoint.root) = true :=
            filtered_through_justified_K cfg hwf hwalk hjust hcFiltered
          have hcA : is_ancestor store (get_node_for_root c)
              (get_node_for_root a) = true :=
            is_ancestor_of_parent hwf hc ha hparentAC
          have hcJ' : (get_ancestor store (ForkChoiceNode.mk c .pending)
              (store.blocks store.justified_checkpoint.root).slot).root =
                store.justified_checkpoint.root := by
            simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hcJ
          have hcA' : (get_ancestor store (ForkChoiceNode.mk c .pending)
              (store.blocks a).slot).root = a := by
            simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hcA
          have haJ : is_ancestor store (get_node_for_root a)
              (get_node_for_root store.justified_checkpoint.root) = true := by
            rcases reroot_comparable hwf
                (hwalk a ha c hc)
                (hwalk store.justified_checkpoint.root hjust c hc)
                hcA' hcJ' with hJA | hAJ
            · rcases reroot_child_squeeze hwf hwalk hjust ha hc hparentAC
                  hJA hcJ' with hEqA | hEqC
              · simpa only [hEqA] using
                  (is_ancestor_refl store (get_node_for_root a))
              · have hcov : is_ancestor store
                    (get_node_for_root store.justified_checkpoint.root)
                    (get_node_for_root c) = true := by
                  simpa only [hEqC] using
                    (is_ancestor_refl store
                      (get_node_for_root store.justified_checkpoint.root))
                exact False.elim (hcovered hcov)
            · simpa only [get_node_for_root, is_ancestor_pending,
                  decide_eq_true_eq] using hAJ
          have hdesc : DescendsTo cfg store
              (get_filtered_block_tree cfg store) c 1 a :=
            hstep.descendsTo (DescendsTo.here hc)
          exact head_ge_of_intermediate_chain cfg hwf hsub hwalk hjust ha haJ
            hheadA hdesc
      have hmemTail : ∀ r ∈ c :: rest, r ∈ store.block_roots := by
        intro r hr
        exact hmem r (List.mem_cons_of_mem a hr)
      have hlastTail : (c :: rest).getLast (List.cons_ne_nil c rest) = b :=
        (List.getLast_cons (List.cons_ne_nil c rest)).symm.trans hlast
      exact ih c hmemTail hparentTail hstepsTail hlastTail hheadC

namespace Execution

variable (E : Execution Root)

/-- Per-endpoint chain supply which stops charging LMD margins once the
endpoint's realized justified root already covers the edge child. -/
def CoveredDescendStepChainSupply
    (b r₀ : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root,
      a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root c) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root c) = true ∨
        DescendStep cfg (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m)) a c

/-- Arbitrary-query selected margins with the endpoint justified-coverage
escape made explicit.  A strict selected edge which is already below the
endpoint's realized justified root needs no filtered-tree margin. -/
def SelectedCoveredMarginSupplyAt
    (glc r₀ : Root) (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.slot_at cfg q ≤ E.slot_at cfg m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) →
    ∀ a c : Root,
      a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root glc) (get_node_for_root c) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root c) = true ∨
        E.SelectedEdgeMarginInputsAt cfg ext glc a c v q query w m

/-- Coverage-aware counterpart of `head_ge_of_safe_scoped_terminal`. -/
theorem head_ge_of_safe_covered_terminal
    {store : Store Root}
    (hwf : ParentSlotLt store)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {r₀ b : Root} (hr₀ : r₀ ∈ store.block_roots) (hb : b ∈ store.block_roots)
    (hheadR₀ : is_ancestor store (get_head cfg store)
      (get_node_for_root r₀) = true)
    (hbR₀ : is_ancestor store (get_node_for_root b)
      (get_node_for_root r₀) = true)
    (hedge : ∀ a c : Root,
      a ∈ store.block_roots → c ∈ store.block_roots →
      (store.blocks c).parent_root = a →
      is_ancestor store (get_node_for_root b) (get_node_for_root c) = true →
      is_ancestor store (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
      is_ancestor store
          (get_node_for_root store.justified_checkpoint.root)
          (get_node_for_root c) = true ∨
        DescendStep cfg store (get_filtered_block_tree cfg store) a c) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  have hbR₀' : is_ancestor store (ForkChoiceNode.mk b .pending)
      (ForkChoiceNode.mk r₀ .pending) = true := by
    simpa only [get_node_for_root] using hbR₀
  have hcase := covered_hcase_of_ancestor hwf (hwalk r₀ hr₀ b hb) hbR₀'
  obtain ⟨hmem, hparent, hlast⟩ := parentChain_at hwf hwalk hr₀ hb hcase
  have hlast? : (r₀ :: get_ancestor_roots store b r₀).getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast]
  have hsteps : List.IsChain (fun a c =>
      is_ancestor store
          (get_node_for_root store.justified_checkpoint.root)
          (get_node_for_root c) = true ∨
        DescendStep cfg store (get_filtered_block_tree cfg store) a c)
      (r₀ :: get_ancestor_roots store b r₀) := by
    refine isChain_imp_of_mem hparent ?_
    intro a ha c hc hlink
    have hbC := Execution.mem_isAncestor_of_parentChain hwf hwalk hb
      hparent hmem hlast? c hc
    have hcR₀ : is_ancestor store (get_node_for_root c)
        (get_node_for_root r₀) = true := by
      rcases List.mem_cons.mp hc with rfl | hcTail
      · exact is_ancestor_refl store _
      · exact get_ancestor_roots_descends hwf hwalk hr₀ hb hcTail
    have hslotLt := parentChain_edge_child_slot_gt_head hwf hmem hparent
      ha hc hlink
    have hcNe : c ≠ r₀ := by
      intro heq
      subst c
      exact (lt_irrefl _) hslotLt
    exact hedge a c (hmem a ha) (hmem c hc) hlink hbC hcR₀ hcNe
  exact head_ge_of_covered_or_descend_chain cfg hwf hsub hwalk hjust hb
    _ r₀ hmem hparent hsteps hlast hheadR₀

/-- Turn the coverage-aware selected-margin functional into the exact chain
functional consumed by the covered fold. -/
theorem coveredDescendStepChainSupply_of_selectedMarginsAt_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {glc r₀ : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q) (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext v q)
    (hglc : glc ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks glc).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true)
    (hsupply : E.SelectedCoveredMarginSupplyAt cfg ext glc r₀ v q query) :
    E.CoveredDescendStepChainSupply cfg ext glc r₀
      (E.slot_start cfg (E.slot_at cfg q)) := by
  obtain ⟨_hsq, _hsH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  intro w hw m hm hHm hIH a c ha hc hlink hscope hscopeR₀ hcne
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← hslotStart]
    exact E.slot_at_mono cfg hm
  have hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hm' hHm'
    have hslotQM' : E.slot_at cfg q ≤ E.slot_at cfg m' := by
      rw [← hslotStart]
      exact E.slot_at_mono cfg hm'
    exact E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hstore glc hqH hglc hparent hconf
      w' hw' m' hslotQM' hHm'
  rcases hsupply w hw m hslotQM hHm hIH
      a c ha hc hlink hscope hscopeR₀ hcne with hcovered | hmargin
  · exact Or.inl hcovered
  · right
    rcases hmargin with
      ⟨lo, es, σ, hsame⟩ | ⟨es, σ, querySlot, hcross⟩ |
        ⟨es, σ, querySlot, hfuture⟩ | ⟨lo, es, hdirect⟩
    · exact E.sameEpoch_descendStep_of_selectedInputsAt_minimal cfg ext hA
        hw hHm hc hscope hglcKnown hIH hsame
    · exact E.crossingEdge_descendStep_of_selectedInputs_minimal cfg ext hA
        hv hqH hw hHm hcross
    · exact E.futureCrossing_descendStep_of_selectedInputs_minimal cfg ext hA
        hv hqH hw hHm hfuture
    · exact E.directWindow_descendStep_of_selectedInputsAt_minimal cfg ext hdirect

/-- Coverage-aware arbitrary-call bridge at the query slot boundary. -/
theorem safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext v q)
    (lcr : Root) (hlcr : lcr ∈ query.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr
      (E.slot_start cfg (E.slot_at cfg q)))
    (hchain :
      find_latest_confirmed_descendant cfg ext query lcr ≠ lcr →
        E.CoveredDescendStepChainSupply cfg ext
          (find_latest_confirmed_descendant cfg ext query lcr) lcr
          (E.slot_start cfg (E.slot_at cfg q))) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query lcr)
      (E.slot_start cfg (E.slot_at cfg q)) := by
  by_cases hsame : find_latest_confirmed_descendant cfg ext query lcr = lcr
  · rw [hsame]
    exact hbase
  rcases E.find_latest_confirmed_descendant_selected_minimal cfg ext hA
      v hv q hqH query hstore lcr hlcr with
    heq | ⟨hconf, hbSelected, hpSelected⟩
  · exact absurd heq hsame
  have hbConfirm : find_latest_confirmed_descendant cfg ext query lcr ∈
      (E.store cfg ext v q).block_roots := by
    simpa only [hstore] using hbSelected
  have hpConfirm : ((E.store cfg ext v q).blocks
        (find_latest_confirmed_descendant cfg ext query lcr)).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    simpa only [hstore] using hpSelected
  have hlcrConfirm : lcr ∈ (E.store cfg ext v q).block_roots := by
    simpa only [hstore] using hlcr
  have hsupply := hchain hsame
  obtain ⟨_hsq, _hsH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  refine E.safeFrom_of_headStep_at cfg ext ?_
  intro w hw m hm hHm hIH
  obtain ⟨hwfConfirm, hwalkConfirm, _hjcConfirm⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  have hheadConfirm : (get_head cfg (E.store cfg ext v q)).root ∈
      (E.store cfg ext v q).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  have hbgeConfirm : is_ancestor (E.store cfg ext v q)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query lcr))
      (get_node_for_root lcr) = true := by
    have hge := (find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hstore] using hwfConfirm)
      (by simpa only [hstore] using hwalkConfirm)
      (by simpa only [hstore] using hheadConfirm) lcr hlcr).1
    simpa only [hstore] using hge
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← hslotStart]
    exact E.slot_at_mono cfg hm
  obtain ⟨hlcrEndpoint, hbEndpoint, hbgeEndpoint⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hstore _ lcr hqH hbConfirm hpConfirm hlcrConfirm
        hbgeConfirm hconf w hw m hslotQM hHm
  have hheadLcr : is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m)) (get_node_for_root lcr) = true :=
    hbase w hw m hm hHm
  obtain ⟨hwfEndpoint, hwalkEndpoint, hjcEndpoint⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  exact head_ge_of_safe_covered_terminal cfg hwfEndpoint
    (filtered_subset_block_roots cfg (E.store cfg ext w m) hjcEndpoint)
    hwalkEndpoint hjcEndpoint hlcrEndpoint hbEndpoint hheadLcr hbgeEndpoint
    (fun a c ha hc hlink hbc hclcr hcne =>
      hsupply w hw m hm hHm hIH a c ha hc hlink hbc hclcr hcne)

/-- Final coverage-aware arbitrary-query bridge.  Safety is first established
at the query slot boundary and then restricted forward to the actual query
second. -/
theorem safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext v q)
    (lcr : Root) (hlcr : lcr ∈ query.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr
      (E.slot_start cfg (E.slot_at cfg q)))
    (hmargin :
      find_latest_confirmed_descendant cfg ext query lcr ≠ lcr →
        E.SelectedCoveredMarginSupplyAt cfg ext
          (find_latest_confirmed_descendant cfg ext query lcr)
          lcr v q query) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query lcr) q := by
  have hslotSafety : E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query lcr)
      (E.slot_start cfg (E.slot_at cfg q)) :=
    E.safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_minimal
      cfg ext hA v hv q hqH query hstore lcr hlcr hbase (by
        intro hne
        rcases E.find_latest_confirmed_descendant_selected_minimal cfg ext hA
            v hv q hqH query hstore lcr hlcr with
          heq | ⟨hconf, hb, hp⟩
        · exact absurd heq hne
        · have hb' : find_latest_confirmed_descendant cfg ext query lcr ∈
              (E.store cfg ext v q).block_roots := by
            simpa only [hstore] using hb
          have hp' : ((E.store cfg ext v q).blocks
                (find_latest_confirmed_descendant cfg ext query lcr)).parent_root ∈
              (E.store cfg ext v q).block_roots := by
            simpa only [hstore] using hp
          exact E.coveredDescendStepChainSupply_of_selectedMarginsAt_minimal
            cfg ext hA hv hqH query hstore hb' hp' hconf (hmargin hne))
  obtain ⟨hstart, _hstartH, _hslot, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  exact hslotSafety.mono cfg ext E hstart

end Execution

end FastConfirmation.Spec

end
