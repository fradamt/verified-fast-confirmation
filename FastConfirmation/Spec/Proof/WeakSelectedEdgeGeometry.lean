module
public import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
public import FastConfirmation.Spec.Proof.WeakSelectorBetween
public import FastConfirmation.Spec.Proof.WeakOneShotSafety

@[expose] public section

/-!
# Spec / Proof / WeakSelectedEdgeGeometry

Margin-discharge wave, Stage J-d: the weak twin of
`SelectedEdgeGeometry.StrictSelectedEdgeGeometry` /
`strictSelectedEdgeGeometry_of_query_minimal`, read at an arbitrary (not
necessarily honest) observer.

`Weak.StrictSelectedEdgeGeometry` is a verbatim clone of the strong record
with

* `result_eq` over `Weak.find_latest_confirmed_descendant`;
* `confirmation` over `Weak.is_one_confirmed`;
* three new endpoint fields `endpoint_block_known` / `endpoint_parent_known`
  / `endpoint_parent_eq`.

The strong record leaves those last three implicit because its consumers
re-derive them from the whole-store inclusion
`(E.store cfg ext u nu).block_roots ⊆ (E.store cfg ext v q).block_roots`
(`hsubUQ` in the strong producer), which is obtained by relaying the honest
past store *into the observer* — `PaperSafetySynchrony.block_relay u hu nu …
v hv q hqH`. That relay direction is exactly what the weak model forbids: the
observer need not be honest, so nothing is ever delivered to it. Here the
endpoint-side block data therefore becomes structure data, supplied by the
producer out of the material every caller already holds at `(w, m)`.

## Substitutions in the producer (design §2-J3)

* `store_domainK_of_selectedMarginDomain … hv q` ↦ `store_parentSlotLt` /
  `store_walkKnownK` (both already proved for an arbitrary node);
* `head_root_known_of_selectedMarginDomain … hv q` ↦ `get_head_root_mem_or`
  + `hW.coherence.justified_root_known` (the `hheadConfirm` idiom of
  `WeakOneShotSafety` §5);
* `find_latest_confirmed_descendant_selected_minimal` ↦
  `find_latest_confirmed_descendant_selected_minimal_weak`; its
  `WeakSelectorGuardEvidence` disjunct is discarded exactly where the strong
  proof discards the certificate, and its strong `is_one_confirmed` component
  is what feeds the two dissemination calls below;
* `find_latest_confirmed_descendant_ge` ↦
  `weak_find_latest_confirmed_descendant_ge`;
* `confirmed_ancestry_at_all_honest_endpoints_minimal` ↦
  `confirmed_ancestry_at_all_honest_endpoints_at_observer`;
* `confirmed_pastDescendant_minimal` ↦ `confirmed_pastDescendant_at_observer`;
* `hsubUQ` + `hagreeUQ` + `chain_descent_restrict` into the query store ↦
  `is_ancestor_transport_closed` / `is_ancestor_replay_closed` at the
  doubly-known witness `d`, plus containment-free
  `WellFormedExecution.blocks_agree`;
* `find_latest_confirmed_descendant_between` ↦
  `Weak.find_latest_confirmed_descendant_between`.

The *endpoint* leg (`hsubUM`, honest `w`) is untouched: `u` and `w` are both
honest, so `block_relay` between them is available, and the three
`chain_descent_restrict` pulls of `c`, `a` and `r0` back into `u`'s store are
verbatim. Only the observer leg is rebuilt. The doubly-known witness `d`
(known at `u`'s own store *and* at the observer's, from
`Execution.confirmed_pastDescendant_at_observer`) drives every observer-side
step:

* `glc` is pushed from the observer's store into `u`'s store
  (`is_ancestor_transport_closed`, with the observer-side ancestry
  `is_ancestor (E.store cfg ext obs q) d glc`), replacing the first
  `chain_descent_restrict`;
* `c` and `a` are pulled back from `u`'s store into the observer's store
  (`is_ancestor_transport_closed` along `d → glc → c` and `d → glc → a`),
  replacing `hsubUQ hcU` / `hsubUQ haU`;
* the two query-side ancestries `glc → c` and `c → r0` come from
  `is_ancestor_replay_closed` at the now doubly-known `glc` and `c`,
  replacing the `is_ancestor_congr`-over-`hagreeUQ` steps;
* `hagreeUQ` itself survives as the containment-free
  `WellFormedExecution.blocks_agree` at roots known to *both* stores, which is
  all the parent-root and child-slot bookkeeping ever needed it for.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-- Query-local, canonical coordinates and geometry for one strict edge of an
actual `Weak.find_latest_confirmed_descendant` result, read at an arbitrary
(not necessarily honest) observer `obs`.

Verbatim clone of `Execution.StrictSelectedEdgeGeometry` with `v := obs`,
`result_eq` over the weak selector and `confirmation` over
`Weak.is_one_confirmed`, plus the three endpoint fields
`endpoint_block_known` / `endpoint_parent_known` / `endpoint_parent_eq`,
which the strong record's consumers re-derive from the observer-relay leg
`hsubUQ` the weak model forbids. As in the strong record, the contents are
only executable selection, block-domain, clock, horizon and epoch-regime
facts: no filter, recording, sibling-score or cross-epoch accounting. -/
structure StrictSelectedEdgeGeometry
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (glc r0 a c : Root) (obs : ValidatorIndex) (q : Nat)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : Nat)
    (lo es sigma querySlot : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext obs q
  result_eq : Weak.find_latest_confirmed_descendant cfg ext query r0 = glc
  confirmation : Weak.is_one_confirmed cfg ext query.store
    (get_current_balance_source query) c = true
  block_known : c ∈ (E.store cfg ext obs q).block_roots
  parent_known : ((E.store cfg ext obs q).blocks c).parent_root ∈
    (E.store cfg ext obs q).block_roots
  parent_eq : ((E.store cfg ext obs q).blocks c).parent_root = a
  endpoint_block_known : c ∈ (E.store cfg ext w m).block_roots
  endpoint_parent_known : ((E.store cfg ext obs q).blocks c).parent_root ∈
    (E.store cfg ext w m).block_roots
  endpoint_parent_eq : ((E.store cfg ext w m).blocks c).parent_root =
    ((E.store cfg ext obs q).blocks c).parent_root
  result_to_child : is_ancestor (E.store cfg ext obs q)
    (get_node_for_root glc) (get_node_for_root c) = true
  child_to_anchor : is_ancestor (E.store cfg ext obs q)
    (get_node_for_root c) (get_node_for_root r0) = true
  parent_slot_lt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks c).parent_root).slot <
    ((E.store cfg ext obs q).blocks c).slot
  child_slot_le_cutoff : ((E.store cfg ext obs q).blocks c).slot ≤ es
  lo_eq : lo = ((E.store cfg ext obs q).blocks
    ((E.store cfg ext obs q).blocks c).parent_root).slot + 1
  cutoff_eq : es = get_current_slot cfg query.store - 1
  query_slot_eq : querySlot = get_current_slot cfg query.store
  sigma_eq : sigma = E.slot_at cfg m - 1
  confirming_cutoff : E.slot_at cfg q = es + 1
  lo_le_cutoff : lo ≤ es
  cutoff_le_sigma : es ≤ sigma
  start_le_cutoff : E.slot_at cfg 0 ≤ es
  sigma_lt_endpoint : sigma < E.slot_at cfg m
  lo_horizon : E.SlotWithinHorizon cfg lo
  cutoff_horizon : E.SlotWithinHorizon cfg es
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  regime : Execution.StrictSelectedEdgeRegime cfg
    (E.store cfg ext obs q) c lo sigma

/-- **Strict edge geometry at a non-honest observer.** Recover a strict
endpoint edge of the actual weakly-selected segment back into the observer's
own store and package its canonical confirmation window, together with the
endpoint-side block data the weak margin classes need.

Weak twin of
`Execution.strictSelectedEdgeGeometry_of_query_minimal`, with
`(v, hv : v ∈ E.honest)` replaced by
`(obs, hW : E.WeakObserverMarginAssumptions cfg ext obs)` and the strong
selector/confirmation predicates replaced by their weak counterparts. The
hypothesis list is otherwise the strong one verbatim; the only edge premise
not implied by ancestry is again `c ≠ r0`, the strict scope used by the chain
walker. -/
theorem strictSelectedEdgeGeometry_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    (q : Nat) (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (r0 : Root) (hr0 : r0 ∈ query.store.block_roots)
    (glc : Root)
    (hresult : Weak.find_latest_confirmed_descendant cfg ext query r0 = glc)
    (hstrict : glc ≠ r0)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : Nat)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hmH : E.WithinHorizon cfg m)
    (a c : Root)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hcR0_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root c) (get_node_for_root r0) = true)
    (hcne : c ≠ r0) :
    ∃ lo es sigma querySlot : Slot,
      Weak.StrictSelectedEdgeGeometry cfg ext E glc r0 a c obs q query w m
        lo es sigma querySlot := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorRoot⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorRoot⟩
  -- the observer's own coherence facts, in place of the strong honesty premise
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  have hjrk : (E.store cfg ext obs q).justified_checkpoint.root ∈
      (E.store cfg ext obs q).block_roots :=
    hW.coherence.justified_root_known q hqH
  have hr0Q : r0 ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [hquery] using hr0
  -- store-domain facts at the observer: honesty-free replacements for
  -- `store_domainK_of_selectedMarginDomain … hv q`
  have hwfQ : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hA.genesis
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hwalkQ := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hA.genesis obs q
  have hheadQ : (get_head cfg (E.store cfg ext obs q)).root ∈
      (E.store cfg ext obs q).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext obs q) with h | h
    · exact h
    · rw [h]
      exact hjrk
  rcases E.find_latest_confirmed_descendant_selected_minimal_weak cfg ext hA
      obs q hqH hjrk query hquery r0 hr0 with
    hsame | ⟨hglcConf0, _hglcWeak0, hglcQ0, hglcParentQ0, _hguard⟩
  · exact False.elim (hstrict (hresult.symm.trans hsame))
  have hglcConf : Spec.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true := by
    rw [hresult] at hglcConf0
    exact hglcConf0
  have hglcQ : glc ∈ (E.store cfg ext obs q).block_roots := by
    rw [hresult] at hglcQ0
    simpa only [hquery] using hglcQ0
  have hglcParentQ : ((E.store cfg ext obs q).blocks glc).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hresult] at hglcParentQ0
    simpa only [hquery] using hglcParentQ0
  have hglcR0_Q : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root glc) (get_node_for_root r0) = true := by
    have hge := (weak_find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hquery] using hwfQ)
      (by simpa only [hquery] using hwalkQ)
      (by simpa only [hquery] using hheadQ) r0 hr0).1
    rw [hresult] at hge
    simpa only [hquery] using hge
  obtain ⟨hr0M, hglcM, _hglcR0M⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hW.validity hcomm query hquery glc r0 hqH hglcQ hglcParentQ hr0Q
        hglcR0_Q hglcConf w hw m hslotQM hmH
  -- the doubly-known past descendant: `d` is known at `u`'s own store *and* at
  -- the observer's, which is what replaces the forbidden observer relay
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hdU, hdQ, hdGlc_Q⟩ :=
    E.confirmed_pastDescendant_at_observer cfg ext hA obs q hW.validity hcomm query hquery
      glc hqH hglcQ hglcParentQ hglcConf
  -- the endpoint leg is unchanged: `u` and `w` are both honest
  have hgateUM : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) :=
    (Nat.succ_le_of_lt hnuq).trans
      (hslotQM.trans (E.slot_at_mono cfg (Nat.le_succ m)))
  have hsubUM : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext w m).block_roots := fun r hr =>
    hA.synchrony.block_relay u hu nu r hnuH hr w hw m hmH hgateUM
  have hagreeUM : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext w m).blocks r :=
    fun r hr => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext w m)
      hr (hsubUM hr)
  -- containment-free stand-in for the strong `hagreeUQ`: block agreement at
  -- roots known to *both* stores needs no relay in either direction
  have hagreeUQ : ∀ r, r ∈ (E.store cfg ext u nu).block_roots →
      r ∈ (E.store cfg ext obs q).block_roots →
      (E.store cfg ext u nu).blocks r = (E.store cfg ext obs q).blocks r :=
    fun r hrU hrQ => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext obs q)
      hrU hrQ
  obtain ⟨hwfU, hwalkU, _hjustU⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain u hu nu hnuH
  have hanchor0U : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgenEq]
    simp [get_forkchoice_store]
  have hanchorU : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0U
  have hanchorBlockSlotU : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hA.wellFormed hgenEq u nu hanchorU]
  have hwalkFromAnchorU : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      WalkKnown (E.store cfg ext u nu) ablk.message.slot r := by
    intro r hr
    have h := hwalkU ablk.root hanchorU r hr
    rwa [hanchorBlockSlotU] at h
  -- `glc` into `u`'s store, by transport at `d` instead of `chain_descent_restrict`
  have hanchorLeGlcQ : ablk.message.slot ≤
      ((E.store cfg ext obs q).blocks glc).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot obs q glc hglcQ
  have hglcU : glc ∈ (E.store cfg ext u nu).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot hanchorLeGlcQ hdQ hdU hglcQ hdGlc_Q
  have hdGlc_U : is_ancestor (E.store cfg ext u nu)
      (get_node_for_root d) (get_node_for_root glc) = true :=
    E.is_ancestor_replay_closed cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot hanchorLeGlcQ hdQ hdU hglcQ hdGlc_Q
  -- the three endpoint pulls, verbatim from the strong proof
  have hanchorLeCM : ablk.message.slot ≤
      ((E.store cfg ext w m).blocks c).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot w m c hcM
  obtain ⟨hcU, hglcC_U⟩ := E.chain_descent_restrict hA.wellFormed
    (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext w m)
    hwfU hwalkFromAnchorU hanchorLeCM hsubUM hglcU hglcU
      (is_ancestor_refl _ _) hglcC_M
  obtain ⟨hwfM, hwalkM, _hjustM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain w hw m hmH
  have hcA_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root c) (get_node_for_root a) = true :=
    is_ancestor_of_parent hwfM hcM haM hparentM
  have hglcA_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root a) = true :=
    is_ancestor_trans (a := get_node_for_root glc) (b := get_node_for_root c)
      (c := get_node_for_root a) hwfM (hwalkM a haM glc hglcM)
      (hwalkM a haM c hcM) hglcC_M hcA_M
  have hanchorLeAM : ablk.message.slot ≤
      ((E.store cfg ext w m).blocks a).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot w m a haM
  obtain ⟨haU, hglcA_U⟩ := E.chain_descent_restrict hA.wellFormed
    (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext w m)
    hwfU hwalkFromAnchorU hanchorLeAM hsubUM hglcU hglcU
      (is_ancestor_refl _ _) hglcA_M
  have hanchorLeR0M : ablk.message.slot ≤
      ((E.store cfg ext w m).blocks r0).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot w m r0 hr0M
  obtain ⟨hr0U, hcR0_U⟩ := E.chain_descent_restrict hA.wellFormed
    (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext w m)
    hwfU hwalkFromAnchorU hanchorLeR0M hsubUM hcU hcU
      (is_ancestor_refl _ _) hcR0_M
  -- back into the observer's store, again by transport/replay at `d` and `glc`
  have hanchorLeCU : ablk.message.slot ≤
      ((E.store cfg ext u nu).blocks c).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot u nu c hcU
  have hanchorLeAU : ablk.message.slot ≤
      ((E.store cfg ext u nu).blocks a).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot u nu a haU
  have hanchorLeR0U : ablk.message.slot ≤
      ((E.store cfg ext u nu).blocks r0).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot u nu r0 hr0U
  have hdC_U : is_ancestor (E.store cfg ext u nu)
      (get_node_for_root d) (get_node_for_root c) = true :=
    is_ancestor_trans (a := get_node_for_root d) (b := get_node_for_root glc)
      (c := get_node_for_root c) hwfU (hwalkU c hcU d hdU)
      (hwalkU c hcU glc hglcU) hdGlc_U hglcC_U
  have hdA_U : is_ancestor (E.store cfg ext u nu)
      (get_node_for_root d) (get_node_for_root a) = true :=
    is_ancestor_trans (a := get_node_for_root d) (b := get_node_for_root glc)
      (c := get_node_for_root a) hwfU (hwalkU a haU d hdU)
      (hwalkU a haU glc hglcU) hdGlc_U hglcA_U
  have hcQ : c ∈ (E.store cfg ext obs q).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot hanchorLeCU hdU hdQ hcU hdC_U
  have haQ : a ∈ (E.store cfg ext obs q).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot hanchorLeAU hdU hdQ haU hdA_U
  have hglcC_Q : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root glc) (get_node_for_root c) = true :=
    E.is_ancestor_replay_closed cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot hanchorLeCU hglcU hglcQ hcU hglcC_U
  have hcR0_Q : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root c) (get_node_for_root r0) = true :=
    E.is_ancestor_replay_closed cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorRoot hanchorLeR0U hcU hcQ hr0U hcR0_U
  have hparentQ : ((E.store cfg ext obs q).blocks c).parent_root = a := by
    have hcUQ := hagreeUQ c hcU hcQ
    have hcUM := hagreeUM c hcU
    rw [← hcUQ, hcUM]
    exact hparentM
  have hparentKnownQ : ((E.store cfg ext obs q).blocks c).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hpstr := Weak.find_latest_confirmed_descendant_between cfg ext query
    (by simpa only [hquery] using hwfQ)
    (by simpa only [hquery] using hwalkQ)
    (by simpa only [hquery] using hheadQ) r0 hr0
  have hcConf : Weak.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) c = true := by
    have hcharge := hpstr.2.2 c (by simpa only [hquery] using hcQ)
      (by simpa only [hquery, hresult] using hglcC_Q)
      (by simpa only [hquery] using hcR0_Q)
    exact hcharge.resolve_left hcne
  have hparentSlotLtQ : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks c).parent_root).slot <
      ((E.store cfg ext obs q).blocks c).slot :=
    hwfQ c hcQ hparentKnownQ
  have hcSlotLeD_U : ((E.store cfg ext u nu).blocks c).slot ≤
      ((E.store cfg ext u nu).blocks d).slot := by
    have h := get_ancestor_slot_le hwfU (hwalkU c hcU d hdU)
    have hroot : (get_ancestor (E.store cfg ext u nu) (get_node_for_root d)
        ((E.store cfg ext u nu).blocks c).slot).root = c := by
      simpa only [is_ancestor_get_node_for_root, decide_eq_true_eq] using hdC_U
    unfold get_node_for_root at hroot
    rw [hroot] at h
    exact h
  have hdSlotLeNu : ((E.store cfg ext u nu).blocks d).slot ≤
      E.slot_at cfg nu := by
    rw [← E.store_current_slot cfg ext u nu]
    exact E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hanchorSlot⟩ u nu d hdU
  have hcSlotLtQ : ((E.store cfg ext obs q).blocks c).slot <
      E.slot_at cfg q := by
    rw [← hagreeUQ c hcU hcQ]
    exact hcSlotLeD_U.trans_lt (hdSlotLeNu.trans_lt hnuq)
  let lo : Slot := ((E.store cfg ext obs q).blocks
    ((E.store cfg ext obs q).blocks c).parent_root).slot + 1
  let es : Slot := get_current_slot cfg query.store - 1
  let sigma : Slot := E.slot_at cfg m - 1
  let querySlot : Slot := get_current_slot cfg query.store
  have hcurrentQ : get_current_slot cfg query.store = E.slot_at cfg q := by
    rw [hquery, E.store_current_slot cfg ext obs q]
  have hqPos : 0 < E.slot_at cfg q := by
    exact lt_of_le_of_lt (Nat.zero_le _) hcSlotLtQ
  have hesEq : es = E.slot_at cfg q - 1 := by
    simp only [es, hcurrentQ]
  have hcutoff : E.slot_at cfg q = es + 1 := by
    rw [hesEq]
    exact (Nat.sub_one_add_one (Nat.ne_of_gt hqPos)).symm
  have hcSlotLeEs : ((E.store cfg ext obs q).blocks c).slot ≤ es := by
    rw [hesEq]
    exact Nat.le_sub_one_of_lt hcSlotLtQ
  have hloLeEs : lo ≤ es := by
    simp only [lo]
    exact (Nat.succ_le_of_lt hparentSlotLtQ).trans hcSlotLeEs
  have hstartLeEs : E.slot_at cfg 0 ≤ es := by
    have hstartNu : E.slot_at cfg 0 ≤ E.slot_at cfg nu :=
      E.slot_at_mono cfg (Nat.zero_le nu)
    rw [hesEq]
    exact Nat.le_sub_one_of_lt (hstartNu.trans_lt hnuq)
  have hesLeSigma : es ≤ sigma := by
    simp only [es, sigma, hcurrentQ]
    exact Nat.sub_le_sub_right hslotQM 1
  have hmPos : 0 < E.slot_at cfg m := hqPos.trans_le hslotQM
  have hsigmaLt : sigma < E.slot_at cfg m := by
    simp only [sigma]
    exact Nat.sub_lt hmPos Nat.one_pos
  have hloLeM : lo ≤ E.slot_at cfg m :=
    hloLeEs.trans (hesLeSigma.trans (Nat.sub_le _ _))
  have hesLeM : es ≤ E.slot_at cfg m :=
    hesLeSigma.trans (Nat.sub_le _ _)
  have hsigmaLeM : sigma ≤ E.slot_at cfg m := Nat.sub_le _ _
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_of_le cfg hloLeM hmH
  have hesH : E.SlotWithinHorizon cfg es :=
    E.slotWithinHorizon_of_le cfg hesLeM hmH
  have hsigmaH : E.SlotWithinHorizon cfg sigma :=
    E.slotWithinHorizon_of_le cfg hsigmaLeM hmH
  have hregime : Execution.StrictSelectedEdgeRegime cfg
      (E.store cfg ext obs q) c lo sigma := by
    by_cases hsame : compute_epoch_at_slot cfg lo =
        compute_epoch_at_slot cfg sigma
    · exact .sameEpoch hsame
    · have hparentChildEpoch : get_block_epoch cfg (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks c).parent_root ≤
          get_block_epoch cfg (E.store cfg ext obs q) c := by
        simp only [get_block_epoch]
        exact Nat.div_le_div_right (Nat.le_of_lt hparentSlotLtQ)
      rcases lt_or_eq_of_le hparentChildEpoch with hcross | hedge
      · exact .crossing hcross
      · apply Execution.StrictSelectedEdgeRegime.futureCrossing hedge.symm
        have hloChild : lo ≤ ((E.store cfg ext obs q).blocks c).slot := by
          simp only [lo]
          exact Nat.succ_le_of_lt hparentSlotLtQ
        have heLoChild : compute_epoch_at_slot cfg lo ≤
            compute_epoch_at_slot cfg ((E.store cfg ext obs q).blocks c).slot :=
          Nat.div_le_div_right hloChild
        have heChildLo : compute_epoch_at_slot cfg
            ((E.store cfg ext obs q).blocks c).slot ≤
            compute_epoch_at_slot cfg lo := by
          have hpLo : ((E.store cfg ext obs q).blocks
              ((E.store cfg ext obs q).blocks c).parent_root).slot ≤ lo := by
            simp only [lo]
            exact Nat.le_succ _
          have hepLo : compute_epoch_at_slot cfg
              ((E.store cfg ext obs q).blocks
                ((E.store cfg ext obs q).blocks c).parent_root).slot ≤
              compute_epoch_at_slot cfg lo :=
            Nat.div_le_div_right hpLo
          simpa only [get_block_epoch] using hedge.symm.trans_le hepLo
        have heChildEqLo := le_antisymm heChildLo heLoChild
        have hloSigma : lo ≤ sigma := hloLeEs.trans hesLeSigma
        have hwindowLe : compute_epoch_at_slot cfg lo ≤
            compute_epoch_at_slot cfg sigma := Nat.div_le_div_right hloSigma
        have hwindowLt : compute_epoch_at_slot cfg lo <
            compute_epoch_at_slot cfg sigma := lt_of_le_of_ne hwindowLe hsame
        rwa [heChildEqLo]
  exact ⟨lo, es, sigma, querySlot,
    { query_store_eq := hquery
      result_eq := hresult
      confirmation := hcConf
      block_known := hcQ
      parent_known := hparentKnownQ
      parent_eq := hparentQ
      endpoint_block_known := hcM
      endpoint_parent_known := by rw [hparentQ]; exact haM
      endpoint_parent_eq := by rw [hparentM]; exact hparentQ.symm
      result_to_child := hglcC_Q
      child_to_anchor := hcR0_Q
      parent_slot_lt := hparentSlotLtQ
      child_slot_le_cutoff := hcSlotLeEs
      lo_eq := rfl
      cutoff_eq := rfl
      query_slot_eq := rfl
      sigma_eq := rfl
      confirming_cutoff := hcutoff
      lo_le_cutoff := hloLeEs
      cutoff_le_sigma := hesLeSigma
      start_le_cutoff := hstartLeEs
      sigma_lt_endpoint := hsigmaLt
      lo_horizon := hloH
      cutoff_horizon := hesH
      sigma_horizon := hsigmaH
      regime := hregime }⟩

end Weak

end FastConfirmation.Spec

end
