module
public import FastConfirmation.Spec.Proof.SameSlotLMD

@[expose] public section

/-!
# Arbitrary-query selected margins

An allowed confirmation query need not occur at the first second of its slot.
The executable query is therefore kept explicit as `(q, query)`, while the
head-safety induction for a newly selected result starts at
`slot_start (slot_at q)`.  Confirmation provenance transports the selected
chain backwards in execution index to that slot boundary, but never backwards
in slot order.

The public `DescendStepChainSupply` and `SafeFrom` predicates remain ordered by
execution index.  This file instantiates them at the slot-start index and only
then restricts the resulting safety fact forward to the actual query index.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Slot-start voter range -/

/-- Any second whose slot is not before the query slot occurs at or after that
slot's first second. -/
theorem query_slot_start_le_of_slot_ge_minimal
    (hA : SelectedMarginAssumptions cfg ext E) {q ni : ℕ}
    (hge : E.slot_at cfg q ≤ E.slot_at cfg ni) :
    E.slot_start cfg (E.slot_at cfg q) ≤ ni := by
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hA.genesis
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hroot
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time :=
    hgws.time_ge_genesis
  apply Nat.le_of_not_gt
  intro hlt
  have hslotlt : E.slot_at cfg ni < E.slot_at cfg q :=
    (E.slot_at_lt_iff cfg hA.whole_seconds hgenTime).2 hlt
  exact (Nat.not_lt_of_ge hge) hslotlt

/-! ## Fresh-voter growth from an arbitrary query slot -/

/-- Fresh voters in the query slot or a later slot lie in the induction range
starting at `slot_start (slot_at q)`.  This is the arbitrary-query analogue of
`freshEngineInputs_of_IH_minimal`; it does not pretend that current-slot voters
occur at or after the later query index `q`. -/
theorem freshEngineInputs_of_slotStart_IH_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q m : ℕ} {glc c : Root}
    {lo es σ σ' : Slot}
    (hq : E.slot_at cfg q = es + 1)
    (hes : es ≤ σ') (hσ' : σ' + 1 ≤ σ) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    E.FreshEngineInputs cfg ext w m c lo σ' := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  intro i hi nᵢ hslotᵢ
  have hiHonest : i ∈ E.honest := (Finset.mem_filter.mp hi).2
  have hquery_le_i : E.slot_at cfg q ≤ E.slot_at cfg nᵢ := by
    rw [hq, hslotᵢ]
    exact Nat.add_le_add_right hes 1
  have hniLower : E.slot_start cfg (E.slot_at cfg q) ≤ nᵢ :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hquery_le_i
  have hniSlotLt : E.slot_at cfg nᵢ < E.slot_at cfg m := by
    rw [hslotᵢ]
    exact lt_of_le_of_lt hσ' hσm
  have hniLt : nᵢ < m := by
    apply Nat.lt_of_not_ge
    intro hmni
    exact (Nat.not_le_of_gt hniSlotLt) (E.slot_at_mono cfg hmni)
  have hHni : E.WithinHorizon cfg nᵢ :=
    E.withinHorizon_mono cfg (Nat.le_of_lt hniLt) hHm
  have hheadGlc : is_ancestor (E.store cfg ext i nᵢ)
      (get_head cfg (E.store cfg ext i nᵢ)) (get_node_for_root glc) = true :=
    hIH i hiHonest nᵢ hniLower hniSlotLt hHni
  have hglcᵢ : glc ∈ (E.store cfg ext i nᵢ).block_roots :=
    hglcKnown i hiHonest nᵢ hniLower hHni
  have hgate : E.slot_at cfg nᵢ + 1 ≤ E.slot_at cfg (m + 1) :=
    le_trans (Nat.succ_le_of_lt hniSlotLt)
      (E.slot_at_mono cfg (Nat.le_succ m))
  have hsub : (E.store cfg ext i nᵢ).block_roots ⊆
      (E.store cfg ext w m).block_roots :=
    E.blockRoots_subset_of_relay cfg ext hA.synchrony
      hiHonest hw hHni hHm hgate
  obtain ⟨hparentᵢ, hwalkK, _hjust⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain i hiHonest nᵢ hHni
  have hhead : (get_head cfg (E.store cfg ext i nᵢ)).root ∈
      (E.store cfg ext i nᵢ).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hiHonest nᵢ hHni
  have hanchor0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext i nᵢ).block_roots :=
    (E.store_storeLE cfg ext i (Nat.zero_le nᵢ)).1 hanchor0
  have hanchorSlot : ((E.store cfg ext i nᵢ).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hA.wellFormed hgeq i nᵢ hanchor]
  have hwalkA : ∀ r ∈ (E.store cfg ext i nᵢ).block_roots,
      WalkKnown (E.store cfg ext i nᵢ) ablk.message.slot r := by
    intro r hr
    have hwalk := hwalkK ablk.root hanchor r hr
    rwa [hanchorSlot] at hwalk
  have hanchorLeC : ablk.message.slot ≤
      ((E.store cfg ext w m).blocks c).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparent w m c hc
  have hheadGlc' : is_ancestor (E.store cfg ext i nᵢ)
      (get_node_for_root (get_head cfg (E.store cfg ext i nᵢ)).root)
      (get_node_for_root glc) = true :=
    (congrArg (· = true) (is_ancestor_pending_root_eq (E.store cfg ext i nᵢ)
      (get_head cfg (E.store cfg ext i nᵢ)).root glc .pending
      (get_head cfg (E.store cfg ext i nᵢ)).payload_status)).mpr hheadGlc
  obtain ⟨hcᵢ, hheadC⟩ := E.chain_descent_restrict hA.wellFormed
    (E.blockProvenance cfg ext i nᵢ) (E.blockProvenance cfg ext w m)
    hparentᵢ hwalkA hanchorLeC hsub hhead hglcᵢ hheadGlc' hchain
  have hheadC' : is_ancestor (E.store cfg ext i nᵢ)
      (get_head cfg (E.store cfg ext i nᵢ)) (get_node_for_root c) = true :=
    (congrArg (· = true) (is_ancestor_pending_root_eq (E.store cfg ext i nᵢ)
      (get_head cfg (E.store cfg ext i nᵢ)).root c .pending
      (get_head cfg (E.store cfg ext i nᵢ)).payload_status)).mp hheadC
  exact ⟨hheadC', hsub, hcᵢ, hwalkK c hcᵢ _ hhead⟩

theorem hgrowS_of_slotStart_IH_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q m : ℕ} {glc c : Root}
    {lo es σ : Slot}
    (hq : E.slot_at cfg q = es + 1)
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hs0 : E.slot_at cfg 0 ≤ es) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    E.Sval cfg ext w m c lo es + (E.Jspec lo σ - E.Jspec lo es) ≤
      E.Sval cfg ext w m c lo σ := by
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hσm) hHm
  refine E.hgrowS_of_engine cfg ext hA.honest_behavior
    hA.externals_coherence hA.wellFormed w m c lo hlo hbase hσH hs0 hsame
      (fun σ' hlow hhigh => ?_)
  exact E.freshEngineInputs_of_slotStart_IH_minimal cfg ext hA hw hq
    hlow (Nat.succ_le_of_lt hhigh) hσm hHm hc hchain hglcKnown hIH

theorem hgrowX_of_slotStart_IH_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q m : ℕ} {glc c : Root}
    {lo es σ : Slot}
    (hq : E.slot_at cfg q = es + 1)
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hs0 : E.slot_at cfg 0 ≤ es) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    E.Xval cfg ext w m c lo σ ≤ E.Xval cfg ext w m c lo es := by
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hσm) hHm
  refine E.hgrowX_of_engine cfg ext hA.honest_behavior
    hA.externals_coherence hA.wellFormed w m c lo hlo hbase hσH hs0 hsame
      (fun σ' hlow hhigh => ?_)
  exact E.freshEngineInputs_of_slotStart_IH_minimal cfg ext hA hw hq
    hlow (Nat.succ_le_of_lt hhigh) hσm hHm hc hchain hglcKnown hIH

/-! ## Explicit arbitrary-query margin interface -/

/-! ### Store-indexed query ledger

The historical ledger accessors are indexed by `(v,q)` and therefore read
`E.store cfg ext v q`.  An action-prefix query must instead classify votes
against the exact store it evaluated.  These accessors are the minimal
store-indexed view needed by the confirmation base and its direct-window
transport; endpoint classes remain the existing execution-store classes.
-/

/-- Newest-through-`σ` support for `b` measured in an explicit store. -/
def StoreSupportsDesc (store : Store Root) (b : Root) (σ : Slot)
    (i : ValidatorIndex) : Prop :=
  ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t ≤ σ ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' ≤ σ → E.vote i t' = none) ∧
    is_ancestor store (get_node_for_root a.data.beacon_block_root)
      (get_node_for_root b) = true

/-- Voteless-or-ancestor classification measured in an explicit store. -/
def StoreAncestorOrVoteless (store : Store Root) (b : Root) (σ : Slot)
    (i : ValidatorIndex) : Prop :=
  (∀ t' : Slot, t' ≤ σ → E.vote i t' = none) ∨
  (∃ (t : Slot) (k : ℕ) (a : Attestation Root),
    t ≤ σ ∧ E.vote i t = some (k, a) ∧
    (∀ t' : Slot, t < t' → t' ≤ σ → E.vote i t' = none) ∧
    is_ancestor store (get_node_for_root b)
      (get_node_for_root a.data.beacon_block_root) = true)

open Classical in
/-- Honest supporting class in the exact query store. -/
noncomputable def StoreSclass (store : Store Root) (b : Root)
    (lo σ : Slot) : Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => E.StoreSupportsDesc store b σ i)

open Classical in
/-- Honest ancestor/voteless class in the exact query store. -/
noncomputable def StoreAclass (store : Store Root) (b : Root)
    (lo σ : Slot) : Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => ¬ E.StoreSupportsDesc store b σ i ∧
      E.StoreAncestorOrVoteless store b σ i)

open Classical in
/-- Remaining honest class in the exact query store. -/
noncomputable def StoreXclass (store : Store Root) (b : Root)
    (lo σ : Slot) : Finset ValidatorIndex :=
  ((E.span_committee lo σ).filter (fun i => i ∈ E.honest)).filter
    (fun i => ¬ E.StoreSupportsDesc store b σ i ∧
      ¬ E.StoreAncestorOrVoteless store b σ i)

/-- Weight of the store-indexed supporting class. -/
noncomputable def StoreSval (store : Store Root) (b : Root)
    (lo σ : Slot) : Gwei :=
  E.weight (E.StoreSclass store b lo σ)

/-- Weight of the store-indexed ancestor/voteless class. -/
noncomputable def StoreAval (store : Store Root) (b : Root)
    (lo σ : Slot) : Gwei :=
  E.weight (E.StoreAclass store b lo σ)

/-- Weight of the store-indexed remaining class. -/
noncomputable def StoreXval (store : Store Root) (b : Root)
    (lo σ : Slot) : Gwei :=
  E.weight (E.StoreXclass store b lo σ)

omit [Inhabited Root] in
/-- The store-indexed classes retain the honest-window partition. -/
theorem store_weight_partition (store : Store Root) (b : Root)
    (lo σ : Slot) :
    E.Jspec lo σ = E.StoreSval store b lo σ
      + E.StoreAval store b lo σ
      + E.StoreXval store b lo σ := by
  classical
  rw [StoreSval, StoreAval, StoreXval, StoreSclass, StoreAclass,
    StoreXclass, Execution.Jspec]
  exact E.weight_three_split
    ((E.span_committee lo σ).filter (fun i => i ∈ E.honest))
    (fun i => E.StoreSupportsDesc store b σ i)
    (fun i => E.StoreAncestorOrVoteless store b σ i)

/-- Honest-class transport from the exact query store to an execution
endpoint.  This is the store-explicit counterpart of
`classes_base_transport_honest`. -/
theorem store_classes_base_transport_honest
    (queryStore : Store Root) (w : ValidatorIndex) (m : ℕ)
    (b : Root) (lo es : Slot)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.StoreSupportsDesc queryStore b es i →
        E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.StoreAncestorOrVoteless queryStore b es i →
        E.AncestorOrVoteless cfg ext w m b es i) :
    E.StoreSval queryStore b lo es ≤
        E.Sval cfg ext w m b lo es ∧
      E.Xval cfg ext w m b lo es ≤
        E.StoreXval queryStore b lo es := by
  classical
  constructor
  · apply E.weight_mono
    intro i hi
    simp only [StoreSclass, Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  · apply E.weight_mono
    intro i hi
    simp only [StoreXclass, Execution.Xclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1,
      fun hS => hi.2.1 (hSt i hi.1.2 hi.1.1 hS),
      fun hA => hi.2.2 (hAt i hi.1.2 hi.1.1 hA)⟩

/-- Same-epoch selected-edge inputs at a real query `(q, query)`.  The query
index is used for the confirmation base; the induction lower bound is the
query slot's first second and is supplied separately by the chain functional. -/
structure SameEpochSelectedMarginInputsAt
    (glc a c : Root) (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) (lo es σ : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext v q
  confirming_cutoff : E.slot_at cfg q = es + 1
  lo_le_es : lo ≤ es
  es_le_σ : es ≤ σ
  start_le_es : E.slot_at cfg 0 ≤ es
  σ_lt_endpoint : σ < E.slot_at cfg m
  same_epoch : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ
  support_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.SupportsDesc cfg ext v q c es i → E.SupportsDesc cfg ext w m c es i
  ancestor_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.AncestorOrVoteless cfg ext v q c es i →
      E.AncestorOrVoteless cfg ext w m c es i
  base_strip : E.Xval cfg ext v q c lo es + E.Bval lo es
      + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
    E.Sval cfg ext v q c lo es
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m c lo σ,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  honest_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) → c' ≠ c →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∈ E.honest → i ∈ E.Xclass cfg ext w m c lo σ
  byzantine_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) → c' ≠ c →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∉ E.honest → i ∈ E.Bwin lo σ

theorem sameEpoch_descendStep_of_selectedInputsAt_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {glc a c : Root} {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true)
    {lo es σ : Slot}
    (hin : E.SameEpochSelectedMarginInputsAt cfg ext glc a c v q query
      w m lo es σ) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c := by
  have hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo :=
    fun t htlo htσ => epoch_eq_of_between cfg htlo htσ hin.same_epoch
  have hgrowS := E.hgrowS_of_slotStart_IH_minimal cfg ext hA hw
    hin.confirming_cutoff hin.lo_le_es hin.es_le_σ hin.start_le_es
    hin.σ_lt_endpoint hHm hsame hchain hc hglcKnown hIH
  have hgrowX := E.hgrowX_of_slotStart_IH_minimal cfg ext hA hw
    hin.confirming_cutoff hin.lo_le_es hin.es_le_σ hin.start_le_es
    hin.σ_lt_endpoint hHm hsame hchain hc hglcKnown hIH
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (Nat.le_of_lt hin.σ_lt_endpoint) hHm
  have hbudget := E.hbudget_sameEpoch_of_IH cfg ext hA.byzantine_bound
    hA.externals_coherence hin.lo_le_es hin.es_le_σ hσH hsame
  have hval : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
      hA.genesis_store hA.domain w hw m hHm
  have hbside := recorded_bside_ge cfg ext hval hin.selected_recording
  have hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c))) → c' ≠ c →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint) ≤
        E.Xval cfg ext w m c lo σ + E.Bval lo σ := by
    intro c' hc' hne
    exact recorded_sibling_le cfg ext hval
      (hin.honest_sibling_confinement c' hc' hne)
      (hin.byzantine_sibling_confinement c' hc' hne)
  exact E.descendStep_of_confirmMargin cfg ext v w q m lo es σ
    hin.support_transport hin.ancestor_transport hin.base_strip
    hgrowS hgrowX hbudget hin.child_filtered hin.status_margin hbside hsib

/-! ## Same-window endpoint margin

When the consuming endpoint is in the query slot, its canonical completed-vote
cutoff is exactly the query cutoff.  In that case the confirmation-time
ground-truth `Bval` strip transports directly to the endpoint; no epoch-local
growth recurrence and no cross-node equivocation visibility are needed.  This
case is deliberately separate from `SameEpochSelectedMarginInputsAt`: the
selected edge itself may cross an epoch boundary even though the two cutoffs
are equal. -/

/-- Inputs for the direct, equal-cutoff endpoint route.  The full Byzantine
window is store-independent, so only the two honest class transports move
between the query and endpoint stores. -/
structure DirectWindowSelectedMarginInputsAt
    (glc a c : Root) (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) (lo es : Slot) : Prop where
  support_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.SupportsDesc cfg ext v q c es i → E.SupportsDesc cfg ext w m c es i
  ancestor_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.AncestorOrVoteless cfg ext v q c es i →
      E.AncestorOrVoteless cfg ext w m c es i
  base_strip : E.Xval cfg ext v q c lo es + E.Bval lo es
      + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
    E.Sval cfg ext v q c lo es
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  selected_score : E.Sval cfg ext w m c lo es ≤
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) → c' ≠ c →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) ≤
      E.Xval cfg ext w m c lo es + E.Bval lo es

/-- Direct-window selected inputs whose confirmation base is classified in
the exact store read by the query.  No equality with `E.store v q` is a field
of this record. -/
structure PrefixDirectWindowSelectedMarginInputsAt
    (glc a c : Root) (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) (lo es : Slot) : Prop where
  support_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.StoreSupportsDesc query.store c es i →
      E.SupportsDesc cfg ext w m c es i
  ancestor_transport : ∀ i, i ∈ E.honest →
    i ∈ E.span_committee lo es →
    E.StoreAncestorOrVoteless query.store c es i →
      E.AncestorOrVoteless cfg ext w m c es i
  base_strip : E.StoreXval query.store c lo es + E.Bval lo es
      + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
    E.StoreSval query.store c lo es
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  selected_score : E.Sval cfg ext w m c lo es ≤
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) → c' ≠ c →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) ≤
      E.Xval cfg ext w m c lo es + E.Bval lo es

/-- A direct-window margin from an action-prefix query store gives the same
endpoint `DescendStep`; only the two honest classes are transported. -/
theorem directWindow_descendStep_of_prefixInputsAt_minimal
    {glc a c : Root} {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : ℕ} {lo es : Slot}
    (hin : E.PrefixDirectWindowSelectedMarginInputsAt cfg ext
      glc a c v q query w m lo es) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c := by
  obtain ⟨hS, hX⟩ := E.store_classes_base_transport_honest cfg ext
    query.store w m c lo es hin.support_transport hin.ancestor_transport
  have hstrip : E.Xval cfg ext w m c lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
      E.Sval cfg ext w m c lo es := by
    calc
      _ ≤ E.StoreXval query.store c lo es + E.Bval lo es
          + get_proposer_score cfg (E.store cfg ext w m) + 1 := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.add_le_add_right hX _) _) _
      _ ≤ E.StoreSval query.store c lo es := hin.base_strip
      _ ≤ E.Sval cfg ext w m c lo es := hS
  exact ledger_descendStep cfg ext hin.child_filtered hin.status_margin
    hin.selected_score
    hstrip hin.sibling_score

/-- Completed-store compatibility adapter for the prefix direct-window
record.  Equality is sufficient here, but absent from the canonical record. -/
theorem prefixDirectWindowSelectedMarginInputsAt_of_boundary
    {glc a c : Root} {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : ℕ} {lo es : Slot}
    (hstore : query.store = E.store cfg ext v q)
    (hin : E.DirectWindowSelectedMarginInputsAt cfg ext glc a c v q query
      w m lo es) :
    E.PrefixDirectWindowSelectedMarginInputsAt cfg ext
      glc a c v q query w m lo es := by
  refine
    { support_transport := ?_
      ancestor_transport := ?_
      base_strip := ?_
      child_filtered := hin.child_filtered
      status_margin := hin.status_margin
      selected_score := hin.selected_score
      sibling_score := hin.sibling_score }
  · intro i hi hiSpan hsupport
    apply hin.support_transport i hi hiSpan
    simpa only [StoreSupportsDesc, Execution.SupportsDesc, hstore] using hsupport
  · intro i hi hiSpan hancestor
    apply hin.ancestor_transport i hi hiSpan
    simpa only [StoreAncestorOrVoteless, Execution.AncestorOrVoteless,
      hstore] using hancestor
  · rw [hstore]
    simpa only [StoreXval, StoreXclass, StoreSval, StoreSclass,
      Execution.Xval, Execution.Xclass, Execution.Sval, Execution.Sclass,
      StoreSupportsDesc, StoreAncestorOrVoteless, Execution.SupportsDesc,
      Execution.AncestorOrVoteless] using hin.base_strip

/-- A confirmation strip at the query cutoff already gives one endpoint
`DescendStep` when the endpoint uses that same cutoff. -/
theorem directWindow_descendStep_of_selectedInputsAt_minimal
    {glc a c : Root} {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : ℕ} {lo es : Slot}
    (hin : E.DirectWindowSelectedMarginInputsAt cfg ext glc a c v q query
      w m lo es) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c := by
  obtain ⟨hS, hX⟩ := E.classes_base_transport_honest cfg ext
    v w q m c lo es hin.support_transport hin.ancestor_transport
  have hstrip : E.Xval cfg ext w m c lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
      E.Sval cfg ext w m c lo es := by
    calc
      _ ≤ E.Xval cfg ext v q c lo es + E.Bval lo es
          + get_proposer_score cfg (E.store cfg ext w m) + 1 := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.add_le_add_right hX _) _) _
      _ ≤ E.Sval cfg ext v q c lo es := hin.base_strip
      _ ≤ E.Sval cfg ext w m c lo es := hS
  exact ledger_descendStep cfg ext hin.child_filtered hin.status_margin
    hin.selected_score
    hstrip hin.sibling_score

inductive SelectedEdgeMarginInputsAt
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (glc a c : Root) (v : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) : Prop where
  | sameEpoch (lo es σ : Slot) :
      E.SameEpochSelectedMarginInputsAt cfg ext glc a c v q query
        w m lo es σ →
      SelectedEdgeMarginInputsAt cfg ext E glc a c v q query w m
  | crossing (es σ querySlot : Slot) :
      E.CrossingEdgeSelectedMarginInputs cfg ext glc a c v q w m query
        es σ querySlot →
      SelectedEdgeMarginInputsAt cfg ext E glc a c v q query w m
  | futureCrossing (es σ querySlot : Slot) :
      E.FutureCrossingSelectedMarginInputs cfg ext glc a c v q w m query
        es σ querySlot →
      SelectedEdgeMarginInputsAt cfg ext E glc a c v q query w m
  | directWindow (lo es : Slot) :
      E.DirectWindowSelectedMarginInputsAt cfg ext glc a c v q query
        w m lo es →
      SelectedEdgeMarginInputsAt cfg ext E glc a c v q query w m

/-- Slot-ordered selected margins for a real arbitrary query.  The consuming
endpoint may precede `q` in execution index when it is the first second of the
same slot.  The head IH starts at that slot boundary, not at `q`. -/
def SelectedMarginSupplyAt
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
      E.SelectedEdgeMarginInputsAt cfg ext glc a c v q query w m

/-! ## Slot-start chain lift and final arbitrary-call safety -/

theorem descendStepChainSupply_of_selectedMarginsAt_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {glc r₀ : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q) (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext v q)
    (hglc : glc ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks glc).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true)
    (hsupply : E.SelectedMarginSupplyAt cfg ext glc r₀ v q query) :
    E.DescendStepChainSupply cfg ext glc r₀
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
      a c ha hc hlink hscope hscopeR₀ hcne with
    ⟨lo, es, σ, hsame⟩ | ⟨es, σ, querySlot, hcross⟩ |
      ⟨es, σ, querySlot, hfuture⟩ | ⟨lo, es, hdirect⟩
  · exact E.sameEpoch_descendStep_of_selectedInputsAt_minimal cfg ext hA
      hw hHm hc hscope hglcKnown hIH hsame
  · exact E.crossingEdge_descendStep_of_selectedInputs_minimal cfg ext hA
      hv hqH hw hHm hcross
  · exact E.futureCrossing_descendStep_of_selectedInputs_minimal cfg ext hA
      hv hqH hw hHm hfuture
  · exact E.directWindow_descendStep_of_selectedInputsAt_minimal cfg ext hdirect

/-- The strongest arbitrary-call bridge: a base safe from the query slot's
first second and a chain supply from that same index make the selected result
safe from the slot boundary, even if the query occurs later. -/
theorem safeFrom_find_latest_confirmed_descendant_at_slotStart_minimal
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
        E.DescendStepChainSupply cfg ext
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
  exact head_ge_of_safe_scoped_terminal cfg hwfEndpoint
    (filtered_subset_block_roots cfg (E.store cfg ext w m) hjcEndpoint)
    hwalkEndpoint hjcEndpoint hlcrEndpoint hbEndpoint hheadLcr hbgeEndpoint
    (fun a c ha hc hlink hbc hclcr =>
      hsupply w hw m hm hHm hIH a c ha hc hlink hbc hclcr)

/-- Final arbitrary-query bridge from the explicit selected-margin supply.
The proof first establishes safety at the query slot boundary and then applies
`SafeFrom.mono` to the actual query index `q`. -/
theorem safeFrom_find_latest_confirmed_descendant_of_selectedMarginsAt_minimal
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
        E.SelectedMarginSupplyAt cfg ext
          (find_latest_confirmed_descendant cfg ext query lcr)
          lcr v q query) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query lcr) q := by
  have hslotSafety : E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext query lcr)
      (E.slot_start cfg (E.slot_at cfg q)) :=
    E.safeFrom_find_latest_confirmed_descendant_at_slotStart_minimal cfg ext
      hA v hv q hqH query hstore lcr hlcr hbase (by
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
          exact E.descendStepChainSupply_of_selectedMarginsAt_minimal cfg ext
            hA hv hqH query hstore hb' hp' hconf (hmargin hne))
  obtain ⟨hstart, _hstartH, _hslot, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  exact hslotSafety.mono cfg ext E hstart

end Execution

end FastConfirmation.Spec

end
