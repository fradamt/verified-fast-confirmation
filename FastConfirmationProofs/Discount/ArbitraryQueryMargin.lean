module
public import FastConfirmationProofs.LMD.SameSlotLMD

@[expose] public section

/-!
# Arbitrary-query selected margins

Carries the head-safety margin from a selected confirmation to later arbitrary queries.

This module contains `query_slot_start_le_of_slot_ge_minimal`, `freshEngineInputs_of_slotStart_IH_minimal`, `hgrowS_of_slotStart_IH_minimal` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

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
  intro i hi nᵢ index hslotᵢ hvote
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
  have hdue : nᵢ ≤ E.slot_start cfg (E.slot_at cfg nᵢ) +
      get_attestation_due_ms cfg / 1000 := by
    simpa only [hslotᵢ] using
      (hA.honest_behavior.vote_deadline i hiHonest (σ' + 1) nᵢ _ hvote).2
  have hheadM := E.honest_head_known_at_later_slot_minimal cfg ext hA
    hiHonest hw hHni hHm hdue hniSlotLt
  have hhead := E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
    hiHonest nᵢ hHni
  obtain ⟨hglcM, hheadGlcM⟩ := E.ancestor_at_common_descendant_minimal cfg ext hA
    hhead hheadM hglcᵢ (by rwa [is_ancestor_node_root] at hheadGlc)
  obtain ⟨hparentM, hwalkM, _⟩ := E.store_domainK_of_selectedMarginDomain cfg ext
    hA.wellFormed hA.externals_coherence hA.genesis hA.domain w hw m hHm
  have hheadCEnd : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (get_head cfg (E.store cfg ext i nᵢ)).root)
      (get_node_for_root c) = true :=
    is_ancestor_trans (b := get_node_for_root glc) hparentM (hwalkM c hc _ hheadM)
      (hwalkM c hc glc hglcM) hheadGlcM hchain
  exact hheadCEnd

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
  have hbudget := E.hbudget_sameEpoch cfg ext hA.byzantine_bound
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
    (cfg : Config) (ext : BeaconFunctionInterface Root) (E : Execution Root)
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


/-! ## Slot-start chain lift and final arbitrary-call safety -/




end Execution

end FastConfirmation.Spec

end
