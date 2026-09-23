module
public import FastConfirmation.Spec.Proof.AnchorClose
public import FastConfirmation.Spec.Proof.CertExtract
public import FastConfirmation.Spec.Proof.FreshProducer
public import FastConfirmation.Spec.Proof.FutureCrossingMargin
public import FastConfirmation.Spec.Proof.SameSlotProvenance

@[expose] public section

/-!
# Spec / Proof / MarginProducer: selected-result edge margins

This module isolates the sound producer boundary for the selected-result
head-descent argument.  It deliberately targets `DescendStepChainSupply`
directly rather than the legacy `ForkEdgeConfirmMarginSupply`:

* the endpoint and induction hypotheses are scoped by `WithinHorizon`, as are
  the execution laws from which they are proved;
* the same-epoch route asks for the two honest vote-class transports directly,
  instead of the stronger whole-store containment which is unavailable at a
  foreign endpoint in the confirming slot;
* `hgrowS`, `hgrowX`, and the aggregate Byzantine budget are not residuals.
  `FreshProducer` derives them from the shell head-safety IH, including the
  first `es -> es + 1` step;
* endpoint score bounds are assembled from the recorded-support and sibling
  confinement predicates by `Endpoint.recorded_bside_ge` and
  `Endpoint.recorded_sibling_le`.

The remaining same-epoch fields are consequently the ordinary confirmation
base strip, the two past-vote ancestry transports, and the endpoint
filter/recording facts.  The crossing arm retains exactly the re-anchored
endpoint certificate consumed by `crossing_ledger_descendStep`; producing that
certificate from a crossing confirmation is a separate, explicitly visible
obligation.

No genesis-slot specialization is used.  The selected block is transported to
all in-horizon endpoints by the executable candidate certificate in
`SameSlotProvenance`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## The same-epoch producer boundary -/

/-- The residual inputs for one same-epoch selected-chain edge `a <- c`.

The confirming endpoint is `(v,n+1)` and the consuming fork-choice endpoint is
`(w,m)`.  The window geometry is explicit.  The three aggregate growth facts
are intentionally absent: `sameEpoch_descendStep_of_selectedInputs` derives
them from the shell IH through `FreshProducer`.
-/
structure SameEpochSelectedMarginInputs
    (E : Execution Root) (glc a c : Root) (v : ValidatorIndex) (n : ℕ)
    (w : ValidatorIndex) (m : ℕ) (lo es σ : Slot) : Prop where
  /-- The confirming cutoff is the slot immediately before `(v,n+1)`. -/
  confirming_cutoff : E.slot_at cfg (n + 1) = es + 1
  /-- The selecting step really advanced the execution clock. -/
  selecting_advance : E.slot_at cfg n < E.slot_at cfg (n + 1)
  /-- The edge window begins no later than the confirming cutoff. -/
  lo_le_es : lo ≤ es
  /-- The endpoint window extends the confirming window. -/
  es_le_σ : es ≤ σ
  /-- The trusted execution start is no later than the confirming cutoff. -/
  start_le_es : E.slot_at cfg 0 ≤ es
  /-- The endpoint has passed the complete vote window. -/
  σ_lt_endpoint : σ < E.slot_at cfg m
  /-- The complete contest window is contained in one epoch. -/
  same_epoch : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ
  /-- Past supporting votes transport from the confirming store to the endpoint. -/
  support_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.SupportsDesc cfg ext v (n + 1) c es i →
      E.SupportsDesc cfg ext w m c es i
  /-- Past ancestor/voteless votes transport from the confirming store. -/
  ancestor_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.AncestorOrVoteless cfg ext v (n + 1) c es i →
      E.AncestorOrVoteless cfg ext w m c es i
  /-- The ordinary confirmation-rule margin at the confirming store. -/
  base_strip :
    E.Xval cfg ext v (n + 1) c lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext v (n + 1) c lo es
  /-- The selected child survives the endpoint filter. -/
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  /-- The required payload status wins the pending-parent contest. -/
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  /-- Every honest support-class member is recorded on the selected side. -/
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m c lo σ,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  /-- Honest recorded supporters of a competing child are confined to `Xclass`. -/
  honest_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) →
    c' ≠ c →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∈ E.honest → i ∈ E.Xclass cfg ext w m c lo σ
  /-- Byzantine recorded supporters of a competing child lie in the window budget. -/
  byzantine_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) →
    c' ≠ c →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∉ E.honest → i ∈ E.Bwin lo σ

omit [Inhabited Root] in
/-- Epoch equality at the endpoints makes every intermediate slot share that
epoch. -/
theorem epoch_eq_of_between {lo t σ : Slot}
    (htlo : lo ≤ t) (htσ : t ≤ σ)
    (heq : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ) :
    compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo := by
  apply le_antisymm
  · rw [heq]
    exact Nat.div_le_div_right htσ
  · exact Nat.div_le_div_right htlo

/-- One same-epoch edge descent from the selected-result shell IH.

The selected block's all-endpoint knownness is supplied separately in the
precise horizon-scoped form.  It is discharged for executable selected results
by `descendStepChainSupply_of_selectedMargins` below.
-/
theorem sameEpoch_descendStep_of_selectedInputs
    (hSA : SpecAssumptions cfg ext E)
    {glc a c : Root} {v : ValidatorIndex} {n : ℕ}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true)
    {lo es σ : Slot}
    (hin : E.SameEpochSelectedMarginInputs cfg ext glc a c v n w m lo es σ) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c := by
  have hSA' := hSA
  obtain ⟨hgen, _hwfE, _hdiv, _hhb, _hsync, hec, _hsv, hbb, hji⟩ := hSA'
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hgen
    exact ⟨ast, ablk, hgeq⟩
  have hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo :=
    fun t htlo htσ => epoch_eq_of_between cfg htlo htσ hin.same_epoch
  have hIH' : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true := by
    intro w' hw' m' hm' hslot
    have hm'lt : m' < m := by
      apply Nat.lt_of_not_ge
      intro hmm'
      exact (Nat.not_le_of_gt hslot) (E.slot_at_mono cfg hmm')
    exact hIH w' hw' m' hm' hslot
      (E.withinHorizon_mono cfg (Nat.le_of_lt hm'lt) hHm)
  have hgrowS := E.hgrowS_of_IH cfg ext hSA hw
    hin.confirming_cutoff hin.selecting_advance hin.lo_le_es hin.es_le_σ
    hin.start_le_es hin.σ_lt_endpoint hHm hsame hchain hc hglcKnown hIH'
  have hgrowX := E.hgrowX_of_IH cfg ext hSA hw
    hin.confirming_cutoff hin.selecting_advance hin.lo_le_es hin.es_le_σ
    hin.start_le_es hin.σ_lt_endpoint hHm hsame hchain hc hglcKnown hIH'
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (Nat.le_of_lt hin.σ_lt_endpoint) hHm
  have hbudget := E.hbudget_sameEpoch_of_IH cfg ext hbb hec
    hin.lo_le_es hin.es_le_σ hσH hsame
  have hval : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_interface cfg ext hec hgen0 hji w hw m hHm
  have hbside := recorded_bside_ge cfg ext hval hin.selected_recording
  have hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c))) →
      c' ≠ c →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint)
        ≤ E.Xval cfg ext w m c lo σ + E.Bval lo σ := by
    intro c' hc' hne
    exact recorded_sibling_le cfg ext hval
      (hin.honest_sibling_confinement c' hc' hne)
      (hin.byzantine_sibling_confinement c' hc' hne)
  exact E.descendStep_of_confirmMargin cfg ext v w (n + 1) m
    lo es σ hin.support_transport hin.ancestor_transport
    hin.base_strip hgrowS hgrowX hbudget hin.child_filtered hin.status_margin
    hbside hsib

/-! ## Crossing producer boundary -/

/-- The exact re-anchored endpoint certificate still needed for a crossing
edge.  Unlike the legacy supply this is horizon-neutral data only after it has
been produced at an in-horizon endpoint; the surrounding functional below
performs that scoping.
-/
structure CrossingSelectedMarginInputs
    (E : Execution Root) (glc a c : Root) (v : ValidatorIndex) (n : ℕ)
    (w : ValidatorIndex) (m : ℕ) (lo σ : Slot)
    (oldSiblingHonest oldSiblingByzantine : ℕ) : Prop where
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  selected_score : E.Sval cfg ext v (n + 1) c lo σ ≤
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  endpoint_margin : oldSiblingHonest
      + E.Xval cfg ext v (n + 1) c lo σ
      + oldSiblingByzantine + E.Bval lo σ
      + get_proposer_score cfg (E.store cfg ext w m) + 1
    ≤ E.Sval cfg ext v (n + 1) c lo σ
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) →
    c' ≠ c →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)
      ≤ oldSiblingHonest + E.Xval cfg ext v (n + 1) c lo σ
        + oldSiblingByzantine + E.Bval lo σ

/-- A re-anchored crossing certificate is already exactly one `DescendStep`. -/
theorem crossing_descendStep_of_selectedInputs
    {glc a c : Root} {v : ValidatorIndex} {n : ℕ}
    {w : ValidatorIndex} {m : ℕ}
    {lo σ : Slot} {oldSiblingHonest oldSiblingByzantine : ℕ}
    (hin : E.CrossingSelectedMarginInputs cfg ext glc a c v n w m lo σ
      oldSiblingHonest oldSiblingByzantine) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c :=
  E.crossing_ledger_descendStep cfg ext hin.child_filtered hin.status_margin
    hin.selected_score
    hin.endpoint_margin hin.sibling_score

/-- The three exhaustive geometric regimes for one selected-chain edge.

The third arm covers an intra-epoch edge whose later contest window crosses an
epoch boundary.  Its concrete producer is
the endpoint-anchored `INV2` recurrence in `FutureCrossingMargin`; no `hBb`
transport or full-`Bval` netting premise is introduced. -/
inductive SelectedEdgeMarginInputs
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (glc a c : Root) (v : ValidatorIndex) (n : ℕ)
    (w : ValidatorIndex) (m : ℕ) : Prop where
  | sameEpoch (lo es σ : Slot) :
      E.SameEpochSelectedMarginInputs cfg ext glc a c v n w m lo es σ →
      SelectedEdgeMarginInputs cfg ext E glc a c v n w m
  | crossing (es σ querySlot : Slot) :
      E.CrossingEdgeSelectedMarginInputs cfg ext glc a c v (n + 1) w m
        (E.fcrStep cfg ext v n) es σ querySlot →
      SelectedEdgeMarginInputs cfg ext E glc a c v n w m
  | futureCrossing (es σ querySlot : Slot) :
      E.FutureCrossingSelectedMarginInputs cfg ext glc a c v (n + 1) w m
        (E.fcrStep cfg ext v n) es σ querySlot →
      SelectedEdgeMarginInputs cfg ext E glc a c v n w m

/-! ## Horizon-scoped selected-result supply and chain lift -/

/-- The selected-result margin functional.  It returns the reduced
per-edge inputs above.  Its consuming endpoint is ordered from the query by
slot, not by execution index, so the first second of a late query's slot is an
admissible internal witness.  The earlier-head IH deliberately remains
index-ordered: pre-query same-slot points are not asserted to be `SafeFrom`
endpoints.  Both endpoint classes are explicitly within the verification
horizon.
-/
def SelectedMarginSupply
    (glc r₀ : Root) (v : ValidatorIndex) (n : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
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
      SelectedEdgeMarginInputs cfg ext E glc a c v n w m

/-- Lift the reduced selected-result margin functional to the exact transparent
chain supply consumed by the closing engine.

The only selected-result provenance inputs are the candidate and parent
knownness retained by `get_latest_confirmed_selected`, plus its successful
confirmation.  They imply `glc` knownness at every in-horizon endpoint,
including a foreign endpoint in the confirming slot.  There is no
`hanchor0`, no whole-store relay premise, and no unscoped execution endpoint.
-/
theorem descendStepChainSupply_of_selectedMargins
    (hSA : SpecAssumptions cfg ext E)
    {glc r₀ : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hglc : glc ∈ (E.store cfg ext v (n + 1)).block_roots)
    (hparent : ((E.store cfg ext v (n + 1)).blocks glc).parent_root ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) glc = true)
    (hsupply : E.SelectedMarginSupply cfg ext glc r₀ v n) :
    E.DescendStepChainSupply cfg ext glc r₀ (n + 1) := by
  intro w hw m hm hHm hIH a c ha hc hlink hscope hscope_r₀ hcne
  have hHn1 : E.WithinHorizon cfg (n + 1) :=
    E.withinHorizon_mono cfg hm hHm
  have hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hm' hHm'
    exact E.confirmed_known_at_all_honest_endpoints cfg ext hSA v hv n glc hHn1
      hglc hparent hconf w' hw' m' (E.slot_at_mono cfg hm') hHm'
  rcases hsupply w hw m (E.slot_at_mono cfg hm) hHm hIH
      a c ha hc hlink hscope hscope_r₀ hcne with
    ⟨lo, es, σ, hsame⟩ | ⟨es, σ, querySlot, hcross⟩ |
      ⟨es, σ, querySlot, hfuture⟩
  · exact E.sameEpoch_descendStep_of_selectedInputs cfg ext hSA hw hHm hc hscope
      hglcKnown hIH hsame
  · exact E.crossingEdge_descendStep_of_selectedInputs cfg ext hSA hv hHn1 hw hHm hcross
  · exact E.futureCrossing_descendStep_of_selectedInputs cfg ext hSA hv hHn1 hw hHm hfuture

/-! ## Anchor charge without a genesis-start specialization -/

/-- The executable selected-result walk supplies its actual reset anchor and
charges every block on `[r₀, glc]` to the confirmation predicate, without a
genesis-slot assumption.  This is the checkpoint-sync-safe replacement for the
`hanchor0`-dependent wrapper `edgeCert_of_confirmation`.
-/
theorem selectedAnchorCharge
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    ∃ r₀ : Root,
      (r₀ = (E.fcrStep cfg ext v n).confirmed_root ∨
        r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∨
        r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) ∧
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ v (n + 1) ∧
      ∀ c : Root, c ∈ (E.store cfg ext v (n + 1)).block_roots →
        is_ancestor (E.store cfg ext v (n + 1))
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)))
          (get_node_for_root c) = true →
        is_ancestor (E.store cfg ext v (n + 1))
          (get_node_for_root c) (get_node_for_root r₀) = true →
        c = r₀ ∨
          is_one_confirmed cfg ext (E.store cfg ext v (n + 1))
            (get_current_balance_source (E.fcrStep cfg ext v n)) c = true := by
  have hSA' := hSA
  obtain ⟨hgen, hwfE, _hdiv, _hhb, _hsync, hec, _hsv, _hbb, hji⟩ := hSA'
  obtain ⟨hconfirmed, hfinalized, hobserved⟩ :=
    E.fcrStep_reset_roots_known_selected cfg ext hSA v hv n hHn1
  have hs : (E.fcrStep cfg ext v n).store = E.store cfg ext v (n + 1) :=
    E.fcrStep_store cfg ext v n
  obtain ⟨hwf, hwalk, hjust⟩ :=
    E.store_domainK cfg ext hwfE hec hgen hji v hv (n + 1) hHn1
  have hhead : (get_head cfg (E.store cfg ext v (n + 1))).root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v (n + 1)) with h | h
    · exact h
    · rw [h]
      exact hjust
  have hb : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    rcases E.get_latest_confirmed_selected cfg ext hSA v hv (n + 1) hHn1
        (E.fcrStep cfg ext v n) hs hconfirmed hfinalized hobserved with
      hreset | hselected
    · rcases hreset with h | h | h
      · rw [h]
        simpa only [hs] using hconfirmed
      · rw [h]
        simpa only [hs] using hfinalized
      · rw [h]
        simpa only [hs] using hobserved
    · simpa only [hs] using hselected.2.1
  obtain ⟨r₀, hkind, hr₀, hbge, hcharge⟩ :=
    get_latest_confirmed_between cfg ext (E.fcrStep cfg ext v n)
      (by rw [hs]; exact hwf) (by rw [hs]; exact hwalk)
      (by rw [hs]; exact hhead)
      (by simpa only [hs] using hconfirmed)
      (by simpa only [hs] using hfinalized)
      (by simpa only [hs] using hobserved)
  rw [hs] at hkind hr₀ hbge hcharge
  exact ⟨r₀, hkind, ⟨hb, hr₀, hbge⟩, hcharge⟩

end Execution

end FastConfirmation.Spec

end
