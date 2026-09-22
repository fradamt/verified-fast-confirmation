import FastConfirmation.Spec.Proof.EndpointLedgerMinimal
import FastConfirmation.Spec.Proof.CrossEpochDynamics
import FastConfirmation.Spec.Proof.EdgeDynamics

/-!
# Re-anchored sibling scores for future-crossing selected margins

The full endpoint ledger confines a sibling's honest and Byzantine supporters
to the parent-to-endpoint window.  The future-crossing endpoint inequality is
instead re-anchored at the selected child's slot.  This module performs that
set-level split faithfully:

* endpoint honest sibling supporters assigned at or after the child slot stay
  in the re-anchored endpoint `Xclass`;
* the remaining honest supporters transport back to the query cutoff and land
  in `crossingXPre` (the `ParentStuck` slice is excluded because it belongs to
  query `Aclass`);
* the Byzantine window splits directly into `crossingByzPre` and the
  re-anchored endpoint `Bwin`.

For an edge that already crosses an epoch, the Byzantine pre-term is sharpened
by subtracting query-visible active equivocators.  This sharpening is valid at
a later-slot endpoint: synchrony relays the query's equivocation evidence to
the endpoint, while `AttSupporters` contains only endpoint-non-equivocators.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- Split a full committee window at `mid`, using the overlap-safe pre-region
at cutoff `es`.  A validator recurring in the re-anchored window is assigned
to the right arm; a non-recurring validator has an assignment strictly before
`mid`, hence no later than `es`. -/
theorem span_committee_subset_crossingPre_union
    {lo mid es sigma : Slot} (hmidEs : mid ≤ es) (hesSigma : es ≤ sigma) :
    E.span_committee lo sigma ⊆
      E.crossingPreRegion lo mid es ∪ E.span_committee mid sigma := by
  intro i hi
  by_cases hpost : i ∈ E.span_committee mid sigma
  · exact Finset.mem_union_right _ hpost
  · apply Finset.mem_union_left
    rw [crossingPreRegion, Finset.mem_sdiff]
    constructor
    · simp only [Execution.span_committee, Finset.mem_biUnion,
        Finset.mem_Icc] at hi ⊢
      obtain ⟨t, ⟨hloT, htSigma⟩, hiT⟩ := hi
      have htMid : t < mid := by
        by_contra hnot
        apply hpost
        simp only [Execution.span_committee, Finset.mem_biUnion,
          Finset.mem_Icc]
        exact ⟨t, ⟨Nat.le_of_not_gt hnot, htSigma⟩, hiT⟩
      exact ⟨t, ⟨hloT, (Nat.le_of_lt htMid).trans hmidEs⟩, hiT⟩
    · intro hiMidEs
      exact hpost (E.span_committee_mono mid hesSigma hiMidEs)

omit [LinearOrder Root] [Inhabited Root] in
/-- Non-honest specialization of
`span_committee_subset_crossingPre_union`. -/
theorem Bwin_subset_crossingByzPre_union
    {lo mid es sigma : Slot} (hmidEs : mid ≤ es) (hesSigma : es ≤ sigma) :
    E.Bwin lo sigma ⊆
      E.crossingByzPre lo mid es ∪ E.Bwin mid sigma := by
  intro i hi
  simp only [Execution.Bwin, Finset.mem_filter, Finset.mem_union] at hi ⊢
  rcases Finset.mem_union.mp
      (span_committee_subset_crossingPre_union (E := E) hmidEs hesSigma hi.1) with
    hpre | hpost
  · apply Or.inl
    simp only [crossingByzPre, Finset.mem_filter]
    exact ⟨hpre, hi.2⟩
  · exact Or.inr ⟨hpost, hi.2⟩

/-- Query-side parent-stuck validators belong to the query `Aclass`, with the
window-scoped recorded-epoch hypothesis used by the selected-margin
construction. -/
theorem parentStuck_subset_query_Aclass_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {q : ℕ} {bs : BeaconState Root}
    {b : Root} {lo es : Slot}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hlo : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hmax : E.WindowRecordedEpochMax cfg ext v q lo es) :
    ParentStuck cfg E (E.store cfg ext v q) bs b ⊆
      E.Aclass cfg ext v q b lo es := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hpsl : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hpsl b hb hparent
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hgenSlot⟩ v q b hb
  have hbanc : is_ancestor (E.store cfg ext v q) (get_node_for_root b)
      (get_node_for_root ((E.store cfg ext v q).blocks b).parent_root) = true :=
    is_ancestor_of_parent hpsl hb hparent rfl
  exact E.ParentStuck_subset_Aclass_window cfg ext hA.honest_behavior
    hA.externals_coherence hgen hprov hlo hes hslotlt hbcur hbanc hmax

/-- A query sibling-stuck validator outside the re-anchored committee window
belongs to the canonical honest pre-term, provided the parent-stuck discount
slice is known to lie in query `Aclass`. -/
theorem mem_crossingXPre_of_query_Xclass_not_mid
    {v : ValidatorIndex} {q : ℕ} {bs : BeaconState Root}
    {b : Root} {lo mid es : Slot} {i : ValidatorIndex}
    (hparentA : ParentStuck cfg E (E.store cfg ext v q) bs b ⊆
      E.Aclass cfg ext v q b lo es)
    (hiX : i ∈ E.Xclass cfg ext v q b lo es)
    (hiNotMid : i ∉ E.span_committee mid es) :
    i ∈ E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es := by
  have hiX' := hiX
  simp only [Execution.Xclass, Finset.mem_filter] at hiX'
  rw [crossingXPre, Finset.mem_sdiff]
  constructor
  · simp only [crossingHonestPre, crossingPreRegion, Finset.mem_filter,
      Finset.mem_sdiff]
    exact ⟨⟨hiX'.1.1, hiNotMid⟩, hiX'.1.2⟩
  · intro hiParentPre
    have hiParent : i ∈ ParentStuck cfg E (E.store cfg ext v q) bs b :=
      (Finset.mem_sdiff.mp hiParentPre).1
    have hiA := hparentA hiParent
    simp only [Execution.Aclass, Finset.mem_filter] at hiA
    exact hiX'.2.2 hiA.2.2

/-- The non-subtractive specialized sibling-score field consumed by
`FutureCrossingSelectedMarginInputs`.

The endpoint ledger is constructed on the full parent-to-endpoint window
`[lo,sigma]`.  This theorem re-anchors its score bound at `mid`, charging only
the overlap-safe query pre-regions plus the endpoint `Xval`/`Bval` suffix.
All inputs beyond `EndpointLedgerFields` are set/class transports already
produced by the selected-margin geometry and slot-start induction. -/
theorem futureCrossing_sibling_score_of_endpointLedger_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {q : ℕ} {w : ValidatorIndex} {m : ℕ}
    {bs : BeaconState Root} {a b : Root} {lo mid es sigma : Slot}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hbQuery : b ∈ (E.store cfg ext v q).block_roots)
    (hparentQuery : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hlo : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hmidEs : mid ≤ es)
    (hesSigma : es ≤ sigma)
    (hmaxQuery : E.WindowRecordedEpochMax cfg ext v q lo es)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i →
        E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
        E.AncestorOrVoteless cfg ext w m b es i)
    (hcommittee : ∀ t : Slot, es < t → t ≤ sigma →
      E.CommitteeSupportsAt cfg ext w m b t)
    (hledger : E.EndpointLedgerFields cfg ext w m a b lo sigma) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a) → c' ≠ b →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint)
        ≤ E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es)
          + E.Xval cfg ext w m b mid sigma
          + E.weight (E.crossingByzPre lo mid es)
          + E.Bval mid sigma := by
  classical
  have hparentA : ParentStuck cfg E (E.store cfg ext v q) bs b ⊆
      E.Aclass cfg ext v q b lo es :=
    E.parentStuck_subset_query_Aclass_minimal cfg ext hA hv hqH hbQuery
      hparentQuery hlo hes hmaxQuery
  have hXback : E.Xclass cfg ext w m b lo sigma ⊆
      E.Xclass cfg ext w m b lo es :=
    E.Xclass_subset_of_committee_support cfg ext hA.honest_behavior
      w m b lo hesSigma hcommittee
  have hXsplit : E.Xclass cfg ext w m b lo sigma ⊆
      E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es ∪
        E.Xclass cfg ext w m b mid sigma := by
    intro i hi
    by_cases hiMid : i ∈ E.span_committee mid sigma
    · apply Finset.mem_union_right
      have hi' := hi
      simp only [Execution.Xclass, Finset.mem_filter] at hi' ⊢
      exact ⟨⟨hiMid, hi'.1.2⟩, hi'.2⟩
    · apply Finset.mem_union_left
      have hiEndEs := hXback hi
      have hiEndEs' := hiEndEs
      simp only [Execution.Xclass, Finset.mem_filter] at hiEndEs'
      have hiQuery : i ∈ E.Xclass cfg ext v q b lo es := by
        simp only [Execution.Xclass, Finset.mem_filter]
        exact ⟨hiEndEs'.1,
          fun hS => hiEndEs'.2.1
            (hSt i hiEndEs'.1.2 hiEndEs'.1.1 hS),
          fun hAnc => hiEndEs'.2.2
            (hAt i hiEndEs'.1.2 hiEndEs'.1.1 hAnc)⟩
      have hiNotMidEs : i ∉ E.span_committee mid es := by
        intro hiMidEs
        exact hiMid (E.span_committee_mono mid hesSigma hiMidEs)
      exact mem_crossingXPre_of_query_Xclass_not_mid (E := E) cfg ext hparentA
        hiQuery hiNotMidEs
  have hXweight : E.Xval cfg ext w m b lo sigma ≤
      E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es) +
        E.Xval cfg ext w m b mid sigma := by
    calc
      E.Xval cfg ext w m b lo sigma =
          E.weight (E.Xclass cfg ext w m b lo sigma) := rfl
      _ ≤ E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es ∪
          E.Xclass cfg ext w m b mid sigma) := E.weight_mono hXsplit
      _ ≤ E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es) +
          E.weight (E.Xclass cfg ext w m b mid sigma) :=
        weight_union_le _ _
      _ = E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es) +
          E.Xval cfg ext w m b mid sigma := rfl
  have hBsplit : E.Bwin lo sigma ⊆
      E.crossingByzPre lo mid es ∪ E.Bwin mid sigma :=
    Bwin_subset_crossingByzPre_union (E := E) (lo := lo)
      hmidEs hesSigma
  have hBweight : E.Bval lo sigma ≤
      E.weight (E.crossingByzPre lo mid es) + E.Bval mid sigma := by
    calc
      E.Bval lo sigma = E.weight (E.Bwin lo sigma) := rfl
      _ ≤ E.weight (E.crossingByzPre lo mid es ∪ E.Bwin mid sigma) :=
        E.weight_mono hBsplit
      _ ≤ E.weight (E.crossingByzPre lo mid es) + E.weight (E.Bwin mid sigma) :=
        weight_union_le _ _
      _ = E.weight (E.crossingByzPre lo mid es) + E.Bval mid sigma := rfl
  intro c' hchild hne
  have hsibling := hledger.sibling_score c' hchild hne
  calc
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint)
        ≤ E.Xval cfg ext w m b lo sigma + E.Bval lo sigma := hsibling
    _ ≤ (E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es) +
          E.Xval cfg ext w m b mid sigma) +
        (E.weight (E.crossingByzPre lo mid es) + E.Bval mid sigma) :=
      Nat.add_le_add hXweight hBweight
    _ = E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es) +
          E.Xval cfg ext w m b mid sigma
          + E.weight (E.crossingByzPre lo mid es)
          + E.Bval mid sigma := by
      simp only [Nat.add_assoc]

/-- The subtractive specialized sibling-score field consumed by
`CrossingEdgeSelectedMarginInputs` at a genuinely later-slot endpoint.

Unlike `futureCrossing_sibling_score_of_endpointLedger_minimal`, this proof
works from the ledger's supporter-set confinements rather than its already
summed `sibling_score` field.  A query-visible active equivocator lies in the
wide Byzantine pre-region.  Under `slot_at q + 1 ≤ slot_at m`, synchrony makes
that validator endpoint-visible as equivocating, so it cannot occur in the
endpoint sibling's `AttSupporters`.  The resulting set difference has weight
exactly `weight crossingByzPre - weight crossingEquivPre`.

The equality `hlo` exposes the exact parent-window anchor used by
`CrossingEdgeSelectedMarginInputs`; callers instantiate `mid` with the selected
block's slot. -/
theorem crossingEdge_sibling_score_of_endpointLedger_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {q : ℕ} {w : ValidatorIndex} {m : ℕ}
    {bs : BeaconState Root} {a b : Root} {lo mid es sigma : Slot}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hrelaySlot : E.slot_at cfg q + 1 ≤ E.slot_at cfg m)
    (hbQuery : b ∈ (E.store cfg ext v q).block_roots)
    (hparentQuery : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hlo : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hmidEs : mid ≤ es)
    (hesSigma : es ≤ sigma)
    (hcross : get_block_epoch cfg (E.store cfg ext v q) b >
      get_block_epoch cfg (E.store cfg ext v q)
        ((E.store cfg ext v q).blocks b).parent_root)
    (hmaxQuery : E.WindowRecordedEpochMax cfg ext v q lo es)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i →
        E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
        E.AncestorOrVoteless cfg ext w m b es i)
    (hcommittee : ∀ t : Slot, es < t → t ≤ sigma →
      E.CommitteeSupportsAt cfg ext w m b t)
    (hledger : E.EndpointLedgerFields cfg ext w m a b lo sigma) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a) → c' ≠ b →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint)
        ≤ E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es)
          + E.Xval cfg ext w m b mid sigma
          + (E.weight (E.crossingByzPre lo mid es) -
            E.weight (E.crossingEquivPre cfg (E.store cfg ext v q) bs
              (compute_start_slot_at_epoch cfg
                (get_block_epoch cfg (E.store cfg ext v q) b)) mid es))
          + E.Bval mid sigma := by
  classical
  let sa := compute_start_slot_at_epoch cfg
    (get_block_epoch cfg (E.store cfg ext v q) b)
  let EqPre := E.crossingEquivPre cfg (E.store cfg ext v q) bs sa mid es
  let XPre := E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es
  let BPre := E.crossingByzPre lo mid es
  have hparentA : ParentStuck cfg E (E.store cfg ext v q) bs b ⊆
      E.Aclass cfg ext v q b lo es :=
    E.parentStuck_subset_query_Aclass_minimal cfg ext hA hv hqH hbQuery
      hparentQuery hlo hes hmaxQuery
  have hXback : E.Xclass cfg ext w m b lo sigma ⊆
      E.Xclass cfg ext w m b lo es :=
    E.Xclass_subset_of_committee_support cfg ext hA.honest_behavior
      w m b lo hesSigma hcommittee
  have hXsplit : E.Xclass cfg ext w m b lo sigma ⊆
      XPre ∪ E.Xclass cfg ext w m b mid sigma := by
    intro i hi
    by_cases hiMid : i ∈ E.span_committee mid sigma
    · apply Finset.mem_union_right
      have hi' := hi
      simp only [Execution.Xclass, Finset.mem_filter] at hi' ⊢
      exact ⟨⟨hiMid, hi'.1.2⟩, hi'.2⟩
    · apply Finset.mem_union_left
      have hiEndEs := hXback hi
      have hiEndEs' := hiEndEs
      simp only [Execution.Xclass, Finset.mem_filter] at hiEndEs'
      have hiQuery : i ∈ E.Xclass cfg ext v q b lo es := by
        simp only [Execution.Xclass, Finset.mem_filter]
        exact ⟨hiEndEs'.1,
          fun hS => hiEndEs'.2.1
            (hSt i hiEndEs'.1.2 hiEndEs'.1.1 hS),
          fun hAnc => hiEndEs'.2.2
            (hAt i hiEndEs'.1.2 hiEndEs'.1.1 hAnc)⟩
      have hiNotMidEs : i ∉ E.span_committee mid es := by
        intro hiMidEs
        exact hiMid (E.span_committee_mono mid hesSigma hiMidEs)
      exact mem_crossingXPre_of_query_Xclass_not_mid (E := E) cfg ext hparentA
        hiQuery hiNotMidEs
  have hBsplit : E.Bwin lo sigma ⊆ BPre ∪ E.Bwin mid sigma := by
    simpa only [BPre] using
      (Bwin_subset_crossingByzPre_union (E := E) (lo := lo)
        hmidEs hesSigma)
  obtain ⟨ast, ablk, hgenEq, _hgenSlot, _hgenParent⟩ := hA.genesis
  have hgen : ∃ (anchor_state : BeaconState Root)
      (anchor_block : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block :=
    ⟨ast, ablk, hgenEq⟩
  have hqueryNonhonest : ∀ i ∈ (E.store cfg ext v q).equivocating_indices,
      i ∉ E.honest :=
    fun i hi hih =>
      (Execution.honest_not_equivocating cfg ext hA.honest_behavior
        hA.externals_coherence hgen hih v q (by assumption) (by assumption)) hi
  have hloSa : lo ≤ sa := by
    dsimp only [sa]
    rw [hlo]
    exact parent_slot_succ_le_crossing_start (Root := Root) cfg hcross
  have hEqBPre : EqPre ⊆ BPre := by
    intro i hi
    have hiSa : i ∈ E.crossingByzPre sa mid es :=
      E.crossing_equivPre_subset_byzPre cfg hqueryNonhonest hi
    exact E.crossingByzPre_mono_lo hloSa hiSa
  have hEqQuery : EqPre ⊆ (E.store cfg ext v q).equivocating_indices := by
    intro i hi
    simp only [EqPre, crossingEquivPre, EquivActive, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_inter] at hi
    exact hi.1.1.2
  have hEqRelay : EqPre ⊆ (E.store cfg ext w m).equivocating_indices :=
    fun i hi => E.equiv_subset_of_relay cfg ext hA.synchrony hv hw hqH hmH
      hrelaySlot (hEqQuery hi)
  have hvalEnd : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
      hA.genesis_store hA.domain w hw m hmH
  have hEqWeightSplit : E.weight EqPre + E.weight (BPre \ EqPre) =
      E.weight BPre := E.weight_add_sdiff hEqBPre
  have hBdiffWeight : E.weight (BPre \ EqPre) =
      E.weight BPre - E.weight EqPre := by
    exact Nat.eq_sub_of_add_eq' hEqWeightSplit
  intro c' hchild hne
  let Supp := (AttSupporters cfg (E.store cfg ext w m)
    (get_node_for_root c')
    ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint)).toFinset
  have hSuppSplit : Supp ⊆
      (XPre ∪ E.Xclass cfg ext w m b mid sigma) ∪
        ((BPre \ EqPre) ∪ E.Bwin mid sigma) := by
    intro i hi
    have hiSupp : i ∈ AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) := by
      simpa only [Supp, List.mem_toFinset] using hi
    by_cases hih : i ∈ E.honest
    · apply Finset.mem_union_left
      exact hXsplit (hledger.honest_sibling_confinement c' hchild hne i
        hiSupp hih)
    · apply Finset.mem_union_right
      rcases Finset.mem_union.mp
          (hBsplit (hledger.byzantine_sibling_confinement c' hchild hne i
            hiSupp hih)) with hiPre | hiPost
      · apply Finset.mem_union_left
        rw [Finset.mem_sdiff]
        refine ⟨hiPre, ?_⟩
        intro hiEq
        obtain ⟨_lm, _hlm, hiNotEquiv, _hsupport⟩ :=
          mem_AttSupporters cfg hiSupp
        exact hiNotEquiv (hEqRelay hiEq)
      · exact Finset.mem_union_right _ hiPost
  rw [attestation_score_eq_weight cfg hvalEnd]
  calc
    E.weight Supp ≤ E.weight
        ((XPre ∪ E.Xclass cfg ext w m b mid sigma) ∪
          ((BPre \ EqPre) ∪ E.Bwin mid sigma)) :=
      E.weight_mono hSuppSplit
    _ ≤ E.weight (XPre ∪ E.Xclass cfg ext w m b mid sigma) +
          E.weight ((BPre \ EqPre) ∪ E.Bwin mid sigma) :=
      weight_union_le _ _
    _ ≤ (E.weight XPre + E.weight (E.Xclass cfg ext w m b mid sigma)) +
          (E.weight (BPre \ EqPre) + E.weight (E.Bwin mid sigma)) :=
      Nat.add_le_add (weight_union_le _ _) (weight_union_le _ _)
    _ = E.weight XPre + E.Xval cfg ext w m b mid sigma +
          (E.weight BPre - E.weight EqPre) + E.Bval mid sigma := by
      rw [hBdiffWeight]
      simp only [Execution.Xval, Execution.Bval, Nat.add_assoc]
    _ = E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs b lo mid es)
          + E.Xval cfg ext w m b mid sigma
          + (E.weight (E.crossingByzPre lo mid es) -
            E.weight (E.crossingEquivPre cfg (E.store cfg ext v q) bs
              (compute_start_slot_at_epoch cfg
                (get_block_epoch cfg (E.store cfg ext v q) b)) mid es))
          + E.Bval mid sigma := by
      rfl

end Execution

end FastConfirmation.Spec
