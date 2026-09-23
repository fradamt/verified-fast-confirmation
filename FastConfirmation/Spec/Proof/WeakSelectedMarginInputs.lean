module
public import FastConfirmation.Spec.Proof.WeakSiblingScore
public import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
public import FastConfirmation.Spec.Proof.MarginProducer
public import FastConfirmation.Spec.Proof.WeakOneShotSafety

@[expose] public section

/-!
# Spec / Proof / WeakSelectedMarginInputs

Margin-discharge wave, Stage J-a: the weak margin-input structures and their
`DescendStep` producers, over the endpoint-direct machinery of Stages G–I
(`WeakFreshSupport.lean`, `WeakQuorumAccounting.lean`, `WeakEndpointClasses.lean`,
`WeakCrossingSets.lean`, `WeakSiblingScore.lean`).

Compared with the strong `ArbitraryQueryMargin.lean` / `FutureCrossingMargin.lean`
structures:

* the two strong crossing structures (`CrossingEdgeSelectedMarginInputs`,
  `FutureCrossingSelectedMarginInputs`) merge into ONE, `CrossingSelectedMarginInputs`
  (`F3`: the weak budget has no equivocation subtraction, so both crossing
  regimes share the same non-subtractive conclusion shape and hence the same
  input record, dispatched by the two edge-crossing cases rather than by two
  separate structures);
* `recorded_epoch_max` is deleted everywhere (Stage I: freshness replaces
  `WindowRecordedEpochMax`);
* `support_transport`/`ancestor_transport` are deleted everywhere (Stage H:
  the base strip / discount / crossing base are already read at the honest
  endpoint, never transported from the query store);
* the same-epoch and direct-window records collapse their query-indexed
  `base_strip` + the two honest-class transports into one endpoint-side
  `endpoint_base_strip` field;
* the crossing record gains three endpoint-side block-data fields
  (`endpoint_block_known`/`endpoint_parent_known`/`endpoint_parent_eq`) that
  the strong record's consumers instead re-derive from the query-to-endpoint
  transport the weak model forbids.

The `Weak.CrossingSelectedMarginInputs.regime` field records the edge/window
geometry as data (parity with `Execution.StrictSelectedEdgeGeometry.regime`),
but the producer below does not pattern-match on it: whether the edge itself
crosses an epoch is a plain decidable fact of the observer's store, and each
of its two outcomes is closed by exactly one of the two Stage-I assemblers,
so the case split is taken directly rather than trusting the structure's
(unenforced) `regime` witness to already agree with it.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## The three weak margin-input records -/

/-- Weak crossing inputs, ONE structure for both crossing regimes (`F3`).
`confirmation` is `Weak.is_one_confirmed`; `recorded_epoch_max`,
`support_transport` and `ancestor_transport` are all deleted (endpoint-direct,
Stages H/I); `parent_sub_endpoint` is stated over `Weak.crossingParentSub`;
`sibling_score` is over `Weak.crossingXPre` and is non-subtractive in both
regimes; the three `endpoint_*` fields are the endpoint-side block data the
class placements need, already available to every caller from
`Weak.SelectedCoveredMarginSupplyAt`'s own quantifier. -/
structure CrossingSelectedMarginInputs
    (E : Execution Root) (glc a b : Root) (obs : ValidatorIndex) (q : ℕ)
    (w : ValidatorIndex) (m : ℕ) (query : FastConfirmationStore Root)
    (es sigma querySlot : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext obs q
  confirmation : Weak.is_one_confirmed cfg ext query.store
    (get_current_balance_source query) b = true
  block_known : b ∈ (E.store cfg ext obs q).block_roots
  parent_known : ((E.store cfg ext obs q).blocks b).parent_root ∈
    (E.store cfg ext obs q).block_roots
  cutoff_eq : es = get_current_slot cfg (E.store cfg ext obs q) - 1
  cutoff_lt_query : es < E.slot_at cfg q
  query_slot_eq : querySlot = get_current_slot cfg (E.store cfg ext obs q)
  es_le_sigma : es ≤ sigma
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  slot_q_le_m : E.slot_at cfg q ≤ E.slot_at cfg m
  regime : Execution.StrictSelectedEdgeRegime cfg (E.store cfg ext obs q) b
    (((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot + 1) sigma
  endpoint_block_known : b ∈ (E.store cfg ext w m).block_roots
  endpoint_parent_known : ((E.store cfg ext obs q).blocks b).parent_root ∈
    (E.store cfg ext w m).block_roots
  endpoint_parent_eq : ((E.store cfg ext w m).blocks b).parent_root =
    ((E.store cfg ext obs q).blocks b).parent_root
  parent_sub_endpoint : E.weight (Weak.crossingParentSub cfg ext E (E.store cfg ext obs q)
      (get_current_balance_source query) b
      ((E.store cfg ext obs q).blocks b).slot es) ≤
    E.Aval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es
  committee_support : ∀ t : Slot, es < t → t ≤ sigma → E.CommitteeSupportsAt cfg ext w m b t
  child_filtered : ForkChoiceNode.mk b .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)))
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b))
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m b
      ((E.store cfg ext obs q).blocks b).slot sigma,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) → c' ≠ b →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)
      ≤ E.weight (Weak.crossingXPre cfg ext E (E.store cfg ext obs q)
            (get_current_balance_source query) b
            (((E.store cfg ext obs q).blocks
              ((E.store cfg ext obs q).blocks b).parent_root).slot + 1)
            ((E.store cfg ext obs q).blocks b).slot es)
        + E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma
        + E.weight (E.crossingByzPre
            (((E.store cfg ext obs q).blocks
              ((E.store cfg ext obs q).blocks b).parent_root).slot + 1)
            ((E.store cfg ext obs q).blocks b).slot es)
        + E.Bval ((E.store cfg ext obs q).blocks b).slot sigma

/-- Weak same-epoch selected inputs.  The query-indexed `base_strip` plus
`support_transport`/`ancestor_transport` collapse into one endpoint field,
since the honest classes never need to move off `(w, m)`. -/
structure SameEpochSelectedMarginInputsAt
    (E : Execution Root) (glc a c : Root) (obs : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) (lo es σ : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext obs q
  confirming_cutoff : E.slot_at cfg q = es + 1
  lo_le_es : lo ≤ es
  es_le_σ : es ≤ σ
  start_le_es : E.slot_at cfg 0 ≤ es
  σ_lt_endpoint : σ < E.slot_at cfg m
  same_epoch : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ
  endpoint_base_strip : E.Xval cfg ext w m c lo es + E.Bval lo es
      + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
    E.Sval cfg ext w m c lo es
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

/-- Weak direct-window selected inputs: the query-cutoff-equal-to-endpoint-cutoff
route, entirely at the endpoint (no query store involved at all). -/
structure DirectWindowSelectedMarginInputsAt
    (E : Execution Root) (glc a c : Root) (obs : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) (lo es : Slot) : Prop where
  endpoint_base_strip : E.Xval cfg ext w m c lo es + E.Bval lo es
      + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤
    E.Sval cfg ext w m c lo es
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

/-- Weak selected-edge margin inputs.  THREE constructors, not four (`F3`):
the two strong crossing regimes merge into `crossing`. -/
inductive SelectedEdgeMarginInputsAt
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (glc a c : Root) (obs : ValidatorIndex) (q : ℕ)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) : Prop where
  | sameEpoch (lo es σ : Slot) :
      Weak.SameEpochSelectedMarginInputsAt cfg ext E glc a c obs q query
        w m lo es σ →
      SelectedEdgeMarginInputsAt cfg ext E glc a c obs q query w m
  | crossing (es σ querySlot : Slot) :
      Weak.CrossingSelectedMarginInputs cfg ext E glc a c obs q w m query
        es σ querySlot →
      SelectedEdgeMarginInputsAt cfg ext E glc a c obs q query w m
  | directWindow (lo es : Slot) :
      Weak.DirectWindowSelectedMarginInputsAt cfg ext E glc a c obs q query
        w m lo es →
      SelectedEdgeMarginInputsAt cfg ext E glc a c obs q query w m

/-- Weak twin of `CoveredMargin.SelectedCoveredMarginSupplyAt`, over
`Weak.SelectedEdgeMarginInputsAt`. -/
def SelectedCoveredMarginSupplyAt
    (E : Execution Root) (glc r₀ : Root) (obs : ValidatorIndex) (q : ℕ)
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
        Weak.SelectedEdgeMarginInputsAt cfg ext E glc a c obs q query w m

/-! ## The three `DescendStep` producers -/

/-- Same-epoch weak producer: `hgrowS_/hgrowX_of_slotStart_IH_minimal` +
`hbudget_sameEpoch_of_IH` + `bval_strip_window_uniform` (`bval_strip_transport`
is skipped — the strip is already at the endpoint) + `ledger_descendStep`. -/
theorem sameEpoch_descendStep_of_selectedInputsAt
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    {glc a c : Root} {obs : ValidatorIndex} {q : ℕ}
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
    (hin : Weak.SameEpochSelectedMarginInputsAt cfg ext E glc a c obs q query
      w m lo es σ) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c := by
  have hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo :=
    fun t htlo htσ => Execution.epoch_eq_of_between cfg htlo htσ hin.same_epoch
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
  have hstrip := E.bval_strip_window_uniform cfg ext w m c lo es σ
    (get_proposer_score cfg (E.store cfg ext w m)) hin.endpoint_base_strip
    hgrowS hgrowX hbudget
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
  exact ledger_descendStep cfg ext hin.child_filtered hin.status_margin hbside hstrip hsib

/-- Direct-window weak producer: `ledger_descendStep` directly, no transport
step of any kind. -/
theorem directWindow_descendStep_of_selectedInputsAt
    {E : Execution Root} {glc a c : Root} {obs : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : ℕ} {lo es : Slot}
    (hin : Weak.DirectWindowSelectedMarginInputsAt cfg ext E glc a c obs q query
      w m lo es) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a c :=
  ledger_descendStep cfg ext hin.child_filtered hin.status_margin hin.selected_score
    hin.endpoint_base_strip hin.sibling_score

/-- Crossing weak producer.  Dispatches on the observer store's actual
edge-crossing condition (a plain decidable fact, recomputed here rather than
trusted from `hin.regime`) into the two Stage-I endpoint-inequality
assemblers, and closes with `crossing_ledger_descendStep`. -/
theorem crossing_descendStep_of_selectedInputs_at_observer
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    {glc a b : Root} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : Weak.CrossingSelectedMarginInputs cfg ext E glc a b obs q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  have hA := hW.base
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconfQ : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hconfStrong : Spec.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true :=
    Spec.is_one_confirmed_of_weak cfg ext _ _ _ hconfQ
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp b
    rw [← hbsEq]
    exact hconfStrong
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen obs q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q cp hkey hqH (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen obs q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩ hA.wellFormed.anchor_parent_unscheduled obs q
  have hprov := E.latestMessageProvenance_of_observer_validity cfg ext hA.wellFormed
    obs hW.validity hgen q
  rw [← E.store_current_slot cfg ext obs q] at hprov
  have hsched : SchedLMProv E cfg (E.store cfg ext obs q) :=
    E.schedLMProv cfg ext hgen obs q
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence
    ⟨ast, ablk, hgeq, hslot, hparent⟩ obs q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds ⟨ast, ablk, hgeq, hslot⟩
      obs q b hin.block_known
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2 (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  have hparentLe : get_block_epoch cfg (E.store cfg ext obs q)
      ((E.store cfg ext obs q).blocks b).parent_root ≤
      get_block_epoch cfg (E.store cfg ext obs q) b := by
    simp only [get_block_epoch]
    exact Nat.div_le_div_right (Nat.le_of_lt hslotlt)
  by_cases hcross : get_block_epoch cfg (E.store cfg ext obs q) b >
      get_block_epoch cfg (E.store cfg ext obs q)
        ((E.store cfg ext obs q).blocks b).parent_root
  · have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m b
      ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
    have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m b
      ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
    have hend := Weak.crossingEdgeFuture_endpoint_inequality_at_observer cfg ext hA hqH hcomm
      hwf hval htab hin.block_known hin.parent_known hprov hsched hconfQ hwalk hin.cutoff_eq
      hin.cutoff_lt_query hslotlt hbcur hcross hin.es_le_sigma hin.sigma_horizon hw hmH
      hin.slot_q_le_m hboost hin.endpoint_block_known hin.endpoint_parent_known
      hin.endpoint_parent_eq hAX hxS
    exact E.crossing_ledger_descendStep cfg ext hin.child_filtered hin.status_margin hbside
      hend hin.sibling_score
  · have hintra : get_block_epoch cfg (E.store cfg ext obs q) b =
        get_block_epoch cfg (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks b).parent_root :=
      le_antisymm (not_lt.mp hcross) hparentLe
    have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m b
      ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
    have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m b
      ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
    have hend := Weak.intraEpochFuture_endpoint_inequality_at_observer cfg ext hA hqH hcomm
      hwf hval htab hin.block_known hin.parent_known hprov hsched hconfQ hwalk hin.cutoff_eq
      hin.cutoff_lt_query hslotlt hbcur hintra hin.es_le_sigma hin.sigma_horizon hw hmH
      hin.slot_q_le_m hboost hin.endpoint_block_known hin.endpoint_parent_known
      hin.endpoint_parent_eq hAX hxS
    exact E.crossing_ledger_descendStep cfg ext hin.child_filtered hin.status_margin hbside
      hend hin.sibling_score

end Weak

end FastConfirmation.Spec

end
