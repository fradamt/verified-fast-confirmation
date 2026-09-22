module
public import FastConfirmation.Spec.Proof.SelectedTraceCoverage
public import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
public import FastConfirmation.Spec.Proof.SelectedFilterChainGeometry

@[expose] public section

/-!
# Complete retained-trace FFG/filter contract

The executable selector can retain several previous- and tentative-loop edges.
Filtered membership is needed for every strict selected edge not already below
the endpoint justified root, not merely for the final result or for a tentative
edge which crosses epochs.

The state transition and justification functions in the transcribed execution
remain opaque, so their concrete certificate/source visibility cannot be
derived internally.  `SelectedTraceFFGPipeline` states exactly that missing
boundary for every retained edge.  The spec's `HonestVotesSupportTarget`
provisos are kept separately and indexed only by helper calls which the
executable path actually relies on.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Normative support provisos for prediction helpers actually used by one
selector call.  Epoch-start short-circuit paths carry no no-conflict proviso,
because that helper need not be evaluated there. -/
structure SelectedHelperProvisosAt (E : Execution Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  current_target : ∀ a c : Root,
    CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  no_conflict : ∀ a c : Root,
    PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  /-- The final tentative stage can return a previous-epoch result even when
  that result is not a retained previous-loop edge.  In a non-start slot the
  wrapper's final guard still used the same no-conflict helper, so its
  normative support proviso must be indexed by the selected result as well as
  by previous-loop edges. -/
  selected_previous_result_no_conflict : ∀ result : Root,
    find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot = result →
    result ≠ latestConfirmedRoot →
    get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q

/-- Every retained tentative edge passed confirmation through the current
observed checkpoint, so at an actual execution query that checkpoint is keyed.
-/
theorem retainedTentativeEdge_current_balance_checkpoint_key
    {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {q : ℕ}
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (hstore : fcrStore.store = E.store cfg ext v q)
    (h : (a, c) ∈
      (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys := by
  have hconf := (mem_findLatestSelectedTrace_tentative cfg ext fcrStore
    latestConfirmedRoot a c h).1
  have hkey := E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q
    fcrStore.current_epoch_observed_justified_checkpoint c
  rw [← hstore] at hkey
  apply hkey
  simpa only [get_current_balance_source] using hconf

/-- Exact opaque-state-transition boundary for all retained selector edges.

The endpoint certificate pipeline is concrete and uses the explicit
`FFGAccountabilityAssumptions`.  The
last field supplies only a known common-descendant leaf, the finalized-boundary
walk to it, and its voting-source freshness, which the current abstract state
transition cannot connect to the executable store.  The ancestor list,
`ChainDown` proof, selected-child list membership, parent-slot discipline, and
ordinary known-root walk domain are constructed internally.  It is conditional
on lack of direct justified coverage and on the spec's actual helper provisos;
it contains no head-safety or margin conclusion.
-/
structure SelectedTraceFFGPipeline (E : Execution Root)
    (anchor : Checkpoint Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  query_store_eq : fcrStore.store = E.store cfg ext v q
  accountability_assumptions : FFGAccountabilityAssumptions cfg ext E
  endpoint : ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    EndpointFFGPipeline cfg E anchor (E.store cfg ext w m)
  retained_edge_tip_source :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys →
      ∀ a c : Root,
      (PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c ∨
        (a, c) ∈
          (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) →
      SelectedHelperProvisosAt cfg ext E v q fcrStore latestConfirmedRoot →
      ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg q ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root c) ≠ true →
      ∃ hplace : RetainedFilterTipPlacement cfg (E.store cfg ext w m) c,
        TipSourceFresh cfg (E.store cfg ext w m) hplace.tip

/-- Mechanical filter certificate for any retained previous or tentative edge.
-/
theorem filterTipCertificate_of_retained_edge
    {E : Execution Root} {anchor : Checkpoint Root}
    {v : ValidatorIndex} {q : ℕ}
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot : Root}
    (hpipeline : SelectedTraceFFGPipeline cfg ext E anchor v q fcrStore
      latestConfirmedRoot)
    {a c : Root}
    (hedge : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c ∨
      (a, c) ∈
        (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q fcrStore
      latestConfirmedRoot)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslot : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
            ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hnot_covered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    Nonempty (FilterTipCertificate cfg (E.store cfg ext w m) c) := by
  have hstore : fcrStore.store = E.store cfg ext v q :=
    hpipeline.query_store_eq
  have hkey : fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys := by
    rcases hedge with hprev | htent
    · exact hprev.current_balance_checkpoint_key cfg ext
        hpipeline.accountability_assumptions.genesis_store hstore
    · exact retainedTentativeEdge_current_balance_checkpoint_key cfg ext
        hpipeline.accountability_assumptions.genesis_store hstore htent
  obtain ⟨hplace, hsource⟩ :=
    hpipeline.retained_edge_tip_source hkey a c hedge hprovisos
      w hw m hslot hHm hnot_covered
  have hendpoint := hpipeline.endpoint w hw m hHm
  obtain ⟨hskel, htip⟩ :=
    SelectedFilterChainGeometry.exists_filterTipSkeleton_of_placement cfg
      hwf hwalkK hendpoint.justified_root_known hc hnot_covered hplace
  have hsource' : TipSourceFresh cfg (E.store cfg ext w m) hskel.tip := by
    rw [htip]
    exact hsource
  exact ⟨filterTipCertificate_of_pipeline cfg
    (CertificateAccountability.of_assumptions cfg ext
      hpipeline.accountability_assumptions)
    hendpoint hskel hsource'⟩

/-- Direct filtered-child output for any retained selected edge. -/
theorem child_filtered_of_retained_edge_pipeline
    {E : Execution Root} {anchor : Checkpoint Root}
    {v : ValidatorIndex} {q : ℕ}
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot : Root}
    (hpipeline : SelectedTraceFFGPipeline cfg ext E anchor v q fcrStore
      latestConfirmedRoot)
    {a c : Root}
    (hedge : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c ∨
      (a, c) ∈
        (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q fcrStore
      latestConfirmedRoot)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslot : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
            ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hparent : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hnot_covered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    ForkChoiceNode.mk c ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a) := by
  exact child_filtered_of_filterTipCertificate_nonempty cfg
    (filterTipCertificate_of_retained_edge cfg ext hpipeline hedge hprovisos
      hw hslot hHm hwf hwalkK hc hnot_covered) hparent

namespace Execution

variable (E : Execution Root)

/-- Complete trace coverage plus the exact FFG pipeline produces
`child_filtered` for any strict edge recovered by the query-local geometry.
-/
theorem strictSelectedEdge_child_filtered_of_trace_pipeline_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (r₀ : Root) (hr₀ : r₀ ∈ query.store.block_roots)
    (hpipeline : SelectedTraceFFGPipeline cfg ext E anchor v q query r₀)
    (hprovisos : SelectedHelperProvisosAt cfg ext E v q query r₀)
    {glc a c : Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {lo es sigma querySlot : Slot}
    (hgeom : StrictSelectedEdgeGeometry cfg ext E glc r₀ a c
      v q query w m lo es sigma querySlot)
    (hcne : c ≠ r₀)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hnot_covered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    ForkChoiceNode.mk c ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a) := by
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  have hheadQ : (get_head cfg (E.store cfg ext v q)).root ∈
      (E.store cfg ext v q).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  have hr₀Q : r₀ ∈ (E.store cfg ext v q).block_roots := by
    simpa only [hgeom.query_store_eq] using hr₀
  have haQ : a ∈ (E.store cfg ext v q).block_roots := by
    rw [← hgeom.parent_eq]
    exact hgeom.parent_known
  have hresultC : is_ancestor (E.store cfg ext v q)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query r₀))
      (get_node_for_root c) = true := by
    rw [hgeom.result_eq]
    exact hgeom.result_to_child
  have hedge := strict_selected_edge_mem_trace cfg ext query
    (by simpa only [hgeom.query_store_eq] using hwfQ)
    (by simpa only [hgeom.query_store_eq] using hwalkQ)
    (by simpa only [hgeom.query_store_eq] using hheadQ)
    r₀ (by simpa only [hgeom.query_store_eq] using hr₀Q)
    (by simpa only [hgeom.query_store_eq] using haQ)
    (by simpa only [hgeom.query_store_eq] using hgeom.block_known)
    (by simpa only [hgeom.query_store_eq, hgeom.parent_eq])
    (by simpa only [hgeom.query_store_eq] using hresultC)
    (by simpa only [hgeom.query_store_eq] using hgeom.child_to_anchor)
    hcne
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [hgeom.confirming_cutoff]
    exact Nat.succ_le_of_lt
      (lt_of_le_of_lt hgeom.cutoff_le_sigma hgeom.sigma_lt_endpoint)
  obtain ⟨hwfM, hwalkM, _hjustM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hmH
  have hcM : c ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hgeom.query_store_eq c hqH hgeom.block_known
        hgeom.parent_known hgeom.confirmation w hw m hslotQM hmH
  exact child_filtered_of_retained_edge_pipeline cfg ext hpipeline
    hedge hprovisos hw hslotQM hmH hwfM hwalkM hcM hparentM hnot_covered

end Execution

end FastConfirmation.Spec

end
