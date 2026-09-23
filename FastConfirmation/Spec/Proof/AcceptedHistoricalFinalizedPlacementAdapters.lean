module
public import FastConfirmation.Spec.Proof.AcceptedHistoricalFinalizedPlacement
public import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Adapters for historical finalized placement

This module connects the consumer-shaped finalized-placement results to the
actual selected-result induction interfaces.

* a non-anchor accepted global finalized checkpoint is strictly older than
  the endpoint current epoch;
* in each of the three early phase cells this puts the finalized boundary at
  or before the selected block;
* the real slot-start head induction and concrete confirmation relay produce
  the post-query canonicality consumed by finalized placement.

The remaining pre-query branch is stated as one exact historical placement
interface.  No producer for that interface is assumed here: the existing
Lemmas 23--26 history object supplies source recency and a past store's own
finalized check, but does not identify a later endpoint finalized checkpoint
on the selected query path.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Non-anchor finalized timing -/

/-- A non-anchor accepted global finalized field is strictly older than its
store's current epoch.  This keeps the exact accepted certificate carrier
until the existing included-finalization timing theorem consumes it. -/
theorem finalizedCheckpoint_epoch_lt_current_of_ne_anchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {w : ValidatorIndex} {m : Nat}
    (hne : (E.store cfg ext w m).finalized_checkpoint ≠ B.anchor) :
    (E.store cfg ext w m).finalized_checkpoint.epoch <
      get_current_store_epoch cfg (E.store cfg ext w m) := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m) with
    hfieldAnchor | ⟨carrier, hcarrier, hcertificate⟩
  · exact False.elim (hne hfieldAnchor)
  · obtain ⟨hcertificate⟩ := hcertificate
    exact E.includedCertifiedFinalized_epoch_lt_current_of_acceptedCarrier
      cfg ext B hT hcarrier.known hcertificate

/-! ## Boundary placement in the early phase matrix -/

/-- In every early phase cell, a non-anchor endpoint finalized epoch is no
later than the selected block epoch.

For `currentSame` the endpoint epoch is the selected epoch.  For `previous`
and `currentNext` it is exactly the successor; strict non-anchor finalized
timing removes that one-epoch gap.  Cross-store block agreement transfers the
selected epoch from the actual query store to the endpoint store. -/
theorem EarlySelectedEndpointPhase.finalizedEpoch_le_selected_of_nonanchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {q : Nat}
    {w : ValidatorIndex} {m : Nat}
    {selected : Root} {e : Epoch}
    (hphase : EarlySelectedEndpointPhase e
      (get_current_store_epoch cfg (E.store cfg ext v q))
      (get_current_store_epoch cfg (E.store cfg ext w m)))
    (hselectedQuery : selected ∈
      (E.store cfg ext v q).block_roots)
    (hselectedEndpoint : selected ∈
      (E.store cfg ext w m).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hne : (E.store cfg ext w m).finalized_checkpoint ≠ B.anchor) :
    (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      get_block_epoch cfg (E.store cfg ext w m) selected := by
  have hblocks : (E.store cfg ext v q).blocks selected =
      (E.store cfg ext w m).blocks selected :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m)
      hselectedQuery hselectedEndpoint
  have hselectedEpochEndpoint : get_block_epoch cfg
      (E.store cfg ext w m) selected = e := by
    simpa only [get_block_epoch, ← hblocks] using hselectedEpoch
  have hfinalizedLt :=
    E.finalizedCheckpoint_epoch_lt_current_of_ne_anchor
      cfg ext B hT hanchor hne
  rw [hselectedEpochEndpoint]
  cases hphase with
  | previous _hquery hendpoint =>
      rw [hendpoint] at hfinalizedLt
      exact Nat.lt_succ_iff.mp (by
        simpa only [Nat.succ_eq_add_one] using hfinalizedLt)
  | currentSame _hquery hendpoint =>
      rw [hendpoint] at hfinalizedLt
      exact hfinalizedLt.le
  | currentNext _hquery hendpoint =>
      rw [hendpoint] at hfinalizedLt
      exact Nat.lt_succ_iff.mp (by
        simpa only [Nat.succ_eq_add_one] using hfinalizedLt)

/-- Executable boundary form of
`finalizedEpoch_le_selected_of_nonanchor`, exactly matching the retained-tip
placement consumer. -/
theorem EarlySelectedEndpointPhase.finalizedBoundary_le_selected_of_nonanchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {q : Nat}
    {w : ValidatorIndex} {m : Nat}
    {selected : Root} {e : Epoch}
    (hphase : EarlySelectedEndpointPhase e
      (get_current_store_epoch cfg (E.store cfg ext v q))
      (get_current_store_epoch cfg (E.store cfg ext w m)))
    (hselectedQuery : selected ∈
      (E.store cfg ext v q).block_roots)
    (hselectedEndpoint : selected ∈
      (E.store cfg ext w m).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hne : (E.store cfg ext w m).finalized_checkpoint ≠ B.anchor) :
    compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      ((E.store cfg ext w m).blocks selected).slot := by
  have hepoch := hphase.finalizedEpoch_le_selected_of_nonanchor
    cfg ext B hT hanchor hselectedQuery hselectedEndpoint
      hselectedEpoch hne
  calc
    compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
        compute_start_slot_at_epoch cfg
          (get_block_epoch cfg (E.store cfg ext w m) selected) :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hepoch
    _ ≤ ((E.store cfg ext w m).blocks selected).slot :=
      start_slot_at_block_epoch_le cfg (E.store cfg ext w m) selected

/-! ## The real post-query head induction adapter -/

/-- Concrete confirmation relay plus the real slot-start head induction
produce the consumer-shaped post-query finalized canonicality.

The selected-root knownness conjunct is not inferred from totalized
`is_ancestor`: it comes from the confirmed candidate's honest supporter via
`confirmed_known_at_all_honest_endpoints_minimal`. -/
theorem StrictSelectedResultMechanicalFacts.selectedCanonicalForFinalizedTargetsAfterQueryAt
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {q : Nat} (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input selected : Root}
    (hquery : query.store = E.store cfg ext v q)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input selected)
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {w : ValidatorIndex} {m : Nat}
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt
      cfg ext q selected m) :
    E.SelectedCanonicalForFinalizedTargetsAfterQueryAt
      cfg ext B q selected w m := by
  intro htarget hpost
  have hslotSecond : E.slot_at cfg q ≤
      E.slot_at cfg htarget.second := by
    rw [htarget.second_slot]
    exact hpost
  have hlower : E.slot_start cfg (E.slot_at cfg q) ≤ htarget.second :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotSecond
  have hselectedKnown : selected ∈
      (E.store cfg ext htarget.validator htarget.second).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hquery selected hqH
      (by simpa only [← hquery] using h.result_known)
      (by simpa only [← hquery] using h.parent_known)
      h.confirmed htarget.validator htarget.validator_honest
      htarget.second hslotSecond htarget.second_within
  have hsecondLtEndpoint : E.slot_at cfg htarget.second <
      E.slot_at cfg m := by
    rw [htarget.second_slot]
    exact htarget.before_endpoint
  exact ⟨hselectedKnown,
    hcanonical htarget.validator htarget.validator_honest
      htarget.second hlower hsecondLtEndpoint htarget.second_within⟩

/-! ## Exact pre-query historical residual -/

/-- The narrow missing historical base: a pre-query formation witness for a
later endpoint finalized checkpoint places that exact checkpoint on the
selected query path.

This conclusion is intentionally executable and query-local.  The formation
vote's old head cannot be required to descend `selected`, which may not yet
exist at the vote time.  No producer is supplied by this module. -/
def AcceptedFinalizedPlacementBeforeQueryAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (query : FastConfirmationStore Root)
    (q : Nat) (selected : Root)
    (w : ValidatorIndex) (m : Nat) : Prop :=
  E.AcceptedFinalizedTargetBeforeQueryAt cfg ext B q w m →
    (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg query.store selected
        (E.store cfg ext w m).finalized_checkpoint.epoch

namespace AcceptedRetainedPhaseSourceCarrierAt

/-- The pre-query historical placement signature is sufficient: paired
selected-root walks transport its exact query computation to the endpoint,
and the retained descendant extends it to the source-compatible tip. -/
theorem finalized_check_of_targetBeforeQueryPlacement
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {q : Nat}
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {w : ValidatorIndex} {m : Nat} {selected : Root}
    (h : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B
      (E.store cfg ext w m) selected)
    (hpre : E.AcceptedFinalizedTargetBeforeQueryAt cfg ext B q w m)
    (hhistory : E.AcceptedFinalizedPlacementBeforeQueryAt
      cfg ext B query q selected w m)
    (hselectedQuery : selected ∈ query.store.block_roots)
    (hboundarySelectedQuery : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      (query.store.blocks selected).slot)
    (hquerySelectedWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) selected)
    (hendpointSelectedWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) selected)
    (hendpointTipWalk : WalkKnown (E.store cfg ext w m)
      (compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch) h.tip) :
    (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext w m) h.tip
        (E.store cfg ext w m).finalized_checkpoint.epoch := by
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    rw [hquery]
    exact E.store_causal cfg ext v q
  have hqueryParent : ParentSlotLt query.store := by
    rw [hquery]
    exact E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure
      hT.wellFormed.anchor_parent_unscheduled v q
  have hendpointParent : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure
      hT.wellFormed.anchor_parent_unscheduled w m
  have hselectedTransport : get_checkpoint_block cfg query.store selected
        (E.store cfg ext w m).finalized_checkpoint.epoch =
      get_checkpoint_block cfg (E.store cfg ext w m) selected
        (E.store cfg ext w m).finalized_checkpoint.epoch :=
    hqueryCausal.getCheckpointBlock_eq_of_pairedWalks cfg ext
      hT.wellFormed h.store_causal hqueryParent hendpointParent
        hquerySelectedWalk hendpointSelectedWalk
  have hfinalizedSelected :
      (E.store cfg ext w m).finalized_checkpoint.root =
        get_checkpoint_block cfg (E.store cfg ext w m) selected
          (E.store cfg ext w m).finalized_checkpoint.epoch :=
    (hhistory hpre).trans hselectedTransport
  have hselectedBlocks : query.store.blocks selected =
      (E.store cfg ext w m).blocks selected :=
    hT.wellFormed.blocks_agree hqueryCausal.blockProvenance
      h.store_causal.blockProvenance hselectedQuery h.selected_known
  have hboundarySelectedEndpoint : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch ≤
      ((E.store cfg ext w m).blocks selected).slot := by
    simpa only [← hselectedBlocks] using hboundarySelectedQuery
  exact finalized_check_of_ancestor cfg hendpointParent
    h.tip_descends_selected hboundarySelectedEndpoint hendpointTipWalk
      hfinalizedSelected

end AcceptedRetainedPhaseSourceCarrierAt

end Execution


end FastConfirmation.Spec

end
