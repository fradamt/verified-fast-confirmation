import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedRetainedPhaseSourceRetarget
import FastConfirmation.Spec.Proof.AcceptedEarlyPhaseSourceWiring
import FastConfirmation.Spec.Proof.AcceptedHistoricalFinalizedPlacementAdapters
import FastConfirmation.Spec.Proof.AcceptedFFGJustifiedMaximality
import FastConfirmation.Spec.Proof.PaperA32SupportRealization
import FastConfirmation.Spec.Proof.SelectedCoveredMarginConstruction
import FastConfirmation.Spec.Proof.AcceptedActualSelectedJustifiedOrientation
import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OriginCall
import FastConfirmation.Spec.Proof.AcceptedCurrentSameEndpointSource
import FastConfirmation.Spec.Proof.AcceptedRecentCarrierFinalizedPlacement
import FastConfirmation.Spec.Proof.AcceptedPreviousEpochStartSupply
import FastConfirmation.Spec.Proof.SelectedA32Semantics

/-!
# Mechanical selected-result to strict-edge filter supply

The phase/history proof should be paid once for the final selected result at
an endpoint, not once for every strict edge below it.  This file isolates the
small endpoint outcome that the later phase dispatcher will construct and
proves its single-edge eliminator.

The outcome has exactly three possibilities:

* the endpoint justified root already descends from (covers) the selected
  result; or
* one recent accepted retained source carrier above the selected result also lies
  above the endpoint justified root and owns the finalized check on its
  unchanged retained tip; or
* one late A3.2 source-visible retained leaf lies above both the selected
  result and endpoint justified root and owns the same-tip finalized check.

For a non-covered strict edge child `c`, the first possibility is impossible.
In the second, comparability below the selected result forces `c` to descend
from the justified root.  The existing retargeting theorem then reuses the
same carrier tip and finalized check at `c`, and the certificate's executable
child theorem gives filter membership under the edge's concrete parent.

This module deliberately exports no universal endpoint-outcome provider.
That expensive producer is derived later by phase dispatch inside the
`SelectedStrictEdgeFilterSupplyAt` lambda.  There is no filter, safety,
selected-margin, or free finalized-placement premise here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Actual-call endpoint order

The arbitrary-query margin API intentionally permits an endpoint earlier in
execution index than a late query in the same slot.  An actual FCR call is
different: its query store is installed at `n + 1`, exactly when the store
clock advances from the preceding slot.  Monotonicity of `slot_at` therefore
forces every endpoint in the query slot or a later slot to have index at least
`n + 1`.

This is a derived call-timing fact, not an ordering premise on the filter
supply.  In particular it discharges the `n + 1 <= m` input of the existing
previous-epoch source producer from the strict-edge geometry already present
inside the supply lambda. -/

/-- An endpoint whose slot is not before an actual call's query slot cannot
precede the query store in execution index. -/
theorem actualCall_queryIndex_le_of_slot_le
    {v : ValidatorIndex} {n m : Nat}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hslot : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m) :
    n + 1 ≤ m := by
  have hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    unfold IsFCRCallAt at hcall
    simpa only [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] using hcall
  by_contra hnot
  have hmLt : m < n + 1 := Nat.lt_of_not_ge hnot
  have hmLeN : m ≤ n := Nat.lt_succ_iff.mp (by
    simpa only [Nat.succ_eq_add_one] using hmLt)
  have hmSlotLt : E.slot_at cfg m < E.slot_at cfg (n + 1) :=
    (E.slot_at_mono cfg hmLeN).trans_lt hadvance
  exact (Nat.not_lt_of_ge hslot) hmSlotLt

/-- The strict-edge geometry itself supplies the slot-order input needed by
`actualCall_queryIndex_le_of_slot_le`. -/
theorem StrictSelectedEdgeGeometry.actualCall_queryIndex_le_endpoint
    {glc r0 a c : Root} {v : ValidatorIndex} {n : Nat}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : Nat}
    {lo es sigma querySlot : Slot}
    (h : StrictSelectedEdgeGeometry cfg ext E glc r0 a c
      v (n + 1) query w m lo es sigma querySlot)
    (hcall : E.IsFCRCallAt cfg ext v n) :
    n + 1 ≤ m := by
  apply E.actualCall_queryIndex_le_of_slot_le cfg ext hcall
  rw [h.confirming_cutoff]
  exact Nat.succ_le_of_lt (h.cutoff_le_sigma.trans_lt h.sigma_lt_endpoint)

/-! ## Actual-call endpoint justified-epoch bound

The late source-visible branches need the endpoint checkpoint's declared
epoch to be no later than the selected block epoch.  This is not a consequence
of tree orientation alone: checkpoint epochs are semantic data.  For an
accepted endpoint the bound follows from the same causal origin split used by
the selected/justified orientation proof.  An anchor endpoint is bounded by
trusted-anchor geometry; a post-query honest target vote is bounded by the
causal head induction; and a pre-query target vote is bounded by the exact
three-region SIR bracket.  In the final case, a larger checkpoint epoch would
put the checkpoint above the selected result and hence above the non-covered
child, a contradiction. -/

/-- Consumer-ready declared-epoch bound for one actual strict selector call.

All accepted certificate producers are reconstructed from the completed
prefix.  No checkpoint-epoch inequality or selected/checkpoint orientation is
taken as a premise. -/
theorem actualCall_strictSelected_endpointJustifiedEpoch_le_result
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n))
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.getLatestConfirmedTraceAt cfg ext v n).result)
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (E.getLatestConfirmedTraceAt cfg ext v n).result) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.static_validators
      byzantine_bound := hC.byzantine_bound
      domain := hdomain }
  have hquery : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hinput' : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, trace] using hinput
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hinputUpper : get_block_epoch cfg query.store trace.afterObserved ≤
      get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (by
      rw [hquery]
      simpa only [E.store_current_slot] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          v (n + 1) trace.afterObserved
            (by simpa only [hquery] using hinput'))
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    rcases Nat.eq_or_lt_of_le hinputUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_iff.mpr hlt) hselector.input_recent)
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)
  have hhistorical : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query trace.afterObserved trace.result := by
    simpa only [query, trace] using
      E.completedPrefix_acceptedHistoricalA32PayloadProducerAt
        cfg ext B hT hC hfit hanchor hboundary hv hcall hHn1 hprior hinput
          hselector
  have hhistorical' : E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      query trace.afterObserved
        (find_latest_confirmed_descendant cfg ext query
          trace.afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hproducer : E.EndpointOriginOrPinnedProducerAt
      cfg ext B.anchor (n + 1) query := by
    simpa only [query] using
      E.completedPrefix_endpointOriginOrPinnedProducerAt
        cfg ext B hT hC hfit hanchor hboundary hv hHn1
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hbracketOrCausal :
      E.PreQueryVoteSelectedSIRBracketAt cfg ext (n + 1) trace.afterObserved
          (find_latest_confirmed_descendant cfg ext query trace.afterObserved)
          w m ∨
        E.CausalHonestTargetAt cfg ext (n + 1) w m :=
    E.preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_acceptedProducers
      cfg ext hA hwalkDomain B hgenShort hanchor hv hHn1 query hquery
      trace.afterObserved hinput' hinputEpoch
      (by simpa only [trace] using hbase) hstrict
      hhistorical' hproducer hw hslotQM hHm
  have hmechanical := E.strictSelectedResultMechanicalFacts cfg ext hA
    hv hHn1 query hquery trace.afterObserved hinput' hinputEpoch hstrict
  have hresultQ : trace.result ∈ query.store.block_roots := by
    rw [hselector.result_eq]
    exact hmechanical.result_known
  have hstartM : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM
  have hresultM : trace.result ∈
      (E.store cfg ext w m).block_roots :=
    hselectedKnown w hw m hstartM hHm
  obtain ⟨hparentM, hwalkM, hjustifiedM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hHm
  have hnotJResult : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root trace.result) ≠ true := by
    intro hJResult
    apply hnotCovered
    exact is_ancestor_trans hparentM
      (hwalkM c hcM
        (E.store cfg ext w m).justified_checkpoint.root hjustifiedM)
      (hwalkM c hcM trace.result hresultM)
      hJResult (by simpa only [trace] using hselectedC)
  have hblocksAgree : query.store.blocks trace.result =
      (E.store cfg ext w m).blocks trace.result := by
    rw [hquery]
    exact hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v (n + 1))
      (E.blockProvenance cfg ext w m)
      (by simpa only [hquery] using hresultQ) hresultM
  rcases hbracketOrCausal with hvoteBracket | hcausal
  · have horigin : E.EndpointJustificationOriginAt
        cfg ext B.anchor w m :=
      ExactPrefixAcceptedFFGSemantics.endpointJustificationOriginAt
        cfg ext B hT hanchor hboundary
    rcases horigin with hanchorEndpoint |
        ⟨i, hi, s, k, a, hs0, hsm, hsH, hvote, htarget⟩
    · have hbound := (E.known_descends_trustedAnchor cfg ext hA hanchor
        w m hresultM).2
      rw [← hanchorEndpoint] at hbound
      simpa only [query, trace, get_block_epoch, hblocksAgree] using hbound
    · by_cases hqs : E.slot_at cfg (n + 1) ≤ s
      · have hbound :=
          E.endpoint_justified_epoch_le_of_causal_honest_target_minimal
            cfg ext hA hwalkDomain hw hHm hselectedKnown hIH hi hqs hsm
            hsH hvote htarget hnotJResult
        simpa only [query, trace, get_block_epoch, hblocksAgree] using hbound
      · have hsq : s < E.slot_at cfg (n + 1) := Nat.lt_of_not_ge hqs
        have hbracket := hvoteBracket i hi s k a hs0 hsq hsm hsH
          hvote htarget
        by_contra hnot
        have habove : get_block_epoch cfg (E.store cfg ext w m)
            trace.result <
            (E.store cfg ext w m).justified_checkpoint.epoch := by
          have hnot' : ¬ (E.store cfg ext w m).justified_checkpoint.epoch ≤
              get_block_epoch cfg query.store trace.result := by
            simpa only [query, trace] using hnot
          have hltQ := Nat.lt_of_not_ge hnot'
          simpa only [get_block_epoch, hblocksAgree] using hltQ
        have hJResult := hbracket.above_selected (by
          rw [← hselector.result_eq]
          exact habove)
        have hresultEq : find_latest_confirmed_descendant cfg ext query
            trace.afterObserved = trace.result := by
          simpa only [query, trace] using hselector.result_eq.symm
        exact hnotJResult (by simpa only [hresultEq] using hJResult)
  · obtain ⟨i, hi, s, k, a, hqs, hsm, hsH, hvote, htarget⟩ := hcausal
    have hbound :=
      E.endpoint_justified_epoch_le_of_causal_honest_target_minimal
        cfg ext hA hwalkDomain hw hHm hselectedKnown hIH hi hqs hsm
        hsH hvote htarget hnotJResult
    simpa only [query, trace, get_block_epoch, hblocksAgree] using hbound

/-- The exact strict trace at an actual call supplies the mechanical selected
facts used by every phase cell.  The input epoch dichotomy follows only from
the ordinary block-slot upper bound and the executable selector guard. -/
theorem actualCall_strictSelectedResultMechanicalFacts
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n)) :
    StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  have hquery : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hinput' : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, trace] using hinput
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hinputUpper : get_block_epoch cfg query.store trace.afterObserved ≤
      get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (by
      rw [hquery]
      simpa only [E.store_current_slot] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          v (n + 1) trace.afterObserved
            (by simpa only [hquery] using hinput'))
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    rcases Nat.eq_or_lt_of_le hinputUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_iff.mpr hlt) hselector.input_recent)
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)
  have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hHn1
    query hquery trace.afterObserved hinput' hinputEpoch hstrict
  rw [← hselector.result_eq] at hfacts
  simpa only [query, trace] using hfacts

/-! ## Epoch-start previous-result canonicity

A strict previous-epoch result does not in general become canonical
retroactively over the part of the current epoch before a mid-epoch query.
The paper therefore uses direct GU/SIR.4 evidence in that branch.  At an
epoch-start call, however, the actual query second is the first second of
epoch `e+1`, so the existing query-indexed endpoint IH really does cover the
whole A3.2 canonicity interval. -/

/-- At an epoch-start actual FCR call, the existing endpoint IH supplies all
of the next epoch for a previous-epoch result.  Knownness is derived from the
concrete confirmation at the boundary, never from totalized ancestry. -/
theorem StrictSelectedResultMechanicalFacts.canonicalThroughoutNextEpoch_of_previousEpochStart
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {input selected : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input selected)
    {e : Epoch}
    (hprevious : e + 1 = get_current_store_epoch cfg
      (E.store cfg ext v (n + 1)))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true)
    {w : ValidatorIndex} {m : Nat}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt
      cfg ext (n + 1) selected m) :
    E.CanonicalThroughoutEpoch cfg ext selected (e + 1) := by
  have hadvance : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n) := by
    unfold IsFCRCallAt at hcall
    simpa only [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] using hcall
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hn1H hadvance
  have hqBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg (e + 1) := by
    have hzero : compute_slots_since_epoch_start cfg
        (E.slot_at cfg (n + 1)) = 0 := by
      simpa only [is_start_slot_at_epoch, decide_eq_true_eq,
        E.store_current_slot cfg ext v (n + 1)] using hstart
    have hboundary : E.slot_at cfg (n + 1) =
        compute_start_slot_at_epoch cfg
          (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
      simp only [compute_slots_since_epoch_start,
        compute_start_slot_at_epoch] at hzero ⊢
      exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hzero)
        (Nat.div_mul_le_self _ cfg.slots_per_epoch)
    simpa only [get_current_store_epoch,
      E.store_current_slot cfg ext v (n + 1), hprevious] using hboundary
  intro w' hw' m' hm'H hm'Epoch
  have hslotLower : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m' := by
    rw [hqBoundary]
    have hboundaryLe : compute_start_slot_at_epoch cfg (e + 1) ≤
        E.slot_at cfg m' := by
      simpa only [compute_start_slot_at_epoch, ← hm'Epoch] using
        Nat.div_mul_le_self (E.slot_at cfg m') cfg.slots_per_epoch
    exact hboundaryLe
  have hqLeM' : n + 1 ≤ m' := by
    have hlower := E.query_slot_start_le_of_slot_ge_minimal
      cfg ext hA hslotLower
    simpa only [hstartEq] using hlower
  have hselectedStart : selected ∈
      (E.store cfg ext w'
        (E.slot_start cfg (E.slot_at cfg (n + 1)))).block_roots :=
    E.confirmed_known_at_query_slot_start_minimal cfg ext hA
      v hv (n + 1) (E.fcrStep cfg ext v n)
      (E.fcrStep_store cfg ext v n) selected hn1H
      (by simpa only [E.fcrStep_store] using h.result_known)
      (by simpa only [E.fcrStep_store] using h.parent_known)
      h.confirmed w' hw'
  have hselectedAtQ : selected ∈
      (E.store cfg ext w' (n + 1)).block_roots := by
    simpa only [hstartEq] using hselectedStart
  have hselectedM' : selected ∈
      (E.store cfg ext w' m').block_roots :=
    (E.store_storeLE cfg ext w' hqLeM').1 hselectedAtQ
  have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch,
      E.store_current_slot cfg ext w m]
  have hslotUpper : E.slot_at cfg m' < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg m' :=
      Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m) ≤
      compute_epoch_at_slot cfg (E.slot_at cfg m') at hepochLe
    rw [hmEpoch, hm'Epoch] at hepochLe
    have hbad : Nat.succ (e + 1) ≤ e + 1 := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.reduceAdd] using hlate.trans hepochLe
    exact (Nat.not_succ_le_self (e + 1)) hbad
  exact ⟨hselectedM', hcanonical w' hw' m'
    (by simpa only [hstartEq] using hqLeM')
    hslotUpper hm'H⟩

/-! ## Mid-epoch previous-result direct GU seed

Paper Lemma 43 does not use A3.2.  If a strict selector advances to a
previous-epoch result away from the epoch boundary, its exact previous-loop
or tentative-loop entry guard exposes a query-known descendant whose
unrealized justification has epoch at least the result epoch.  The accepted
store projection identifies that executable UJ with semantic GU. -/

/-- Query-local Lemma-43 seed for a strict mid-epoch previous result.

The previous-loop guard may name either `previous_slot_head` or the query
head; the tentative-loop guard names the query head.  Both are kept as real
roots with concrete query ancestry. -/
theorem StrictSelectedResultMechanicalFacts.previousOffStart_queryGUEpochSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input selected : Root}
    (hinput : input ∈ (E.fcrStep cfg ext v n).store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext
      (E.fcrStep cfg ext v n) input = selected)
    (hstrict : selected ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input selected)
    (hprevious : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        selected + 1 =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.fcrStep cfg ext v n).store) ≠ true) :
    ∃ seed : Root,
      seed ∈ (E.fcrStep cfg ext v n).store.block_roots ∧
        is_ancestor (E.fcrStep cfg ext v n).store
          (get_node_for_root seed) (get_node_for_root selected) = true ∧
        get_block_epoch cfg (E.fcrStep cfg ext v n).store selected ≤
          (B.state.GU seed).epoch := by
  let query := E.fcrStep cfg ext v n
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    simpa only [query, E.fcrStep_store] using
      E.store_causal cfg ext v (n + 1)
  obtain ⟨hparent, hwalk, _hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv (n + 1) hn1H
  have hparentQ : ParentSlotLt query.store := by
    simpa only [query, E.fcrStep_store] using hparent
  have hwalkQ : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.fcrStep_store] using hwalk
  have hheadKnown : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    simpa only [query, E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hn1H
  have hpreviousHeadKnown : query.previous_slot_head ∈
      query.store.block_roots := by
    simpa only [query] using E.fcrStep_previousSlotHead_known cfg ext
      hT.genesis hdomain v hv n hn1H
  have hheadSelected : is_ancestor query.store
      (get_head cfg query.store) (get_node_for_root selected) = true := by
    have hstrict' : find_latest_confirmed_descendant cfg ext query input ≠
        input := by
      simpa only [query, hout] using hstrict
    simpa only [query, hout] using
      strictSelectedResult_below_head cfg ext hparentQ hwalkQ
        hheadKnown (by simpa only [query] using hinput) hstrict'
  have hprojection :=
    Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection
      B hqueryCausal
  have lower_of_raw {seed : Root}
      (hseed : seed ∈ query.store.block_roots)
      (hraw : (query.store.unrealized_justifications seed).epoch + 1 ≥
        get_current_store_epoch cfg query.store) :
      get_block_epoch cfg query.store selected ≤
        (B.state.GU seed).epoch := by
    have hguEq : query.store.unrealized_justifications seed =
        B.state.GU seed := hprojection.unrealized_justification seed hseed
    apply Nat.le_of_add_le_add_right
    calc
      get_block_epoch cfg query.store selected + 1 =
          get_current_store_epoch cfg query.store := by
        simpa only [query] using hprevious
      _ ≤ (query.store.unrealized_justifications seed).epoch + 1 := hraw
      _ = (B.state.GU seed).epoch + 1 := by rw [hguEq]
  rcases h.trace_origin with
      ⟨_a, _hedge, hentry, _hrecent, hpreviousDesc⟩ |
      ⟨_a, _hedge, hentry, _hfinal⟩
  · rcases hentry.2.2 with hstart | ⟨_noConflict, hgu⟩
    · exact False.elim (hnotStart hstart)
    · rcases hgu with hpreviousGU | hheadGU
      · exact ⟨query.previous_slot_head, hpreviousHeadKnown,
          hpreviousDesc,
          lower_of_raw hpreviousHeadKnown hpreviousGU⟩
      · exact ⟨(get_head cfg query.store).root, hheadKnown,
          hheadSelected, lower_of_raw hheadKnown hheadGU⟩
  · rcases hentry with hstart | hheadGU
    · exact False.elim (hnotStart hstart)
    · exact ⟨(get_head cfg query.store).root, hheadKnown,
        hheadSelected, lower_of_raw hheadKnown hheadGU⟩

/-- Narrow derived outcome for one selected result at one causal endpoint.

`justifiedCovers` retains result knownness explicitly because the cover arm
has no retained carrier from which to recover it.  The `retained` arm keeps
the finalized equation indexed by the carrier's exact tip, preventing a
certificate on some unrelated store root from being substituted. -/
inductive AcceptedSelectedResultFilterOutcomeAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (endpoint : Store Root) (glc : Root) : Prop where
  | justifiedCovers
      (result_known : glc ∈ endpoint.block_roots)
      (covers : is_ancestor endpoint
        (get_node_for_root endpoint.justified_checkpoint.root)
        (get_node_for_root glc) = true)
  | retained
      (carrier : E.AcceptedRetainedPhaseSourceCarrierAt
        cfg ext B endpoint glc)
      (result_descends_justified : is_ancestor endpoint
        (get_node_for_root glc)
        (get_node_for_root endpoint.justified_checkpoint.root) = true)
      (finalized_check :
        endpoint.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
          endpoint.finalized_checkpoint.root =
            get_checkpoint_block cfg endpoint carrier.tip
              endpoint.finalized_checkpoint.epoch)
  | retainedVisible
      (result_known : glc ∈ endpoint.block_roots)
      (tip : Root)
      (tip_known : tip ∈ endpoint.block_roots)
      (tip_descends_result : is_ancestor endpoint
        (get_node_for_root tip) (get_node_for_root glc) = true)
      (tip_is_leaf : endpoint.block_roots.filter
        (fun r => (endpoint.blocks r).parent_root = tip) = [])
      (result_descends_justified : is_ancestor endpoint
        (get_node_for_root glc)
        (get_node_for_root endpoint.justified_checkpoint.root) = true)
      (source_eq_justified :
        (get_voting_source cfg endpoint tip).epoch =
          endpoint.justified_checkpoint.epoch)
      (finalized_check :
        endpoint.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
          endpoint.finalized_checkpoint.root =
            get_checkpoint_block cfg endpoint tip
              endpoint.finalized_checkpoint.epoch)

/-! ## Late historical A3.2 source visibility

The late branch is genuinely different from the three early phase cells.
Assumption A3.2 supplies an old seed whose source sees the endpoint justified
epoch; it does not supply the numeric `source + 2 >= current` bound at an
arbitrarily late endpoint.  The branch therefore targets the
`retainedVisible` outcome arm above rather than pretending that the early
retained carrier remains recent. -/

private theorem AcceptedBlockAt.executionRoot_for_lateSelectedSupply
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Materialize a retained historical payload at its current selected tip in
the exact query store.  This is ordinary accepted-root reflection plus the
trusted boundary walk; no endpoint or safety fact occurs here. -/
theorem AcceptedHistoricalA32LineageCoreAt.payloadAtQuery_nonempty
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {selected : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B selected e
      Cert Supp)
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hsuppT : B.state.C selected e = B.state.C hlineage.origin e →
      B.state.GJ selected = B.state.GJ hlineage.origin →
      Supp hlineage.origin e → Supp selected e) :
    Nonempty (E.AcceptedHistoricalA32GatePayloadCoreAt
      cfg ext B selected e Cert Supp) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  let query := E.store cfg ext v q
  have hqueryCausal : E.CausalStore cfg ext query := by
    simpa only [query] using E.store_causal cfg ext v q
  have hqueryParent : ParentSlotLt query := by
    simpa only [query] using E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled v q
  have hselectedQ' : selected ∈ query.block_roots := by
    simpa only [query] using hselectedQ
  have horiginRoot : E.ExecutionRoot hlineage.origin :=
    hlineage.payload.origin_at.executionRoot_for_lateSelectedSupply cfg ext
  have horiginReflection :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      hselectedQ horiginRoot hlineage.descends
  have horiginQ : hlineage.origin ∈ query.block_roots := by
    simpa only [query] using horiginReflection.1
  have hselectedOrigin : is_ancestor query
      (get_node_for_root selected)
      (get_node_for_root hlineage.origin) = true := by
    simpa only [query] using horiginReflection.2
  have horiginAtQ : E.AcceptedBlockAt cfg ext hlineage.origin
      (query.blocks hlineage.origin) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal horiginQ
  have horiginBlocks : hlineage.payload.origin_block =
      query.blocks hlineage.origin :=
    hlineage.payload.origin_at.unique cfg ext E hT.wellFormed horiginAtQ
  have horiginEpoch : get_block_epoch cfg query hlineage.origin = e := by
    simpa only [get_block_epoch, ← horiginBlocks] using
      hlineage.payload.origin_epoch
  have hselectedEpoch' : get_block_epoch cfg query selected = e := by
    simpa only [query] using hselectedEpoch
  have hanchorLeE : B.anchor.epoch ≤ e := hlineage.payload.anchor_epoch_le
  have hselectedWalk : WalkKnown query
      (compute_start_slot_at_epoch cfg e) selected := by
    simpa only [query] using
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v q hanchorLeE hselectedQ
  exact ⟨hlineage.payloadAtTip cfg ext hphase0 hqueryCausal hqueryParent
    horiginQ hselectedQ' horiginEpoch hselectedEpoch' hselectedOrigin
      hselectedWalk hsuppT⟩

/-- Eager instantiation of the query-store materialization.  The support
obligation transports by the same one-line re-indexing it always did. -/
theorem AcceptedHistoricalA32LineageAt.payloadAtQuery_nonempty
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {selected : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e) :
    Nonempty (E.AcceptedHistoricalA32GatePayloadAt
      cfg ext B selected e) :=
  AcceptedHistoricalA32LineageCoreAt.payloadAtQuery_nonempty cfg ext B hT
    hphase0 hanchor hboundary hlineage hselectedQ hselectedEpoch
    (fun hcheckpoint hsource hsupp w hw m hmH hlate =>
      AcceptedHistoricalA32GatePayloadCoreAt.quorumDisjunction_transport
        cfg ext hcheckpoint hsource (hsupp w hw m hmH hlate))

/-- A retained historical A3.2 payload produces one source-visible seed at a
late honest endpoint.  The anchor support arm is discharged directly from
accepted AU certification; the non-anchor arm realizes the retained concrete
quorum through the paper assumption.

This is the **support-branch-free** form: it takes the anchor-or-quorum
disjunction at the *tip* as a plain hypothesis, so that the eager trunk can
supply it from the payload field and the lazy trunk can manufacture it at the
consuming call (`docs/crossing-call-support-residue.md` §4.3). -/
theorem acceptedHistoricalA32LateVisibleSeed_of_support
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext selected (e + 1))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e)
    (hsupport : B.state.C selected e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B selected e)) :
    ∃ seed : Root,
      seed ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root seed) (get_node_for_root selected) = true ∧
        SourceVisibleAtTip cfg (E.store cfg ext w m) seed := by
  have hendpointCausal : E.CausalStore cfg ext
      (E.store cfg ext w m) := E.store_causal cfg ext w m
  rcases hsupport with htargetAnchor | hquorum
  · have heq : e = B.anchor.epoch := by
      have hepoch := congrArg Checkpoint.epoch htargetAnchor
      simpa only [B.state.checkpoint_epoch] using hepoch
    have hsourceAU := hendpointCausal.getVotingSource_AU
      cfg ext B hselectedM
    obtain ⟨hsourceIncluded⟩ :=
      B.state.includedJustifiedAtTip_of_AU cfg ext hsourceAU
    have hanchorLeSource : B.anchor.epoch ≤
        (get_voting_source cfg (E.store cfg ext w m) selected).epoch :=
      IncludedCertifiedJustified.anchor_epoch_le
        (cfg := cfg) hsourceIncluded
    refine ⟨selected, hselectedM,
      is_ancestor_refl (E.store cfg ext w m)
        (get_node_for_root selected), ?_⟩
    exact ⟨hjustifiedEpoch.trans (by
      simpa only [heq] using hanchorLeSource)⟩
  · obtain ⟨hQ⟩ := hquorum
    rcases hQ with ⟨deadline, target, Q, hdeadline, htarget,
      _htargetNeAnchor, hsource⟩
    subst deadline
    subst target
    have hsourceQuery : Q.source =
        B.state.VSAt cfg ext (E.store cfg ext v q) selected e := by
      simpa only [AcceptedChainFFGState.VSAt, hselectedEpoch,
        if_pos] using hsource
    have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
      E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
        cfg ext B hT hanchor hboundary
    have hboundarySlot : compute_start_slot_at_epoch cfg (e + 2) ≤
        E.slot_at cfg m := by
      have hepoch : e + 2 ≤
          compute_epoch_at_slot cfg (E.slot_at cfg m) := by
        simpa only [get_current_store_epoch,
          E.store_current_slot cfg ext w m] using hlate
      simpa only [compute_start_slot_at_epoch] using
        (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hepoch
    obtain ⟨seed, hincluded⟩ :=
      E.accepted_paperA32IncludedAtTip_of_concreteQuorum cfg ext
        hT.wellFormed hT.honest_behavior hsync hT.externals_coherence
        hT.whole_seconds hT.genesis hwalkDomain
        B.coherence.toAcceptedFFGSelectorCoherence hpaper
        hv hqH hselectedQ hselectedEpoch hcanonical Q hsourceQuery
        hw hmH hboundarySlot
    exact ⟨seed, hincluded.executable.seed_known,
      hincluded.executable.seed_descends_selected,
      hincluded.executable.sourceVisible cfg hlate hjustifiedEpoch⟩

/-- Eager instantiation: the retained payload's own `support_branch` field
supplies the disjunction the late seed construction needs. -/
theorem AcceptedHistoricalA32LineageAt.lateVisibleSeedAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext selected (e + 1))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e) :
    ∃ seed : Root,
      seed ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root seed) (get_node_for_root selected) = true ∧
        SourceVisibleAtTip cfg (E.store cfg ext w m) seed := by
  obtain ⟨hpayload⟩ := hlineage.payloadAtQuery_nonempty cfg ext B hT
    hphase0 hanchor hboundary hselectedQ hselectedEpoch
  exact E.acceptedHistoricalA32LateVisibleSeed_of_support cfg ext B hT hsync
    hanchor hboundary hpaper hv hqH hselectedQ hselectedEpoch hcanonical
    hw hmH hselectedM hlate hjustifiedEpoch
    (hpayload.support_branch w hw m hmH hlate)

/-- Accepted global-finalized provenance supplies the executable finalized
boundary at every concrete store.  This is the accepted-state counterpart of
the older migration-state trajectory theorem and prevents the late branch
from taking finalized geometry as a free premise. -/
theorem ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (w : ValidatorIndex) (m : Nat) :
    FinalizedBoundaryRealization cfg (E.store cfg ext w m) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  let store := E.store cfg ext w m
  have hstoreCausal : E.CausalStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext w m
  have hparent : ParentSlotLt store := by
    simpa only [store] using E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled w m
  rcases B.globalFinalized_anchor_or_AUEvidence hgenShort hanchor
      hstoreCausal with hfinalizedAnchor | hevidence
  · have hanchorRoot : B.anchor.root = ablk.root := by
      have hr := congrArg Checkpoint.root hanchor
      rw [hgen] at hr
      simpa only [get_forkchoice_store] using hr
    have hanchorKnown : B.anchor.root ∈ store.block_roots := by
      have hknown0 : B.anchor.root ∈ E.genesis_store.block_roots := by
        rw [hgen, hanchorRoot]
        simp only [get_forkchoice_store, List.mem_singleton]
      simpa only [store] using
        (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hknown0
    have hanchorBlock : store.blocks B.anchor.root = ablk.message := by
      have hablkKnown : ablk.root ∈
          (E.store cfg ext w m).block_roots := by
        simpa only [← hanchorRoot, store] using hanchorKnown
      have hablkBlock :=
        E.store_anchor_block cfg ext hT.wellFormed hgen w m hablkKnown
      simpa only [store, hanchorRoot] using hablkBlock
    have hboundary' : ablk.message.slot ≤
        compute_start_slot_at_epoch cfg B.anchor.epoch := by
      simpa only [TrustedAnchorBoundaryAligned, hgen, hanchorRoot,
        get_forkchoice_store, Function.update_self] using hboundary
    refine {
      finalized_root_known := ?_
      finalized_root_slot_le_boundary := ?_ }
    · simpa only [store, hfinalizedAnchor] using hanchorKnown
    · simpa only [store, hfinalizedAnchor, hanchorBlock] using hboundary'
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hcertificate⟩ := carrier.formed_evidence.certified
    have hglobal : CertifiedJustified cfg E B.anchor
        store.finalized_checkpoint :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedIncludedAttestationRelation.relation
          cfg ext E B.state.includedAttestations) hcertificate
    have hanchorLe : B.anchor.epoch ≤
        store.finalized_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hglobal
    have hwalk : WalkKnown store
        (compute_start_slot_at_epoch cfg
          store.finalized_checkpoint.epoch) carrier.tip := by
      simpa only [store] using
        E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
          hanchor hboundary w m hanchorLe carrier.tip_carrier.known
    have hrootKnown : store.finalized_checkpoint.root ∈
        store.block_roots :=
      carrier.checkpointRoot_known B.coherence hstoreCausal hparent hwalk
    have hcheckpoint := B.coherence.au_checkpoint_of_known
      hstoreCausal carrier.tip carrier.tip_carrier.known
        store.finalized_checkpoint carrier.au
    have hroot : store.finalized_checkpoint.root =
        get_checkpoint_block cfg store carrier.tip
          store.finalized_checkpoint.epoch := by
      have hr := congrArg Checkpoint.root hcheckpoint
      simpa only [get_checkpoint_for_block] using hr
    have hspec := get_ancestor_spec hparent hwalk
    have hslotCheckpoint :
        (store.blocks (get_checkpoint_block cfg store carrier.tip
          store.finalized_checkpoint.epoch)).slot ≤
            compute_start_slot_at_epoch cfg
              store.finalized_checkpoint.epoch := by
      simpa only [get_checkpoint_block] using hspec.2
    rw [← hroot] at hslotCheckpoint
    refine {
      finalized_root_known := hrootKnown
      finalized_root_slot_le_boundary := ?_ }
    simpa only [store] using hslotCheckpoint

/-- A query-local Lemma-43 GU seed produces the complete late endpoint
outcome without invoking paper A3.2.

Epoch separation gives a full relay slot and forces the endpoint executable
selector to read `GU(seed)`.  The local SIR orientation `J.epoch ≤ e` then
turns the retained `e ≤ GU(seed).epoch` bound into source visibility. -/
noncomputable def
    acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {selected seed : Root} {e : Epoch}
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hseedQ : seed ∈ (E.store cfg ext v q).block_roots)
    (hseedSelected : is_ancestor (E.store cfg ext v q)
      (get_node_for_root seed) (get_node_for_root selected) = true)
    (hguLower : e ≤ (B.state.GU seed).epoch)
    (hqueryEpoch : get_current_store_epoch cfg
      (E.store cfg ext v q) = e + 1)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  let query := E.store cfg ext v q
  let endpoint := E.store cfg ext w m
  have hqueryCausal : E.CausalStore cfg ext query := by
    simpa only [query] using E.store_causal cfg ext v q
  have hendpointCausal : E.CausalStore cfg ext endpoint := by
    simpa only [endpoint] using E.store_causal cfg ext w m
  obtain ⟨hqueryParent, hqueryWalk, _hqueryJustified⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv q hqH
  obtain ⟨hendpointParent, hendpointWalk, hendpointJustified⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hmH
  have hendpointParent' : ParentSlotLt endpoint := by
    simpa only [endpoint] using hendpointParent
  have hendpointWalk' : ∀ t ∈ endpoint.block_roots,
      ∀ r ∈ endpoint.block_roots,
        WalkKnown endpoint (endpoint.blocks t).slot r := by
    simpa only [endpoint] using hendpointWalk
  have hendpointJustified' : endpoint.justified_checkpoint.root ∈
      endpoint.block_roots := by
    simpa only [endpoint] using hendpointJustified
  have hqEpoch : compute_epoch_at_slot cfg (E.slot_at cfg q) = e + 1 := by
    simpa only [query, get_current_store_epoch,
      E.store_current_slot cfg ext v q] using hqueryEpoch
  have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      get_current_store_epoch cfg endpoint := by
    simp only [endpoint, get_current_store_epoch,
      E.store_current_slot cfg ext w m]
  have hslotLt : E.slot_at cfg q < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg q := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m) ≤
      compute_epoch_at_slot cfg (E.slot_at cfg q) at hepochLe
    rw [hmEpoch, hqEpoch] at hepochLe
    have hbad : Nat.succ (e + 1) ≤ e + 1 := by
      simpa only [endpoint, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.reduceAdd] using hlate.trans hepochLe
    exact (Nat.not_succ_le_self (e + 1)) hbad
  have hrelayGate : E.slot_at cfg q + 1 ≤ E.slot_at cfg (m + 1) :=
    (Nat.succ_le_of_lt hslotLt).trans
      (E.slot_at_mono cfg (Nat.le_succ m))
  have hseedM : seed ∈ endpoint.block_roots := by
    simpa only [query, endpoint] using hsync.block_relay
      v hv q seed hqH hseedQ w hw m hmH hrelayGate
  have hqueryParent' : ParentSlotLt query := by
    simpa only [query] using hqueryParent
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor (E.blockProvenance cfg ext v q)
      hqueryParent'
      (by
        simpa only [query] using hqueryWalk selected hselectedQ seed hseedQ)
      (by simpa only [query] using hseedSelected)
  have hselectedRoot : E.ExecutionRoot selected :=
    (E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal
      (by simpa only [query] using hselectedQ)
      ).executionRoot_for_lateSelectedSupply cfg ext
  obtain ⟨hselectedM, hseedSelectedM⟩ :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      (by simpa only [endpoint] using hseedM) hselectedRoot hsemantic
  have hseedBlockAgree : query.blocks seed = endpoint.blocks seed :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m)
      (by simpa only [query] using hseedQ)
      (by simpa only [endpoint] using hseedM)
  have hseedEpochLeQ : get_block_epoch cfg query seed ≤
      get_current_store_epoch cfg query := by
    simp only [get_block_epoch, get_current_store_epoch]
    exact Nat.div_le_div_right
      (E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        hgenShort v q seed (by simpa only [query] using hseedQ))
  have hseedOld : get_block_epoch cfg endpoint seed <
      get_current_store_epoch cfg endpoint := by
    calc
      get_block_epoch cfg endpoint seed =
          get_block_epoch cfg query seed := by
        simp only [get_block_epoch, hseedBlockAgree]
      _ ≤ get_current_store_epoch cfg query := hseedEpochLeQ
      _ = e + 1 := by simpa only [query] using hqueryEpoch
      _ < e + 2 := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.reduceAdd] using Nat.lt_succ_self (e + 1)
      _ ≤ get_current_store_epoch cfg endpoint := by
        simpa only [endpoint] using hlate
  have hsourceGU : get_voting_source cfg endpoint seed = B.state.GU seed := by
    have hselector := hendpointCausal.getVotingSource_eq_acceptedSelector
      cfg ext B (by simpa only [endpoint] using hseedM)
    simpa only [if_pos hseedOld] using hselector
  have hseedVisible : SourceVisibleAtTip cfg endpoint seed := by
    refine ⟨?_⟩
    calc
      endpoint.justified_checkpoint.epoch ≤ e := by
        simpa only [endpoint] using hjustifiedEpoch
      _ ≤ (B.state.GU seed).epoch := hguLower
      _ = (get_voting_source cfg endpoint seed).epoch := by rw [hsourceGU]
  have hnonfuture : BlocksSlotLe
      (get_current_slot cfg endpoint) endpoint := by
    simpa only [endpoint] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        hgenShort w m
  have hpersistence : VotingSourceEpochChainPersistence cfg endpoint :=
    E.acceptedVotingSourceEpochChainPersistence cfg ext B hendpointCausal
      hendpointParent'
      (E.blockProvenance cfg ext w m)
      hendpointWalk' hnonfuture
  obtain ⟨tip, htipKnown, _htipWalk, htipSeed, htipLeaf,
      htipVisible⟩ :=
    exists_visible_store_leaf_extension cfg
      hendpointParent' hpersistence
      hseedM hseedVisible
  have htipSelected : is_ancestor endpoint
      (get_node_for_root tip) (get_node_for_root selected) = true :=
    is_ancestor_trans hendpointParent'
      (hendpointWalk' selected hselectedM tip htipKnown)
      (hendpointWalk' selected hselectedM seed hseedM)
      htipSeed hseedSelectedM
  have hsourceLe : (get_voting_source cfg endpoint tip).epoch ≤
      endpoint.justified_checkpoint.epoch :=
    B.causalVotingSource_epoch_le_justified hT.whole_seconds hgenShort
      hanchor hendpointCausal htipKnown
  have hsourceEq : (get_voting_source cfg endpoint tip).epoch =
      endpoint.justified_checkpoint.epoch :=
    Nat.le_antisymm hsourceLe htipVisible.justified_epoch_le_source
  have htipJustified : is_ancestor endpoint
      (get_node_for_root tip)
      (get_node_for_root endpoint.justified_checkpoint.root) = true :=
    is_ancestor_trans hendpointParent'
      (hendpointWalk' endpoint.justified_checkpoint.root
        hendpointJustified' tip htipKnown)
      (hendpointWalk' endpoint.justified_checkpoint.root
        hendpointJustified' selected hselectedM)
      htipSelected (by simpa only [endpoint] using hselectedJustified)
  have hfinalized : FinalizedBoundaryRealization cfg endpoint := by
    simpa only [endpoint] using
      Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
        cfg ext B hT hanchor hboundary w m
  let hplace : RetainedFilterTipPlacement cfg endpoint selected :=
    { tip := tip
      tip_known := htipKnown
      tip_descends_justified := htipJustified
      tip_descends_child := htipSelected
      tip_is_leaf := htipLeaf
      finalized_walk_known :=
        hfinalized.finalizedWalkKnown cfg hendpointWalk' htipKnown }
  have hfinalizedCheck : endpoint.finalized_checkpoint.root =
      get_checkpoint_block cfg endpoint tip
        endpoint.finalized_checkpoint.epoch := by
    have hcheck := hplace.finalizedRoot_eq_checkpointBlock_of_acceptedVisible
      cfg ext B hgenShort hanchor P V hanchorExact hacc
        hendpointCausal hendpointParent' htipVisible
    simpa only [hplace] using hcheck
  exact .retainedVisible hselectedM tip htipKnown htipSelected htipLeaf
    (by simpa only [endpoint] using hselectedJustified)
    hsourceEq (Or.inr hfinalizedCheck)

/-- Complete actual-call Lemma-43 branch for a strict previous-epoch result
selected away from epoch start.  This path uses the executable GU seed above
and never invokes paper A3.2 or full-epoch canonicity. -/
noncomputable def
    StrictSelectedResultMechanicalFacts.fcrStep_previousOffStart_late_endpointFilterOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input selected : Root}
    (hinput : input ∈ (E.fcrStep cfg ext v n).store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext
      (E.fcrStep cfg ext v n) input = selected)
    (hstrict : selected ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input selected)
    (hprevious : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        selected + 1 =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.fcrStep cfg ext v n).store) ≠ true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hlate : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        selected + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg (E.fcrStep cfg ext v n).store selected)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨seed, hseedQ, hseedSelected, hguLower⟩ :=
    h.previousOffStart_queryGUEpochSeed cfg ext B hT hdomain
      hv hn1H hinput hout hstrict hprevious hnotStart
  exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed
    cfg ext B hT hsync hdomain hanchor hboundary P V hanchorExact hacc
      hv hn1H
      (by simpa only [E.fcrStep_store] using h.result_known)
      (by simpa only [E.fcrStep_store] using hseedQ)
      (by simpa only [E.fcrStep_store] using hseedSelected)
      hguLower
      (by simpa only [E.fcrStep_store] using hprevious.symm)
      hw hmH hlate hjustifiedEpoch hselectedJustified

/-- Complete late endpoint outcome from a retained historical A3.2 support
disjunction.  A visible seed is extended to a finite childless descendant;
accepted justified maximality turns visibility into the exact source/J epoch
equality required by the executable filter, and accepted global-finalized
provenance places finality on that same leaf.

The anchor-or-quorum disjunction enters as a plain hypothesis, so both the
eager trunk (which reads it off the payload) and the lazy trunk (which
manufactures it from origin-call data at the consuming call) share this
proof. -/
noncomputable def acceptedSelectedResultFilterOutcome_retainedVisible_of_lateSupport
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hsupport : B.state.C selected e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B selected e))
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext selected (e + 1))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  let endpoint := E.store cfg ext w m
  have hendpointCausal : E.CausalStore cfg ext endpoint := by
    simpa only [endpoint] using E.store_causal cfg ext w m
  have hparent : ParentSlotLt endpoint := by
    simpa only [endpoint] using E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ endpoint.block_roots,
      ∀ r ∈ endpoint.block_roots,
        WalkKnown endpoint (endpoint.blocks t).slot r := by
    simpa only [endpoint] using
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ w m
  have hnonfuture : BlocksSlotLe
      (get_current_slot cfg endpoint) endpoint := by
    simpa only [endpoint] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        hgenShort w m
  obtain ⟨seed, hseedKnown, hseedSelected, hseedVisible⟩ :=
    E.acceptedHistoricalA32LateVisibleSeed_of_support cfg ext B hT hsync
      hanchor hboundary hpaper hv hqH hselectedQ hselectedEpoch hcanonical
      hw hmH hselectedM hlate hjustifiedEpoch hsupport
  have hpersistence : VotingSourceEpochChainPersistence cfg endpoint :=
    E.acceptedVotingSourceEpochChainPersistence cfg ext B hendpointCausal
      hparent (E.blockProvenance cfg ext w m) hwalkK hnonfuture
  obtain ⟨tip, htipKnown, _htipWalk, htipSeed, htipLeaf,
      htipVisible⟩ :=
    exists_visible_store_leaf_extension cfg hparent hpersistence
      (by simpa only [endpoint] using hseedKnown)
      (by simpa only [endpoint] using hseedVisible)
  have htipSelected : is_ancestor endpoint
      (get_node_for_root tip) (get_node_for_root selected) = true :=
    is_ancestor_trans hparent
      (hwalkK selected (by simpa only [endpoint] using hselectedM)
        tip htipKnown)
      (hwalkK selected (by simpa only [endpoint] using hselectedM)
        seed (by simpa only [endpoint] using hseedKnown))
      htipSeed (by simpa only [endpoint] using hseedSelected)
  have hsourceLe : (get_voting_source cfg endpoint tip).epoch ≤
      endpoint.justified_checkpoint.epoch :=
    B.causalVotingSource_epoch_le_justified hT.whole_seconds hgenShort
      hanchor hendpointCausal htipKnown
  have hsourceEq : (get_voting_source cfg endpoint tip).epoch =
      endpoint.justified_checkpoint.epoch :=
    Nat.le_antisymm hsourceLe htipVisible.justified_epoch_le_source
  have htipJustified : is_ancestor endpoint
      (get_node_for_root tip)
      (get_node_for_root endpoint.justified_checkpoint.root) = true :=
    is_ancestor_trans hparent
      (hwalkK endpoint.justified_checkpoint.root
        (by
          have hdomain := E.store_domainK_of_selectedMarginDomain
            cfg ext hT.wellFormed hT.externals_coherence
              ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
              hdomain w hw m hmH
          exact hdomain.2.2)
        tip htipKnown)
      (hwalkK endpoint.justified_checkpoint.root
        (by
          have hdomain := E.store_domainK_of_selectedMarginDomain
            cfg ext hT.wellFormed hT.externals_coherence
              ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
              hdomain w hw m hmH
          exact hdomain.2.2)
        selected (by simpa only [endpoint] using hselectedM))
      htipSelected (by simpa only [endpoint] using hselectedJustified)
  have hfinalized : FinalizedBoundaryRealization cfg endpoint := by
    simpa only [endpoint] using
      Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
        cfg ext B hT hanchor hboundary w m
  let hplace : RetainedFilterTipPlacement cfg endpoint selected :=
    { tip := tip
      tip_known := htipKnown
      tip_descends_justified := htipJustified
      tip_descends_child := htipSelected
      tip_is_leaf := htipLeaf
      finalized_walk_known :=
        hfinalized.finalizedWalkKnown cfg hwalkK htipKnown }
  have hfinalizedCheck : endpoint.finalized_checkpoint.root =
      get_checkpoint_block cfg endpoint tip
        endpoint.finalized_checkpoint.epoch := by
    have hcheck := hplace.finalizedRoot_eq_checkpointBlock_of_acceptedVisible
      cfg ext B hgenShort hanchor P V hanchorExact hacc
        hendpointCausal hparent htipVisible
    simpa only [hplace] using hcheck
  exact .retainedVisible
    (by simpa only [endpoint] using hselectedM) tip htipKnown
    htipSelected htipLeaf
    (by simpa only [endpoint] using hselectedJustified)
    hsourceEq (Or.inr hfinalizedCheck)

/-- Eager instantiation of the late retained outcome: the lineage's own
payload supplies the anchor-or-quorum disjunction.  This is the form both
trunks' dispatchers already call. -/
noncomputable def acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (hselectedQ : selected ∈ (E.store cfg ext v q).block_roots)
    (hselectedEpoch : get_block_epoch cfg
      (E.store cfg ext v q) selected = e)
    (hcanonical : E.CanonicalThroughoutEpoch cfg ext selected (e + 1))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨hpayload⟩ := hlineage.payloadAtQuery_nonempty cfg ext B hT
    hphase0 hanchor hboundary hselectedQ hselectedEpoch
  exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_lateSupport
    cfg ext B hT hsync hdomain hanchor hboundary hpaper P V hanchorExact hacc
    hv hqH (hpayload.support_branch w hw m hmH hlate) hselectedQ
    hselectedEpoch hcanonical hw hmH hselectedM hlate hjustifiedEpoch
    hselectedJustified

/-! ## Early retained-outcome scaffold

The previous and current/next phase producers both end in the same
consumer-shaped fact: `RecentSourceSeedAt` in the concrete endpoint.  The
next theorem performs only the common mechanical tail.  It extends that seed
to a retained accepted leaf, uses the accepted causal finalization-lag theorem
to place finality on the exact same leaf, and packages the retained outcome.

Justified/result orientation is intentionally an input to this local tail.
The final dispatcher derives it inside the strict-edge lambda from the
endpoint justification-origin split and its existing earlier-head induction;
it is not a public safety premise or a generic cross-store monotonicity law. -/

/-- Common retained tail for every early recent-source branch.

No lineage, filter fact, margin, safety conclusion, source visibility, or free
finalized placement occurs in the interface. -/
noncomputable def acceptedSelectedResultFilterOutcome_retained_of_carrier
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {w : ValidatorIndex} {m : Nat} {selected : Root}
    (carrier : E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B
      (E.store cfg ext w m) selected)
    (hparent : ParentSlotLt (E.store cfg ext w m))
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
    E.causalRealizedFinalizationLag_of_acceptedDelay
      cfg ext B hT hanchor hDelay
  have hfinalizedBoundary : FinalizedBoundaryRealization cfg
      (E.store cfg ext w m) :=
    Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
      cfg ext B hT hanchor hboundary w m
  have hfinalized := carrier.finalizedRoot_eq_checkpointBlock_of_causalLag
    cfg ext hgenShort hanchor hLag P V hanchorExact hacc
      hfinalizedBoundary hparent hwalkK
  exact .retained carrier hselectedJustified (Or.inr hfinalized)

/-- Turn an endpoint recent seed into the carrier consumed by the common
retained tail above. -/
noncomputable def acceptedSelectedResultFilterOutcome_retained_of_recentSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {w : ValidatorIndex} {m : Nat}
    {selected : Root}
    (hselectedEndpoint : selected ∈
      (E.store cfg ext w m).block_roots)
    (hparent : ParentSlotLt (E.store cfg ext w m))
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    (hnonfuture : BlocksSlotLe
      (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hrecent : RecentSourceSeedAt cfg
      (E.store cfg ext w m) selected)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨seed, hseedKnown, hseedSelected, hseedRecent⟩ := hrecent
  let carrier := E.acceptedRetainedPhaseSourceCarrier_of_recentSeed
    cfg ext B (E.store_causal cfg ext w m) hparent
      (E.blockProvenance cfg ext w m) hwalkK hnonfuture
      hselectedEndpoint hseedKnown hseedSelected hseedRecent
  exact E.acceptedSelectedResultFilterOutcome_retained_of_carrier
    cfg ext B hT hanchor hboundary hDelay P V hanchorExact hacc
      carrier hparent hwalkK hselectedJustified

/-- Actual-call previous-result branch of the endpoint outcome dispatcher.

The strict-edge geometry derives the endpoint index order; it is not exposed
as a separate premise.  Confirmation derives selected-root knownness at the
endpoint, the existing previous-phase producer supplies source recency, and
the common historical-lineage tail supplies finality on the same retained
tip. -/
noncomputable def StrictSelectedResultMechanicalFacts.fcrStep_previous_endpointFilterOutcome
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {input result : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input result)
    (hprevious : get_block_epoch cfg
        (E.fcrStep cfg ext v n).store result + 1 =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : StrictSelectedEdgeGeometry cfg ext E result r0 a c
      v (n + 1) (E.fcrStep cfg ext v n) w m
        lo es sigma querySlot)
    (hresultJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) result := by
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m := by
    rw [hgeom.confirming_cutoff]
    exact Nat.succ_le_of_lt
      (hgeom.cutoff_le_sigma.trans_lt hgeom.sigma_lt_endpoint)
  have hnm : n + 1 ≤ m :=
    hgeom.actualCall_queryIndex_le_endpoint cfg ext hcall
  have hselectedEndpoint : result ∈
      (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hMargin
      v hv (n + 1) (E.fcrStep cfg ext v n)
      (E.fcrStep_store cfg ext v n) result hn1H
      (by simpa only [E.fcrStep_store] using h.result_known)
      (by simpa only [E.fcrStep_store] using h.parent_known)
      h.confirmed w hw m hslotQM hmH
  obtain ⟨hparent, hwalkK, _hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hmH
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hnonfuture : BlocksSlotLe
      (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hgenSlot⟩ w m
  have hrecent : RecentSourceSeedAt cfg
      (E.store cfg ext w m) result :=
    h.fcrStep_previous_endpointRecentSourceSeed cfg ext hT hsync hstatic
      hbyz hdomain B hv hn1H hcall hprevious hw hmH hnm hsameEpoch
  exact E.acceptedSelectedResultFilterOutcome_retained_of_recentSeed
    cfg ext B hT hanchor hboundary hDelay P V hanchorExact hacc
      hselectedEndpoint hparent hwalkK hnonfuture hrecent
      hresultJustified

/-- Actual-call current-result / same-epoch endpoint branch.

The callback-free Lemma-26 history theorem chooses the executable recent
carrier (including its justified-fallback subcase).  Accepted causal
finalization lag then places finality on that same carrier without a selected
historical-lineage premise. -/
noncomputable def
    StrictSelectedResultMechanicalFacts.fcrStep_currentSame_endpointFilterOutcome
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.getLatestConfirmedTraceAt cfg ext v n).result)
    (hcurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : StrictSelectedEdgeGeometry cfg ext E
      (E.getLatestConfirmedTraceAt cfg ext v n).result r0 a c
      v (n + 1) (E.fcrStep cfg ext v n) w m
        lo es sigma querySlot)
    (hresultJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.getLatestConfirmedTraceAt cfg ext v n).result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m)
        (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m := by
    rw [hgeom.confirming_cutoff]
    exact Nat.succ_le_of_lt
      (hgeom.cutoff_le_sigma.trans_lt hgeom.sigma_lt_endpoint)
  have hselectedEndpoint :
      (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
        (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hMargin
      v hv (n + 1) (E.fcrStep cfg ext v n)
      (E.fcrStep_store cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).result hn1H
      (by simpa only [E.fcrStep_store] using h.result_known)
      (by simpa only [E.fcrStep_store] using h.parent_known)
      h.confirmed w hw m hslotQM hmH
  have hhistory := h.actualCurrentSame_sourceHistoryOutcome cfg ext B hT
    hsync hstatic hbyz hdomain hanchor hboundary hDelay hspe
      hv hn1H hcall hcurrent
  have hselectedQuery :
      (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
        (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using h.result_known
  have hcurrentStore : get_block_epoch cfg
        (E.store cfg ext v (n + 1))
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.fcrStep_store] using hcurrent
  have hsameStore : get_current_store_epoch cfg
        (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.fcrStep_store] using hsameEpoch
  obtain ⟨carrier⟩ := hhistory.retainedAt_currentSameEndpoint cfg ext
    hT hsync hanchor hboundary P V hanchorExact hdomain
      hselectedQuery hcurrentStore hw hmH hslotQM hsameStore
      hselectedEndpoint
  obtain ⟨hparent, hwalkK, _hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hmH
  exact E.acceptedSelectedResultFilterOutcome_retained_of_carrier
    cfg ext B hT hanchor hboundary hDelay P V hanchorExact hacc
      carrier hparent hwalkK hresultJustified

/-- Actual-call current-result / next-epoch branch of the endpoint outcome
dispatcher.

The existing Lemma-13 source producer performs the cross-epoch relay.  This
wrapper derives endpoint selected-root knownness from the concrete
confirmation and then sends that recent source through the same retained-tip
historical-finality tail as the previous branch. -/
noncomputable def StrictSelectedResultMechanicalFacts.fcrStep_currentNext_endpointFilterOutcome
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input result : Root}
    (hinput : input ∈ (E.fcrStep cfg ext v n).store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext
      (E.fcrStep cfg ext v n) input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input result)
    (hcurrent : get_block_epoch cfg
        (E.fcrStep cfg ext v n).store result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store + 1)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : StrictSelectedEdgeGeometry cfg ext E result r0 a c
      v (n + 1) (E.fcrStep cfg ext v n) w m
        lo es sigma querySlot)
    (hresultJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) result := by
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m := by
    rw [hgeom.confirming_cutoff]
    exact Nat.succ_le_of_lt
      (hgeom.cutoff_le_sigma.trans_lt hgeom.sigma_lt_endpoint)
  have hselectedEndpoint : result ∈
      (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hMargin
      v hv (n + 1) (E.fcrStep cfg ext v n)
      (E.fcrStep_store cfg ext v n) result hn1H
      (by simpa only [E.fcrStep_store] using h.result_known)
      (by simpa only [E.fcrStep_store] using h.parent_known)
      h.confirmed w hw m hslotQM hmH
  obtain ⟨hparent, hwalkK, _hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hmH
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hnonfuture : BlocksSlotLe
      (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hgenSlot⟩ w m
  have hrecent : RecentSourceSeedAt cfg
      (E.store cfg ext w m) result :=
    h.fcrStep_currentNext_endpointRecentSourceSeed cfg ext hT hsync
      hstatic hbyz hdomain B hv hn1H hinput hout hstrict hcurrent
        hw hmH hnextEpoch
  exact E.acceptedSelectedResultFilterOutcome_retained_of_recentSeed
    cfg ext B hT hanchor hboundary hDelay P V hanchorExact hacc
      hselectedEndpoint hparent hwalkK hnonfuture hrecent
      hresultJustified

/-! ## Exhaustive actual-call endpoint dispatcher -/

/-- Read the lineage's semantic epoch back in any causal execution store
which knows its tip.  This is the small adapter needed when the completed
prefix invariant existentially packages the lineage epoch. -/
theorem AcceptedHistoricalA32LineageAt.tip_epoch_eq_of_causal_known
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {store : Store Root} {selected : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32LineageAt cfg ext B selected e)
    (hcausal : E.CausalStore cfg ext store)
    (hknown : selected ∈ store.block_roots) :
    get_block_epoch cfg store selected = e := by
  have hselectedAt : E.AcceptedBlockAt cfg ext selected
      (store.blocks selected) :=
    E.acceptedBlockAt_of_causal_known cfg ext hcausal hknown
  have htipBlock : h.tip_block = store.blocks selected :=
    h.tip_at.unique cfg ext E hT.wellFormed hselectedAt
  simpa only [get_block_epoch, ← htipBlock] using h.tip_epoch

/-- Exhaustive endpoint outcome for one actual strict selector result.

The proof splits first on whether the selected result is current or previous
in the query store and then on the endpoint epoch.  Early cells use the
paper's Lemma-13/Lemma-26/Lemma-43 retained-source arguments.  Late current
and epoch-start previous cells use accepted historical A3.2 lineage; the
mid-epoch previous cell uses its direct GU seed.  The epoch-start previous
origin split is operational and exhaustive: carried, finalized-reset, and
observed-reset inputs each use their dedicated accepted producer. -/
noncomputable def
    StrictSelectedResultMechanicalFacts.fcrStep_endpointFilterOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (horigin : OrderedCandidateInputOrigin cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n))
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n))
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.getLatestConfirmedTraceAt cfg ext v n).result)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : StrictSelectedEdgeGeometry cfg ext E
      (E.getLatestConfirmedTraceAt cfg ext v n).result r0 a c
      v (n + 1) (E.fcrStep cfg ext v n) w m
        lo es sigma querySlot)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.getLatestConfirmedTraceAt cfg ext v n).result)
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
      (E.getLatestConfirmedTraceAt cfg ext v n).result m)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m)
      (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  let hMargin : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.static_validators
      byzantine_bound := hC.byzantine_bound
      domain := hdomain }
  have hacc : CheckpointCertificateAccountability cfg E B.anchor :=
    CheckpointCertificateAccountability.of_assumptions cfg
      (SelectedMarginAssumptions.toFFGAccountabilityAssumptions
        cfg ext E hMargin)
  have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
    E.causalRealizedFinalizationLag_of_acceptedDelay
      cfg ext B hT hanchor hDelay
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m := by
    rw [hgeom.confirming_cutoff]
    exact Nat.succ_le_of_lt
      (hgeom.cutoff_le_sigma.trans_lt hgeom.sigma_lt_endpoint)
  have hstartM : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hMargin hslotQM
  have hselectedM : trace.result ∈
      (E.store cfg ext w m).block_roots := by
    exact hselectedKnown w hw m hstartM hmH
  have hresultJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root trace.result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true := by
    exact (E.actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified
      cfg ext B hT hC hfit hdomain hanchor hboundary hv hcall hn1H hprior
      hinput hbase hselector hw hmH hslotQM hcM
      (by simpa only [trace] using hselectedC) hselectedKnown hIH
      hnotCovered).2
  have hjustifiedEpoch :
      (E.store cfg ext w m).justified_checkpoint.epoch ≤
        get_block_epoch cfg (E.fcrStep cfg ext v n).store trace.result := by
    exact E.actualCall_strictSelected_endpointJustifiedEpoch_le_result
      cfg ext B hT hC hfit hdomain hanchor hboundary hv hcall hn1H hprior
      hinput hbase hselector hw hmH hslotQM hcM
      (by simpa only [trace] using hselectedC) hselectedKnown hIH
      hnotCovered
  have hqueryEpochLeEndpoint :
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store ≤
        get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.fcrStep_store,
      E.store_current_slot, compute_epoch_at_slot]
    exact Nat.div_le_div_right hslotQM
  rcases h.current_or_previous_epoch with hcurrent | hprevious
  · by_cases hsame : get_current_store_epoch cfg (E.store cfg ext w m) =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store
    · exact h.fcrStep_currentSame_endpointFilterOutcome cfg ext hT
        hC.synchrony hC.static_validators hC.byzantine_bound hdomain B
        hanchor hboundary hDelay hspe P V hanchorExact hacc hv hn1H
        hcall hcurrent hw hmH hsame hgeom
        (by simpa only [trace] using hresultJustified)
    · by_cases hnext : get_current_store_epoch cfg (E.store cfg ext w m) =
          get_current_store_epoch cfg (E.fcrStep cfg ext v n).store + 1
      · exact h.fcrStep_currentNext_endpointFilterOutcome cfg ext hT
          hC.synchrony hC.static_validators hC.byzantine_bound hdomain B
          hanchor hboundary hDelay P V hanchorExact hacc hv hn1H
          hinput hselector.result_eq.symm hselector.result_ne_input
          hcurrent hw hmH hnext hgeom
          (by simpa only [trace] using hresultJustified)
      · have hlate : get_block_epoch cfg
            (E.fcrStep cfg ext v n).store trace.result + 2 ≤
          get_current_store_epoch cfg (E.store cfg ext w m) := by
          have hqLt : get_current_store_epoch cfg
                (E.fcrStep cfg ext v n).store <
              get_current_store_epoch cfg (E.store cfg ext w m) :=
            Nat.lt_of_le_of_ne hqueryEpochLeEndpoint
              (fun heq => hsame heq.symm)
          have hqNextLe : get_current_store_epoch cfg
                (E.fcrStep cfg ext v n).store + 1 ≤
              get_current_store_epoch cfg (E.store cfg ext w m) := hqLt
          have hqNextNe : get_current_store_epoch cfg
                (E.fcrStep cfg ext v n).store + 1 ≠
              get_current_store_epoch cfg (E.store cfg ext w m) :=
            fun heq => hnext heq.symm
          have hqNextLt : get_current_store_epoch cfg
                (E.fcrStep cfg ext v n).store + 1 <
              get_current_store_epoch cfg (E.store cfg ext w m) :=
            Nat.lt_of_le_of_ne hqNextLe hqNextNe
          rw [hcurrent]
          simpa only [Nat.add_assoc, Nat.reduceAdd] using hqNextLt
        have hwrite : E.confirmed cfg ext v (n + 1) = trace.result := by
          exact (E.confirmed_succ_of_advance cfg ext v n hcall).trans
            trace.result_eq.symm
        have hcurrentConfirmed : get_block_epoch cfg
              (E.store cfg ext v (n + 1))
              (E.confirmed cfg ext v (n + 1)) =
            get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
          rw [hwrite]
          simpa only [trace, E.fcrStep_store] using hcurrent
        obtain ⟨e, ⟨hlineageConfirmed⟩⟩ :=
          E.acceptedHistoricalA32CurrentLineage_of_completedPrefixes
            cfg ext B hT hC hfit hanchor hboundary hv hn1H
              hcurrentConfirmed
        have hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B
            trace.result e := by
          simpa only [hwrite] using hlineageConfirmed
        have hselectedQ : trace.result ∈
            (E.store cfg ext v (n + 1)).block_roots := by
          simpa only [trace, E.fcrStep_store] using h.result_known
        have hselectedEpoch : get_block_epoch cfg
            (E.store cfg ext v (n + 1)) trace.result = e :=
          hlineage.tip_epoch_eq_of_causal_known cfg ext hT
            (E.store_causal cfg ext v (n + 1)) hselectedQ
        have heCurrent : e = get_current_store_epoch cfg
            (E.store cfg ext v (n + 1)) := by
          exact hselectedEpoch.symm.trans
            (by simpa only [trace, E.fcrStep_store] using hcurrent)
        have hcanonical : E.CanonicalThroughoutEpoch cfg ext
            trace.result (e + 1) :=
          E.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch
            cfg ext hMargin hv hn1H hselectedQ heCurrent
              (by simpa only [trace, E.fcrStep_store, hselectedEpoch]
                using hlate) hIH
        exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage
          cfg ext B hT hC.synchrony hdomain hC.phase0_source hanchor
            hboundary hpaper P V hanchorExact hacc hv hn1H hlineage
            hselectedQ hselectedEpoch hcanonical hw hmH
            (by simpa only [trace] using hselectedM)
            (by simpa only [trace, E.fcrStep_store, hselectedEpoch]
              using hlate)
            (by simpa only [trace, E.fcrStep_store, hselectedEpoch]
              using hjustifiedEpoch)
            (by simpa only [trace] using hresultJustified)
  · by_cases hsame : get_current_store_epoch cfg (E.store cfg ext w m) =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store
    · exact h.fcrStep_previous_endpointFilterOutcome cfg ext hT
        hC.synchrony hC.static_validators hC.byzantine_bound hdomain B
        hanchor hboundary hDelay P V hanchorExact hacc hv hn1H hcall
        hprevious hw hmH hsame hgeom
        (by simpa only [trace] using hresultJustified)
    · have hlate : get_block_epoch cfg
          (E.fcrStep cfg ext v n).store trace.result + 2 ≤
        get_current_store_epoch cfg (E.store cfg ext w m) := by
        have hqLt : get_current_store_epoch cfg
              (E.fcrStep cfg ext v n).store <
            get_current_store_epoch cfg (E.store cfg ext w m) :=
          Nat.lt_of_le_of_ne hqueryEpochLeEndpoint
            (fun heq => hsame heq.symm)
        calc
          get_block_epoch cfg (E.fcrStep cfg ext v n).store
                trace.result + 2 =
              (get_block_epoch cfg (E.fcrStep cfg ext v n).store
                trace.result + 1) + 1 := by
                  simp only [Nat.add_assoc, Nat.reduceAdd]
          _ = get_current_store_epoch cfg
                (E.fcrStep cfg ext v n).store + 1 := by rw [hprevious]
          _ ≤ get_current_store_epoch cfg (E.store cfg ext w m) := hqLt
      by_cases hstart : is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.fcrStep cfg ext v n).store) = true
      · have hpreviousQ : get_block_epoch cfg
              (E.store cfg ext v (n + 1)) trace.result + 1 =
            get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
          simpa only [trace, E.fcrStep_store] using hprevious
        have hstartN1 : is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1))) = true := by
          simpa only [E.fcrStep_store] using hstart
        have hcanonicalFor
            {e : Epoch}
            (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B
              trace.result e) :
            E.CanonicalThroughoutEpoch cfg ext trace.result (e + 1) := by
          have hselectedEpoch : get_block_epoch cfg
              (E.store cfg ext v (n + 1)) trace.result = e :=
            hlineage.tip_epoch_eq_of_causal_known cfg ext hT
              (E.store_causal cfg ext v (n + 1))
              (by simpa only [trace, E.fcrStep_store] using h.result_known)
          exact h.canonicalThroughoutNextEpoch_of_previousEpochStart
            cfg ext hMargin hv hn1H hcall
              (by simpa only [hselectedEpoch] using hpreviousQ)
              (by simpa only [E.fcrStep_store] using hstart)
              (by simpa only [trace, E.fcrStep_store, hselectedEpoch]
                using hlate) hIH
        have lateFromLineage
            {e : Epoch}
            (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B
              trace.result e) :
            E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
              (E.store cfg ext w m) trace.result := by
          have hselectedQ : trace.result ∈
              (E.store cfg ext v (n + 1)).block_roots := by
            simpa only [trace, E.fcrStep_store] using h.result_known
          have hselectedEpoch : get_block_epoch cfg
              (E.store cfg ext v (n + 1)) trace.result = e :=
            hlineage.tip_epoch_eq_of_causal_known cfg ext hT
              (E.store_causal cfg ext v (n + 1)) hselectedQ
          exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage
            cfg ext B hT hC.synchrony hdomain hC.phase0_source hanchor
              hboundary hpaper P V hanchorExact hacc hv hn1H hlineage
              hselectedQ hselectedEpoch (hcanonicalFor hlineage) hw hmH
              (by simpa only [trace] using hselectedM)
              (by simpa only [trace, E.fcrStep_store, hselectedEpoch]
                using hlate)
              (by simpa only [trace, E.fcrStep_store, hselectedEpoch]
                using hjustifiedEpoch)
              (by simpa only [trace] using hresultJustified)
        cases horigin with
        | carried hcarried =>
            obtain ⟨hlineage⟩ :=
              Execution.StrictSelectorAdvanceAt.previousCarried_epochStartLineage
                cfg ext B hT hC hfit hdomain hanchor hboundary hv hn1H hcall
                  hstartN1 hcarried hselector hprevious
            exact lateFromLineage hlineage
        | finalizedReset hfinalized =>
            obtain ⟨hlineage⟩ :=
              Execution.StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage
                cfg ext B hT hdomain hanchor hboundary hLag hanchorExact hv
                  hn1H hfinalized hselector hprevious
            exact lateFromLineage hlineage
        | observedReset hobserved =>
            obtain ⟨seed, hseedQ, hseedSelected, hguLower⟩ :=
              Execution.StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed
                cfg ext B hT hdomain hanchor hboundary hv hn1H hobserved
                  hselector hprevious
            exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed
              cfg ext B hT hC.synchrony hdomain hanchor hboundary P V
                hanchorExact hacc hv hn1H
                (by simpa only [trace, E.fcrStep_store] using h.result_known)
                (by simpa only [E.fcrStep_store] using hseedQ)
                (by simpa only [trace, E.fcrStep_store] using hseedSelected)
                hguLower
                (by simpa only [trace, E.fcrStep_store] using hprevious.symm)
                hw hmH
                (by simpa only [trace, E.fcrStep_store] using hlate)
                (by simpa only [trace, E.fcrStep_store] using hjustifiedEpoch)
                (by simpa only [trace] using hresultJustified)
      · exact h.fcrStep_previousOffStart_late_endpointFilterOutcome
          cfg ext B hT hC.synchrony hdomain hanchor hboundary P V
            hanchorExact hacc hv hn1H hinput hselector.result_eq.symm
            hselector.result_ne_input hprevious hstart hw hmH hlate
            hjustifiedEpoch
            (by simpa only [trace] using hresultJustified)

namespace AcceptedSelectedResultFilterOutcomeAt

/-- Eliminate one endpoint outcome at an arbitrary non-covered strict edge.

The returned statement is exactly the membership required by
`SelectedStrictEdgeFilterSupplyAt`; no edge-specific source-history argument
is repeated. -/
theorem child_filtered
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {endpoint : Store Root} {glc parent child : Root}
    (h : E.AcceptedSelectedResultFilterOutcomeAt cfg ext B endpoint glc)
    (hfinalized : FinalizedBoundaryRealization cfg endpoint)
    (hparent : ParentSlotLt endpoint)
    (hwalkK : ∀ t ∈ endpoint.block_roots,
      ∀ r ∈ endpoint.block_roots,
        WalkKnown endpoint (endpoint.blocks t).slot r)
    (hjustifiedKnown : endpoint.justified_checkpoint.root ∈
      endpoint.block_roots)
    (hchildKnown : child ∈ endpoint.block_roots)
    (hparentEdge : (endpoint.blocks child).parent_root = parent)
    (hresultChild : is_ancestor endpoint
      (get_node_for_root glc) (get_node_for_root child) = true)
    (hnotCovered : is_ancestor endpoint
      (get_node_for_root endpoint.justified_checkpoint.root)
      (get_node_for_root child) ≠ true) :
    ForkChoiceNode.mk child ∈
      get_node_children endpoint (get_filtered_block_tree cfg endpoint)
        (ForkChoiceNode.mk parent) := by
  cases h with
  | justifiedCovers hresultKnown hcovers =>
      have hcoveredChild : is_ancestor endpoint
          (get_node_for_root endpoint.justified_checkpoint.root)
          (get_node_for_root child) = true :=
        is_ancestor_trans hparent
          (hwalkK child hchildKnown endpoint.justified_checkpoint.root
            hjustifiedKnown)
          (hwalkK child hchildKnown glc hresultKnown)
          hcovers hresultChild
      exact False.elim (hnotCovered hcoveredChild)
  | retained carrier hresultJustified hfinalizedCheck =>
      have hchildJustified : is_ancestor endpoint
          (get_node_for_root child)
          (get_node_for_root endpoint.justified_checkpoint.root) = true := by
        rcases is_ancestor_comparable hparent
            (hwalkK endpoint.justified_checkpoint.root hjustifiedKnown
              glc carrier.selected_known)
            (hwalkK child hchildKnown glc carrier.selected_known)
            hresultJustified hresultChild with
          hforward | hreverse
        · exact hforward
        · exact False.elim (hnotCovered hreverse)
      obtain ⟨hcertificate⟩ :=
        carrier.filterTipCertificate_retarget_ancestor cfg ext
          hfinalized hparent hwalkK hjustifiedKnown hchildKnown
          hresultChild hchildJustified hnotCovered hfinalizedCheck
      exact hcertificate.child_filtered cfg hparentEdge
  | retainedVisible hresultKnown tip htipKnown htipResult htipLeaf
      hresultJustified hsourceEq hfinalizedCheck =>
      have htipChild : is_ancestor endpoint
          (get_node_for_root tip) (get_node_for_root child) = true :=
        is_ancestor_trans hparent
          (hwalkK child hchildKnown tip htipKnown)
          (hwalkK child hchildKnown glc hresultKnown)
          htipResult hresultChild
      have htipJustified : is_ancestor endpoint
          (get_node_for_root tip)
          (get_node_for_root endpoint.justified_checkpoint.root) = true :=
        is_ancestor_trans hparent
          (hwalkK endpoint.justified_checkpoint.root hjustifiedKnown
            tip htipKnown)
          (hwalkK endpoint.justified_checkpoint.root hjustifiedKnown
            glc hresultKnown)
          htipResult hresultJustified
      let hplace : RetainedFilterTipPlacement cfg endpoint child :=
        { tip := tip
          tip_known := htipKnown
          tip_descends_justified := htipJustified
          tip_descends_child := htipChild
          tip_is_leaf := htipLeaf
          finalized_walk_known :=
            hfinalized.finalizedWalkKnown cfg hwalkK htipKnown }
      obtain ⟨hskel, htipEq⟩ :=
        SelectedFilterChainGeometry.exists_filterTipSkeleton_of_placement
          cfg hparent hwalkK hjustifiedKnown hchildKnown hnotCovered hplace
      let hcertificate : FilterTipCertificate cfg endpoint child :=
        { mids := hskel.mids
          tip := hskel.tip
          chain := hskel.chain
          child_on_chain := hskel.child_on_chain
          tip_is_leaf := hskel.tip_is_leaf
          parent_slot_lt := hskel.parent_slot_lt
          justified_ok := Or.inr (Or.inl (by
            simpa only [htipEq] using hsourceEq))
          finalized_ok := by
            simpa only [htipEq] using hfinalizedCheck }
      exact hcertificate.child_filtered cfg hparentEdge

end AcceptedSelectedResultFilterOutcomeAt

/-! ## Final strict-edge filter supplier -/

/-- Complete filter supply for the strict branch of one actual FCR call.

Every quantified endpoint edge is sent through the exhaustive phase
dispatcher above.  The resulting endpoint-level certificate is then
retargeted to the concrete child edge.  Thus the public supplier exposes no
free filter-membership, source-visibility, finalized-placement, lineage,
orientation, checkpoint-epoch, or canonicity premise. -/
noncomputable def
    StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (horigin : OrderedCandidateInputOrigin cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n))
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n)) :
    E.SelectedStrictEdgeFilterSupplyAt cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).result
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      v (n + 1) (E.fcrStep cfg ext v n) := by
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hmechanical := E.actualCall_strictSelectedResultMechanicalFacts
    cfg ext hT hC.synchrony hC.static_validators hC.byzantine_bound
      hdomain hv hn1H hinput hselector
  intro a c w m lo es sigma querySlot hw hmH hgeom _hcne hcM
    hparentEdge hselectedC hselectedKnown hIH hnotCovered
  have houtcome := hmechanical.fcrStep_endpointFilterOutcome cfg ext B hT
    hC hfit hdomain hanchor hboundary hDelay hspe hpaper P V hanchorExact
      hv hn1H hcall hprior hinput hbase horigin hselector hw hmH hgeom hcM
      hselectedC hselectedKnown hIH hnotCovered
  have hfinalized : FinalizedBoundaryRealization cfg
      (E.store cfg ext w m) :=
    Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
      cfg ext B hT hanchor hboundary w m
  obtain ⟨hparent, hwalkK, hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hmH
  exact houtcome.child_filtered cfg ext hfinalized hparent hwalkK
    hjustifiedKnown hcM hparentEdge hselectedC hnotCovered

end Execution


end FastConfirmation.Spec
