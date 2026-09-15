import FastConfirmation.Spec.Proof.WeakPreQuerySIR
import FastConfirmation.Spec.Proof.WeakHistoricalA32Step
import FastConfirmation.Spec.Proof.WeakHistoricalA32CallSupplier
import FastConfirmation.Spec.Proof.WeakSelectedStrictEdgeFilterSupply

/-!
# Spec / Proof / WeakSelectedJustifiedOrientation

Stage S8 of the `hfilter`-discharge wave: the observer-side twins of
`AcceptedSelectedJustifiedOrientation.lean`'s three producer wrappers and of
the two actual-call facts the weak phase dispatcher still carries as residual
inputs

* `Weak.ObserverStrictCallFilterInputsAt.result_descends_endpoint_justified`,
  the observer twin of
  `Execution.actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified`
  (`AcceptedActualSelectedJustifiedOrientation.lean`);
* `Weak.ObserverStrictCallFilterInputsAt.endpoint_justified_epoch_le_result`,
  the observer twin of
  `Execution.actualCall_strictSelected_endpointJustifiedEpoch_le_result`
  (`AcceptedSelectedStrictEdgeFilterSupply.lean`).

## What this module does and does not change

Everything below the pre-query SIR bracket has already been re-proved at a
possibly-Byzantine observer in `WeakPreQuerySIR.lean` (stage S8a): the two
receiver-side relays are gone, replaced by one
`Execution.is_ancestor_replay_closed`, and the query-node instantiation of the
honest-quantified input safety is gone, replaced by
`Weak.strictSelectedResult_below_head`.  The producer layer is
`WeakHistoricalA32CallSupplier.lean`.  This module is the *assembly*: it
threads those two layers through the strong, honesty-free endpoint tails

* `Execution.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal`,
* `Execution.endpoint_justified_epoch_le_of_causal_honest_target_minimal`,
* `Execution.known_descends_trustedAnchor`,

all of which are stated at the *honest endpoint* `(w, m)` and never mention
the query node's honesty.

## The one premise that stays

`hbase : E.SafeFrom cfg ext input (E.slot_start cfg (E.slot_at cfg (n + 1)))`
is **kept**, exactly as in the strong development.  Stage S8a established that
`hbase` is not only used at the query node (that use is removed): it is also
instantiated at the *honest endpoint* `w` by
`Execution.preQueryVote_belowInput_of_safeInput`, where nothing about a
Byzantine observer weakens it.  It is not a new assumption — it is the outer
safety induction's carried input-safety hypothesis, the same one the strong
actual-call theorem takes, and the caller supplies it from the fold.

## The producer that is still a premise

`hhistorical : E.AcceptedHistoricalA32PayloadProducerAt …` is taken as an
explicit argument rather than built here.  Its observer-side construction is
the A3.2 write-back induction over `E.weakConfirmed`
(`WeakHistoricalA32Induction.lean`), which is the same object the residual
record's `current_lineage` / `previous_epochStart_carried_lineage` fields
need; keeping it a premise here means this module's content — the assembly —
is independent of that induction's progress.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-! ## The weak historical-A3.2 producer interface

`Execution.AcceptedHistoricalA32PayloadProducerAt`
(`AcceptedHistoricalA32Payload.lean`) is **not** reusable at the weak
evaluator: its no-crossing hypothesis names the strong
`CurrentTargetAcceptedEdge`, hence the strong `findLatestSelectedTrace`.  A
Byzantine observer runs `Weak.findLatestSelectedTrace` (rule delta 1 drops the
discount), so the two propositions are different and there is no bridge in the
direction the producer needs.  The weak interface below is the same statement
over `Weak.CurrentTargetAcceptedEdge` (`WeakHistoricalA32Step.lean`); the
*payload* it produces, `Execution.AcceptedHistoricalA32GatePayloadAt`, is
evaluator-free and reused unchanged. -/

/-- Weak twin of `Execution.AcceptedHistoricalA32PayloadProducerAt`: the
no-crossing side condition is stated over the weak selector's own tentative
edge list. -/
def HistoricalA32PayloadProducerAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (query : FastConfirmationStore Root) (input result : Root) : Prop :=
  get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store →
  (¬ ∃ a c : Root, Weak.CurrentTargetAcceptedEdge cfg ext query input a c) →
    ∃ e : Epoch,
      get_current_target cfg query.store = B.state.C result e ∧
      Nonempty (E.AcceptedHistoricalA32GatePayloadAt cfg ext B result e)

/-- Observer twin of
`Execution.epochStart_or_endpointCurrentTargetPinned_of_acceptedCallSite`.

Only two things change.  The call-site classifier is stage S8a's weak
inductive, whose two executable gates are the *weak* rule booleans, so each is
converted to the strong one the accepted producers consume by the stage-B8
bridges `will_current_target_be_justified_of_weak` /
`will_no_conflicting_of_weak` (`WeakRulePredicateBridge.lean`) — both are
one-directional weak ⇒ strong, which is exactly the direction needed here.
And the historical arm consumes the weak producer interface above instead of
the strong one.  The accountability step
(`CertificateAccountability.justified_unique`) and the endpoint certificate
(`ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate`) are read at
the honest endpoint's store and are reused verbatim. -/
theorem epochStart_or_endpointCurrentTargetPinned_of_observerCallSite
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {q : Nat} {query : FastConfirmationStore Root}
    {input result : Root} {store : Store Root}
    (hstore : E.CausalStore cfg ext store)
    (hcall : Weak.StrictSelectedHistoricalSIRCallSite cfg ext E q query
      input result)
    (hacc : CertificateAccountability cfg E B.anchor)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      query input result)
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query) :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
      (store.justified_checkpoint.epoch =
          (get_current_target cfg query.store).epoch →
        store.justified_checkpoint.root =
          (get_current_target cfg query.store).root) := by
  have hcurrent' : E.CurrentTargetCertificateProducerAt
      cfg ext B.anchor q query :=
    E.acceptedCurrentTargetCertificateProducerAt_of_gateProducer
      cfg ext B hcurrent
  obtain ⟨hJ⟩ :=
    Execution.ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate
      cfg ext B hgen hanchor hstore
  cases hcall with
  | currentCrossing _resultCurrent _a _c _mem _lt hgate hsupport =>
      right
      intro hepoch
      obtain ⟨hT⟩ := hcurrent'
        (will_current_target_be_justified_of_weak cfg ext
          query.store hgate) hsupport
      exact hacc.justified_unique hJ hT hepoch
  | currentHistorical hresultCurrent hnone =>
      right
      intro hepoch
      obtain ⟨e, htarget, ⟨hpayload⟩⟩ := hhistorical hresultCurrent hnone
      have hT : CertifiedJustified cfg E B.anchor
          (get_current_target cfg query.store) := by
        rw [htarget]
        exact hpayload.certified.some
      exact hacc.justified_unique hJ hT hepoch
  | previousEpochStart _resultPrevious hstart =>
      exact Or.inl hstart
  | previousNoConflict _resultPrevious _notStart hgate hsupport =>
      right
      intro hepoch
      exact hnoConflict
        (will_no_conflicting_of_weak cfg ext query.store
          (get_current_balance_source query) hgate) hsupport
        store.justified_checkpoint hJ hepoch

/-! ## The three producer wrappers -/

/-- Observer twin of
`Execution.preQueryVoteSelectedSIRBracketAt_of_acceptedProducers`.

The honest-node binder `hv` becomes `E.ObserverCoherence cfg ext obs`; the
call-site classifier and the three-region bracket are stage S8a's observer
twins; `Execution.epochStart_or_endpointCurrentTargetPinned_of_acceptedCallSite`
and `Execution.certificateAccountability_of_selectedMarginAssumptions` are
honesty-free and reused verbatim. -/
theorem preQueryVoteSelectedSIRBracketAt_of_observerProducers
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E obs q query input)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      query input (Weak.find_latest_confirmed_descendant cfg ext query input))
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    E.PreQueryVoteSelectedSIRBracketAt cfg ext q input
      (Weak.find_latest_confirmed_descendant cfg ext query input) w m := by
  intro i hi s k a hs0 hsq _hsm hsH hvote htarget
  have hcall := Weak.strictSelectedHistoricalSIRCallSite cfg ext hA
    hcoh hqH query hquery input hinput hinputEpoch hstrict hprovisos
  have hacc : CertificateAccountability cfg E B.anchor :=
    E.certificateAccountability_of_selectedMarginAssumptions cfg ext hA
  have hstartOrPin :=
    Weak.epochStart_or_endpointCurrentTargetPinned_of_observerCallSite
      cfg ext B hgen hanchor (E.store_causal cfg ext w m)
      hcall hacc hcurrent hhistorical hnoConflict
  exact Weak.selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning
    cfg ext hA hwalkDomain hcoh hqH query hquery input hinput hinputEpoch
      hbase hstrict hw hslotQM hHm hi hs0 hsq hsH hvote htarget
      hstartOrPin

/-- Observer twin of
`Execution.preQuerySelectedJustifiedCompatibilityAt_of_acceptedProducers`. -/
theorem preQuerySelectedJustifiedCompatibilityAt_of_observerProducers
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E obs q query input)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      query input (Weak.find_latest_confirmed_descendant cfg ext query input))
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    E.PreQuerySelectedJustifiedCompatibilityAt cfg ext B.anchor q
      (Weak.find_latest_confirmed_descendant cfg ext query input) w m := by
  have hvoteBracket :=
    Weak.preQueryVoteSelectedSIRBracketAt_of_observerProducers cfg ext hA
      hwalkDomain B hgen hanchor hcoh hqH query hquery input hinput
      hinputEpoch hbase hstrict hprovisos hcurrent hhistorical hnoConflict
      hw hslotQM hHm
  have hbracket := Weak.preQuerySelectedSIRBracketAt_of_voteBracket_strict
    cfg ext hA hanchor hcoh hqH query hquery input hinput hstrict
      hw hslotQM hHm hvoteBracket
  exact Weak.preQuerySelectedJustifiedCompatibilityAt_of_threeRegionBracket
    cfg ext hA hcoh hqH query hquery input hinput hstrict hw hslotQM hHm
      hbracket

/-- Observer twin of
`Execution.strictSelected_result_and_child_ancestor_of_endpointJustified_accepted`.

The endpoint tail
`selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal` is
reused verbatim: every one of its relays leaves from the *honest endpoint*. -/
theorem strictSelected_result_and_child_ancestor_of_endpointJustified_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext obs q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict :
      Weak.find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E obs q query input)
    (hcurrent : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      query input (Weak.find_latest_confirmed_descendant cfg ext query input))
    (hnoConflict : E.NoConflictCertificatePinningProducerAt
      cfg ext B.anchor q query)
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query input))
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      Weak.find_latest_confirmed_descendant cfg ext query input ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (Weak.find_latest_confirmed_descendant cfg ext query input)) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root c)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (Weak.find_latest_confirmed_descendant cfg ext query input))
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hpre :=
    Weak.preQuerySelectedJustifiedCompatibilityAt_of_observerProducers
      cfg ext hA hwalkDomain B hgenShort hanchor hcoh hqH query hquery
      input hinput hinputEpoch hbase hstrict hprovisos hcurrent
      hhistorical hnoConflict hw hslotQM hHm
  have horigin : E.EndpointJustificationOriginAt cfg ext B.anchor w m :=
    Execution.ExactPrefixAcceptedFFGSemantics.endpointJustificationOriginAt
      cfg ext B hT hanchor hboundary
  exact E.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
    cfg ext hA hwalkDomain hw hHm hslotQM hcM hselectedC
      hselectedKnown hIH hpre horigin hnotCovered

/-! ## The two actual-call facts of the residual bundle

Both are stated exactly as the corresponding fields of
`Weak.ObserverStrictCallFilterInputsAt`, so that the final producer can hand
them over directly.  The shared plumbing is the strong wrappers' verbatim: the
input epoch dichotomy from the block-slot upper bound and
`StrictSelectorAdvanceAt.input_recent`, and the rewriting of the trace result
along `hselector.result_eq`. -/

/-- The observer-call form of the two orientation premises, shared by both
theorems below: the query store identity, the input's epoch dichotomy, the
strictness of the selector step, the observer-quantified helper provisos, and
the two accepted producers landed in `WeakHistoricalA32CallSupplier.lean`. -/
private theorem observerCall_orientation_inputs
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    (get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store ∨
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved + 1 =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) ∧
    (Weak.find_latest_confirmed_descendant cfg ext
        (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ≠
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved) ∧
    Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∧
    E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext B.anchor
      B.state (n + 1) (E.weakFcrStep cfg ext obs n) ∧
    E.NoConflictCertificatePinningProducerAt cfg ext B.anchor (n + 1)
      (E.weakFcrStep cfg ext obs n) := by
  have hquery : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hinputUpper : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ≤
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (by
      rw [hquery]
      simpa only [E.store_current_slot] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          obs (n + 1)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
            (by simpa only [hquery] using hinput))
  refine ⟨?_, ?_, hC.observer_helper_provisos n hcall hHn1
      hselector.guard_true,
    E.observerCall_acceptedTargetGateProducerAt cfg ext B hT hC.base hfit
      hanchor hboundary hcoh hcall hHn1,
    E.observerCall_noConflictCertificatePinningProducerAt cfg ext B hT
      hC.base hfit hanchor hboundary hcoh hHn1⟩
  · rcases Nat.eq_or_lt_of_le hinputUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_iff.mpr hlt) hselector.input_recent)
  · intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)

/-- **Observer twin of
`Execution.actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified`**,
stated exactly as
`Weak.ObserverStrictCallFilterInputsAt.result_descends_endpoint_justified`
(second component).

`hC` is the observer-quantified call contract (obligation X1's resolution);
`hbase` is the outer safety induction's carried input safety, as in the strong
theorem; `hhistorical` is the weak historical-A3.2 producer, built by the
observer-side write-back induction. -/
theorem observerCall_strictSelected_result_and_child_ancestor_of_endpointJustified
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.base.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.base.static_validators
      byzantine_bound := hC.base.byzantine_bound
      domain := hdomain }
  have hquery : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  obtain ⟨hinputEpoch, hstrict, hprovisos, hcurrent, hnoConflict⟩ :=
    Weak.observerCall_orientation_inputs cfg ext B hT hC hfit hanchor
      hboundary hcoh hcall hHn1 hinput hselector
  have hhistorical' : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      query trace.afterObserved
      (Weak.find_latest_confirmed_descendant cfg ext query
        trace.afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hselectedC' : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved))
      (get_node_for_root c) = true := by
    rw [← hselector.result_eq]
    exact hselectedC
  have hselectedKnown' : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved ∈
        (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hstart hm'H
    rw [← hselector.result_eq]
    exact hselectedKnown w' hw' m' hstart hm'H
  have hIH' : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (Weak.find_latest_confirmed_descendant cfg ext query
            trace.afterObserved)) = true := by
    intro w' hw' m' hstart hm'Lt hm'H
    rw [← hselector.result_eq]
    exact hIH w' hw' m' hstart hm'Lt hm'H
  have hout :=
    Weak.strictSelected_result_and_child_ancestor_of_endpointJustified_at_observer
      cfg ext hA B hT hanchor hboundary hcoh hHn1 query hquery
      trace.afterObserved hinput hinputEpoch hbase hstrict hprovisos
      hcurrent hhistorical' hnoConflict hw hHm hslotQM hcM hselectedC'
      hselectedKnown' hIH' hnotCovered
  have hsecond := hout.2
  rw [← hselector.result_eq] at hsecond
  exact hsecond

/-- **Observer twin of
`Execution.actualCall_strictSelected_endpointJustifiedEpoch_le_result`**,
stated exactly as
`Weak.ObserverStrictCallFilterInputsAt.endpoint_justified_epoch_le_result`.

The three endpoint-origin arms are the strong ones verbatim — the trusted
anchor bound, the honest-target bound at a post-query vote slot, and the
bracket's `above_selected` region at a pre-query vote slot — because each is
read at the honest endpoint `(w, m)`.  Only the pre-query bracket is the
observer twin. -/
theorem observerCall_strictSelected_endpointJustifiedEpoch_le_result
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hhistorical : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.base.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.base.static_validators
      byzantine_bound := hC.base.byzantine_bound
      domain := hdomain }
  have hquery : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  obtain ⟨hinputEpoch, hstrict, hprovisos, hcurrent, hnoConflict⟩ :=
    Weak.observerCall_orientation_inputs cfg ext B hT hC hfit hanchor
      hboundary hcoh hcall hHn1 hinput hselector
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hhistorical' : Weak.HistoricalA32PayloadProducerAt cfg ext E B
      (E.weakFcrStep cfg ext obs n) (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (Weak.find_latest_confirmed_descendant cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hvoteBracket : E.PreQueryVoteSelectedSIRBracketAt cfg ext
      (n + 1) (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (Weak.find_latest_confirmed_descendant cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved) w m :=
    Weak.preQueryVoteSelectedSIRBracketAt_of_observerProducers cfg ext hA
      hwalkDomain B hgenShort hanchor hcoh hHn1 (E.weakFcrStep cfg ext obs n) hquery
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved hinput
      hinputEpoch hbase hstrict hprovisos hcurrent hhistorical' hnoConflict
      hw hslotQM hHm
  have hmechanical := Weak.strictSelectedResultMechanicalFacts cfg ext hA
    hcoh hHn1 (E.weakFcrStep cfg ext obs n) hquery
    (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved hinput
    hinputEpoch hstrict
  have hresultQ : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
    rw [hselector.result_eq]
    exact hmechanical.result_known
  have hstartM : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM
  have hresultM : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
      (E.store cfg ext w m).block_roots :=
    hselectedKnown w hw m hstartM hHm
  obtain ⟨hparentM, hwalkM, hjustifiedM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hHm
  have hnotJResult : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result) ≠ true := by
    intro hJResult
    apply hnotCovered
    exact is_ancestor_trans hparentM
      (hwalkM c hcM
        (E.store cfg ext w m).justified_checkpoint.root hjustifiedM)
      (hwalkM c hcM (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result hresultM)
      hJResult hselectedC
  have hblocksAgree : (E.weakFcrStep cfg ext obs n).store.blocks
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      (E.store cfg ext w m).blocks (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
    rw [hquery]
    exact hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs (n + 1))
      (E.blockProvenance cfg ext w m)
      (by simpa only [hquery] using hresultQ) hresultM
  have horigin : E.EndpointJustificationOriginAt cfg ext B.anchor w m :=
    Execution.ExactPrefixAcceptedFFGSemantics.endpointJustificationOriginAt
      cfg ext B hT hanchor hboundary
  rcases horigin with hanchorEndpoint |
      ⟨i, hi, s, k, a, hs0, hsm, hsH, hvote, htarget⟩
  · have hbound := (E.known_descends_trustedAnchor cfg ext hA hanchor
      w m hresultM).2
    rw [← hanchorEndpoint] at hbound
    simpa only [get_block_epoch, hblocksAgree] using hbound
  · by_cases hqs : E.slot_at cfg (n + 1) ≤ s
    · have hbound :=
        E.endpoint_justified_epoch_le_of_causal_honest_target_minimal
          cfg ext hA hwalkDomain hw hHm hselectedKnown hIH hi hqs hsm
          hsH hvote htarget hnotJResult
      simpa only [get_block_epoch, hblocksAgree] using hbound
    · have hsq : s < E.slot_at cfg (n + 1) := Nat.lt_of_not_ge hqs
      have hbracket := hvoteBracket i hi s k a hs0 hsq hsm hsH
        hvote htarget
      by_contra hnot
      have habove : get_block_epoch cfg (E.store cfg ext w m)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result <
          (E.store cfg ext w m).justified_checkpoint.epoch := by
        have hltQ := Nat.lt_of_not_ge hnot
        simpa only [get_block_epoch, hblocksAgree] using hltQ
      have hJResult := hbracket.above_selected (by
        rw [← hselector.result_eq]
        exact habove)
      exact hnotJResult (by
        simpa only [hselector.result_eq] using hJResult)

end Weak

end FastConfirmation.Spec
