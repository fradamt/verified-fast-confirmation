module
public import FastConfirmationProofs.Weak.History.WeakPreQuerySIR
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32Step
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32CallSupplier
public import FastConfirmationProofs.Weak.Common.WeakSelectedStrictEdgeFilterSupply

@[expose] public section

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

`Execution.HistoricalCurrentTargetCertificateProducerAt`
(`SelectedPreQueryHistoricalSIR.lean`) is **not** reusable at the weak
evaluator: its no-crossing hypothesis names the strong
`CurrentTargetSelectedEdge`, hence the strong `findLatestSelectedTrace`.  A
Byzantine observer runs `Weak.findLatestSelectedTrace` (rule delta 1 drops the
discount), so the two propositions are different and there is no bridge in the
direction the producer needs.  The weak interface below is the same statement
over `Weak.CurrentTargetSelectedEdge` (`WeakHistoricalA32Step.lean`); the
*certificate* it produces, `CertifiedJustified`, is evaluator-free and reused
unchanged.

Before `docs/weak-final-wave.md` W5 this was
`Weak.HistoricalA32PayloadProducerAt`, which handed back the whole retained
A3.2 payload.  The single consumer read only `hpayload.certified.some`, and
that stronger interface is exactly what the lazy route cannot supply at a
consuming call, so it was weakened to the certificate and deleted. -/

/-- Weak twin of `Execution.HistoricalCurrentTargetCertificateProducerAt`
(`SelectedPreQueryHistoricalSIR.lean`), over the weak selector's own tentative
edge list.

This is the *only* thing the `currentHistorical` arm of the call-site
classifier ever extracted from the retained payload
(`hpayload.certified.some`), so taking it directly is a strict premise
weakening — and it is what lets the lazy route supply the arm without ever
realizing a payload at the consuming call: under `hnoCrossing` the one-call
transformer creates no payload, so the certificate comes from the invariant at
second `n` and is discharged by the fold output strictly below `n` (D1†).
`docs/weak-final-wave.md` §4. -/
def HistoricalCurrentTargetCertificateProducerAt (E : Execution Root)
    (anchor : Checkpoint Root)
    (query : FastConfirmationStore Root) (input result : Root) : Prop :=
  get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store →
  (¬ ∃ a c : Root, Weak.CurrentTargetSelectedEdge cfg ext query input a c) →
    Nonempty (CertifiedJustified cfg E anchor
      (get_current_target cfg query.store))

/-- Observer twin of
`Execution.epochStart_or_endpointOriginOrPinned_of_acceptedCallSite`.

Only two things change.  The call-site classifier is stage S8a's weak
inductive, whose two executable gates are the *weak* rule booleans, so each is
converted to the strong one the accepted producers consume by the stage-B8
bridges `will_current_target_be_justified_of_weak` /
`will_no_conflicting_of_weak` (`WeakRulePredicateBridge.lean`) — both are
one-directional weak ⇒ strong, which is exactly the direction needed here.
And the historical arm consumes the weak producer interface above instead of
the strong one.  The accountability step
(`CertificateAccountability.justified_unique`), the endpoint certificate
(`CausalPrefixFFGInterpretation.endpointJustified_certificate`) and the
gate-driven endpoint disjunction
(`Execution.EndpointOriginOrPinnedProducerAt`) are read at the honest
endpoint's store and are reused verbatim. -/
theorem epochStart_or_endpointOriginOrPinned_of_observerCallSite
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {q : Nat} {query : FastConfirmationStore Root}
    {input result : Root} {w : ValidatorIndex} {m : Nat}
    (hcall : Weak.StrictSelectedHistoricalSIRCallSite cfg ext q query
      input result)
    (hacc : CertificateAccountability cfg E B.anchor)
    (hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext E
      B.anchor query input result)
    (hproducer : E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor q query) :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
      E.EndpointOriginOrPinnedAt cfg ext B.anchor q w m
        (get_current_target cfg query.store) := by
  cases hcall with
  | currentCrossing _resultCurrent _a _c _mem _lt hgate =>
      exact Or.inr (hproducer (Or.inr
        (will_current_target_be_justified_of_weak cfg ext
          query.store hgate)) w m)
  | currentHistorical hresultCurrent hnone =>
      refine Or.inr (Or.inr (Or.inr ?_))
      intro hepoch
      obtain ⟨hJ⟩ :=
        Execution.CausalPrefixFFGInterpretation.endpointJustified_certificate
          cfg ext B hgen hanchor (E.store_causal cfg ext w m)
      obtain ⟨hT⟩ := hhistorical hresultCurrent hnone
      exact hacc.justified_unique hJ hT hepoch
  | previousEpochStart _resultPrevious hstart =>
      exact Or.inl hstart
  | previousNoConflict _resultPrevious _notStart hgate =>
      exact Or.inr (hproducer (Or.inl
        (will_no_conflicting_of_weak cfg ext query.store
          (get_current_balance_source query) hgate)) w m)

/-! ## The three producer wrappers -/

/-- Observer twin of
`Execution.preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_acceptedProducers`.

The honest-node binder `hv` becomes `E.ObserverCoherence cfg ext obs`; the
call-site classifier, the three-region bracket and the trusted-anchor bracket
are stage S8a's observer twins;
`Execution.certificateAccountability_of_selectedMarginAssumptions` and the
endpoint-side arms of the disjunction are honesty-free and reused verbatim. -/
theorem preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_observerProducers
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
    (hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext E
      B.anchor query input
      (Weak.find_latest_confirmed_descendant cfg ext query input))
    (hproducer : E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor q query)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    E.PreQueryVoteSelectedSIRBracketAt cfg ext q input
        (Weak.find_latest_confirmed_descendant cfg ext query input) w m ∨
      E.CausalHonestTargetAt cfg ext q w m := by
  have hcall := Weak.strictSelectedHistoricalSIRCallSite cfg ext hA
    hcoh hqH query hquery input hinput hinputEpoch hstrict
  have hacc : CertificateAccountability cfg E B.anchor :=
    E.certificateAccountability_of_selectedMarginAssumptions cfg ext hA
  rcases Weak.epochStart_or_endpointOriginOrPinned_of_observerCallSite
      cfg ext B hgen hanchor (w := w) (m := m) hcall hacc hhistorical
      hproducer with hstart | hJanchor | hcausal | hpin
  · exact Or.inl (Weak.preQueryVoteSelectedSIRBracketAt_of_startOrPin cfg ext
      hA hwalkDomain hcoh hqH query hquery input hinput hinputEpoch hbase
      hstrict hw hslotQM hHm (Or.inl hstart))
  · exact Or.inl
      (Weak.preQueryVoteSelectedSIRBracketAt_of_trustedAnchorEndpoint cfg ext
        hA hanchor hcoh hqH query hquery input hinput hstrict hw hslotQM hHm
        hJanchor)
  · exact Or.inr hcausal
  · exact Or.inl (Weak.preQueryVoteSelectedSIRBracketAt_of_startOrPin cfg ext
      hA hwalkDomain hcoh hqH query hquery input hinput hinputEpoch hbase
      hstrict hw hslotQM hHm (Or.inr hpin))

/-- Observer twin of
`Execution.strictSelected_result_and_child_ancestor_of_endpointJustified_accepted`.

The endpoint tail
`selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal` is
reused verbatim: every one of its relays leaves from the *honest endpoint*. -/
theorem strictSelected_result_and_child_ancestor_of_endpointJustified_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
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
    (hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext E
      B.anchor query input
      (Weak.find_latest_confirmed_descendant cfg ext query input))
    (hproducer : E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor q query)
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
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  rcases
      Weak.preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_observerProducers
        cfg ext hA hwalkDomain B hgenShort hanchor hcoh hqH query hquery
        input hinput hinputEpoch hbase hstrict hhistorical hproducer
        hw hslotQM hHm with hvoteBracket | hcausal
  · have hpre :=
      Weak.preQuerySelectedJustifiedCompatibilityAt_of_voteBracket
        cfg ext hA hanchor hcoh hqH query hquery input hinput hstrict
          hw hslotQM hHm hvoteBracket
    have horigin : E.EndpointJustificationOriginAt cfg ext B.anchor w m :=
      Execution.CausalPrefixFFGInterpretation.endpointJustificationOriginAt
        cfg ext B hT hanchor hboundary
    exact E.selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
      cfg ext hA hwalkDomain hw hHm hslotQM hcM hselectedC
        hselectedKnown hIH hpre horigin hnotCovered
  · exact E.selected_result_and_child_ancestor_of_causalHonestTarget
      cfg ext hA hwalkDomain hw hHm hslotQM hcM hselectedC hselectedKnown
        hIH hcausal hnotCovered

/-! ## The two actual-call facts of the residual bundle

Both are stated exactly as the corresponding fields of
`Weak.ObserverStrictCallFilterInputsAt`, so that the final producer can hand
them over directly.  The shared plumbing is the strong wrappers' verbatim: the
input epoch dichotomy from the block-slot upper bound and
`StrictSelectorAdvanceAt.input_recent`, and the rewriting of the trace result
along `hselector.result_eq`. -/

/-- The observer-call form of the two orientation premises, shared by both
theorems below: the input's epoch dichotomy, the strictness of the selector
step, and the gate-driven endpoint origin/pinning producer landed in
`WeakHistoricalA32CallSupplier.lean`.

Since **N5** of `docs/trunkB-two-case-discharge.md` §7 the Trunk-B route needs
neither an observer-side normative proviso nor the accepted live
current-target gate producer: both gate arms of the call site are served by
`Execution.EndpointOriginOrPinnedProducerAt`. -/
private theorem observerCall_orientation_inputs
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (_hcall : E.IsScheduledFCRCallAt cfg ext obs n)
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
    E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor (n + 1)
      (E.weakFcrStep cfg ext obs n) := by
  have hquery : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
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
  refine ⟨?_, ?_,
    E.observerCall_endpointOriginOrPinnedProducerAt cfg ext B hT
      hCbase hfit hanchor hboundary hcoh hHn1⟩
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

`hCbase` is the unchanged 6-field completed-prefix call contract -- no
observer proviso: since `docs/weak-final-wave.md` W5 this module reads only
`hC.base`.  `hbase` is the outer safety induction's carried input safety, as in
the strong theorem; `hhistorical` is the weak historical current-target
*certificate* producer, built by the observer-side write-back induction through
its no-crossing route. -/
theorem observerCall_strictSelected_result_and_child_ancestor_of_endpointJustified
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext E
      B.anchor (E.weakFcrStep cfg ext obs n)
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
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hCbase.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hCbase.static_validators
      byzantine_bound := hCbase.byzantine_bound
      domain := hdomain }
  have hquery : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  obtain ⟨hinputEpoch, hstrict, hproducer⟩ :=
    Weak.observerCall_orientation_inputs cfg ext B hT hCbase hfit hanchor
      hboundary hcoh hcall hHn1 hinput hselector
  have hhistorical' : Weak.HistoricalCurrentTargetCertificateProducerAt
      cfg ext E B.anchor query trace.afterObserved
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
      trace.afterObserved hinput hinputEpoch hbase hstrict
      hhistorical' hproducer hw hHm hslotQM hcM hselectedC'
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
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    {obs : ValidatorIndex}
    (hCbase : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hhistorical : Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext E
      B.anchor (E.weakFcrStep cfg ext obs n)
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
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hCbase.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hCbase.static_validators
      byzantine_bound := hCbase.byzantine_bound
      domain := hdomain }
  have hquery : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  obtain ⟨hinputEpoch, hstrict, hproducer⟩ :=
    Weak.observerCall_orientation_inputs cfg ext B hT hCbase hfit hanchor
      hboundary hcoh hcall hHn1 hinput hselector
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary
  have hhistorical' : Weak.HistoricalCurrentTargetCertificateProducerAt
      cfg ext E B.anchor
      (E.weakFcrStep cfg ext obs n) (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (Weak.find_latest_confirmed_descendant cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hbracketOrCausal :
      E.PreQueryVoteSelectedSIRBracketAt cfg ext
          (n + 1) (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
          (Weak.find_latest_confirmed_descendant cfg ext
            (E.weakFcrStep cfg ext obs n)
            (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
          w m ∨
        E.CausalHonestTargetAt cfg ext (n + 1) w m :=
    Weak.preQueryVoteSelectedSIRBracket_or_causalHonestTarget_of_observerProducers
      cfg ext hA hwalkDomain B hgenShort hanchor hcoh hHn1
      (E.weakFcrStep cfg ext obs n) hquery
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved hinput
      hinputEpoch hbase hstrict hhistorical' hproducer hw hslotQM hHm
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
      hT.externals_coherence hT.genesis_structure hdomain w hw m hHm
  have hnotJResult : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result) ≠ true := by
    intro hJResult
    apply hnotCovered
    exact is_ancestor_trans
      (a := get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (b := get_node_for_root (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      (c := get_node_for_root c) hparentM
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
  rcases hbracketOrCausal with hvoteBracket | hcausal
  · have horigin : E.EndpointJustificationOriginAt cfg ext B.anchor w m :=
      Execution.CausalPrefixFFGInterpretation.endpointJustificationOriginAt
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
  · obtain ⟨i, hi, s, k, a, hqs, hsm, hsH, hvote, htarget⟩ := hcausal
    have hbound :=
      E.endpoint_justified_epoch_le_of_causal_honest_target_minimal
        cfg ext hA hwalkDomain hw hHm hselectedKnown hIH hi hqs hsm
        hsH hvote htarget hnotJResult
    simpa only [get_block_epoch, hblocksAgree] using hbound

end Weak

end FastConfirmation.Spec

end
