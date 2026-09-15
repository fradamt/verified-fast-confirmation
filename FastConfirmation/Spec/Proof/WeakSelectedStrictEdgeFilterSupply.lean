import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedSelectedStrictEdgeFilterSupply
import FastConfirmation.Spec.Proof.WeakCandidateSourceHistory
import FastConfirmation.Spec.Proof.WeakCoveredMarginConstruction

/-!
# Spec / Proof / WeakSelectedStrictEdgeFilterSupply

Stage S7 of the `hfilter`-discharge wave: the weak twin of
`AcceptedSelectedStrictEdgeFilterSupply.lean`'s phase dispatcher and
strict-edge filter supplier, run at a possibly-Byzantine observer over its own
weak call trajectory (`E.weakFcrStep` / `E.weakGetLatestConfirmedTraceAt`).

## What is reused verbatim

* `Execution.AcceptedSelectedResultFilterOutcomeAt` and its eliminator
  `…child_filtered` — both are stated over a bare `endpoint : Store Root`
  with zero honesty, so the weak development targets exactly the strong
  inductive;
* the two retained tails
  `Execution.acceptedSelectedResultFilterOutcome_retained_of_carrier` /
  `…_of_recentSeed` — every hypothesis is indexed at the honest endpoint
  `(w, m)`;
* `Execution.AcceptedCurrentSameSourceHistoryOutcome.retainedAt_currentSameEndpoint`
  — already honesty-free at the query node (its relays all leave from the
  *honest past supporter* recorded inside the carrier);
* `Execution.actualCall_queryIndex_le_of_slot_le` — a pure `slot_at`
  monotonicity fact about `E.IsFCRCallAt`, which is a store-level (honesty-free)
  predicate shared by both developments.

## The substitutions

Per the wave's stage-S0 audit, the query node's honesty binder resolves to a
relay, `ExternalsCoherence.committees_agree`, or
`SelectedMarginDomain.justified_root_known`. Here:

* `confirmed_known_at_all_honest_endpoints_minimal … hv` becomes
  `Execution.confirmed_known_at_all_honest_endpoints_at_observer`
  (`WeakConfirmedDissemination.lean`), fed `hcoh.committees_agree`;
* `store_domainK_of_selectedMarginDomain … hv` at the *query* node becomes
  `Execution.observerStoreDomainK`; at the endpoint it is unchanged (the
  endpoint is honest in both developments);
* `head_root_known_of_selectedMarginDomain … hv` becomes
  `Execution.head_root_known_at_observer`;
* the per-branch recent-source producers become their stage-S5 twins
  (`Weak.StrictSelectedResultMechanicalFacts.fcrStep_previous_/
  fcrStep_currentNext_endpointRecentSourceSeed`);
* the Lemma-26 history becomes stage S6's
  `Weak.StrictSelectedResultMechanicalFacts.actualCurrentSame_sourceHistoryOutcome`.

## What is delivered

* the four per-branch endpoint filter outcomes
  `Weak.StrictSelectedResultMechanicalFacts.fcrStep_previous_/
  fcrStep_currentSame_/fcrStep_currentNext_/
  fcrStep_previousOffStart_late_endpointFilterOutcome`;
* site 7, `Weak.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed`,
  with the observer-as-sender relay replaced by an explicit endpoint-knownness
  premise, together with the seed producer
  `Weak.StrictSelectedResultMechanicalFacts.previousOffStart_queryGUEpochSeed`,
  which returns the seed's dissemination alongside the seed by threading the
  stage-S2 entry witnesses' certificates
  (`PreviousSelectedEntryWitness.witness_certificate` for the
  `previous_slot_head` arm, `has_head_broadcast_certificate` for both `head`
  arms) into the stage-S3 dissemination lemmas;
* site 1's full-epoch canonicity at a confirmed current-epoch result
  (`Weak.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch_at_observer`)
  and its epoch-start previous sibling
  (`Weak.StrictSelectedResultMechanicalFacts.canonicalThroughoutNextEpoch_of_previousEpochStart`);
* two of the three epoch-start previous origins —
  `Weak.StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage` (with
  `…extendHistoricalLineage_sameEpoch_actual`) and
  `Weak.StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed`
  (query-local half);
* the phase dispatcher
  `Weak.StrictSelectedResultMechanicalFacts.fcrStep_endpointFilterOutcome`
  and the top-level supplier
  `Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt`;
* obligation X1's resolution, `Weak.SelectedHelperProvisosAt` +
  `Weak.ObserverHistoricalA32CallAssumptions` (see the section below).

## What is carried, and why

`Weak.ObserverStrictCallFilterInputsAt` is the record of facts the dispatcher
still consumes and this module does not prove.  It is a **proof obligation,
not an assumption**, and it is deliberately as small as the stage could make
it.  Its four fields and the exact reason each is open:

1. `result_descends_endpoint_justified` and
2. `endpoint_justified_epoch_le_result` — the observer twins of
   `actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified`
   and `actualCall_strictSelected_endpointJustifiedEpoch_le_result`.  Both
   bottom out in the pre-query SIR chain
   (`SelectedPreQueryHistoricalSIR.lean` →
   `AcceptedSelectedJustifiedOrientation.lean`).  That chain's query-node
   honesty is *not* uniformly of the three substitutable kinds: besides the
   usual domain/committee uses it contains
   (a) relay applications with the query node as **receiver**
   (`MinimalSelectedDomain.ancestry_of_known_honest_past_descendant_minimal`,
   `SelectedPreQueryHistoricalSIR.preQueryHonestTarget_sourceWitnessAtQuery`),
   for which the weak model supplies no delivery, and
   (b) one instantiation of the honest-endpoint-quantified input-safety
   premise at the query node itself (`hbase v hv q …` in
   `selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning`), which a
   Byzantine observer is outside of.  (b) is repairable — in the strict case
   the observer's own head descends its input via
   `Weak.strictSelectedResult_below_head` composed with
   `StrictSelectedResultMechanicalFacts.descends_input` — but (a) needs new
   weak-side infrastructure and is the wave's remaining scout question.
3. `current_lineage` and
4. `previous_epochStart_carried_lineage` — the observer-side instance of the
   accepted historical A3.2 write-back induction
   (`AcceptedHistoricalA32Induction.lean`, one call step in
   `AcceptedHistoricalA32OneStep.lean`), re-indexed over `E.weakConfirmed` /
   `E.weakFcrStep`.  Every honesty use in that stack is of the substitutable
   kinds (all of them route through
   `historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory`'s two domain
   hubs, plus one `committees_agree`), so this is a mechanical — but not
   small — port; it is structurally an induction over the *observer's own*
   call history and cannot be imported from an honest node.
5. `previous_epochStart_observedReset_headDisseminated` — §4 of the wave
   design's known epoch-start escape; see that field's own docstring.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-! ## The observer-side normative call contract (obligation X1)

`Execution.AcceptedHistoricalA32CompletedPrefixCallAssumptions.helper_provisos`
(`AcceptedHistoricalA32CallSupplier.lean`) is quantified as
`∀ v ∈ E.honest, …` and indexed at the *strong* evaluator
(`E.fcrStep` / `E.getLatestConfirmedTraceAt` /
`SelectedHelperProvisosAt`, which itself names
`find_latest_confirmed_descendant` and the strong
`PreviousAcceptedEdge` / `CurrentTargetAcceptedEdge`).  A Byzantine observer
is outside that quantifier, and its calls run the weak evaluator, so neither
the quantifier nor the indexing fits.

Resolution, per the wave design's target end state: the strong record is left
untouched and a **parallel observer-quantified contract** is added on the weak
side — `Weak.SelectedHelperProvisosAt` (the weak twin of the proviso record,
over `Weak.findLatestSelectedTrace`) plus
`Weak.ObserverHistoricalA32CallAssumptions`, which bundles the unchanged
strong record with one observer-indexed field.  Nothing in the strong
development changes.

**This is floor-classified.**  `helper_provisos` is a normative FCR-spec
contract (the literal helper provisos the specification attaches to a
selector invocation), not a derived fact; extending it to cover the observer
adds an assumption of exactly the same accepted-FFG-contract shape as the
strong one it mirrors, and it is carried, not discharged. -/

/-- Weak twin of `SelectedHelperProvisosAt`, over the weak evaluator trace.
Field-for-field identical to the strong record with
`findLatestSelectedTrace` / `PreviousAcceptedEdge` /
`find_latest_confirmed_descendant` replaced by their `Weak.` counterparts.
The strong `CurrentTargetAcceptedEdge`'s two conjuncts are inlined, because
`WeakSelectedTrace.lean` (stage S2) landed no weak twin of that abbreviation. -/
structure SelectedHelperProvisosAt (E : Execution Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  current_target : ∀ a c : Root,
    (a, c) ∈ (Weak.findLatestSelectedTrace cfg ext fcrStore
      latestConfirmedRoot).2.2 →
    get_block_epoch cfg fcrStore.store a <
      get_block_epoch cfg fcrStore.store c →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  no_conflict : ∀ a c : Root,
    Weak.PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  selected_previous_result_no_conflict : ∀ result : Root,
    Weak.find_latest_confirmed_descendant cfg ext fcrStore
      latestConfirmedRoot = result →
    result ≠ latestConfirmedRoot →
    get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q

/-- The accepted FFG call contract, extended to cover one fixed observer.

`base` is `Execution.AcceptedHistoricalA32CompletedPrefixCallAssumptions`
**verbatim and unchanged**; `observer_helper_provisos` is the single parallel
field obligation X1 asks for.  Floor-classified together with `base`. -/
structure ObserverHistoricalA32CallAssumptions (E : Execution Root)
    (obs : ValidatorIndex) : Prop where
  base : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext
  observer_helper_provisos : ∀ n : ℕ,
    E.IsFCRCallAt cfg ext obs n → E.WithinHorizon cfg (n + 1) →
      getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved →
        Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1)
          (E.weakFcrStep cfg ext obs n)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved

/-! ## Actual-call endpoint order

`Execution.actualCall_queryIndex_le_of_slot_le` is reused verbatim; only the
geometry wrapper needs a weak twin, because `Weak.StrictSelectedEdgeGeometry`
is a different (weak-selector-indexed) structure with the same three fields
the strong wrapper reads. -/

/-- Weak twin of `Execution.StrictSelectedEdgeGeometry.actualCall_queryIndex_le_endpoint`. -/
theorem StrictSelectedEdgeGeometry.actualCall_queryIndex_le_endpoint
    {glc r0 a c : Root} {obs : ValidatorIndex} {n : Nat}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : Nat}
    {lo es sigma querySlot : Slot}
    (h : Weak.StrictSelectedEdgeGeometry cfg ext E glc r0 a c
      obs (n + 1) query w m lo es sigma querySlot)
    (hcall : E.IsFCRCallAt cfg ext obs n) :
    n + 1 ≤ m := by
  apply E.actualCall_queryIndex_le_of_slot_le cfg ext hcall
  rw [h.confirming_cutoff]
  exact Nat.succ_le_of_lt (h.cutoff_le_sigma.trans_lt h.sigma_lt_endpoint)

/-- The endpoint slot order carried by any weak strict-edge geometry. -/
theorem StrictSelectedEdgeGeometry.query_slot_le_endpoint
    {glc r0 a c : Root} {obs : ValidatorIndex} {q : Nat}
    {query : FastConfirmationStore Root}
    {w : ValidatorIndex} {m : Nat}
    {lo es sigma querySlot : Slot}
    (h : Weak.StrictSelectedEdgeGeometry cfg ext E glc r0 a c
      obs q query w m lo es sigma querySlot) :
    E.slot_at cfg q ≤ E.slot_at cfg m := by
  rw [h.confirming_cutoff]
  exact Nat.succ_le_of_lt (h.cutoff_le_sigma.trans_lt h.sigma_lt_endpoint)

/-! ## The three early phase cells -/

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_previous_
endpointFilterOutcome`. -/
noncomputable def StrictSelectedResultMechanicalFacts.fcrStep_previous_endpointFilterOutcome
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {input result : Root}
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input result)
    (hprevious : get_block_epoch cfg
        (E.weakFcrStep cfg ext obs n).store result + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : Weak.StrictSelectedEdgeGeometry cfg ext E result r0 a c
      obs (n + 1) (E.weakFcrStep cfg ext obs n) w m
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
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hcommN1 : E.PrefixCommitteeAgreement cfg ext
      (E.store cfg ext obs (n + 1)) :=
    hcoh.committees_agree (n + 1) hn1H
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    hgeom.query_slot_le_endpoint cfg ext
  have hnm : n + 1 ≤ m :=
    hgeom.actualCall_queryIndex_le_endpoint cfg ext hcall
  have hselectedEndpoint : result ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hMargin
      obs (n + 1) hcommN1 (E.weakFcrStep cfg ext obs n) hqCurrent result hn1H
      (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
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
  have hrecent : Execution.RecentSourceSeedAt cfg
      (E.store cfg ext w m) result :=
    h.fcrStep_previous_endpointRecentSourceSeed cfg ext hT hsync hstatic
      hbyz hdomain hji B hcoh hn1H hprevious hw hmH hnm hsameEpoch
  exact E.acceptedSelectedResultFilterOutcome_retained_of_recentSeed
    cfg ext B hT hanchor hboundary hDelay P V hanchorExact hacc
      hselectedEndpoint hparent hwalkK hnonfuture hrecent
      hresultJustified

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_currentSame_
endpointFilterOutcome`. The Lemma-26 history comes from stage S6; the endpoint
carrier extraction `retainedAt_currentSameEndpoint` is reused verbatim. -/
noncomputable def
    StrictSelectedResultMechanicalFacts.fcrStep_currentSame_endpointFilterOutcome
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {input : Root}
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : Weak.StrictSelectedEdgeGeometry cfg ext E
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result r0 a c
      obs (n + 1) (E.weakFcrStep cfg ext obs n) w m
        lo es sigma querySlot)
    (hresultJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
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
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hcommN1 : E.PrefixCommitteeAgreement cfg ext
      (E.store cfg ext obs (n + 1)) :=
    hcoh.committees_agree (n + 1) hn1H
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    hgeom.query_slot_le_endpoint cfg ext
  have hselectedEndpoint :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
        (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hMargin
      obs (n + 1) hcommN1 (E.weakFcrStep cfg ext obs n) hqCurrent
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result hn1H
      (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
      h.confirmed w hw m hslotQM hmH
  have hhistory := h.actualCurrentSame_sourceHistoryOutcome cfg ext B hT
    hsync hstatic hbyz hdomain hji hanchor hboundary hDelay hcoh hn1H hcall
      hcurrent
  have hselectedQuery :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
    simpa only [hqCurrent] using h.result_known
  have hcurrentStore : get_block_epoch cfg
        (E.store cfg ext obs (n + 1))
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
    simpa only [hqCurrent] using hcurrent
  have hsameStore : get_current_store_epoch cfg
        (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.store cfg ext obs (n + 1)) := by
    simpa only [hqCurrent] using hsameEpoch
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

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_currentNext_
endpointFilterOutcome`. -/
noncomputable def StrictSelectedResultMechanicalFacts.fcrStep_currentNext_endpointFilterOutcome
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input result : Root}
    (hinput : input ∈ (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hout : Weak.find_latest_confirmed_descendant cfg ext
      (E.weakFcrStep cfg ext obs n) input = result)
    (hstrict : result ≠ input)
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input result)
    (hcurrent : get_block_epoch cfg
        (E.weakFcrStep cfg ext obs n).store result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store + 1)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : Weak.StrictSelectedEdgeGeometry cfg ext E result r0 a c
      obs (n + 1) (E.weakFcrStep cfg ext obs n) w m
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
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hcommN1 : E.PrefixCommitteeAgreement cfg ext
      (E.store cfg ext obs (n + 1)) :=
    hcoh.committees_agree (n + 1) hn1H
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    hgeom.query_slot_le_endpoint cfg ext
  have hselectedEndpoint : result ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hMargin
      obs (n + 1) hcommN1 (E.weakFcrStep cfg ext obs n) hqCurrent result hn1H
      (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
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
  have hrecent : Execution.RecentSourceSeedAt cfg
      (E.store cfg ext w m) result :=
    h.fcrStep_currentNext_endpointRecentSourceSeed cfg ext hT hsync
      hstatic hbyz hdomain hji B hcoh hn1H hinput hout hstrict hcurrent
        hw hmH hnextEpoch
  exact E.acceptedSelectedResultFilterOutcome_retained_of_recentSeed
    cfg ext B hT hanchor hboundary hDelay P V hanchorExact hacc
      hselectedEndpoint hparent hwalkK hnonfuture hrecent
      hresultJustified

/-! ## Site 7 — the late mid-epoch previous cell

`Execution.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed`
relays the GU seed out of the observer's own store with
`hsync.block_relay v hv q seed …`.  At a Byzantine observer there is no such
relay, so the seed's endpoint knownness becomes an explicit premise
(`hseedEndpoint`) discharged by the caller from the certificate the weak
selector guard carries — which is exactly why the weak
`previousOffStart_queryGUEpochSeed` below returns the dissemination
conclusion alongside the seed rather than the bare triple.  No other use of
the query node's honesty occurs in that proof: the query-side
`store_domainK_of_selectedMarginDomain` becomes
`Execution.observerStoreDomainK`, and `hsync` leaves the signature entirely. -/

/-- Clone of `AcceptedSelectedStrictEdgeFilterSupply.lean`'s `private`
`AcceptedBlockAt.executionRoot_for_lateSelectedSupply` (a `private` declaration
cannot be reused across modules).  Pure provenance bookkeeping, no honesty. -/
private theorem executionRoot_of_acceptedBlockAt
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Weak twin of
`Execution.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed`,
with the observer-as-sender relay replaced by the premise `hseedEndpoint`. -/
noncomputable def
    acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    (hdomain : SelectedMarginDomain cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {selected seed : Root} {e : Epoch}
    (hselectedQ : selected ∈ (E.store cfg ext obs q).block_roots)
    (hseedQ : seed ∈ (E.store cfg ext obs q).block_roots)
    (hseedSelected : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root seed) (get_node_for_root selected) = true)
    (hguLower : e ≤ (B.state.GU seed).epoch)
    (hqueryEpoch : get_current_store_epoch cfg
      (E.store cfg ext obs q) = e + 1)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hseedEndpoint : seed ∈ (E.store cfg ext w m).block_roots)
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
  let query := E.store cfg ext obs q
  let endpoint := E.store cfg ext w m
  have hqueryCausal : E.CausalStore cfg ext query := by
    simpa only [query] using E.store_causal cfg ext obs q
  have hendpointCausal : E.CausalStore cfg ext endpoint := by
    simpa only [endpoint] using E.store_causal cfg ext w m
  obtain ⟨hqueryParent, hqueryWalk, _hqueryJustified⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh q hqH
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
  have hseedM : seed ∈ endpoint.block_roots := by
    simpa only [endpoint] using hseedEndpoint
  have hqueryParent' : ParentSlotLt query := by
    simpa only [query] using hqueryParent
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor (E.blockProvenance cfg ext obs q)
      hqueryParent'
      (by
        simpa only [query] using hqueryWalk selected hselectedQ seed hseedQ)
      (by simpa only [query] using hseedSelected)
  have hselectedRoot : E.ExecutionRoot selected :=
    executionRoot_of_acceptedBlockAt cfg ext
      (E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal
        (by simpa only [query] using hselectedQ))
  obtain ⟨hselectedM, hseedSelectedM⟩ :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      (by simpa only [endpoint] using hseedM) hselectedRoot hsemantic
  have hseedBlockAgree : query.blocks seed = endpoint.blocks seed :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs q)
      (E.blockProvenance cfg ext w m)
      (by simpa only [query] using hseedQ)
      (by simpa only [endpoint] using hseedM)
  have hseedEpochLeQ : get_block_epoch cfg query seed ≤
      get_current_store_epoch cfg query := by
    simp only [get_block_epoch, get_current_store_epoch]
    exact Nat.div_le_div_right
      (E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        hgenShort obs q seed (by simpa only [query] using hseedQ))
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
  have hsourceGU : get_voting_source cfg endpoint seed =
      B.state.GU seed := by
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

/-- Weak twin of `StrictSelectedResultMechanicalFacts.previousOffStart_
queryGUEpochSeed`, extended with the seed's dissemination to every honest
endpoint at or past the query slot.

Both arms of the strong disjunction name a *certified* root under the weak
rule: the previous-loop arm's `previous_slot_head` carries
`Weak.has_justification_witness_certificate` (the named
`PreviousSelectedEntryWitness.witness_certificate` field, stage S2), and
every `head` arm carries `Weak.has_head_broadcast_certificate`.  Stage S3's
two dissemination lemmas turn each into endpoint knownness, which is what
site 7 consumes in place of the observer-as-sender relay. -/
theorem StrictSelectedResultMechanicalFacts.previousOffStart_queryGUEpochSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input selected : Root}
    (hinput : input ∈ (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hout : Weak.find_latest_confirmed_descendant cfg ext
      (E.weakFcrStep cfg ext obs n) input = selected)
    (hstrict : selected ≠ input)
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input selected)
    (hprevious : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        selected + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) ≠ true) :
    ∃ seed : Root,
      seed ∈ (E.weakFcrStep cfg ext obs n).store.block_roots ∧
        is_ancestor (E.weakFcrStep cfg ext obs n).store
          (get_node_for_root seed) (get_node_for_root selected) = true ∧
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store selected ≤
          (B.state.GU seed).epoch ∧
        (∀ w ∈ E.honest, ∀ m : Nat, E.WithinHorizon cfg m →
          E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
          seed ∈ (E.store cfg ext w m).block_roots) := by
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
  let query := E.weakFcrStep cfg ext obs n
  have hqCurrent : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    rw [hqCurrent]; exact E.store_causal cfg ext obs (n + 1)
  obtain ⟨hparent, hwalk, _hjustifiedKnown⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh (n + 1) hn1H
  have hparentQ : ParentSlotLt query.store := by
    simpa only [query, hqCurrent] using hparent
  have hwalkQ : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, hqCurrent] using hwalk
  have hheadKnown : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    simpa only [query, hqCurrent] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hn1H
  have hpreviousHeadKnown : query.previous_slot_head ∈
      query.store.block_roots := by
    simpa only [query] using
      Weak.weakFcrStep_previousSlotHead_known cfg ext hT.genesis hcoh n hn1H
  have hheadSelected : is_ancestor query.store
      (get_head cfg query.store) (get_node_for_root selected) = true := by
    have hstrict' : Weak.find_latest_confirmed_descendant cfg ext query
        input ≠ input := by
      simpa only [query, hout] using hstrict
    simpa only [query, hout] using
      Weak.strictSelectedResult_below_head cfg ext hparentQ hwalkQ
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
  -- the query slot is past slot 0, so the certificate span's endpoint gate
  -- `(current_slot - 1) + 1` is exactly the query slot
  have hstart0 : is_start_slot_at_epoch cfg 0 = true := by
    simp [is_start_slot_at_epoch, compute_slots_since_epoch_start]
  have hslotPos : 1 ≤ get_current_slot cfg query.store := by
    rcases Nat.eq_zero_or_pos (get_current_slot cfg query.store) with hz | hpos
    · exact absurd (hz ▸ hstart0) hnotStart
    · exact hpos
  have hcurSlotEq : get_current_slot cfg query.store =
      E.slot_at cfg (n + 1) := by
    rw [hqCurrent]; exact E.store_current_slot cfg ext obs (n + 1)
  have hslotPosAt : 1 ≤ E.slot_at cfg (n + 1) := by
    rw [← hcurSlotEq]; exact hslotPos
  have gate_of {m : Nat} (hslot : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m) :
      (get_current_slot cfg query.store - 1) + 1 ≤ E.slot_at cfg m := by
    rw [hcurSlotEq, Nat.sub_add_cancel hslotPosAt]
    exact hslot
  have headDissem (hcert : Weak.has_head_broadcast_certificate cfg ext
      query.store (get_current_balance_source query) = true) :
      ∀ w ∈ E.honest, ∀ m : Nat, E.WithinHorizon cfg m →
        E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
        (get_head cfg query.store).root ∈ (E.store cfg ext w m).block_roots := by
    intro w hw m hmH hslot
    exact Weak.headSeed_known_at_all_honest_endpoints_at_observer cfg ext hA
      hsync hji hn1H hcoh (by simpa only [query] using hqCurrent) hcert
      hw hmH (gate_of hslot)
  have witnessDissem (hcert : Weak.has_justification_witness_certificate
      cfg ext query = true) :
      ∀ w ∈ E.honest, ∀ m : Nat, E.WithinHorizon cfg m →
        E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
        query.previous_slot_head ∈ (E.store cfg ext w m).block_roots := by
    intro w hw m hmH hslot
    exact Weak.witnessSeed_known_at_all_honest_endpoints_at_observer cfg ext
      hA hsync hji hn1H (hcoh.committees_agree (n + 1) hn1H)
      (by simpa only [query] using hqCurrent) hcert
      (by simpa only [hqCurrent] using hpreviousHeadKnown)
      hw hmH (gate_of hslot)
  rcases h.trace_origin with
      ⟨_a, _hedge, hentry, _hrecent, hpreviousDesc⟩ |
      ⟨_a, _hedge, hentry, _hfinal⟩
  · rcases hentry.inner_gate with hstart | ⟨_noConflict, hgu⟩
    · exact False.elim (hnotStart hstart)
    · rcases hgu with hpreviousGU | ⟨hheadGU, hheadCert⟩
      · exact ⟨query.previous_slot_head, hpreviousHeadKnown,
          hpreviousDesc,
          lower_of_raw hpreviousHeadKnown hpreviousGU,
          witnessDissem hentry.witness_certificate⟩
      · exact ⟨(get_head cfg query.store).root, hheadKnown,
          hheadSelected, lower_of_raw hheadKnown hheadGU,
          headDissem hheadCert⟩
  · rcases hentry with hstart | ⟨hheadGU, hheadCert⟩
    · exact False.elim (hnotStart hstart)
    · exact ⟨(get_head cfg query.store).root, hheadKnown,
        hheadSelected, lower_of_raw hheadKnown hheadGU,
        headDissem hheadCert⟩

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_previousOffStart_
late_endpointFilterOutcome`. -/
noncomputable def
    StrictSelectedResultMechanicalFacts.fcrStep_previousOffStart_late_endpointFilterOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input selected : Root}
    (hinput : input ∈ (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hout : Weak.find_latest_confirmed_descendant cfg ext
      (E.weakFcrStep cfg ext obs n) input = selected)
    (hstrict : selected ≠ input)
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input selected)
    (hprevious : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        selected + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) ≠ true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hlate : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        selected + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store selected)
    (hselectedJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root selected)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m) selected := by
  obtain ⟨seed, hseedQ, hseedSelected, hguLower, hseedDissem⟩ :=
    h.previousOffStart_queryGUEpochSeed cfg ext B hT hsync hstatic hbyz
      hdomain hji hcoh hn1H hinput hout hstrict hprevious hnotStart
  exact Weak.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed
    cfg ext B hT hanchor hboundary P V hanchorExact hacc hdomain hcoh hn1H
      (by simpa only [E.weakFcrStep_store] using h.result_known)
      (by simpa only [E.weakFcrStep_store] using hseedQ)
      (by simpa only [E.weakFcrStep_store] using hseedSelected)
      hguLower
      (by simpa only [E.weakFcrStep_store] using hprevious.symm)
      hw hmH (hseedDissem w hw m hmH hslotQM) hlate hjustifiedEpoch
      hselectedJustified

/-! ## Site 1 — full-epoch canonicity of a current-epoch confirmed result

`Execution.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch`
relays `selected` out of the query node's store.  At the dispatcher's only
call site `selected` is the *confirmed* strict-selector result, so the relay
is replaced by `Execution.confirmed_known_at_all_honest_endpoints_at_observer`
and the confirmation data it needs (`hparent`, `hconf`, `hcomm`) joins the
signature.  Everything else in the strong proof is clock arithmetic. -/

/-- Weak twin of
`Execution.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch`,
for a confirmed current-epoch result at a possibly-Byzantine observer. -/
theorem canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext obs q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext obs q).block_roots)
    (hparentKnown : ((E.store cfg ext obs q).blocks selected).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hconf : Spec.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) selected = true)
    (heCurrent : e = get_current_store_epoch cfg (E.store cfg ext obs q))
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m) :
    E.CanonicalThroughoutEpoch cfg ext selected (e + 1) := by
  intro w' hw' m' hm'H hm'Epoch
  have hqEpoch : compute_epoch_at_slot cfg (E.slot_at cfg q) = e := by
    calc
      compute_epoch_at_slot cfg (E.slot_at cfg q) =
          get_current_store_epoch cfg (E.store cfg ext obs q) := by
        simp only [get_current_store_epoch,
          E.store_current_slot cfg ext obs q]
      _ = e := heCurrent.symm
  have hslotLower : E.slot_at cfg q < E.slot_at cfg m' := by
    by_contra hnot
    have hle : E.slot_at cfg m' ≤ E.slot_at cfg q := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m') ≤
      compute_epoch_at_slot cfg (E.slot_at cfg q) at hepochLe
    rw [hm'Epoch, hqEpoch] at hepochLe
    exact (Nat.not_succ_le_self e) (by
      simpa only [Nat.succ_eq_add_one] using hepochLe)
  have hindexLower : E.slot_start cfg (E.slot_at cfg q) ≤ m' :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotLower.le
  have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext w m]
  have hslotUpper : E.slot_at cfg m' < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg m' := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m) ≤
      compute_epoch_at_slot cfg (E.slot_at cfg m') at hepochLe
    rw [hmEpoch, hm'Epoch] at hepochLe
    have hbad : Nat.succ (e + 1) ≤ e + 1 := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        hlate.trans hepochLe
    exact (Nat.not_succ_le_self (e + 1)) hbad
  have hknown : selected ∈ (E.store cfg ext w' m').block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hquery selected hqH hselected hparentKnown hconf
      w' hw' m' hslotLower.le hm'H
  exact ⟨hknown, hcanonical w' hw' m' hindexLower hslotUpper hm'H⟩

/-! ## Epoch-start previous origins: the two honesty-clean arms

`AcceptedPreviousEpochStartSupply.lean`'s three origin producers consume the
query node's honesty only through `store_domainK_of_selectedMarginDomain` and
`head_root_known_of_selectedMarginDomain` — both class (c) — *except* the
`carried` arm, which additionally re-runs the accepted historical A3.2
write-back induction over the node's own confirmed-root trajectory.  The two
arms below are therefore ported in full; the `carried` arm is the residue. -/

/-- Weak twin of
`Execution.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual`. -/
noncomputable def
    StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hinputKnown : trace.afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B
      trace.afterObserved e)
    (hinputEpoch : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      trace.afterObserved = e)
    (hresultEpoch : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      trace.result = e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e := by
  let query := E.weakFcrStep cfg ext obs n
  let ast : BeaconState Root := Classical.choose hT.genesis
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hgenSlot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hgenParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore
      hT.externals_coherence.state_transition_slot hgenCore
  have hstore : E.CausalStore cfg ext query.store := by
    simpa only [query, E.weakFcrStep_store] using
      E.store_causal cfg ext obs (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.weakFcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.weakFcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have hinputKnownQ : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query] using hinputKnown
  have hgeometry := hselector.geometry cfg ext hparent hwalk hhead
    hinputKnownQ
  have hlands : get_ancestor query.store
      (get_node_for_root trace.result)
      (query.store.blocks trace.afterObserved).slot =
        get_node_for_root trace.afterObserved := by
    simpa only [is_ancestor, decide_eq_true_eq, get_node_for_root] using
      hgeometry.descends_input
  have hinputEpochQ : get_block_epoch cfg query.store
      trace.afterObserved = e := by
    simpa only [query] using hinputEpoch
  have hresultEpochQ : get_block_epoch cfg query.store trace.result = e := by
    simpa only [query] using hresultEpoch
  have hsame : compute_epoch_at_slot cfg
        (query.store.blocks trace.afterObserved).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      hinputEpochQ.trans hresultEpochQ.symm
  have hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [query, E.weakFcrStep_store] using hr
    have hanchorBlock : query.store.blocks ablk.root = ablk.message := by
      simpa only [query, E.weakFcrStep_store] using
        E.store_anchor_block cfg ext hT.wellFormed hgen obs (n + 1)
          hanchorKnown
    have hinputKnownN1 : trace.afterObserved ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      simpa only [query, E.weakFcrStep_store] using hinputKnownQ
    have hanchorLeInput : ablk.message.slot ≤
        (query.store.blocks trace.afterObserved).slot := by
      simpa only [query, E.weakFcrStep_store] using
        E.store_anchor_min_slot cfg ext hT.wellFormed
          hT.externals_coherence hgen hgenSlot hgenParent obs (n + 1)
            trace.afterObserved hinputKnownN1
    have hbad : (query.store.blocks trace.afterObserved).slot <
        ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeInput) hbad
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store trace.afterObserved
        trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor cfg hparent
      (hwalk trace.afterObserved hinputKnownQ trace.result
        hgeometry.result_known)
      hlands hsame hstrictNonGenesis
  have hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      trace.afterObserved trace.result :=
    E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
      hT.wellFormed hcore hstore hknownSegment
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore
      hgeometry.result_known
  exact hlineage.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [query, get_block_epoch] using hresultEpoch)
    (E.acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-- Weak twin of
`Execution.StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage`. -/
theorem StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (horigin : Weak.FinalizedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hprevious : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          trace.result + 1 =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) :
    Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
      (get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        trace.result)) := by
  let query := E.weakFcrStep cfg ext obs n
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := obs) (n + 1)
  have hstore : E.CausalStore cfg ext query.store := by
    simpa only [query, E.weakFcrStep_store] using
      E.store_causal cfg ext obs (n + 1)
  have hfinalizedKnown : query.store.finalized_checkpoint.root ∈
      query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using hrealized.root_known
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, horigin.input_eq] using hfinalizedKnown
  have hrecentFinalized : get_block_epoch cfg query.store
        query.store.finalized_checkpoint.root + 1 ≥
      get_current_store_epoch cfg query.store := by
    simpa only [query, horigin.input_eq] using hselector.input_recent
  have hfinalizedAnchor : query.store.finalized_checkpoint = B.anchor := by
    by_contra hne
    have hstale := E.finalizedResetRoot_stale_of_causalLag cfg ext hLag
      hstore (by simpa only [query, E.weakFcrStep_store] using hrealized) hne
    exact (Nat.not_lt_of_ge hrecentFinalized) hstale
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.weakFcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.weakFcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.weakFcrStep_store] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have hgeometry := hselector.geometry cfg ext hparent hwalk hhead
    hinputKnown
  have hinputResultEpoch : get_block_epoch cfg query.store
        trace.afterObserved =
      get_block_epoch cfg query.store trace.result := by
    have hresultPrevious : get_block_epoch cfg query.store trace.result + 1 =
        get_current_store_epoch cfg query.store := by
      simpa only [query] using hprevious
    have hlower : get_block_epoch cfg query.store trace.result + 1 ≤
        get_block_epoch cfg query.store trace.afterObserved + 1 := by
      calc
        get_block_epoch cfg query.store trace.result + 1 =
            get_current_store_epoch cfg query.store := hresultPrevious
        _ ≤ get_block_epoch cfg query.store trace.afterObserved + 1 :=
          hselector.input_recent
    have hupper : get_block_epoch cfg query.store trace.afterObserved + 1 ≤
        get_block_epoch cfg query.store trace.result + 1 :=
      Nat.add_le_add_right hgeometry.input_epoch_le_result 1
    exact Nat.add_right_cancel (Nat.le_antisymm hupper hlower)
  have hinputRoot : trace.afterObserved = B.anchor.root := by
    calc
      trace.afterObserved = query.store.finalized_checkpoint.root :=
        horigin.input_eq
      _ = B.anchor.root := congrArg Checkpoint.root hfinalizedAnchor
  have hanchorKnown : B.anchor.root ∈ query.store.block_roots := by
    simpa only [hinputRoot] using hinputKnown
  have hanchor0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
    have hroot : B.anchor.root = ablk.root := by
      rw [hanchor, hgen]
      rfl
    rw [hgen, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorBlocks : E.genesis_store.blocks B.anchor.root =
      query.store.blocks B.anchor.root :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext obs 0)
      (by simpa only [query, E.weakFcrStep_store] using
        E.blockProvenance cfg ext obs (n + 1))
      (by simpa only [show E.store cfg ext obs 0 = E.genesis_store from rfl]
        using hanchor0)
      hanchorKnown
  have hanchorSlot := E.trustedAnchor_slot_eq_start_of_trajectory
    cfg ext hT hanchor hboundary
  have hanchorEpoch : get_block_epoch cfg query.store B.anchor.root =
      B.anchor.epoch := by
    simp only [get_block_epoch, ← hanchorBlocks, hanchorSlot,
      compute_start_slot_at_epoch, compute_epoch_at_slot]
    exact Nat.mul_div_cancel _ cfg.slots_per_epoch_pos
  have hinputEpoch : get_block_epoch cfg query.store trace.afterObserved =
      B.anchor.epoch := by
    simpa only [hinputRoot] using hanchorEpoch
  have hresultEpoch : get_block_epoch cfg query.store trace.result =
      B.anchor.epoch := hinputResultEpoch.symm.trans hinputEpoch
  have hanchorAt : E.AcceptedBlockAt cfg ext B.anchor.root
      (query.store.blocks B.anchor.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hanchorKnown
  have hpayload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B
      B.anchor.root B.anchor.epoch :=
    Execution.AcceptedHistoricalA32GatePayloadAt.of_anchor cfg ext B hanchorAt
      (by simpa only [get_block_epoch] using hanchorEpoch)
      hanchorExact.symm
  have hlineageAnchor : E.AcceptedHistoricalA32LineageAt cfg ext B
      B.anchor.root B.anchor.epoch :=
    Execution.AcceptedHistoricalA32LineageAt.refl cfg ext hpayload
  have hlineageInput : E.AcceptedHistoricalA32LineageAt cfg ext B
      trace.afterObserved B.anchor.epoch := by
    simpa only [hinputRoot] using hlineageAnchor
  have hextended : E.AcceptedHistoricalA32LineageAt cfg ext B
      trace.result B.anchor.epoch :=
    Weak.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual
      cfg ext B hT hcoh hHn1 hselector
        (by simpa only [query] using hinputKnown) hlineageInput
        (by simpa only [query] using hinputEpoch)
        (by simpa only [query] using hresultEpoch)
  simpa only [query, hresultEpoch] using
    (show Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      trace.result B.anchor.epoch) from ⟨hextended⟩)

/-- Clone of `WeakBankedJustification.lean`'s `private auTip_walkKnown` (a
`private` declaration cannot be reused across modules).  Honesty-free. -/
private theorem auTip_walkKnown
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) :
    WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [Execution.TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  obtain ⟨carr, _hdesc, hformed⟩ := hAU
  obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
  have hcertified : CertifiedJustified cfg E B.anchor c :=
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.AcceptedIncludedAttestationRelation.relation cfg ext E
        B.state.includedAttestations) hincluded
  have hanchorEpochLe : B.anchor.epoch ≤ c.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
  have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
      compute_start_slot_at_epoch cfg c.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks B.anchor.root).slot tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
      B.anchor.root hanchorMem tip htip
  apply hwalkAnchor.mono
  rw [hanchorBlock]
  exact hboundary'.trans hstartLe

/-- The block epoch of an accepted AU checkpoint's root is at most the
checkpoint's own epoch, at an arbitrary observer's store.

This is the slot bound `Weak.auCheckpoint_known_and_below_tip`
(`WeakBankedJustification.lean`) derives internally and discards; it is the
observer-side replacement for `ResetCheckpointRealizedAt.root_slot_le_boundary`
in the observed-reset arm below. -/
theorem auCheckpoint_blockEpoch_le
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) :
    get_block_epoch cfg (E.store cfg ext obs n) c.root ≤ c.epoch := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  have hwalk : WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip :=
    auTip_walkKnown cfg ext B hT hanchor hboundary obs n htip hAU
  have hcheckpoint := B.coherence.au_checkpoint_of_known hstore tip htip c hAU
  have hroot : c.root = (get_ancestor (E.store cfg ext obs n)
      (ForkChoiceNode.mk tip)
      (compute_start_slot_at_epoch cfg c.epoch)).root := by
    have hr := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block, get_checkpoint_block] using hr
  obtain ⟨_hknown, hslotLe⟩ := get_ancestor_spec hparentSlots hwalk
  have hcSlot : ((E.store cfg ext obs n).blocks c.root).slot ≤
      compute_start_slot_at_epoch cfg c.epoch := by
    rw [hroot]; exact hslotLe
  have hscaled : get_block_epoch cfg (E.store cfg ext obs n) c.root *
      cfg.slots_per_epoch ≤ c.epoch * cfg.slots_per_epoch :=
    (start_slot_at_block_epoch_le cfg (E.store cfg ext obs n) c.root).trans
      hcSlot
  exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos

/-- Query-local weak twin of
`Execution.StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed`.

Rule delta 5 makes the observed checkpoint literally the head's own
unrealized justification (`observed_eq_head_unrealized`), so the GU seed is
the query fork-choice head and the "checkpoint root is at or below its
boundary" step is the accepted AU geometry above rather than a reset
realization record.  This discharges the *query-local* half of the
observed-reset origin; only the seed's dissemination to honest endpoints is
left in the residual record. -/
theorem StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : Weak.GetLatestConfirmedTrace cfg ext
      (E.weakFcrStep cfg ext obs n)}
    (horigin : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hprevious : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          trace.result + 1 =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) :
    (get_head cfg (E.weakFcrStep cfg ext obs n).store).root ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots ∧
      is_ancestor (E.weakFcrStep cfg ext obs n).store
        (get_node_for_root
          (get_head cfg (E.weakFcrStep cfg ext obs n).store).root)
        (get_node_for_root trace.result) = true ∧
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          trace.result ≤
        (B.state.GU
          (get_head cfg (E.weakFcrStep cfg ext obs n).store).root).epoch := by
  let query := E.weakFcrStep cfg ext obs n
  have hqCurrent : query.store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  let head := (get_head cfg query.store).root
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh (n + 1) hHn1
  have hparentQ : ParentSlotLt query.store := by
    simpa only [query, hqCurrent] using hparentN1
  have hwalkQ : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, hqCurrent] using hwalkN1
  have hheadKnown : head ∈ query.store.block_roots := by
    simpa only [query, head, hqCurrent] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hHn1
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    rw [horigin.afterObserved_eq, hqCurrent]
    exact Weak.weakFcrStep_observed_known cfg ext B hT hanchor hboundary obs n
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)
  have hheadResult : is_ancestor query.store
      (get_node_for_root head) (get_node_for_root trace.result) = true := by
    have hbelow := Weak.strictSelectedResult_below_head cfg ext hparentQ
      hwalkQ hheadKnown hinputKnown hstrict
    simpa only [head, hselector.result_eq] using hbelow
  have hheadKnownN1 : head ∈ (E.store cfg ext obs (n + 1)).block_roots := by
    simpa only [hqCurrent] using hheadKnown
  have hguHead : query.store.unrealized_justifications head =
      B.state.GU head := by
    rw [hqCurrent]
    exact E.accepted_unrealized_justification_eq
      B.coherence.toAcceptedFFGSelectorCoherence obs (n + 1) hheadKnownN1
  have hobservedGU :
      query.current_epoch_observed_justified_checkpoint =
        B.state.GU head := by
    exact horigin.observed_eq_head_unrealized.trans hguHead
  have hAU : B.state.AU cfg ext head (B.state.GU head) :=
    B.state.gu_AU cfg ext
      (E.acceptedRoot_of_causal_known cfg ext
        (E.store_causal cfg ext obs (n + 1)) hheadKnownN1)
  have hobservedBlockLe : get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root ≤
      query.current_epoch_observed_justified_checkpoint.epoch := by
    rw [hobservedGU, hqCurrent]
    exact Weak.auCheckpoint_blockEpoch_le cfg ext B hT hanchor hboundary
      obs (n + 1) hheadKnownN1 hAU
  have hresultEpochEq : get_block_epoch cfg query.store trace.result =
      get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root :=
    Nat.add_right_cancel
      (hprevious.trans horigin.observed_previous_epoch.symm)
  refine ⟨hheadKnown, hheadResult, ?_⟩
  calc
    get_block_epoch cfg query.store trace.result =
        get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root :=
      hresultEpochEq
    _ ≤ query.current_epoch_observed_justified_checkpoint.epoch :=
      hobservedBlockLe
    _ = (B.state.GU head).epoch :=
      congrArg Checkpoint.epoch hobservedGU

/-- Weak twin of `StrictSelectedResultMechanicalFacts.
canonicalThroughoutNextEpoch_of_previousEpochStart`.  The strong proof's
`confirmed_known_at_query_slot_start_minimal` (query node as relay receiver)
is replaced by `confirmed_known_at_all_honest_endpoints_at_observer` read at
the query second itself — at an epoch-start call the query slot's first second
*is* `n + 1`, so the two coincide. -/
theorem StrictSelectedResultMechanicalFacts.canonicalThroughoutNextEpoch_of_previousEpochStart
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {n : Nat}
    (hcomm : E.PrefixCommitteeAgreement cfg ext
      (E.store cfg ext obs (n + 1)))
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    {input selected : Root}
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input selected)
    {e : Epoch}
    (hprevious : e + 1 = get_current_store_epoch cfg
      (E.store cfg ext obs (n + 1)))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext obs (n + 1))) = true)
    {w : ValidatorIndex} {m : Nat}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt
      cfg ext (n + 1) selected m) :
    E.CanonicalThroughoutEpoch cfg ext selected (e + 1) := by
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store =
      E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hadvance : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
      get_current_slot cfg (E.store cfg ext obs n) := by
    unfold Execution.IsFCRCallAt at hcall
    simpa only [E.store_current_slot cfg ext obs n,
      E.store_current_slot cfg ext obs (n + 1)] using hcall
  have hstartEq : E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext hA n hn1H hadvance
  have hqBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg (e + 1) := by
    have hzero : compute_slots_since_epoch_start cfg
        (E.slot_at cfg (n + 1)) = 0 := by
      simpa only [is_start_slot_at_epoch, decide_eq_true_eq,
        E.store_current_slot cfg ext obs (n + 1)] using hstart
    have hboundaryEq : E.slot_at cfg (n + 1) =
        compute_start_slot_at_epoch cfg
          (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
      simp only [compute_slots_since_epoch_start,
        compute_start_slot_at_epoch] at hzero ⊢
      exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hzero)
        (Nat.div_mul_le_self _ cfg.slots_per_epoch)
    simpa only [get_current_store_epoch,
      E.store_current_slot cfg ext obs (n + 1), hprevious] using hboundaryEq
  intro w' hw' m' hm'H hm'Epoch
  have hslotLower : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m' := by
    rw [hqBoundary]
    simpa only [compute_start_slot_at_epoch, ← hm'Epoch] using
      Nat.div_mul_le_self (E.slot_at cfg m') cfg.slots_per_epoch
  have hqLeM' : n + 1 ≤ m' := by
    have hlower := E.query_slot_start_le_of_slot_ge_minimal
      cfg ext hA hslotLower
    simpa only [hstartEq] using hlower
  have hselectedAtQ : selected ∈
      (E.store cfg ext w' (n + 1)).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs (n + 1) hcomm (E.weakFcrStep cfg ext obs n) hqCurrent selected
      hn1H (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
      h.confirmed w' hw' (n + 1) (Nat.le_refl _) hn1H
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

/-! ## The residual observer-side inputs of the phase dispatcher

The strong dispatcher
(`StrictSelectedResultMechanicalFacts.fcrStep_endpointFilterOutcome`) consumes
four facts which are *not* phase bookkeeping and whose weak twins live outside
this module's remit:

1. the endpoint selected/justified **orientation**
   (`actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified`),
2. the endpoint **declared-epoch bound**
   (`actualCall_strictSelected_endpointJustifiedEpoch_le_result`),
3. the **late current-epoch** arm (accepted historical A3.2 lineage,
   full-epoch canonicity, paper A3.2 realization), and
4. the **late epoch-start previous** arm (the three
   `OrderedCandidateInputOrigin` producers of
   `AcceptedPreviousEpochStartSupply.lean`).

Each of 1–4 bottoms out in the accepted SIR / A3.2 stack, whose observer-side
port is the wave's remaining work (see this module's final section).  They are
therefore collected here as one explicitly-named record so that the dispatcher
below proves exactly the S7 content — the phase split, the three early cells,
the mid-epoch previous cell, and the strict-edge elimination — with the
residue carried, named, and reportable rather than silently absorbed.

The record is *not* floor-classified: it is a proof obligation, not an
assumption. -/

/-- The four residual endpoint inputs of the weak phase dispatcher.

Every field is stated exactly as the corresponding strong fact's conclusion,
instantiated at the weak evaluator's own call, with the same binder list the
strong dispatcher passes. -/
structure ObserverStrictCallFilterInputsAt (E : Execution Root)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (obs : ValidatorIndex) (n : Nat) : Prop where
  /-- Weak twin of
  `actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified`'s
  second component. -/
  result_descends_endpoint_justified :
    ∀ {c : Root} {w : ValidatorIndex} {m : Nat}, w ∈ E.honest →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
      c ∈ (E.store cfg ext w m).block_roots →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
        (get_node_for_root c) = true →
      (∀ w' ∈ E.honest, ∀ m' : Nat,
        E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
        E.WithinHorizon cfg m' →
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
          (E.store cfg ext w' m').block_roots) →
      E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root c) ≠ true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true
  /-- Weak twin of
  `actualCall_strictSelected_endpointJustifiedEpoch_le_result`. -/
  endpoint_justified_epoch_le_result :
    ∀ {c : Root} {w : ValidatorIndex} {m : Nat}, w ∈ E.honest →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
      c ∈ (E.store cfg ext w m).block_roots →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
        (get_node_for_root c) = true →
      (∀ w' ∈ E.honest, ∀ m' : Nat,
        E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
        E.WithinHorizon cfg m' →
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
          (E.store cfg ext w' m').block_roots) →
      E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root c) ≠ true →
      (E.store cfg ext w m).justified_checkpoint.epoch ≤
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
  /-- The accepted historical A3.2 lineage of a current-epoch weak confirmed
  result: the weak twin of
  `Execution.acceptedHistoricalA32CurrentLineage_of_completedPrefixes`, i.e.
  the observer-side instance of the `AcceptedHistoricalA32Induction.lean`
  write-back induction, run over `E.weakConfirmed`.

  This is the *only* input the late current-epoch cell still needs: site 1's
  full-epoch canonicity is discharged above, and
  `acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage` is
  applied at the honest endpoint itself (its query-node honesty binder is
  inert — it reads the query store only through knownness and the block
  epoch, both of which hold at `(w, m)`). -/
  current_lineage :
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    ∃ e : Epoch, Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e)
  /-- The `carried` origin of an epoch-start strict previous result: the weak
  twin of
  `Execution.StrictSelectorAdvanceAt.previousCarried_epochStartLineage`.  Like
  `current_lineage` it bottoms out in the observer-side instance of the
  historical A3.2 write-back induction — that induction is the *only* thing it
  needs beyond the already-ported
  `Weak.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual`. -/
  previous_epochStart_carried_lineage :
    Weak.CarriedCandidateInputAt cfg ext (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) →
    get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) = true →
    Nonempty (E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result))
  /-- The `observedReset` origin of an epoch-start strict previous result.
  Its query-local GU seed is fully discharged above
  (`Weak.StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed`);
  what remains is exactly the *dissemination* of that seed — the query
  fork-choice head at an epoch-start second — to honest endpoints.

  This is §4 of the wave design: at an epoch start the tentative-entry gate
  takes the uncertified `is_start_slot_at_epoch` escape, so no head broadcast
  certificate is available at the query second itself and stage S3's
  `Weak.headSeed_known_at_all_honest_endpoints_at_observer` does not apply.
  Under rule delta 5 the observed checkpoint is the banked `UJ(head)` and the
  banking gate certifies its *supplier*, so this is the site
  `WeakBankedJustification.lean`'s consumption lemmas are expected to close
  (the design's alternative is rule delta 5′, which would certify the
  epoch-start escape directly). -/
  previous_epochStart_observedReset_headDisseminated :
    Weak.ObservedResetCandidateInputAt cfg ext (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) →
    ∀ w ∈ E.honest, ∀ m : Nat, E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
      (get_head cfg (E.weakFcrStep cfg ext obs n).store).root ∈
        (E.store cfg ext w m).block_roots

/-! ## Exhaustive weak actual-call endpoint dispatcher -/

/-- **Weak twin of
`StrictSelectedResultMechanicalFacts.fcrStep_endpointFilterOutcome`.**

The phase split is identical to the strong one: current vs previous in the
observer's own weak query store, then same-epoch / next-epoch / late at the
endpoint, with the mid-epoch previous cell taking the direct GU-seed route.
The three early cells and the mid-epoch previous cell are fully discharged
above; the two late cells are supplied by `hinputs`. -/
noncomputable def
    StrictSelectedResultMechanicalFacts.fcrStep_endpointFilterOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (horigin : Weak.OrderedCandidateInputOrigin cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (h : Weak.StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
    (hinputs : Weak.ObserverStrictCallFilterInputsAt cfg ext E B obs n)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    {r0 a c : Root} {lo es sigma querySlot : Slot}
    (hgeom : Weak.StrictSelectedEdgeGeometry cfg ext E
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result r0 a c
      obs (n + 1) (E.weakFcrStep cfg ext obs n) w m
        lo es sigma querySlot)
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
    (hIH : E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
      (E.store cfg ext w m)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
  classical
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
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
  have hacc : CheckpointCertificateAccountability cfg E B.anchor :=
    CheckpointCertificateAccountability.of_assumptions cfg
      (Execution.SelectedMarginAssumptions.toFFGAccountabilityAssumptions
        cfg ext E hMargin)
  have hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    hgeom.query_slot_le_endpoint cfg ext
  have hstartM : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hMargin hslotQM
  have hselectedM : trace.result ∈ (E.store cfg ext w m).block_roots :=
    hselectedKnown w hw m hstartM hmH
  have hresultJustified : is_ancestor (E.store cfg ext w m)
      (get_node_for_root trace.result)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true :=
    hinputs.result_descends_endpoint_justified hw hmH hslotQM hcM
      hselectedC hselectedKnown hIH hnotCovered
  have hjustifiedEpoch :
      (E.store cfg ext w m).justified_checkpoint.epoch ≤
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          trace.result :=
    hinputs.endpoint_justified_epoch_le_result hw hmH hslotQM hcM
      hselectedC hselectedKnown hIH hnotCovered
  have hqueryEpochLeEndpoint :
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store ≤
        get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.weakFcrStep_store,
      E.store_current_slot, compute_epoch_at_slot]
    exact Nat.div_le_div_right hslotQM
  rcases h.current_or_previous_epoch with hcurrent | hprevious
  · by_cases hsame : get_current_store_epoch cfg (E.store cfg ext w m) =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store
    · exact h.fcrStep_currentSame_endpointFilterOutcome cfg ext hT hsync
        hstatic hbyz hdomain hji B hanchor hboundary hDelay P V
        hanchorExact hacc hcoh hn1H hcall hcurrent hw hmH hsame hgeom
        hresultJustified
    · by_cases hnext : get_current_store_epoch cfg (E.store cfg ext w m) =
          get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store + 1
      · exact h.fcrStep_currentNext_endpointFilterOutcome cfg ext hT hsync
          hstatic hbyz hdomain hji B hanchor hboundary hDelay P V
          hanchorExact hacc hcoh hn1H hinput hselector.result_eq.symm
          hselector.result_ne_input hcurrent hw hmH hnext hgeom
          hresultJustified
      · have hlate : get_block_epoch cfg
            (E.weakFcrStep cfg ext obs n).store trace.result + 2 ≤
          get_current_store_epoch cfg (E.store cfg ext w m) := by
          have hqLt : get_current_store_epoch cfg
                (E.weakFcrStep cfg ext obs n).store <
              get_current_store_epoch cfg (E.store cfg ext w m) :=
            Nat.lt_of_le_of_ne hqueryEpochLeEndpoint
              (fun heq => hsame heq.symm)
          have hqNextLt : get_current_store_epoch cfg
                (E.weakFcrStep cfg ext obs n).store + 1 <
              get_current_store_epoch cfg (E.store cfg ext w m) :=
            Nat.lt_of_le_of_ne hqLt (fun heq => hnext heq.symm)
          rw [hcurrent]
          simpa only [Nat.add_assoc, Nat.reduceAdd] using hqNextLt
        obtain ⟨e, ⟨hlineage⟩⟩ := hinputs.current_lineage hcurrent
        have hqCurrent : (E.weakFcrStep cfg ext obs n).store =
            E.store cfg ext obs (n + 1) :=
          E.weakFcrStep_store cfg ext obs n
        have hselectedQ : trace.result ∈
            (E.store cfg ext obs (n + 1)).block_roots := by
          simpa only [hqCurrent] using h.result_known
        have hselectedEpochQ : get_block_epoch cfg
            (E.store cfg ext obs (n + 1)) trace.result = e :=
          hlineage.tip_epoch_eq_of_causal_known cfg ext hT
            (E.store_causal cfg ext obs (n + 1)) hselectedQ
        have heCurrent : e = get_current_store_epoch cfg
            (E.store cfg ext obs (n + 1)) := by
          rw [← hselectedEpochQ]
          simpa only [hqCurrent] using hcurrent
        have hlateE : e + 2 ≤
            get_current_store_epoch cfg (E.store cfg ext w m) := by
          simpa only [hqCurrent, hselectedEpochQ] using hlate
        have hjustifiedEpochE :
            (E.store cfg ext w m).justified_checkpoint.epoch ≤ e := by
          simpa only [hqCurrent, hselectedEpochQ] using hjustifiedEpoch
        have hcanonical : E.CanonicalThroughoutEpoch cfg ext
            trace.result (e + 1) :=
          Weak.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch_at_observer
            cfg ext hMargin (hcoh.committees_agree (n + 1) hn1H) hn1H
            hqCurrent hselectedQ
            (by simpa only [hqCurrent] using h.parent_known)
            h.confirmed heCurrent hlateE hIH
        -- the query-node honesty binder of the late-lineage producer is
        -- inert, so it is instantiated at the honest endpoint itself
        have hselectedEpochM : get_block_epoch cfg
            (E.store cfg ext w m) trace.result = e :=
          hlineage.tip_epoch_eq_of_causal_known cfg ext hT
            (E.store_causal cfg ext w m) hselectedM
        exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage
          cfg ext B hT hsync hdomain hphase0 hanchor hboundary hpaper P V
            hanchorExact hacc hw hmH hlineage hselectedM hselectedEpochM
            hcanonical hw hmH hselectedM hlateE hjustifiedEpochE
            hresultJustified
  · by_cases hsame : get_current_store_epoch cfg (E.store cfg ext w m) =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store
    · exact h.fcrStep_previous_endpointFilterOutcome cfg ext hT hsync
        hstatic hbyz hdomain hji B hanchor hboundary hDelay P V
        hanchorExact hacc hcoh hn1H hcall hprevious hw hmH hsame hgeom
        hresultJustified
    · have hlate : get_block_epoch cfg
          (E.weakFcrStep cfg ext obs n).store trace.result + 2 ≤
        get_current_store_epoch cfg (E.store cfg ext w m) := by
        have hqLt : get_current_store_epoch cfg
              (E.weakFcrStep cfg ext obs n).store <
            get_current_store_epoch cfg (E.store cfg ext w m) :=
          Nat.lt_of_le_of_ne hqueryEpochLeEndpoint
            (fun heq => hsame heq.symm)
        calc
          get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
                trace.result + 2 =
              (get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
                trace.result + 1) + 1 := by
                  simp only [Nat.add_assoc, Nat.reduceAdd]
          _ = get_current_store_epoch cfg
                (E.weakFcrStep cfg ext obs n).store + 1 := by rw [hprevious]
          _ ≤ get_current_store_epoch cfg (E.store cfg ext w m) := hqLt
      by_cases hstart : is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) = true
      · have hqCurrent : (E.weakFcrStep cfg ext obs n).store =
            E.store cfg ext obs (n + 1) :=
          E.weakFcrStep_store cfg ext obs n
        have hselectedQ : trace.result ∈
            (E.store cfg ext obs (n + 1)).block_roots := by
          simpa only [hqCurrent] using h.result_known
        have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
          E.causalRealizedFinalizationLag_of_acceptedDelay
            cfg ext B hT hanchor hDelay
        have lateFromLineage : ∀ {e : Epoch},
            E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e →
            E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
              (E.store cfg ext w m) trace.result := by
          intro e hlineage
          have hselectedEpochQ : get_block_epoch cfg
              (E.store cfg ext obs (n + 1)) trace.result = e :=
            hlineage.tip_epoch_eq_of_causal_known cfg ext hT
              (E.store_causal cfg ext obs (n + 1)) hselectedQ
          have hpreviousE : e + 1 = get_current_store_epoch cfg
              (E.store cfg ext obs (n + 1)) := by
            rw [← hselectedEpochQ]
            simpa only [hqCurrent] using hprevious
          have hlateE : e + 2 ≤
              get_current_store_epoch cfg (E.store cfg ext w m) := by
            simpa only [hqCurrent, hselectedEpochQ] using hlate
          have hjustifiedEpochE :
              (E.store cfg ext w m).justified_checkpoint.epoch ≤ e := by
            simpa only [hqCurrent, hselectedEpochQ] using hjustifiedEpoch
          have hcanonical : E.CanonicalThroughoutEpoch cfg ext
              trace.result (e + 1) :=
            h.canonicalThroughoutNextEpoch_of_previousEpochStart cfg ext
              hMargin (hcoh.committees_agree (n + 1) hn1H) hn1H hcall
              hpreviousE (by simpa only [hqCurrent] using hstart)
              hlateE hIH
          have hselectedEpochM : get_block_epoch cfg
              (E.store cfg ext w m) trace.result = e :=
            hlineage.tip_epoch_eq_of_causal_known cfg ext hT
              (E.store_causal cfg ext w m) hselectedM
          exact E.acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage
            cfg ext B hT hsync hdomain hphase0 hanchor hboundary hpaper P V
              hanchorExact hacc hw hmH hlineage hselectedM hselectedEpochM
              hcanonical hw hmH hselectedM hlateE hjustifiedEpochE
              hresultJustified
        cases horigin with
        | carried hcarried =>
            obtain ⟨hlineage⟩ :=
              hinputs.previous_epochStart_carried_lineage hcarried hprevious
                hstart
            exact lateFromLineage hlineage
        | finalizedReset hfinalized =>
            obtain ⟨hlineage⟩ :=
              Weak.StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage
                cfg ext B hT hanchor hboundary hLag hanchorExact hcoh hn1H
                  hfinalized hselector hprevious
            exact lateFromLineage hlineage
        | observedReset hobserved =>
            obtain ⟨hseedQ, hseedSelected, hguLower⟩ :=
              Weak.StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed
                cfg ext B hT hanchor hboundary hcoh hn1H hobserved hselector
                  hprevious
            exact
              Weak.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed
                cfg ext B hT hanchor hboundary P V hanchorExact hacc hdomain
                hcoh hn1H hselectedQ
                (by simpa only [hqCurrent] using hseedQ)
                (by simpa only [hqCurrent] using hseedSelected)
                hguLower
                (by simpa only [hqCurrent] using hprevious.symm)
                hw hmH
                (hinputs.previous_epochStart_observedReset_headDisseminated
                  hobserved w hw m hmH hslotQM)
                hlate hjustifiedEpoch hresultJustified
      · exact h.fcrStep_previousOffStart_late_endpointFilterOutcome
          cfg ext B hT hsync hstatic hbyz hdomain hji hanchor hboundary P V
            hanchorExact hacc hcoh hn1H hinput hselector.result_eq.symm
            hselector.result_ne_input hprevious hstart hw hmH hslotQM hlate
            hjustifiedEpoch hresultJustified

/-! ## Final weak strict-edge filter supplier -/

/-- **Complete weak filter supply for the strict branch of one actual
observer FCR call.**  Weak twin of
`Execution.StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`.

Every quantified endpoint edge is sent through the weak phase dispatcher and
the resulting endpoint outcome is retargeted to the concrete child edge by the
(reused, honesty-free) `AcceptedSelectedResultFilterOutcomeAt.child_filtered`.
The observer's honesty is nowhere assumed: it appears only as
`hcoh : E.ObserverCoherence cfg ext obs`. -/
noncomputable def
    StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (horigin : Weak.OrderedCandidateInputOrigin cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n))
    (hinputs : Weak.ObserverStrictCallFilterInputsAt cfg ext E B obs n) :
    Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      obs (n + 1) (E.weakFcrStep cfg ext obs n) := by
  have hmechanical := Weak.StrictSelectorAdvanceAt.mechanicalFacts cfg ext
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
    hcoh hn1H (E.weakFcrStep_store cfg ext obs n) hinput hselector
  intro a c w m lo es sigma querySlot hw hmH hgeom _hcne hcM
    hparentEdge hselectedC hselectedKnown hIH hnotCovered
  have houtcome := hmechanical.fcrStep_endpointFilterOutcome cfg ext B hT
    hsync hstatic hbyz hdomain hji hanchor hboundary hDelay hphase0 hpaper
      P V hanchorExact hcoh hn1H hcall hinput horigin hselector hinputs hw hmH
      hgeom hcM hselectedC hselectedKnown hIH hnotCovered
  have hfinalized : FinalizedBoundaryRealization cfg
      (E.store cfg ext w m) :=
    Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
      cfg ext B hT hanchor hboundary w m
  obtain ⟨hparent, hwalkK, hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain w hw m hmH
  exact houtcome.child_filtered cfg ext hfinalized hparent hwalkK
    hjustifiedKnown hcM hparentEdge hselectedC hnotCovered

end Weak

end FastConfirmation.Spec
