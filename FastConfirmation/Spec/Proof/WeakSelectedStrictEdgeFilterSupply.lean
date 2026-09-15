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
    acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed_at_observer
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
  exact Weak.acceptedSelectedResultFilterOutcome_retainedVisible_of_queryGUEpochSeed_at_observer
    cfg ext B hT hanchor hboundary P V hanchorExact hacc hdomain hcoh hn1H
      (by simpa only [E.weakFcrStep_store] using h.result_known)
      (by simpa only [E.weakFcrStep_store] using hseedQ)
      (by simpa only [E.weakFcrStep_store] using hseedSelected)
      hguLower
      (by simpa only [E.weakFcrStep_store] using hprevious.symm)
      hw hmH (hseedDissem w hw m hmH hslotQM) hlate hjustifiedEpoch
      hselectedJustified

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
  /-- The late current-epoch cell: the composite of
  `acceptedHistoricalA32CurrentLineage_of_completedPrefixes`,
  `canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch` (site 1 of
  the design's inventory) and
  `acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage`. -/
  current_late_outcome :
    ∀ {w : ValidatorIndex} {m : Nat}, w ∈ E.honest →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
      E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
        (E.store cfg ext w m).block_roots →
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result + 2 ≤
        get_current_store_epoch cfg (E.store cfg ext w m) →
      (E.store cfg ext w m).justified_checkpoint.epoch ≤
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true →
      Nonempty (E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
        (E.store cfg ext w m)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
  /-- The late epoch-start previous cell: the three-way
  `Weak.OrderedCandidateInputOrigin` split of
  `AcceptedPreviousEpochStartSupply.lean` composed with
  `canonicalThroughoutNextEpoch_of_previousEpochStart`. -/
  previous_epochStart_late_outcome :
    ∀ {w : ValidatorIndex} {m : Nat}, w ∈ E.honest →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) ≤ E.slot_at cfg m →
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result + 1 =
        get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store →
      is_start_slot_at_epoch cfg
        (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) = true →
      E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result ∈
        (E.store cfg ext w m).block_roots →
      get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result + 2 ≤
        get_current_store_epoch cfg (E.store cfg ext w m) →
      (E.store cfg ext w m).justified_checkpoint.epoch ≤
        get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true →
      Nonempty (E.AcceptedSelectedResultFilterOutcomeAt cfg ext B
        (E.store cfg ext w m)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result)

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
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
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
        exact (hinputs.current_late_outcome hw hmH hslotQM hcurrent hIH
          hselectedM hlate hjustifiedEpoch hresultJustified).some
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
      · exact (hinputs.previous_epochStart_late_outcome hw hmH hslotQM
          hprevious hstart hIH hselectedM hlate hjustifiedEpoch
          hresultJustified).some
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
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
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
    hsync hstatic hbyz hdomain hji hanchor hboundary hDelay P V hanchorExact
      hcoh hn1H hcall hinput hselector hinputs hw hmH hgeom hcM hselectedC
      hselectedKnown hIH hnotCovered
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
