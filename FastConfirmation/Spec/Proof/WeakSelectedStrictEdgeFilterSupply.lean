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

end Weak

end FastConfirmation.Spec
