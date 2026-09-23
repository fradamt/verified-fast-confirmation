# The epoch-indexed restructure — consumption trace of the positive A3.2 certification

Analysis only; **nothing under `FastConfirmation/` was modified**. Branch
`centaur/discharge-helper-provisos-202609161`. Paths relative to the repo root
(`/home/agent/workspace/vfc`). Companion notes:
[`proviso-discharge-map.md`](proviso-discharge-map.md),
[`justification-causality-contract.md`](justification-causality-contract.md).

---

## 0. Headline verdict

**The epoch-indexed restructure is sound for Trunk A — every consumption of the
positive quorum content of `AcceptedHistoricalA32GatePayloadAt.support_branch`
is gated on `e + 2 ≤ get_current_store_epoch (E.store w m)`, i.e. on the target
epoch being at least *two* epochs behind the consuming store.** This overturns
the pessimistic reading in the causality contract §6: the full-epoch span in
`currentTargetFutureSpan` is a *producer*-side obligation, never a consumer-side
one, so moving production into a per-epoch layer that runs after epoch `e` has
elapsed is type-correct at every A3.2 site.

**It is *not* sound as stated for Trunk B.** Three of the four arms of
`epochStart_or_endpointCurrentTargetPinned_of_callSite` consume a
`CertifiedJustified` for the *query's own current-epoch* target `T`. Those uses
are structurally class (b) — the opposing object is always the endpoint store's
already-materialized `justified_checkpoint` — but re-deriving the pin from
"causality + elapsed support" only covers the slot window `[slot_at q,
slot_at m)`. The **epoch-`e` prefix `[start_slot(e), slot_at q)` is uncovered**,
and the executable gate is arithmetically too weak to exclude a `>1/3`
conflicting quorum living entirely in that prefix. That is the true residual
obstruction; §7 states it exactly.

Two dead sub-clusters were found on the way (§8) — `currentSame`-cell payload
consumption and the retained-quorum-source structure — both deletable today and
both *removing* apparent counterexamples to the restructure. **Both have since
been deleted** (see the §8 annotations); line numbers quoted below are those of
the pre-deletion tree.

---

## 1. What counts as "positive certification content"

The payload (`FastConfirmation/Spec/Proof/AcceptedHistoricalA32Payload.lean:47-57`):

```lean
structure AcceptedHistoricalA32GatePayloadAt (B) (origin) (e) where
  origin_block …  origin_at …  origin_epoch …
  certified : Nonempty (CertifiedJustified cfg E B.anchor (B.state.C origin e))
  support_branch : B.state.C origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)
```

and the quorum record at `:32-41`, whose `quorum : ConcreteA32QuorumBefore cfg
ext E deadline target` carries `deadline = compute_start_slot_at_epoch cfg
(e+1)` (`deadline_eq`, `:38`).

**Excluded from this trace** (and deliberately so): every
`…formed_evidence.certified` occurrence — that is
`AcceptedFormedCheckpointEvidence.certified`, a *materialized store*
justification, a different field with a different provenance. `rg '\.certified\b'`
returns 50 hits; only the 13 listed in §2 originate from the gate payload or
from the gate realization that builds it.

---

## 2. Complete inventory of eliminations

| # | File:line | Eliminated | Enclosing declaration | What is extracted |
|---|---|---|---|---|
| P1 | `AcceptedHistoricalA32Payload.lean:106` | `hgate.certified` | `…GatePayloadAt.of_fixedSourceCurrentTarget` (`:88`) | producer-side `rw`; nothing used |
| P2 | `AcceptedHistoricalA32Payload.lean:107` | `hgate.support_branch` | same | producer-side repackaging |
| P3 | `AcceptedHistoricalA32Payload.lean:178` | `hpayload.certified` | `…GatePayloadAt.transport_sameEpoch` (`:134`) | `rw [hcheckpoint]`, opaque re-index |
| P4 | `AcceptedHistoricalA32Payload.lean:179` | `hpayload.support_branch` | same | opaque re-index |
| P5 | `AcceptedHistoricalA32Crossing.lean:50/51` | `hgate.certified/.support_branch` | `…GateRealization.fixedSource_of_acceptedSameEpochSegment` (`:35`) | producer-side source rewrite |
| P6 | `AcceptedCurrentTargetGateBridge.lean:373/374`, `CurrentTargetCertificateRealization.lean:1041-1047` | gate realization | quorum builder | **producer** |
| D1 | `AcceptedSelectedStrictEdgeFilterSupply.lean:705` | `hlineage.payload.certified` | `…LineageAt.payloadAtQuery_nonempty` (`:655`) | `CertifiedJustified.anchor_epoch_le` → `B.anchor.epoch ≤ e` only |
| D2 | `AcceptedActualSelectedJustifiedOrientation.lean:450` | idem | `…LineageAt.payloadAtExecutionStore` (`:403`) | idem |
| D3 | `AcceptedActualSelectedJustifiedOrientation.lean:562` | idem | `completedPrefix_acceptedHistoricalA32PayloadProducerAt` (`:467`) | idem (for `hwalkHead`) |
| D4 | `WeakHistoricalA32Induction.lean:695` | idem | `…LineageAt.payloadAtObserverStore` (`:647`) | idem |
| D5 | `WeakHistoricalA32Induction.lean:794` | idem | `observerCall_currentTargetHistoricalA32Payload` (`:726`) | idem |
| D6 | `AcceptedHistoricalLineageFinalizedPlacement.lean:429`, `:696` | idem | `…finalizedRoot_eq_queryCheckpointBlock_of_lineage` (`:356`), `…finalized_check_of_earlyHistoricalLineage` (`:637` — **since deleted**, §8.1) | idem |
| **A1** | `AcceptedSelectedStrictEdgeFilterSupply.lean:755` | `hpayload.support_branch` | `…LineageAt.lateVisibleSeedAt` (`:723`) | **quorum used positively** → `accepted_paperA32IncludedAtTip_of_concreteQuorum` |
| **A2** | `SelectedA32Semantics.lean:369` | gate-core `support_branch` | `selectedA32Semantic_of_fixedSourceGate_currentEpoch` (`:338`) | **quorum used positively** → `paperA32SupportThroughoutEpoch_of_concreteQuorum` |
| **B1** | `AcceptedHistoricalA32Payload.lean:310` | `hpayload.certified` | `acceptedHistoricalA32PayloadProducerAt_to_certificateProducer` (`:300`) | → `HistoricalCurrentTargetCertificateProducerAt` → Trunk B pin |
| **B2** | `WeakSelectedJustifiedOrientation.lean:157` | `hpayload.certified.some` | `Weak.epochStart_or_endpointCurrentTargetPinned_of_observerCallSite` (`:112`) | → `hacc.justified_unique hJ hT hepoch` |
| F1 | `AcceptedHistoricalLineageFinalizedPlacement.lean:443/451/526` | `hpayload.certified`, `.support_branch` | `…finalizedRoot_eq_queryCheckpointBlock_of_lineage` (`:356`) | pin against `IncludedCertifiedFinalized`, surround exclusion |
| F2 | `AcceptedHistoricalLineageFinalizedPlacement.lean:335-337` | `hQ.quorum` | `AcceptedHistoricalA32QuorumAt.exactFinalizedPrefix_of_included` (`:203`) | `not_surround_includedLink` → `False` |
| X1 | `AcceptedPhaseSourceCarriers.lean:449` | `h.payload.support_branch` | `…LineageAt.anchor_or_retainedQuorumSource` (`:442`) | pure repackaging — **DEAD, zero consumers**; **deleted**, see §8.2 |

`D1-D6` are *degenerate*: the only thing pulled out of `certified` is the
numeric inequality `B.anchor.epoch ≤ e` (via `CertifiedJustified.anchor_epoch_le`),
which licenses `trustedAnchor_boundaryWalkAtEpoch_of_trajectory`. No
justification content, weight, or uniqueness is touched. They survive **any**
weakening of the payload and would even survive replacing `certified` by a bare
`B.anchor.epoch ≤ e` field.

---

## 3. The write-back's same-epoch carry is **opaque**

Asked explicitly in the brief. Answer: **the current-epoch lineage *is* carried
to later calls inside the same epoch, but the write-back never eliminates
`certified` or `support_branch` while doing so.**

* The invariant field is
  `AcceptedHistoricalA32CurrentLineageAt.current_lineage`
  (`AcceptedHistoricalA32Induction.lean:36-40`), guarded by
  `get_block_epoch (store v n) (confirmed v n) = get_current_store_epoch (store v n)`
  — so the carried `e` is always the carrier store's own current epoch.
* Succ step (`acceptedHistoricalA32CurrentLineageAt_all`, `:214-315`): the
  call branch consumes `hprevious.current_lineage` at `:271` through
  `getLatestConfirmedTraceAt_currentLineage_step`
  (`AcceptedHistoricalA32OneStep.lean:27-247`). Inside, the previous lineage is
  used at `:130`, `:151-157` and flows into `hnoCrossingLineage` (`:101-113`) =
  `selectedCurrentNoCrossingLineage` (`AcceptedHistoricalA32Step.lean:115`),
  which ends at `:187` with `hprevious.extend …`.
* `AcceptedHistoricalA32LineageAt.extend`
  (`AcceptedHistoricalA32Payload.lean:240-258`) sets `payload := hlineage.payload`
  verbatim. The idle branch (`:301-315`) likewise just re-indexes.
* The only *fresh* payloads in the step are the crossing branch
  (`OneStep:78-100` → `selectedCurrentCrossingLineage_of_fixedSourceProducer`,
  `AcceptedHistoricalA32Step.lean:376`) and the anchor branch
  (`OneStep:176`, `:194` → `actualFinalizedResetCurrentAnchorLineage`,
  `AcceptedHistoricalA32Step.lean:580`). The observed-restart branch is
  vacuous (`OneStep:218-225`, `:240-247`).

**Consequence for the restructure.** The write-back is a *producer* of the
positive content, not a consumer of it; the intra-epoch carry is a structural
copy. A per-epoch layer can therefore replace the payload's positive fields by a
deferred/late-materialized object without touching the write-back recursion at
all, provided the object still supports `extend`/`transport_sameEpoch`.
Weak twins: `WeakHistoricalA32OneStep.lean:150/162/230/248`,
`WeakHistoricalA32Induction.lean:616` — identical shape.

---

## 4. `AcceptedPreviousEpochStartSupply` — confirmed previous-epoch (class **a**)

`StrictSelectorAdvanceAt.previousCarried_epochStartLineage`
(`AcceptedPreviousEpochStartSupply.lean:275-376`), the `current_lineage`
consumer at `:312`:

* `hstart : is_start_slot_at_epoch cfg (get_current_slot (E.store v (n+1))) = true`
  (`:287-288`) — the call sits at an **epoch-start slot**.
* `hprevious : get_block_epoch (fcrStep v n).store trace.result + 1 =
  get_current_store_epoch (fcrStep v n).store` (`:294-296`).
* The invariant is read at second `n` (`:302-304`), i.e. the *preceding* store,
  where `hcurrentN` (`:310-311`) makes the confirmed root current for that
  store; `hinputPrevious` (`:335-360`) then shows
  `e + 1 = currentEpoch(query)`.

So the supplied lineage is at epoch `e = currentEpoch(query) − 1` and the query's
current slot is `start_slot(e+1)`: **every vote slot of epoch `e` is strictly in
the past at the consuming second**. Name and behaviour agree. The sibling
`previousFinalizedReset_anchorLineage` (`:390-…`) supplies the anchor disjunct
and needs no quorum at all.

---

## 5. Trunk A — every positive quorum consumption is class **(a)**

The master dispatcher is
`StrictSelectedResultMechanicalFacts.fcrStep_endpointFilterOutcome`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:~1719-2018`). At `:1831` it splits
on `h.current_or_previous_epoch`, and in each arm it *first* excludes the two
near cells:

* `hsame : currentEpoch(endpoint) = currentEpoch(query)` → `:1834`
  `fcrStep_currentSame_endpointFilterOutcome` (`:1503`), and `:1913`
  `fcrStep_previous_endpointFilterOutcome` (`:1414`);
* `hnext : currentEpoch(endpoint) = currentEpoch(query) + 1` → `:1841`
  `fcrStep_currentNext_endpointFilterOutcome` (`:1606`).

`rg 'Lineage|payload|certified|support_branch|A32Quorum'` over `:1414-1718`
returns **nothing** — those three producers never touch the payload. Only after
both are excluded is `hlate` derived (`:1847-1867`, `:1918-1934`) and the
lineage route taken (`:1877-1910`, `:1960-1995`).

`acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage`
(`:1167-1200`) and `AcceptedHistoricalA32LineageAt.lateVisibleSeedAt`
(`:723-801`) both carry the hypothesis verbatim:

```lean
(hlate : e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m))
(hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e)
```

and `lateVisibleSeedAt` converts it at `:784-791` into
`hboundarySlot : compute_start_slot_at_epoch cfg (e+2) ≤ E.slot_at cfg m`
before handing `Q` to `accepted_paperA32IncludedAtTip_of_concreteQuorum`. The
quorum's deadline is `start_slot(e+1)` (`AcceptedHistoricalA32Payload.lean:38`)
and every `ConcreteHonestTargetVoteBefore` carries `before_deadline`
(`CurrentTargetA32Support.lean:~179-181`): **the whole quorum is a set of votes
cast at least one full epoch before the consuming second.** Nothing future-dated
is asserted at the consumption site.

`SelectedA32Semantics.lean:338-387` (A2) has exactly the same guard at `:358-359`.
Weak twins: `WeakSelectedStrictEdgeFilterSupply.lean:614`, `:1008`, `:1888`,
routed identically at `:2209-2372`.

`AcceptedHistoricalLineageFinalizedPlacement` (F1/F2) is store-time-free at
`:203-337` (no store, no slot, no current epoch in the signature) and
pin/exclude-only: `hacc.justified_unique` at `:297`/`:314` against an
`IncludedCertifiedFinalized`, and `not_surround_includedLink` at `:335-337`
deriving `False`. Class (a)/(b); no fresh weight is exported.

**Verdict for Trunk A: (a) everywhere.** The `currentTargetFutureSpan`
full-epoch reach (`CurrentTargetFutureSupport.lean:28/41`,
`CurrentTargetA32Support.lean:197-201`) is a burden on the *supplier*
(`AcceptedCurrentTargetA32GateRealizationProducerAt` at the crossing call), not
on any consumer. Deferring that supply by one epoch is compatible with every
consumer.

---

## 6. Trunk B — structurally class **(b)**, with the exact materialization citation

`epochStart_or_endpointCurrentTargetPinned_of_callSite`
(`SelectedPreQueryHistoricalSIR.lean:825-861`), accepted twin
`AcceptedSelectedJustifiedOrientation.lean:176-232`, weak twin
`WeakSelectedJustifiedOrientation.lean:112-167`. Four arms:

| Arm | Line (weak twin) | Source of `hT` | `J` = | Class |
|---|---|---|---|---|
| `currentCrossing` | `:843-848` (`:143-149`) | `CurrentTargetCertificateProducerAt` fed by the **proviso** (`gate ∧ support`) | endpoint `justified_checkpoint` | (b) |
| `currentHistorical` | `:849-854` (`:150-158`) | payload `certified` (B1/B2) | endpoint `justified_checkpoint` | (b) |
| `previousEpochStart` | `:855-856` (`:159-160`) | — | — | short circuit |
| `previousNoConflict` | `:857-861` (`:161-167`) | `noConflict_certifiedJustified_root_eq_currentTarget` **arithmetic branch** (`NoConflictCertificatePinning.lean:782`) | endpoint `justified_checkpoint` | (b) |

**Is `J` always materialized in the endpoint store at the bracket's endpoint
second `m`? Yes — cite:**

* Strong path: the pinning theorem takes
  `hendpoint : EndpointFFGPipeline cfg E anchor store`
  (`SelectedPreQueryHistoricalSIR.lean:831`), whose field
  `justified_certificate : Nonempty (CertifiedJustified cfg E anchor
  store.justified_checkpoint)` is `SelectedFilterBridge.lean:403-404`. Both call
  sites instantiate `store := E.store cfg ext w m`:
  `SelectedPreQueryHistoricalSIR.lean:1318` and `:1373`.
* Weak path: `WeakSelectedJustifiedOrientation.lean:139-141` obtains `hJ` from
  `ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate`
  (`AcceptedSelectedJustifiedOrientation.lean:154-172`) applied to
  `hstore : E.CausalStore cfg ext store`, and the caller at `:220` passes
  `E.store_causal cfg ext w m`, i.e. `store = E.store cfg ext w m`.
* `store.justified_checkpoint` is a *field of the endpoint store at second `m`*,
  and `endpointJustified_certificate`'s non-anchor arm reads it off
  `carrier.formed_evidence.certified` (`:168`). So `J` is materialized in a real
  honest view at `m` by construction. The `hepoch` premise is only introduced
  *after* `intro hepoch`, so the fact is used purely conditionally on
  `J.epoch = T.epoch`.

So the classification is **(b)** at all three live arms: no future vote content
is *named* in the conclusion; the target `T` is compared against a
past-materialized object. `NoConflictCertificatePinning.lean:782`'s arithmetic
branch is (b) in the same sense — `hc : CertifiedJustified anchor c` is the
*given* endpoint certificate, and the branch only manufactures the opposing
honest signer set.

---

## 7. The residual obstruction (why (b) here is not free)

Class (b) says the *conclusion* is past-facing. It does **not** by itself say
the pin is re-derivable once the current-epoch positive certification is gone.
Working the replacement out exactly:

Let `q = n+1` be the call second, `e = currentEpoch(query)`, `T = get_current_target query.store`,
and let `J = (E.store w m).justified_checkpoint` with `J.epoch = e`, `hslotQM :
slot_at q ≤ slot_at m` (`SelectedPreQueryHistoricalSIR.lean:1316`). Available
after the restructure:

1. **Causality** (`justification-causality-contract.md` §1): `J`'s 2/3 signer
   set `S ⊆ span_committee(e·SPE, e·SPE + SPE−1)` with every member's target
   attestation at `a.data.slot + 1 ≤ slot_at m`.
2. **Elapsed support**, derived from the strict-edge supplier's own induction
   `hIH` (`AcceptedSelectedStrictEdgeFilterSupply.lean:152-159`: every honest
   head at `slot_start(slot_at q) ≤ m'`, `slot_at m' < slot_at m` descends from
   `result`) plus `votes_head` + `get_checkpoint_block_of_ancestor`: every
   honest epoch-`e` vote at a slot in `[slot_at q, slot_at m)` targets `T`.
3. **Byzantine bound**: `weight(byzantine) < total/3`.

Split `S` by attestation slot. Honest members with slot `≥ slot_at q` target
`T`; if `J ≠ T` they cannot be in `S`. Hence
`weight(S ∩ {slot ≥ slot_at q}) ≤ weight(byzantine) < total/3`, so

> **`weight(S ∩ {start_slot(e) ≤ slot < slot_at q}) > total/3`.**

That set lives entirely in `currentTargetElapsedSpan`
(`CurrentTargetFutureSupport.lean:~36-38`). Nothing in the development excludes
it:

* The gate is `3 * honest_ffg_support > 1 * total_active_balance`
  (`FastConfirmation/Spec/Model/FFGHelpers.lean:103-110`; weak twin
  `Model/WeakSynchrony.lean:314-323`), and
  `compute_honest_ffg_support_for_current_target` *already blends* the observed
  elapsed score with the **projected future honest remainder**. Removing the
  future half leaves `observedHonest` alone, which is near-zero early in an
  epoch.
* The existing proof closes the gap the other way: it builds
  `currentTargetA32Signers = observedHonest ∪ (currentTargetFutureSpan).filter honest`
  (`CurrentTargetA32Support.lean:197-201`), proves `total < 3 · weight(signers)`
  via `noConflict_arithmeticBranch_oneThird`
  (`NoConflictCertificatePinning.lean:91-110`, used at `:793-796`), and
  intersects with `link.signers` through `one_third_honest_intersects_two_thirds`
  (`FFGQuorum.lean:89-96`) at `:826-829`. The `>1/3` comes from
  `currentTargetFutureHonestSeat_vote` (`CurrentTargetA32Support.lean:457`,
  proviso unfolded at `:504`) — i.e. **exactly the deleted proviso**.
* The epoch-indexed layer cannot help here: it supplies epoch `e`'s full
  support only from epoch `e+1` onward, whereas `m` may satisfy
  `slot_at m = slot_at q`, still inside epoch `e`. Trying to bootstrap from an
  *earlier call in epoch `e`* works for every call except the **first call of
  epoch `e` that is not at a start slot** — and that is precisely the
  configuration `previousNoConflict` is selected in (`hnotStart`,
  `SelectedPreQueryHistoricalSIR.lean:788-789`), while `previousEpochStart`
  (`:855-856`) already short-circuits the start-slot case.

**Statement of the obstruction.** *Under the restructure, Trunk B's pinning at
the epoch-`e` prefix `[start_slot(e), slot_at q)` is unprovable: a conflicting
epoch-`e` quorum can be assembled entirely from votes cast before the call,
carrying more than one third of total active weight, and the executable
no-conflict gate (`3·honest_ffg_support > total`) is satisfied by the projected
future half alone and therefore cannot exclude it.* This is not a futurity
obstruction in the sense of class (c) — nothing about future votes is asserted —
but the *replacement* argument the restructure offers for class (b) does not
reach. The obstruction is a **weight-coverage** gap on a past interval, and its
only current plugs are (i) the proviso itself, or (ii) an independent bound on
elapsed conflicting weight that the gate does not provide.

Corollary: the restructure **splits the trunks**, which is option (ii) of
`justification-causality-contract.md` §6, but with the trunks' difficulty
*reversed* relative to that note's prediction. Trunk A (the "most likely to
fail" one) is clean; Trunk B (the one that note hoped to save with E1) is where
the residue sits.

---

## 8. Dead sub-clusters found (deletable, and they remove apparent blockers)

1. **`currentSame`-cell payload consumption is dead.**
   `AcceptedCurrentSameSourceHistoryOutcome.retainedFinalizedAt_currentSameEndpoint`
   (`AcceptedCurrentSameEndpointSource.lean:710-756`) is the *only* site in the
   repo that consumes a lineage in the `EarlySelectedEndpointPhase.currentSame`
   cell (`AcceptedPhaseSourceCarriers.lean:387-397`), i.e. with
   `e = currentEpoch(query) = currentEpoch(endpoint)` (derived at `:745-752`).
   It and its result type `AcceptedCurrentSameRetainedFinalizedCarrierAt`
   (`:695-700`) have **zero consumers** (`rg` returns only `:695`, `:710`, `:741`).
   The live current-same route is the finality-free sibling
   `retainedAt_currentSameEndpoint` (`:652-693`, no `hlineage` argument), used at
   `AcceptedSelectedStrictEdgeFilterSupply.lean:1588` and
   `WeakSelectedStrictEdgeFilterSupply.lean:459`, which then closes finality from
   `hDelay : AcceptedRealizedFinalizationDelay`.
   **This is the single genuine same-epoch counterexample to the restructure, and
   it is dead code.** Deleting it (plus `…finalizedPlacementBeforeQueryAt_of_lineage`,
   `AcceptedHistoricalLineageFinalizedPlacement.lean:588`, also unreferenced)
   should be a precondition of any restructure wave.
   **Status: fully deleted. `retainedFinalizedAt_currentSameEndpoint`,
   `AcceptedCurrentSameRetainedFinalizedCarrierAt`, and — in the R0 follow-up
   sweep — `AcceptedRetainedPhaseSourceCarrierAt.finalized_check_of_earlyHistoricalLineage`
   (was `AcceptedHistoricalLineageFinalizedPlacement.lean:637`, consumed only
   here) and `…acceptedFinalizedPlacementBeforeQueryAt_of_lineage` (was `:588`)
   are all gone.**
2. **`AcceptedHistoricalRetainedQuorumSourceAt`** (`AcceptedPhaseSourceCarriers.lean:432-439`)
   and its producer `…anchor_or_retainedQuorumSource` (`:442-465`, `support_branch`
   at `:449`) — zero consumers repo-wide. Pure repackaging; delete.
   **Status: deleted.**
3. Already recorded in the map: `no_conflict` (landed), `gate_sound`,
   `target_justified_sound`, `SelectedA32Support.lean:147`.

---

## 9. Shape of the restructure, if Trunk B's residue is accepted or solved

### 9.1 What survives unchanged

Everything in §2 rows `D1-D6`, `P1-P6`, `F1-F2`, and the entire write-back
recursion (§3). Specifically:

* `AcceptedHistoricalA32Payload.lean` `extend` / `transport_sameEpoch` /
  `payloadAtTip` / `refl` — structural, opaque in the payload's positive fields.
* `AcceptedHistoricalA32Induction.lean:214-355` and
  `WeakHistoricalA32Induction.lean` twins — no change to the recursion, only to
  the *type* of the field the payload carries.
* `AcceptedPreviousEpochStartSupply.lean` (§4) — already previous-epoch.
* `AcceptedSelectedStrictEdgeFilterSupply.lean:1414-1718` (the three near-cell
  producers) — never touch the payload.
* `AcceptedHistoricalLineageFinalizedPlacement.lean` — store-time-free.

### 9.2 The per-epoch layer (new)

Introduce a *deferred* payload: replace `certified`/`support_branch` by a
predicate indexed by the consuming second,

```
A32DeferredCertification B origin e :=
  ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m → e + 2 ≤ get_current_store_epoch (E.store w m) →
     Nonempty (CertifiedJustified …) ∧ (anchor ∨ Nonempty (AcceptedHistoricalA32QuorumAt …))
```

so the payload is *constructed* at the crossing call as an obligation and
*discharged* by the per-epoch layer. The per-epoch layer proves, for each epoch
`e` and each honest `v` whose call in epoch `e` crossed:

> from the fold invariant `SafeFrom result (n+1)` established at the epoch-`e`
> call `n`, and from `HonestTargetAgreement.lean`'s constructor
> `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate` (wave 2, landed),
> derive the *full-epoch* `HonestVotesSupportTarget T (n+1)` once
> `start_slot(e+1) ≤ slot_at m` — every remaining vote slot of epoch `e` is then
> `≥ n+1` and the forward-unbounded `SafeFrom` covers it — and feed it to the
> existing producer `AcceptedCurrentTargetA32GateRealizationProducerAt`
> (`CurrentTargetA32Support.lean:701`) unchanged.

Because `currentTargetFutureSpan` reaches `currentTargetEpochEnd`, this is the
**exact** cap the existing quorum builder demands; no capped-proviso predicate
(`HonestVotesSupportTargetUpTo`) and no re-proof of
`currentTargetFutureHonestSeat_vote` / `AcceptedCurrentTargetGateBridge.lean:1042`
is needed. That is the main saving over map §6 wave 5.

Non-circularity: the epoch-`e` call's `SafeFrom` conclusion is consumed only at
`e+2`-or-later endpoints (§5), and the per-epoch discharge itself is invoked only
at those endpoints, so the dependency is `call(e) → layer(e) → consumer(≥ e+2)`
with strictly increasing epoch index.

### 9.3 Where the causality field is invoked

Only in the Trunk-B replacement (§7 item 1), i.e. only if the residue of §7 is
solved. It is *not* needed for Trunk A at all under this restructure — the
`e + 2` guard already places every quorum vote in the consumer's past without
any appeal to `justified_targets_before_endpoint`.

### 9.4 Wave spec

| Wave | Content | Blast radius | Green? |
|---|---|---|---|
| R0 | Delete §8 dead code (`retainedFinalizedAt_currentSameEndpoint`, `AcceptedCurrentSameRetainedFinalizedCarrierAt`, `acceptedFinalizedPlacementBeforeQueryAt_of_lineage`, `AcceptedHistoricalRetainedQuorumSourceAt`, `anchor_or_retainedQuorumSource`), plus the follow-up sweep (`finalized_check_of_earlyHistoricalLineage`, `honest_target_vote_before_next_epoch`, `selected_strict_current_balance_checkpoint_key`, the two `SelectedFilterFFGPipeline` tip-source fields) | 5 files | **fully landed** |
| R1 | Replace `D1-D6`'s `certified` elimination by an explicit `anchor_epoch_le : B.anchor.epoch ≤ e` payload field (additive) — decouples 6 sites from the positive content | `AcceptedHistoricalA32Payload.lean` + 5 consumers | **landed** |
| R2 | Introduce `A32DeferredCertification` and thread it through `extend`/`transport_sameEpoch`/`payloadAtTip`; keep a `≥ e+2`-gated projection used at A1/A2 | `AcceptedHistoricalA32Payload.lean`, `…Step`, `…Crossing`, `…OneStep`, `…Induction`, weak twins | **landed for `support_branch` only** — see §10 |
| R3 | Per-epoch discharge layer (§9.2) over `WeakTrajectorySafety.lean`'s strengthened `∀ k ≤ n` fold (wave 3, landed) | new file + `WeakTrajectorySafety.lean` | **blocked** — §10 |
| R4 | Drop the Trunk-A half of `Weak.SelectedHelperProvisosAt.current_target` at `WeakHistoricalA32Step.lean:280` | `WeakHistoricalA32Step.lean`, `SelectedA32Support.lean` | **blocked by R3** |
| R5 | **Blocked by §7.** Trunk B: needs either a new elapsed-conflicting-weight bound or retention of the proviso at `WeakPreQuerySIR.lean:339` | — | — |

---

## 10. Correction: `certified` is **not** `e+2`-gated, and that blocks R3/R4

Written while landing R1/R2; it supersedes §9.2's claim that *both* positive
payload fields can move behind the guard, and §9.1's claim that `F1`/`F2`
survive unchanged.

### 10.1 `F1`/`F2` were dead, and are now deleted

`EarlySelectedEndpointPhase.finalizedRoot_eq_queryCheckpointBlock_of_lineage`
(row `F1`) lost its only consumer when R0's follow-up sweep deleted
`AcceptedRetainedPhaseSourceCarrierAt.finalized_check_of_earlyHistoricalLineage`
(§8.1). `rg` over the tree then returned **zero** external references to any
public declaration of `AcceptedHistoricalLineageFinalizedPlacement.lean` —
`F1`, `AcceptedHistoricalA32QuorumAt.exactFinalizedPrefix_of_included` (`F2`),
`ConcreteA32QuorumBefore.not_surround_includedLink` and
`…intersects_supermajorityLink_honest` — so the whole module is gone. Its two
importers (`AcceptedSelectedStrictEdgeFilterSupply.lean`,
`AcceptedCurrentSameEndpointSource.lean`) now import
`AcceptedHistoricalFinalizedPlacementAdapters` directly.

**Consequence.** After that deletion `support_branch` has exactly one consumer
outside the payload module's own transport, namely `A1`
(`AcceptedHistoricalA32LineageAt.lateVisibleSeedAt`), and that consumer *is*
`e+2`-gated. So the guarded form is now the honest type of the field, and R2
lands it: `Execution.AcceptedHistoricalA32DeferredSupportAt`.

### 10.2 `certified` cannot follow it

`certified` still has two live consumers with **no** `e+2` guard in scope, both
in the `currentHistorical` arm of the two surviving orientation dispatchers:

* `B1` `acceptedHistoricalA32PayloadProducerAt_to_certificateProducer`
  (`AcceptedHistoricalA32Payload.lean`) →
  `Execution.epochStart_or_endpointOriginOrPinned_of_acceptedCallSite`
  (`AcceptedSelectedJustifiedOrientation.lean`, `currentHistorical` arm);
* `B2` `Weak.epochStart_or_endpointOriginOrPinned_of_observerCallSite`
  (`WeakSelectedJustifiedOrientation.lean`, `currentHistorical` arm).

Both arms are *live* — `StrictSelectedHistoricalSIRCallSite.currentHistorical`
is constructed at `SelectedPreQueryHistoricalSIR.lean:128` and
`WeakPreQuerySIR.lean:368` — and both use the certificate for
`hacc.justified_unique hJ hT hepoch` against the endpoint's *own*
`justified_checkpoint` at an endpoint `m` that may still be inside epoch `e`
(the arm is selected precisely when the result is current-epoch and the call
found no crossing edge). N5/N6 removed the proviso from the `currentCrossing`
and `previousNoConflict` arms by routing them through
`EndpointOriginOrPinnedProducerAt`, but that producer's antecedent is one of
the two *executable gate booleans at the current query*, and the
`currentHistorical` arm has neither.

### 10.3 Why that blocks R3/R4

In the non-anchor branch the payload's `certified` is *manufactured from the
quorum*: `certifiedCurrentTarget_of_gate_and_stateSemantics`
(`CurrentTargetCertificateRealization.lean:~508-700`) builds
`currentTargetA32Signers` and the certificate from
`currentTargetFutureHonestSeat_vote`, which unfolds `hsupport` at
`CurrentTargetA32Support.lean:504`. So `certified` and `support_branch` have a
*single* producer-side dependency on `HonestVotesSupportTarget`, and deferring
only one of them removes nothing from the crossing call's premise list.
R3's per-epoch discharge therefore cannot make `of_fixedSourceCurrentTarget`
proviso-free while `B1`/`B2` read `certified` ungated, and R4 cannot drop
`SelectedHelperProvisosAt.current_target`.

Two further obstacles stand behind that one, and both should be checked before
R3 is attempted again:

1. **The discharge needs the fold, and the fold sits above a frozen witness.**
   The only route to `HonestVotesSupportTarget T q` without the proviso is
   `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
   (`HonestTargetAgreement.lean:244`, still **zero consumers**), whose
   `hsafe : SafeFrom b q` at an *earlier* call second can only come from
   `weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`
   (`WeakTrajectorySafety.lean:400`). That fold *calls*
   `Execution.weak_safeFrom_observerCall_closed`, which is one of the audit's
   23 public witnesses and whose signature may not change; supplying the
   all-seconds witness to it would require either a new argument (forbidden)
   or a new field on `Weak.ObserverHistoricalA32CallAssumptions` (circular —
   the fold is what proves it). The real fix is to interleave the A3.2
   write-back recursion (`observerHistoricalA32CurrentLineageAt_all`) with the
   safety fold so the lineage at second `n` is built from the safety invariant
   at seconds `< n`. That is an architectural wave in its own right.
2. **The strong one-shot path needs its own fold instance.** `A1` is reached
   from `AcceptedActualFCRNextSlotSafetyAssumptions.findLatestConfirmedDescendant_safeFrom_of_actualCall`,
   also a frozen witness. Here the trajectory invariant *is* derivable from the
   record (`AcceptedActualFCRNextSlotSafetyAssumptions.confirmed_safeFromFollowingSlot`
   → `confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold`), so this side
   is threading work rather than a genuine gap.

### 10.4 What R2 actually landed

`AcceptedHistoricalA32GatePayloadAt.support_branch` now has type
`E.AcceptedHistoricalA32DeferredSupportAt cfg ext B origin e`, i.e.

```lean
∀ w : ValidatorIndex, w ∈ E.honest → ∀ m : ℕ, E.WithinHorizon cfg m →
  e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
    B.state.C origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)
```

`of_anchor` and `of_fixedSourceCurrentTarget` discharge it by ignoring the new
binders, `transport_sameEpoch` re-indexes under them, and `A1` supplies
`hw`/`hmH`/`hlate` from its own hypothesis list. The `A2` site
(`selectedA32Semantics.selectedA32Semantic_of_fixedSourceGate_currentEpoch`)
is **not** rewired: it reads
`FixedSourceCurrentTargetA32GateRealizationCore.support_branch`, the *gate
realization* rather than the payload, at the producing call itself. Guarding
that record would have to propagate through its three other readers
(`AcceptedHistoricalA32Crossing.lean:51`,
`AcceptedCurrentTargetGateBridge.lean:374`,
`CurrentTargetCertificateRealization.lean:1042`) and buys nothing while the
record's sibling `certified` stays ungated (§10.2).

R0-R2 therefore narrow the payload's positive surface to a single ungated
field, `certified`, read at exactly two sites. Removing the Trunk-A proviso
requires a proviso-free supply of `CertifiedJustified anchor T` in the
`currentHistorical` configuration — the same shape of gap as §7's Trunk-B
residue, and the next thing to attack.
