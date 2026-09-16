# The weak final wave — dropping `observer_helper_provisos` from the fold headlines

Analysis only; **nothing under `FastConfirmation/` was modified**, no build was
run, no commit was made. Branch `centaur/discharge-helper-provisos-202609161`,
`HEAD a54764c`. Paths relative to the repo root (`/home/agent/workspace/vfc`).
Companions: [`crossing-call-support-residue.md`](crossing-call-support-residue.md)
(esp. §9), [`trunkA-final-discharge.md`](trunkA-final-discharge.md) §5.5/§9,
[`trunkB-two-case-discharge.md`](trunkB-two-case-discharge.md) §7,
[`proviso-discharge-map.md`](proviso-discharge-map.md) §4/§5.1.

---

## 0. Headline verdict

1. **The flagged obstruction does not bite.** The observer's non-honesty blocks
   *nothing* in the lazy machinery. Every one of the four consumptions of
   `AcceptedHistoricalA32OriginCallAt.node_honest` has an already-landed,
   honesty-free observer substitute in-tree (§1). The decisive one —
   `confirmed_known_at_all_honest_endpoints_minimal` — already has a verbatim
   conclusion-matching twin,
   `Execution.confirmed_known_at_all_honest_endpoints_at_observer`
   (`WeakConfirmedDissemination.lean:186-216`), whose only replacement for
   `hv : v ∈ E.honest` is `hcomm : E.PrefixCommitteeAgreement …`, i.e. exactly
   `WeakObserverAssumptions.committees_agree`.

2. **`honestVotesSupportTarget_of_engineInv_currentEpochCandidate` is
   honesty-free in the querying node.** Its query argument is a bare
   `FastConfirmationStore Root`; it has **no** honesty binder and **no**
   committee-membership hypothesis on the querying node
   (`HonestTargetAgreement.lean:283-323`). Items 9-18 of its hypothesis list
   split cleanly into query-store geometry (all supplied honesty-free by
   `Weak.weakFcrStep_historicalA32QueryGeometryAt`,
   `WeakHistoricalA32Geometry.lean:147-157`) and honest-voter-side families
   (already quantified over `E.honest`). **§5.1 of `proviso-discharge-map.md`'s
   diagnosis is confirmed and is now moot**: the blocker it names is the
   *current-epoch placement of the safe root*, which a crossing call supplies by
   construction and which the origin-call record records.

3. **The weak side is strictly easier than the strong side in one place.**
   §9.1's Correction to A4 — `AcceptedFoldSafetyAt.callSecond` must be
   conditioned on `trace.result ≠ trace.afterObserved` — **does not port and is
   not needed**. `weak_safeFrom_observerCall_closed`
   (`WeakOneShotSafetyClosed.lean:113-174`) already produces the *unweakened*
   `SafeFrom trace.result (n+1)` on **all four** candidate-history branches,
   because the weak fold carries `hbase` at `slot_start (slot_at (n+1)) = n+1`
   (`:151-163`). The weak fold's `.mono` at `WeakTrajectorySafety.lean:369-370`
   simply throws that witness away. The weak T2 twin therefore keeps it, with no
   side condition, and the weak origin-call record can drop `origin_strict`.

4. **The weak `hIH` is present and identical.** The weak dispatcher already
   binds `hIH : E.SelectedCanonicalBeforeEndpointAt cfg ext (n+1) trace.result m`
   (`WeakSelectedStrictEdgeFilterSupply.lean:2136-2137`) and already consumes it
   at both late branches (`:2240`, `:2310`). `engineInv_of_selectedCanonical_lateEndpoint`
   (`SelectedA32Semantics.lean:188-196`) is **honesty-free** — no `hv`, `w`/`m`
   arbitrary — so the `start(e+1)` cap is reachable at the weak A1 site verbatim.

5. **The genuine, irreducible cost is isolated to exactly four public
   witnesses.** Only `weak_safeFrom_observerCall_closed`,
   `weak_confirmed_head_closed`, `weak_safeFrom_observerCall_closed_from_finalized`
   and `weak_confirmed_head_closed_from_finalized`
   (`WeakOneShotSafetyClosed.lean:113`, `:179`, `:227`, `:274`) mention `hC`.
   The other six weak witnesses carry `hmargin`/`hfilter` instead and never see
   the record. **The two fold headlines are not audit witnesses at all**
   (`scripts/Audit.lean:22-47`) and have **zero in-tree consumers**, so dropping
   `hC` to `hC.base` there changes no frozen statement and breaks nothing.

6. **§5.5 of `trunkA-final-discharge.md` is correct but over-scoped.** Its
   obstruction ("one-shot weak theorems with a non-honest observer") is real and
   applies to those four witnesses only. It was stated as if it blocked
   `observer_helper_provisos` *entirely*; it does not — it blocks deleting the
   record, not removing it from the trajectory statements. The corrected
   statement is in §5.4 below.

---

## 1. Question 1 — where `node_honest` is consumed, and the weak substitutes

`Execution.AcceptedHistoricalA32OriginCallAt.node_honest`
(`AcceptedHistoricalA32OriginCall.lean:75`) is read at exactly **four** places.
`rg 'node_honest'` over the whole tree finds `:75` (the field), `:139` (the
crossing constructor discharging it from `hv`), and the four uses below.

| # | site | what it buys | honesty-free weak substitute | verdict |
|---|---|---|---|---|
| 1 | `AcceptedHistoricalA32OriginCall.lean:274-275` — `store_domainK_of_selectedMarginDomain … node h.node_honest q hqH`, destructured `⟨hparentQ, _hwalkQ, _hjustQ⟩` | `ParentSlotLt` at the query store | **the honest component is discarded.** `store_domainK_of_selectedMarginDomain` (`MinimalSelectedDomain.lean:142-155`) needs `hdom.justified_root_known w hw m` only for its **third** component; `.1` is `E.store_parentSlotLt … w m`, node-generic. Weak-side: `hG.parent` from `Weak.weakFcrStep_historicalA32QueryGeometryAt` (`WeakHistoricalA32Geometry.lean:147-157`; record fields `AcceptedHistoricalA32Step.lean:456-474`) | **free** |
| 2 | `:280-281` — `head_root_known_of_selectedMarginDomain … h.node_honest q hqH` | `(get_head query.store).root ∈ block_roots` | its fallback branch (`MinimalSelectedDomain.lean:157-166`) needs `justified_root_known` at the node — supplied at the observer by `E.ObserverCoherence.justified_root_known` (`WeakOneShotSafety.lean:90-92`), itself **derived**, never assumed (`ObserverCoherence.of_acceptedTrajectory`, `WeakOneShotSafety.lean:94-111`; `WeakObserverAssumptions.toMarginAssumptions`, `:256-268`). Weak-side one-liner: `hG.head_known` | **free** |
| 3 | `:327-329` — `confirmed_known_at_all_honest_endpoints_minimal cfg ext hA node h.node_honest q …` | the crossing origin is known at **every** honest endpoint `(i,k)` with `slot_at q ≤ slot_at k` | `Execution.confirmed_known_at_all_honest_endpoints_at_observer` (`WeakConfirmedDissemination.lean:186-216`). Its docstring is explicit: "*Verbatim conclusion match for `MinimalSelectedDomain.confirmed_known_at_all_honest_endpoints_minimal` (`:589`), with `hv : v ∈ E.honest` replaced by `hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)`*". The relay direction is inverted (honest supporter `i` as **sender**, never into the observer, `:203-216`) | **free**; `hcomm` is `hW.committees_agree (n+1) hn1H` |
| 4 | `safeFrom_of_prior` (`:387`) — `hprior node h.node_honest second hlt …` | picks the origin node out of `PriorStrictCallWriteBackSafe`'s `∀ i ∈ E.honest` | **not** a substitution: the weak predicate is single-node by construction. `Weak.ObserverPriorCallWriteBackSafe obs n := ∀ k < n, WithinHorizon (k+1) → IsFCRCallAt obs k → SafeFrom (weakConfirmed obs (k+1)) (k+1)` — no honesty quantifier at all, and *no strictness conjunct* (§3.2) | **free** |

Two further hypotheses of the reconstruction that could have needed honesty and
do not:

* `hqStart` — `slot_start_eq_succ_of_advance_minimal`
  (`SelectedCoveredMarginConstruction.lean:787-806`) takes `hA` and an implicit
  `v` with **no** membership hypothesis; it is already applied at the observer
  in `WeakOneShotSafetyClosed.lean:151-152`.
* `hqueryHeadWalk` / `hqueryWalk` / `hanchorLe` — `trustedAnchor_boundaryWalkAtEpoch`
  (`TrustedAnchorGeometry.lean:85-125`) and `trustedAnchor_epoch_le_currentEpoch`
  (`:160-…`) quantify `(v : ValidatorIndex) (n : ℕ)` with no honesty binder.
* `hagree` — `hA.wellFormed.blocks_agree (E.blockProvenance … i k) (E.blockProvenance … node q)`;
  `blockProvenance` is node-generic and is already used at a Byzantine observer
  in `WeakConfirmedDissemination.lean` / `MinimalSelectedDomain.lean:620-630`.

And the executable side conditions of the record itself:

* `origin_known` / `origin_parent_known` / `origin_confirmed` at a weak crossing
  come from `find_latest_confirmed_descendant_selected_minimal_weak`
  (`WeakSelectorInversion.lean:449-471`), which has **no honesty binder** — it
  takes `hjrk : (E.store cfg ext v n).justified_checkpoint.root ∈ …`, i.e.
  `ObserverCoherence.justified_root_known` — and whose conclusion already
  contains the *strong* `is_one_confirmed … = true` (`:460-462`) that item 3
  above consumes. The strong twin
  (`MinimalSelectedDomain.lean:699-…`) does need `hv`; the weak one does not.
* `head_descends` from `Weak.strictSelectedResult_below_head`
  (used honesty-free at `WeakHistoricalA32Step.lean:643-646`), `gate` from
  `Weak.CurrentTargetAcceptedEdge.current_target_gate` +
  `will_current_target_be_justified_of_weak`
  (`WeakHistoricalA32Step.lean:292-294`), `target_eq` from
  `Execution.current_target_eq_checkpoint_of_current_epoch_ancestor`
  (`WeakHistoricalA32Step.lean:649-666`, already done verbatim),
  `origin_writeback` from
  `E.weakActualCandidateHistoryRecurrence … |>.result_writeback`
  (`WeakTrajectorySafety.lean:365-367`).

### 1.1 The one hypothesis the reconstruction lemma itself needs — and the
committee finding

`honestVotesSupportTarget_of_engineInv_currentEpochCandidate`
(`HonestTargetAgreement.lean:283-323`) binds, in order:

```
hhb hps hdiv hgen | hqH hqStart heng hcap | hqueryParent hqueryHead hbEpoch
hqueryHeadWalk hqueryWalk | hvoterHeadSlot hvoterParent hvoterHeadWalk
hvoterWalk hagree
```

* items 1-4 are ambient (`hA.honest_behavior`,
  `hA.externals_coherence.process_slots_slot`, `hA.whole_seconds`, a genesis
  clock fact);
* items 5-8 are the call's own horizon/slot-start plus the capped safety and cap
  bound — the **only** non-local inputs;
* **items 9-13 are query-store geometry** at a bare store: `ParentSlotLt`, head
  descends `b`, `b` is current-epoch, two boundary walks. Every one is a field
  of `E.HistoricalA32QueryGeometryAt` or a `trustedAnchor_*` application, all
  honesty-free at the observer;
* **items 14-18 are the voter-side families**, each already `∀ v ∈ E.honest`,
  plus `hagree` (block-provenance agreement), all node-generic.

**There is no committee membership of the querying node anywhere in the list**,
and no honesty binder on it. The docstring's own warning
(`HonestTargetAgreement.lean:260-266`) names the real gap — "*the
current-epoch placement of `b` is exactly what the live
`observer_helper_provisos` sites cannot supply (there the safe root is one epoch
too low)*" — and at a **crossing** call the safe root is by construction
current-epoch (`origin_current`), which is precisely why the origin-call route
closes what the direct route could not.

**Verdict Q1: no genuine obstruction.** Every `node_honest` consumption has an
honesty-free substitute already in the tree. The weak twin of
`AcceptedHistoricalA32OriginCallAt` is the strong record with `node_honest` and
`origin_strict` deleted, the evaluator swapped to `weakFcrStep` /
`weakGetLatestConfirmedTraceAt` / `weakConfirmed`, and one field added:
`coherence`-derived data is passed as arguments, not stored.

---

## 2. Question 2 — the weak endpoint-induction hypothesis

**It is there, it is the same object, and the cap still dominates.**

The weak strict-edge dispatcher
`Weak.StrictSelectedResultMechanicalFacts.weakFcrStep_endpointFilterOutcome`
binds

```lean
(hIH : E.SelectedCanonicalBeforeEndpointAt cfg ext (n + 1)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m)
```

at `WeakSelectedStrictEdgeFilterSupply.lean:2136-2137` — character-for-character
the strong binder at `AcceptedSelectedStrictEdgeFilterSupply.lean:1889-1890`
modulo the evaluator. The same binder is also a *hypothesis of two fields* of
the residual record `Weak.ObserverStrictCallFilterInputsAt`
(`:2000-2001` and `:2027-2028`), so it is available at every consumption site of
that record too.

It is already consumed in both late branches, in exactly the shape §2.2 of the
residue note predicted:

* current-epoch late (`:2236-2241`) —
  `Weak.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch_at_observer
   … hIH`, whose honest-node binder is replaced by
  `hcomm : PrefixCommitteeAgreement (E.store cfg ext obs q)`
  (`:983-1000`);
* previous-epoch-start late (`:2306-2311`) —
  `h.canonicalThroughoutNextEpoch_of_previousEpochStart … hIH`.

The cap conversion is unchanged: `engineInv_of_selectedCanonical_lateEndpoint`
(`SelectedA32Semantics.lean:188-212`) takes only `hA`, `hlate` and `hcanonical`;
its `w`/`m` are implicit and **never constrained to be honest** — the proof goes
through `E.store_current_slot` and pure epoch arithmetic. So

```
hlateE : e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m)
hIH    : SelectedCanonicalBeforeEndpointAt (n+1) result m
  ⟹ EngineInv result (n+1) (compute_start_slot_at_epoch cfg (e+1))
```

holds at the weak A1 site verbatim, and `start(e+1) < start(e+2) ≤ slot_at m`
still dominates the whole epoch-`e` vote span (residue §2.3, §9.1 Correction 1).

**One difference, and it is in the weak side's favour.** The strong A1 site
converts `hIH` into safety of `E.confirmed v (n+1)` via `hwrite`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:1985-1987`). The weak site needs
`E.weakConfirmed obs (n+1) = trace.result`, which is
`(E.weakActualCandidateHistoryRecurrence cfg ext hcall).result_writeback`
(`WeakTrajectorySafety.lean:365-367`); `hcall : E.IsFCRCallAt cfg ext obs n` is
already a binder of the weak dispatcher (used at `:2311`). No new input.

**The `(v,q)` slot of the A1 consumer is already instantiated at the honest
endpoint on the weak side.** `acceptedSelectedResultFilterOutcome_retainedVisible_of_lateSupport`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:1235-1268`) carries
`{v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat} (hqH …)`, but the weak
dispatcher passes `hw hmH … hselectedM hselectedEpochM` — i.e. it instantiates
`(v,q) := (w,m)` and reads the query store only through knownness and the block
epoch (`WeakSelectedStrictEdgeFilterSupply.lean:2241-2252`, and the comment at
`:2241-2242`). So the flip to `_of_lateSupport` costs nothing: the support
disjunction is supplied as a plain hypothesis and the honesty binder stays
inert.

**Verdict Q2: the weak `hIH` is identical in shape and placement; the
`start(e+1)` cap is reachable and still dominates.**

---

## 3. Question 3 — the weak fold's callSecond strengthening (weak T2)

### 3.1 What is needed

The exact mirror of `Execution.AcceptedFoldSafetyAt`
(`AcceptedActualFCRNextSlotSafetyFold.lean:64-69`):

```lean
structure Weak.ObserverFoldSafetyAt (E) (obs : ValidatorIndex) (n : ℕ) : Prop where
  followingSlot : E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n
  callSecond    : ∀ k : ℕ, n = k + 1 → E.IsFCRCallAt cfg ext obs k →
                    E.SafeFrom cfg ext (E.weakConfirmed cfg ext obs n) n
```

and `weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`'s conclusion
(`WeakTrajectorySafety.lean:398-402`) moves from
`∀ n, ∀ k ≤ n, WithinHorizon k → WeakConfirmedSafeFromFollowingSlot obs k`
to `… → Weak.ObserverFoldSafetyAt obs k`. The projection
`Weak.observerPriorCallWriteBackSafe_of_weakFullRuleFold` is then a one-liner,
mirroring `priorStrictCallWriteBackSafe_of_acceptedActualFCRFold`
(`AcceptedActualFCRNextSlotSafetyFold.lean:485-501`).

### 3.2 The `result ≠ afterObserved` conditioning does **not** port, and is not
needed

§9.1's Correction to A4 is a *strong-side* artefact. There, the
`finalizedResetUnchanged` arm recovers safety from
`finalizedReset_safeFrom_of_nextSlotSynchrony`
(`AcceptedFinalizedNextSlotSafety.lean:120-140`), which genuinely needs
`slot_at (n+1) + 1 ≤ slot_at q` and so fails at `q = n+1`.

The weak fold has no such arm. Its step
`weakConfirmedSafeFromFollowingSlot_succ_of_call`
(`WeakTrajectorySafety.lean:333-371`) computes

```
hbase   : SafeFrom trace.afterObserved (slot_start (slot_at (n+1)))   -- :356-357
hresult : SafeFrom trace.result (n+1)                                 -- :358-360
```

and `weak_safeFrom_observerCall_closed` closes **all four** branches of
`Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch` unconditionally
(`WeakOneShotSafetyClosed.lean:153-174`): the three "unchanged" branches
rewrite `result = afterObserved` and use `hbase` under
`hstartEq : slot_start (slot_at (n+1)) = n+1` (`:151-152`); the `strictSelected`
branch runs the discharged native theorem. `hresult` is then *weakened* away at
`:369-370` by `.mono … (lt_followingSlotStart …)`.

So the weak `callSecond` is **unconditional**, and the weak origin-call record
does not need `origin_strict`, and
`Weak.ObserverCallWriteBackEngineSafeUpTo obs N cap` does not need the
`≠ afterObserved` antecedent that `CallWriteBackEngineSafeUpTo`
(`AcceptedHistoricalA32OriginCall.lean:155-161`) carries. That in turn deletes
the `origin_strict` side condition from the weak `lazySupport` /
`lazyCert` discharges (cf. the strong `:740-741`, `:707-709`).

*(Consequence worth recording: the weak fold's step is `∀`-free in the branch
dimension, so the weak `ObserverFoldSafetyAt.callSecond` is actually the
**stronger** of the two records.)*

### 3.3 Signature impact — internals only

* `weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`
  (`WeakTrajectorySafety.lean:400`) — **not** in `scripts/Audit.lean:22-47`.
* Its only consumer in-tree is
  `weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold` (the `k := n`
  instance) and hence the two fold headlines — also not audited, and `rg` finds
  **zero** other consumers of either headline anywhere under `FastConfirmation/`
  or `scripts/`.
* `weakConfirmedSafeFromFollowingSlot_succ_of_call` (`:333`) — internal.
* Strengthening the motive is a **conclusion strengthening** of an unaudited
  internal theorem; the old conclusion is recovered by `.followingSlot`, exactly
  as on the strong side (`AcceptedActualFCRNextSlotSafetyFold.lean:474-481`).

**Verdict Q3: the weak T2 twin is a conclusion strengthening of one unaudited
internal theorem plus a one-line projection; no public witness signature moves;
the `result ≠ afterObserved` conditioning is not required.**

---

## 4. Question 4 — the `k = n` no-crossing form on the weak side

**Yes, identically, and the pieces are already shaped for it.**

The strong split landed as
`getLatestConfirmedTraceAt_currentLineage_step_core`
(`AcceptedHistoricalA32OneStep.lean:27-61`), parameterized by
`{Cert} {Supp} (hanchorCert) (hanchorSupp) (hcross …)`, with two
instantiations: `…_step_lazy` (`:244-291`, `hcross` = the lazy crossing builder
at `N = n+1`) and `…_step_noCrossing` (`:301-330`, `hcross` = `absurd`).

The weak one-call transformer `Weak.getLatestConfirmedTraceAt_currentLineage_step`
(`WeakHistoricalA32OneStep.lean:78-287`) has **the same two internal
abbreviations already factored out** — `hcrossingLineage` (`:130-152`) and
`hnoCrossingLineage` (`:153-165`) — and the crossing one is the *only* place
`hprovisos` is consumed (`:152`, `hprovisos hselector`). Lifting `hcrossingLineage`
to a `hcross` binder and abstracting `Cert`/`Supp` is a mechanical edit of the
same shape as the strong one: the four dispatch arms (`:166-287`) never mention
the payload's obligations.

The write-back induction
`Weak.observerHistoricalA32CurrentLineageAt_all`
(`WeakHistoricalA32Induction.lean:280-…`) then carries
`Weak.LazyCertAt B obs n` / `Weak.LazySupportAt B obs n` in its retained record
`Weak.ObserverHistoricalA32CurrentLineageAt` (`:94-104`), with
`Weak.acceptedHistoricalA32LazyLineage_mono`-style widening at the succ step —
the weak twin of `AcceptedHistoricalA32Induction.lean:274`, `:320`.

The `currentHistorical` consumer then takes the same route as the strong one.
The strong template is
`completedPrefix_acceptedHistoricalCertificateProducerAt`
(`AcceptedActualSelectedJustifiedOrientation.lean:604-660`), whose docstring
(`:596-603`) states the argument verbatim: under `hnoCrossing` the transformer
creates no payload, so it runs the `…_step_noCrossing` form from the invariant
at second `n`, whose `LazyCertAt B n` closure `hprior` discharges. The weak
consumer is `Weak.observerCall_currentTargetHistoricalA32Payload`
(`WeakHistoricalA32Induction.lean:716-846`) →
`Weak.observerCall_historicalA32PayloadProducerAt`
(`WeakHistoricalA32PayloadProducer.lean:50-73`) →
`epochStart_or_endpointOriginOrPinned_of_observerCallSite`'s
`currentHistorical` arm (`WeakSelectedJustifiedOrientation.lean:136-147`), which
reads exactly one thing: `hpayload.certified.some` at `:146`.

So the weak wave repeats T4d's weakening: introduce

```lean
def Weak.HistoricalCurrentTargetCertificateProducerAt (E) (B) (anchor) (q)
    (query) (input result : Root) : Prop :=
  get_block_epoch cfg query.store result = get_current_store_epoch cfg query.store →
  (¬ ∃ a c : Root, Weak.CurrentTargetAcceptedEdge cfg ext query input a c) →
    Nonempty (CertifiedJustified cfg E anchor (get_current_target cfg query.store))
```

— the weak-edge re-spelling of `Execution.HistoricalCurrentTargetCertificateProducerAt`
(`SelectedPreQueryHistoricalSIR.lean:739-746`), needed for exactly the reason
`WeakHistoricalA32PayloadProducer.lean:20-28` already documents (the strong
no-crossing side condition names `findLatestSelectedTrace`, and rule delta 1
gives the observer a different selector) — and weaken
`epochStart_or_endpointOriginOrPinned_of_observerCallSite` to take it instead of
`Weak.HistoricalA32PayloadProducerAt`. The arm body then becomes
`rw [htarget]; exact hproducer hresultCurrent hnone` with no payload in sight.

**Verdict Q4: yes. The weak transformer admits the same `hcross`
parameterization, the weak `currentHistorical` consumer admits the same
`…_step_noCrossing` route, and `hprior` discharges its `LazyCertAt` closure at
`N = n` — strictly below the fold step being proved (D1†).**

---

## 5. Question 5 — the one-shot statements

### 5.1 Exactly four of the 23 witnesses carry `hC`

`scripts/Audit.lean:22-47` lists 23 names; ten are weak.

| # | witness | file:line | carries `hC : Weak.ObserverHistoricalA32CallAssumptions`? |
|---|---|---|---|
| 14 | `Execution.weak_safeFrom_find_latest_confirmed_descendant` | `WeakOneShotSafety.lean:1116` | **no** — `hW : WeakObserverMarginAssumptions`, `hmargin` |
| 15 | `Execution.weak_confirmed_head` | `WeakOneShotSafety.lean:1175` | **no** |
| 16 | `…_from_finalized` | `WeakFinalizedInput.lean:679` | **no** — `hW`, `B`, `hmargin` |
| 17 | `weak_confirmed_head_from_finalized` | `WeakFinalizedInput.lean:726` | **no** |
| 18 | `…_discharged` | `WeakOneShotSafetyNative.lean:199` | **no** — `hfilter` |
| 19 | `weak_confirmed_head_discharged` | `WeakOneShotSafetyNative.lean:223` | **no** |
| 20 | `Execution.weak_safeFrom_observerCall_closed` | `WeakOneShotSafetyClosed.lean:113` (`hC` at `:131`) | **yes** |
| 21 | `Execution.weak_confirmed_head_closed` | `:179` (`hC` at `:197`) | **yes** |
| 22 | `Execution.weak_safeFrom_observerCall_closed_from_finalized` | `:227` (`hC` at `:246`) | **yes** |
| 23 | `Execution.weak_confirmed_head_closed_from_finalized` | `:274` (`hC` at `:293`) | **yes** |

Witnesses 1-13 are strong/LMD/HFC and never mention the weak record
(`trunkA-final-discharge.md` §5.4 already checked them).

### 5.2 Why those four genuinely cannot lose the premise

`Weak.ObserverPriorCallWriteBackSafe obs n` quantifies over the observer's
**earlier** calls. A one-shot statement's only safety input is `hbase` at its own
second (`WeakOneShotSafetyClosed.lean:138-140`, `:264-269`;
`WeakOneShotSafety.lean:1123`; `WeakOneShotSafetyNative.lean:207`). There is no
route from one second's `hbase` to the trajectory's history, and the observer's
non-honesty rules out borrowing the strong fold's honest-node output
(`WeakObserverAssumptions.observer : obs ∉ E.honest`, `WeakOneShotSafety.lean:245`).
**This half of §5.5 stands, verified.**

### 5.3 The fold headlines *can* bypass them

`weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
(`WeakObservedResetSeedSafety.lean:146-172`) and
`weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot` (`:179-211`) are

* **not** audit witnesses, and
* consumed by **nothing** (`rg` over `FastConfirmation/` and `scripts/` finds
  only their own definitions and the `WeakTrajectorySafety` originals).

So replacing `hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs`
(`:164`, `:197`) by
`hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext`
(the 7-field, proviso-free record since `f2ee223`) is a free premise weakening.

The mechanism: the whole chain between the fold and the four witnesses must be
made **`(Cert, Supp)`-polymorphic with two elimination arguments**, then
instantiated twice — exactly the pattern T4d used for
`getLatestConfirmedTraceAt_currentLineage_step_core`. Concretely, one record

```lean
structure Weak.ObserverLineageEliminationAt (E) (B) (obs) (n)
    (Cert : Checkpoint Root → Prop) (Supp : Root → Epoch → Prop) : Prop where
  certElim : ∀ {c}, Cert c → Nonempty (CertifiedJustified cfg E B.anchor c)
  suppElim : ∀ {o e}, Supp o e → ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
    e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
    E.SelectedCanonicalBeforeEndpointAt cfg ext (n+1)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result m →
    E.IsFCRCallAt cfg ext obs n →
      B.state.C o e = B.anchor ∨ Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B o e)
```

threaded down `…OneStep → …Induction → …PayloadProducer →
WeakSelectedJustifiedOrientation → WeakSelectedStrictEdgeFilterSupply →
WeakObserverStrictCallFilterInputs → WeakOneShotSafetyClosed`, with:

* **eager instantiation** (the four frozen witnesses): `Cert`/`Supp` = the
  existing eager `AcceptedHistoricalA32EagerCert`/`EagerSupp`; both eliminations
  are `id`-shaped and ignore their extra arguments; the crossing builder is the
  unchanged `Weak.selectedCurrentCrossingLineage_of_fixedSourceProducer`
  (`WeakHistoricalA32Step.lean:694-770`) driven by `hC.observer_helper_provisos`.
  **The four witness statements and bodies are unchanged up to one extra
  applied argument.**
* **lazy instantiation** (the fold): `Cert`/`Supp` = `Weak.LazyCertAt B n` /
  `Weak.LazySupportAt B obs n`; `certElim` is `fun h => h hprior`; `suppElim`
  builds `Weak.ObserverCallWriteBackEngineSafeUpTo obs (n+1) (start(e+1))` from
  `hprior` (`k < n`) plus `engineInv_of_selectedCanonical_lateEndpoint … hIH`
  (`k = n`), exactly as `callWriteBackEngineSafeUpTo_of_prior_and_current`
  does on the strong side (`AcceptedHistoricalA32OriginCall.lean:182-196`,
  discharged at `AcceptedSelectedStrictEdgeFilterSupply.lean:2024-2031`); the
  crossing builder is the new `Weak.selectedCurrentCrossingLazyLineage`.

Both instantiations produce the *same* `Weak.SelectedStrictEdgeFilterSupplyAt`
conclusion, so nothing downstream of
`StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_closed`
(`WeakObserverStrictCallFilterInputs.lean:104-148`) needs to know which ran.

**The alternative (cheaper, but it moves four frozen statements).** Drop the
polymorphism, make the stack lazy-only, and give witnesses 20-23 the premise
`hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n` in place of `hC`
(keeping `hC.base`). This is what §0 item 5 of `crossing-call-support-residue.md`
would call an *explicit history-supply premise*. Costs and benefits:

* `scripts/Audit.lean` stays green either way — it checks name existence,
  theorem-hood and axiom use (`:119-129`), **never signatures**;
* the premise swapped in is a *derived trajectory fact* (discharged by the fold)
  rather than a carried normative FCR-spec contract, so the epistemic position
  improves;
* but it is a change to four audited statements and should be raised as such,
  exactly as `trunkA-final-discharge.md` §8 says.

**Recommendation: the polymorphic route (Option A).** It costs ~2-4 extra
binders on ~10 declarations and keeps every frozen statement byte-identical;
the cheaper route can be taken later as a separate, explicitly-flagged change.

**Verdict Q5: four witnesses (20-23) keep the proviso premise under Option A;
the fold headlines' internals bypass them through parametrized twins with no
witness signature change.**

### 5.4 The corrected residual statement

> `Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`
> (`WeakSelectedStrictEdgeFilterSupply.lean:239-245`) is the price of the **four
> closed one-shot weak witnesses** (`WeakOneShotSafetyClosed.lean:113`, `:179`,
> `:227`, `:274`), not of the weak development as a whole. The weak **trajectory**
> statements can and should drop it: they are all-seconds forms, they are not in
> the audited witness set, and the observer's non-honesty obstructs nothing in
> the lazy machinery.

This supersedes the scope (not the content) of `trunkA-final-discharge.md` §5.5
and §8.

---

## 6. Question 6 — wave plan, blast radius, coordinated deletion

### 6.1 Green-commit sequence

| wave | content | files | risk |
|---|---|---|---|
| **W0** | **Free deletions.** `witnessSelectedHelperProvisos` (`AcceptedActualFCRJointNonVacuityFinal.lean:207-223`) is dead since `f2ee223` (`rg` finds no caller). Strong crossing constructors unreachable since T4d: `selectedCurrentCrossingLineage` / `…_of_fixedSourceProducer` (`AcceptedHistoricalA32Step.lean:277`, `:378`) and their two `…At_of_*` wrappers (`:934`, `:978`), the `carriedCurrentCrossingLineage*` family (`AcceptedHistoricalA32Crossing.lean:80`, `:258`, `:343`; `AcceptedHistoricalA32GlobalTrajectory.lean:263`), `Execution.currentTargetAcceptedEdge_gate_and_support` (`SelectedA32Support.lean:38`), then `Execution.SelectedHelperProvisosAt` (`SelectedTraceFilterPipeline.lean:40`) and its binders in `SelectedCoveredMarginConstruction`, `SelectedTraceFFGRealizationPipeline`, `SelectedTraceFilterPipeline`. **Verify first** that `SelectedGetLatestPipelineAt` / `selectedCoveredMarginSupplyAt_of_pipeline_minimal` (`SelectedCoveredMarginConstruction.lean:328-349`, `:620-635`) are genuinely off every live path — they are described in-file as "compatibility wrapper"/"legacy", but that is not a proof. | `AcceptedActualFCRJointNonVacuityFinal`, `AcceptedHistoricalA32Step`, `…Crossing`, `…GlobalTrajectory`, `SelectedA32Support`, `SelectedTraceFilterPipeline`, `SelectedCoveredMarginConstruction`, `SelectedTraceFFGRealizationPipeline` — **8** | none; build gets faster. Orthogonal to W1-W6; can land first or last |
| **W1** | **Weak T2.** `Weak.ObserverFoldSafetyAt`; strengthen `weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`'s motive; `Weak.ObserverPriorCallWriteBackSafe` + `.mono` + the projection supplier. No `≠ afterObserved` condition (§3.2). | `WeakTrajectorySafety` (+ `WeakObservedResetSeedSafety` unchanged for now) — **1** | low; the retained witness is `hresult` at `:358-360`, currently discarded |
| **W2** | **Weak T4b/T4c.** New `WeakHistoricalA32LazyCrossing.lean`: `Weak.ObserverHistoricalA32OriginCallAt` (no `node_honest`, no `origin_strict`), its `…_of_crossing` constructor, the honesty-free `honestVotesSupportTarget_capped` twin (§1), `gateRealization`/`certifiedFixedSource`/`deferredSupport` twins, `Weak.ObserverCallWriteBackEngineSafeUpTo` + monos + the prior/current splitter, `Weak.LazyCertAt`/`LazySupportAt` + monos + `…_of_eager` + `…_anchor` + `…_transport`. **All additive.** Nothing in `HonestTargetAgreement`, `SelectedA32Semantics`, `CurrentTargetA32Support` or `CurrentTargetCertificateRealization` moves — the T4b capped twins (`a0a5be9`) are honesty-free and reused verbatim. | **1 new** | low; ~350 lines, ~90 % copied from `AcceptedHistoricalA32OriginCall` / `AcceptedHistoricalA32LazyCrossing` with the four substitutions of §1 |
| **W3** | **Weak T4a-lite.** `(Cert, Supp)`-generalize the weak step constructors: `Weak.selectedCurrentNoCrossingLineage` (`WeakHistoricalA32Step.lean:409-436`) to `…LineageCoreAt`, mirroring the strong `AcceptedHistoricalA32Step.lean:140-144`. The payload/lineage **shim itself is trunk-neutral and already landed** (`0263ceb`); no second shim is needed (residue §9.2). | `WeakHistoricalA32Step` — **1** | low; `Weak.selectedCurrentCrossingLineage*` stay as the eager builders |
| **W4** | **Weak T4d.** `Weak.getLatestConfirmedTraceAt_currentLineage_step_core` (`hcross`-parameterized) + `_eager` / `_lazy` / `_noCrossing` instantiations; `Weak.ObserverHistoricalA32CurrentLineageAt` becomes `(Cert, Supp)`-indexed, `…_zero` / `…_all` / `…_invariant` / `observerCall_currentLineage` / `observerCall_previousCarried_epochStartLineage` follow; `Weak.HistoricalCurrentTargetCertificateProducerAt` (§4) and `Weak.observerCall_historicalCertificateProducerAt` via the `_noCrossing` route; `Weak.ObserverLineageEliminationAt` (§5.3). `Weak.ObserverHistoricalA32CallInterfaceAt.helper_provisos` (`WeakHistoricalA32Induction.lean:117-122`) becomes the crossing-builder slot. | `WeakHistoricalA32OneStep`, `WeakHistoricalA32Induction`, `WeakHistoricalA32PayloadProducer` — **3** | **high**; the wave's centre of gravity |
| **W5** | **Weak T3 (threading) + the two A1 discharges.** Weaken `epochStart_or_endpointOriginOrPinned_of_observerCallSite` and its three producer wrappers to the certificate producer; `(Cert, Supp)` + elimination on `Weak.ObserverStrictCallFilterInputsAt.current_lineage` / `.previous_epochStart_carried_lineage` (`WeakSelectedStrictEdgeFilterSupply.lean:2037-2083`); flip the dispatcher's two late branches (`:2247`, `:2315`) from `…retainedVisible_of_lateLineage` to `…_of_lateSupport` with `suppElim … hIH hcall`; thread `hprior` through `observerStrictCallFilterInputsAt_of_observerCall` and `…observerCall_selectedStrictEdgeFilterSupplyAt_closed`. | `WeakSelectedJustifiedOrientation`, `WeakSelectedStrictEdgeFilterSupply`, `WeakObserverStrictCallFilterInputs` — **3** | medium-high; mechanical but wide |
| **W6** | **The headline flip.** Lazy internal twins of the four closed one-shot theorems in `WeakOneShotSafetyClosed` taking `(hCbase, hprior)`; the four **frozen witnesses stay byte-identical**, re-proved from the eager instantiation. `WeakTrajectorySafety`'s step calls the lazy twin with `hprior` from the W1 IH. Then `weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold` (`WeakObservedResetSeedSafety.lean:164`) and `…_head_of_…_nextSlot` (`:197`) take `hCbase` instead of `hC`. | `WeakOneShotSafetyClosed`, `WeakTrajectorySafety`, `WeakObservedResetSeedSafety` — **3** | medium |
| **W7** | **Coordinated deletion + docs.** See §6.3. | **~5** | low once W6 is green |

Cumulative weak blast radius ≈ **12 files** (+8 for W0's strong-side cleanup).
No audit witness signature changes under Option A.

### 6.2 Gate after each wave

`scripts/check_build.sh` + `lake env lean scripts/Audit.lean`, plus two
invariants:

* after W2 and W3, `git diff --stat HEAD~1 -- 'FastConfirmation/Spec/Proof/Weak*'`
  should touch only the named files, and **no strong file at all** (the reverse
  of T4a's `git diff --stat -- '*Weak*'` = empty check);
* after W6, `rg 'observer_helper_provisos'` should return hits only in
  `WeakSelectedStrictEdgeFilterSupply.lean` (the definition), the eager
  instantiation in `WeakOneShotSafetyClosed.lean`, and docs.

### 6.3 The coordinated deletion the strong wave deferred

Residue §9.2 left the strong crossing constructors in place deliberately: "*they
are the structural analogue of the weak constructors, and deleting them is
orthogonal cleanup that should happen with, not before, the weak wave.*" With
the weak wave landed, the full list is:

1. **Strong unreachable crossing constructors** — as enumerated in W0. Note that
   under Option A the *weak* analogues (`Weak.selectedCurrentCrossingLineage`,
   `…_of_fixedSourceProducer`, `Weak.currentTargetAcceptedEdge_gate_and_support`,
   `WeakHistoricalA32Step.lean:280-294`, `:589-679`, `:694-770`) stay alive —
   they are the eager instantiation's builders. They die only under Option B.
2. **Both `SelectedHelperProvisosAt` records** — `Execution.SelectedHelperProvisosAt`
   (`SelectedTraceFilterPipeline.lean:40-48`) dies in W0 unconditionally;
   `Weak.SelectedHelperProvisosAt` (`WeakSelectedStrictEdgeFilterSupply.lean:197-211`)
   dies **only under Option B**.
3. **`observer_helper_provisos`** and the collapse of
   `Weak.ObserverHistoricalA32CallAssumptions` to its `base` — **Option B only**.
   Under Option A the record survives with two fields, used by four witnesses,
   and its docstring (`:171-196`) must be rewritten to say so: it is no longer
   "the observer-side normative call contract of the weak development", it is
   "the isolation price of the four closed one-shot statements".
4. **Docs and premise tables.**
   * `docs/proviso-discharge-map.md` §4 and §5.1 — §4's stated purpose of the
     all-seconds fold ("*Any discharge of `observer_helper_provisos` from the
     trajectory invariant …*", quoted verbatim in `WeakTrajectorySafety.lean:100-107`
     and `:390-397`) is now **achieved**; §5.1's "the live
     `observer_helper_provisos` sites cannot supply the current-epoch placement"
     must gain the correction that the *crossing* sites can, via the origin-call
     record.
   * `docs/trunkA-final-discharge.md` §5.5 and §8 — add the §5.4 correction
     above; the residual is four one-shot witnesses, not the weak development.
   * `docs/crossing-call-support-residue.md` §7 row **T6** ("blocked") and §9.2
     bullet 2 — replace with the W0-W7 table.
   * `docs/weak-full-rule.md` and `docs/weak-synchrony.md` premise tables — the
     fold headlines' premise list loses `observer_helper_provisos`.
   * `docs/REVIEW_GUIDE.md` — if it lists the weak premise surface, same edit.
5. **The audit / stage-7 note.** `scripts/Audit.lean` needs **no change** (still
   23 names, all still theorems, no new axioms). But the stage-7 commentary in
   `WeakSelectedStrictEdgeFilterSupply.lean:158-196` ("*This is floor-classified
   … it is carried, not discharged*") is no longer true of the trajectory path
   and must be re-scoped to the four one-shot witnesses, as must the note at
   `WeakSelectedJustifiedOrientation.lean:320-326` and the residual-record
   commentary at `WeakSelectedStrictEdgeFilterSupply.lean:2198-2223`
   (its `current_lineage` field is no longer "the accepted SIR / A3.2 stack's
   observer-side port … the wave's remaining work" — it is landed and lazy).

### 6.4 Residual risk register

| risk | where | mitigation |
|---|---|---|
| the `(Cert, Supp)` elimination binder needs `hcall` and `hIH` at a site that does not have them | `Weak.ObserverStrictCallFilterInputsAt.previous_epochStart_carried_lineage` (`:2059-2083`) is stated *without* an `hIH` binder | that branch's payloads were created at calls strictly earlier than `n` (their epoch was current at a strictly earlier slot), so `suppElim` there needs only `hprior` (`k < n`), exactly as the strong `lateFromLineage` at `AcceptedSelectedStrictEdgeFilterSupply.lean:2113-2119` does. Use a **second**, `hIH`-free elimination field for the epoch-start route |
| W4 regresses the one-shot path silently | the eager instantiation is only exercised by witnesses 20-23 | assert after W4 that the four witnesses still elaborate with unchanged statements (`#check` in a scratch file, or `git diff` on their signature lines) |
| `SelectedGetLatestPipelineAt` turns out to be live | W0 | check `rg 'SelectedGetLatestPipelineAt'` reachability from the 23 witnesses before deleting; if live, keep the record and delete only the crossing constructors |
| `Weak.LazySupportAt`'s antecedent needs `hcall` inside the closure | the weak `k = n` conversion needs `weakConfirmed obs (n+1) = trace.result` | `E.weakActualCandidateHistoryRecurrence cfg ext hcall |>.result_writeback` — `hcall` is already a dispatcher binder (used at `WeakSelectedStrictEdgeFilterSupply.lean:2311`); pass it through `suppElim` as shown in §5.3 |

---

## 7. Verdict table

| # | claim | verdict |
|---|---|---|
| 1 | `node_honest` has an honesty-free substitute at every consumption | **holds** — 4 sites, 4 substitutes (§1); the load-bearing one is `confirmed_known_at_all_honest_endpoints_at_observer`, `WeakConfirmedDissemination.lean:186` |
| 2 | `honestVotesSupportTarget_of_engineInv_currentEpochCandidate` requires no committee membership / honesty of the querying node | **holds** (`HonestTargetAgreement.lean:283-323`) |
| 3 | items 9-13 (query geometry) are honesty-free on the weak query store | **holds** — `Weak.weakFcrStep_historicalA32QueryGeometryAt`, `WeakHistoricalA32Geometry.lean:147` |
| 4 | the origin's one-confirmation / parent knownness is reachable weak-side | **holds** — `find_latest_confirmed_descendant_selected_minimal_weak`, `WeakSelectorInversion.lean:449`, no honesty binder |
| 5 | the weak dispatcher carries the same `hIH` | **holds** (`WeakSelectedStrictEdgeFilterSupply.lean:2136`) |
| 6 | `engineInv_of_selectedCanonical_lateEndpoint` is honesty-free, so `start(e+1)` is reachable weak-side | **holds** (`SelectedA32Semantics.lean:188-212`) |
| 7 | the weak fold's callSecond needs the `result ≠ afterObserved` conditioning | **fails** — not needed (`WeakOneShotSafetyClosed.lean:153-163`); §9.1's Correction to A4 is strong-side only |
| 8 | strengthening `…_of_weakFullRuleFold_all_le` changes a public witness | **fails** — it is not audited and has no consumers beyond the headlines |
| 9 | the weak write-back admits the `…_step_noCrossing` split | **holds** — `hcrossingLineage`/`hnoCrossingLineage` are already factored (`WeakHistoricalA32OneStep.lean:130-165`) |
| 10 | exactly four public witnesses keep the proviso | **holds** (`WeakOneShotSafetyClosed.lean:113`, `:179`, `:227`, `:274`) |
| 11 | the fold headlines can drop `hC` to `hC.base` with no witness signature change | **holds**, via the `(Cert, Supp)`-polymorphic stack (§5.3, Option A) |
| 12 | the observer's non-honesty blocks a step of the design | **fails** — it blocks nothing in the lazy machinery; it blocks only the *one-shot* discharge of the history premise, which is §5.5's real content |
| 13 | `trunkA-final-discharge.md` §5.5 | **holds in content, over-scoped** — corrected in §5.4 |
| 14 | the strong crossing-constructor deletion is free today | **holds** for the strong side (W0); the weak analogues survive under Option A |

---

## 8. Landing report — W0–W7 all green

Landed on `centaur/discharge-helper-provisos-202609161`, one commit per wave,
full gate (`scripts/check_build.sh` + `lake env lean scripts/Audit.lean`) after
each.

| wave | SHA | content |
|---|---|---|
| **W0** | `9d3c0ad` | the unreachable strong crossing constructors + `witnessSelectedHelperProvisos` + `currentTargetAcceptedEdge_gate_and_support` |
| **W1** | `ac6040a` | `Weak.ObserverFoldSafetyAt`, `Weak.ObserverPriorCallWriteBackSafe`, the strengthened fold motive and `observerPriorCallWriteBackSafe_of_weakFullRuleFold` |
| **W2** | `e2ac2cd` | `WeakHistoricalA32OriginCall` (the weak origin-call record + the honesty-free reconstruction + the lazy closures) and `WeakHistoricalA32LazyCrossing` |
| **W3** | `e8edc77` | `(Cert, Supp)` on `Weak.selectedCurrentNoCrossingLineage` and `Weak.actualFinalizedResetCurrentAnchorLineage_core` |
| **W4a** | `e7bbd5d` | `Weak.getLatestConfirmedTraceAt_currentLineage_step_core` with `_lazy` / `_noCrossing` instantiations |
| **W4b** | `6b44eae` | `(Cert, Supp)` on the weak lineage helpers; `Weak.ObserverLineageRouteAt` and the four obligation families |
| **W4c/W5** | `497d2d0` | the route threaded through the write-back induction, the orientation, the filter-input record and the dispatcher; both weak A1 sites flipped to `…retainedVisible_of_lateSupport` |
| **W6** | `07f0a0e` | `weak_safeFrom_observerCall_closed_lazy` and the headline flip |
| **W7** | `c20bf35` | deletion of the superseded weak payload-producer surface and the in-file commentary re-scoping |

### 8.1 Deviations from the plan

1. **`Execution.SelectedHelperProvisosAt` was not deleted (W0).** It is
   unreachable from the 23 audit witnesses, but it is still read by the legacy
   retained-trace pipeline and the FFG state-realization *public function
   contracts* (`SelectedTraceFilterPipeline`,
   `SelectedTraceFFGRealizationPipeline`, and
   `SelectedCoveredMarginConstruction`'s `Spec_Safety_of_selectedStateRealization_minimal`
   and ~25 siblings). Deleting the record forces either deleting that whole
   contract surface — far beyond a free deletion — or stripping the antecedent
   from *hypothesis-record fields*
   (`SelectedTraceFFGPipeline.retained_edge_tip_source` and
   `SelectedTraceFFGStateRealizationFor`'s four), which **strengthens** those
   assumption records and hence weakens every consumer. Reported instead of
   done.

2. **`observer_helper_provisos` was not deleted (W7), and cannot be under the
   recommended route.** It now has exactly **one** code reader in the whole
   tree: `Weak.observerLineageRoute_eager`
   (`WeakHistoricalA32Induction.lean`), the eager instantiation that keeps the
   four closed one-shot witnesses' statements byte-identical. Deleting it means
   those four witnesses must acquire
   `hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n`, which §5.2
   shows a one-shot statement cannot supply from its own `hbase` — i.e. it is
   Option B, four audited signature changes. The W7 bullet as written ("delete
   `observer_helper_provisos` … four one-shot witnesses keep it") is internally
   inconsistent; this landing keeps the four witnesses frozen, which is what
   §0 item 5 and §5.4 actually argue for.

   Consequently `Weak.SelectedHelperProvisosAt` and
   `Weak.ObserverHistoricalA32CallAssumptions` also survive, both with their
   original shape. The record's docstring has been re-scoped in place.

3. **The eager one-call wrapper was deleted rather than kept.**
   `Weak.getLatestConfirmedTraceAt_currentLineage_step` (the byte-identical
   pre-wave statement) became unreachable once the eager route went through
   `Weak.observerLineageRoute_eager`, so W7 removed it.

4. **The obligation parameters are *families* `ℕ → …`, not the fixed pair of
   §5.3.** The lazy closures are indexed by the write-back second, and the
   induction's extension step widens that bound, so a fixed `(Cert, Supp)` pair
   does not close. `Weak.ObserverLineageRouteAt` carries the anchor discharges,
   the widening (`mono`), the same-epoch support transport and the crossing
   builder; `Weak.ObserverStrictCallFilterInputsAt` carries the two
   eliminations (`supp_elim_current` with `hIH`/`hcall`, `supp_elim_prior`
   without — the §6.4 risk-register entry, confirmed).

### 8.2 Premise surface of the two fold headlines, exactly

`Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
(`WeakObservedResetSeedSafety.lean`):

```
(B : ExactPrefixAcceptedFFGSemantics cfg ext E)
(hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
(hji : JustificationInterface cfg ext E)
(hanchor : B.anchor = E.genesis_store.justified_checkpoint)
(hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
(hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
(hphase0 : Phase0SourceCoherence cfg ext)
(hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
(hpaper : B.state.PaperA32Inclusion cfg ext)
(P : AcceptedEpochCheckpointProjection B.anchor (E.AcceptedRoot cfg ext) B.state.C)
(V : B.state.ExactLinkValidity)
(hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
{obs : ValidatorIndex}
(hW : E.WeakObserverAssumptions cfg ext obs)
(hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
(hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
(hfit : EpochEndsFitUint64 cfg)
```

`…_head_of_acceptedWeakFullRuleFold_nextSlot` is the same list plus the
endpoint binders `{n} {w} (hw : w ∈ E.honest) {m} (hnm : n ≤ m)
(hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m) (hHm : E.WithinHorizon cfg m)`.

The only change against `45f6e84` is
`hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs` →
`hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext`, i.e.
the record's `.base` projection: a strict premise weakening.

`#print axioms` on both: `propext`, `Classical.choice`, `Quot.sound`.

### 8.3 What still carries the proviso

Exactly four declarations, all in `WeakOneShotSafetyClosed.lean` and all with
statements unchanged by the wave (the file's diff since `45f6e84` contains no
deletions at all):

* `Execution.weak_safeFrom_observerCall_closed`
* `Execution.weak_confirmed_head_closed`
* `Execution.weak_safeFrom_observerCall_closed_from_finalized`
* `Execution.weak_confirmed_head_closed_from_finalized`
