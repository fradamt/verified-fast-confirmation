# Trunk A's final discharge — adversarial verification of D1/D2/D3

Analysis only; **nothing under `FastConfirmation/` was modified**. Branch
`centaur/discharge-helper-provisos-202609161`, `HEAD e942c17`. Paths relative to
the repo root (`/home/agent/workspace/vfc`). Companions:
[`epoch-indexed-restructure.md`](epoch-indexed-restructure.md) (esp. §10),
[`trunkB-two-case-discharge.md`](trunkB-two-case-discharge.md),
[`proviso-discharge-map.md`](proviso-discharge-map.md).

---

## 0. Headline verdict

1. **D1's diagnosis is right and its mechanism is right, but its stated form is
   not the one that works.** The decisive constraint is *laziness*: the payload
   must carry the **originating-call data only**, and the positive content must
   be manufactured **at the consuming call**, never at the crossing call. An
   eager field (a disjunction, or a certificate, proved when the payload is
   built) is **same-step circular** — the fact it needs is the crossing call's
   own safety conclusion. A lazy field is not: the consuming call is strictly
   later than the crossing call, so the required input is a *strictly earlier*
   fold output. This is the one genuinely new finding of this note.

2. **Once lazy, the `EndpointOriginOrPinnedAt` re-indexing that D1 proposes is
   unnecessary.** With the origin-call data plus `SafeFrom origin` from that
   call, `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
   (`HonestTargetAgreement.lean:244`, still zero consumers) reconstructs the
   **whole proviso at `q'`**, which discharges `certified` *and*
   `support_branch` through the unchanged existing producers. D1's q′-vs-q index
   gap (question (c)) is real and unfixable *as an index transport* — arm 2 of
   `EndpointOriginOrPinnedAt` is anti-monotone in `q` and its two downstream
   consumers require `hIH`/`hglcKnown` at the *same* `q` and about the *same*
   `glc` — but the repair for it needs exactly the same input as the full
   proviso, so the weaker object buys nothing. Recommendation: **drop the
   disjunction-transport half of D1 and keep only the origin-call transport.**

3. **D2 fails on its premise.** `lateVisibleSeedAt`'s own hypothesis is
   `hjustifiedEpoch : (E.store w m).justified_checkpoint.epoch ≤ e`
   (`AcceptedSelectedStrictEdgeFilterSupply.lean:738`): in the branch where the
   quorum is consumed there is, by hypothesis, **no realized epoch-`e`
   justification at the endpoint** to extract. And the quorum is not consumed as
   a justification at all — it is consumed as the antecedent of the *paper's
   liveness assumption* `PaperA32Inclusion`, which needs full span structure
   that included evidence for a different checkpoint cannot supply. §3 gives the
   exact missing conjuncts.

4. **The endgame splits the two trunks' *records*, not the two rules.** On the
   **strong/accepted** path everything needed is derivable in-repo (threading +
   one fold-motive strengthening), so `SelectedHelperProvisosAt` and
   `AcceptedHistoricalA32CompletedPrefixCallAssumptions.helper_provisos` can go.
   On the **weak/observer** path the residual is structural and I judge it
   **closed**: every weak public witness is a *one-shot* theorem
   (`hbase` at the call's own second — `WeakOneShotSafety.lean:1123`,
   `WeakOneShotSafetyNative.lean:207`, `WeakOneShotSafetyClosed.lean:138`,
   `:204`), the missing input is a *fold* output, and the observer is explicitly
   **not honest** (`WeakObserverAssumptions.observer : obs ∉ E.honest`,
   `WeakOneShotSafety.lean:245`) so no honest-behaviour argument substitutes for
   it. `observer_helper_provisos` is the price of one-shot-ness.

5. **The `selected_previous_result_no_conflict` deletion is a free win** — and
   slightly larger than §10/the previous report claims (§5.1).

---

## 1. What the `currentHistorical` arms actually extract — D1(a)

**Verdict: holds, exactly as the brief guesses, and the extraction is even
narrower than "pin/epoch-bound content".**

Strong arm (`AcceptedSelectedJustifiedOrientation.lean:211-218`):

```lean
  | currentHistorical hresultCurrent hnone =>
      refine Or.inr (Or.inr (Or.inr ?_))          -- arm 3 of EndpointOriginOrPinnedAt
      intro hepoch
      obtain ⟨hJ⟩ := ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate …
      obtain ⟨hT⟩ := hhistorical' hresultCurrent hnone
      exact hacc.justified_unique hJ hT hepoch
```

Weak twin `WeakSelectedJustifiedOrientation.lean:138-147`, identical modulo the
weak producer. `hhistorical'` is
`acceptedHistoricalA32PayloadProducerAt_to_certificateProducer`
(`AcceptedHistoricalA32Payload.lean:344-354`), whose entire body is

```lean
  obtain ⟨e, htarget, ⟨hpayload⟩⟩ := hproducer hcurrent hnoCrossing
  rw [htarget]; exact hpayload.certified
```

So the *only* thing read out of `certified` at both live sites is
`Nonempty (CertifiedJustified cfg E B.anchor T)` with
`T = get_current_target cfg query.store`, consumed once by
`CertificateAccountability.justified_unique` (`SelectedFilterBridge.lean:321-324`)
to produce **arm 3** of `EndpointOriginOrPinnedAt`
(`SelectedJustifiedCompatibility.lean:88-93`). No weight, no signer set, no
quorum, no source, no deadline. Both arms are live
(`SelectedPreQueryHistoricalSIR.lean:78-82` constructor;
`WeakPreQuerySIR.lean` twin) and neither has a gate boolean in scope — confirmed
independently: the call-site classifier derives the two booleans only from a
crossing edge (`CurrentTargetAcceptedEdge.current_target_gate`,
`SelectedFilterBridge.lean:206-211`) or from a *previous-epoch* strict result away
from an epoch start (`selected_previous_result_no_conflict_gate`, `:298-310`);
the `currentHistorical` configuration is neither.

**Therefore any object that yields arm 3 (or arms 1/2 at the *consuming* `q`)
can replace `certified` at both sites.** `EndpointOriginOrPinnedAt` qualifies —
subject to §2.

---

## 2. Target constancy and the index gap — D1(b), D1(c)

### 2.1 Target constancy — **holds**, and it is already a field-level fact

The doc's claim is confirmed, but the citation is different from the one the
brief expects. The constancy is not carried by `target_eq`/`same_epoch_segment`
directly; it is carried by the **producer type**:

* `AcceptedHistoricalA32PayloadProducerAt` (`AcceptedHistoricalA32Payload.lean:331-341`)
  concludes `∃ e, get_current_target cfg query.store = B.state.C result e ∧
  Nonempty (payload at result e)` — the query-store current target **is** the
  checkpoint `B.state.C result e`, at the consuming call `q`.
* `AcceptedHistoricalA32GatePayloadAt.transport_sameEpoch`
  (`:175-232`) proves `hcheckpoint : B.state.C tip e = B.state.C origin e`
  (`:203-211`) from `get_checkpoint_block_of_ancestor` + `B.coherence.checkpoint_of_known`,
  and re-indexes `certified` by exactly `rw [hcheckpoint]` (`:225-226`).
* At the crossing call, `of_fixedSourceCurrentTarget` (`:123-167`) is handed
  `htarget : get_current_target cfg store = B.state.C origin e` (`:128`).

**Consequence for the design.** Any replacement field must be indexed by the
*checkpoint* `B.state.C · e`, not by a store-dependent `get_current_target`.
Then it transports by the same one-line `rw [hcheckpoint]` that `certified` uses
today, and `extend` (`:279-297`) copies it verbatim — the write-back recursion
(`AcceptedHistoricalA32Induction.lean:214-297`, weak twin
`WeakHistoricalA32Induction.lean:280-403`) is untouched, exactly as
`epoch-indexed-restructure.md` §3 predicts. ✔

### 2.2 The q′-vs-q index gap — **fails as an index transport**

`EndpointOriginOrPinnedAt anchor q w m T` (`SelectedJustifiedCompatibility.lean:88-93`):

| arm | statement | `q`-dependence |
|---|---|---|
| 1 | `(store w m).justified_checkpoint = anchor` | none |
| 2 | `CausalHonestTargetAt q w m` (`:42-49`) — `slot_at q ≤ s < slot_at m` | **anti-monotone**: `q' ≤ q` gives a *weaker* statement |
| 3 | `J.epoch = T.epoch → J.root = T.root` | none |

Arms 1 and 3 transport free. Arm 2 does not, and it cannot be repaired by
re-indexing the consumer, because the two consumers demand `q`-matching *and*
`glc`-matching:

* `selected_result_and_child_ancestor_of_causalHonestTarget`
  (`SelectedJustifiedCompatibility.lean:265-297`) takes `hglcKnown`/`hIH` over
  `E.slot_start cfg (E.slot_at cfg q) ≤ m'` **about `glc`**, and `hcausal` at the
  **same `q`** (`:279-286`); internally it routes to
  `endpoint_justified_ancestor_of_causal_honest_target_minimal`
  (`CausalCheckpointCompatibility.lean:37`) and
  `endpoint_justified_epoch_le_of_causal_honest_target_minimal`
  (`CausalCheckpointEpochBound.lean:87`), both of which convert `slot_at q ≤ s`
  into `slot_start (slot_at q) ≤ k` via `query_slot_start_le_of_slot_ge_minimal`
  and then apply `hIH i hi k …`.
* At the consumption site, `glc` is `find_latest_confirmed_descendant … input`
  **at `q`** (`AcceptedSelectedJustifiedOrientation.lean:305-307`), whereas the
  `q'`-indexed `hIH` would be about the crossing call's own result. Different
  object, so no re-indexing exists.

**So arm-2-at-`q'` with `s ∈ [slot_at q', slot_at q)` must be converted into arm
3.** That conversion is: honest `i` voted at `s` with `a.data.target = J`;
`HonestBehavior.votes_head` (`Model/Assumptions.lean:88-96`) makes that target
the epoch-`e` checkpoint of `i`'s own head at second `k`; if `i`'s head descends
`origin` then by `get_checkpoint_block_of_ancestor` the target is
`B.state.C origin e = T`, hence `J = T`. The premise "`i`'s head descends
`origin`" for every second in `[slot_start (slot_at q'), …)` is **exactly**
`E.SafeFrom cfg ext origin (E.slot_start cfg (E.slot_at cfg q'))`.

### 2.3 What supplies "origin safe from `q'`" at the arm bodies — **nothing, today**

Adversarial answer to the brief's question: in the arm bodies the *only* safety
in scope is

* `hbase : E.SafeFrom cfg ext input (E.slot_start cfg (E.slot_at cfg q))`
  (`AcceptedSelectedJustifiedOrientation.lean:299-300`, weak `:...` twin) — the
  **input** at `q`, not the origin at `q'`; and
* `hIH` from `slot_start (slot_at q)` (`:325-332`).

Both start at `q`. The A3.2 write-back invariant carries **no** safety by
construction (`AcceptedHistoricalA32Payload.lean:14-18`: "No canonicity,
endpoint head conclusion, `SafeFrom`, or historical SIR result is a field of the
payload"). So the answer is: the one-shot `hbase` chain does **not** supply it,
and the A3.2 write-back does not either.

### 2.4 The decisive structural fact: **eager is circular, lazy is not**

This is what neither §10 nor the brief states, and it changes the plan.

* **Eager** (prove the disjunction, or `certified`, when the payload is built at
  crossing call second `n`, `q' = n+1`, `origin = trace.result`): the needed
  input is `SafeFrom trace.result (n+1)` — which is *literally the conclusion of
  the one-shot theorem at second `n`*
  (`WeakOneShotSafetyClosed.lean:141-142`; strong analogue inside
  `AcceptedActualFCRNextSlotSafetyFacade.lean:75-…`). Same-step circular. This
  is the real content of `epoch-indexed-restructure.md` §10.3, and it is fatal
  for R3-as-written and for a disjunction-valued payload field.
* **Lazy** (payload carries only the origin-call data; the positive content is
  manufactured at the *consuming* call `q = n''+1`): the `currentHistorical`
  arm fires precisely when there is **no** crossing edge at this call
  (`StrictSelectedHistoricalSIRCallSite.currentHistorical`,
  `SelectedPreQueryHistoricalSIR.lean:78-82`), so the origin call is at a second
  `k < n''`, and the needed input is `SafeFrom (confirmed v (k+1)) (k+1)` with
  `k+1 ≤ n''` — a **strictly earlier** fold output. Well-founded.

Note the boundary is tight: `E.slot_start_eq_succ_of_advance_minimal`
(used at `WeakOneShotSafetyClosed.lean:151-152`) gives
`slot_start (slot_at (k+1)) = k+1` at a call, so the one-shot's own conclusion
`SafeFrom result (k+1)` is *exactly* the `slot_start`-form the repair needs — no
`followingSlotStart` weakening may be applied on the way (see §5.3, motive note).

### 2.5 Consequence: the disjunction is the wrong payload field

Once lazy origin-call data + `SafeFrom origin (slot_start (slot_at q'))` are
available at the consuming call, `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
(`HonestTargetAgreement.lean:244-286`) applies **verbatim** with `b := origin`,
`q := q'`, `query.store := E.store v' q'`:

* `hsafe : E.SafeFrom cfg ext b q` ✔ (the fold output);
* `hqStart : E.slot_start cfg (E.slot_at cfg q) = q` ✔ (`slot_start_eq_succ_of_advance_minimal`);
* `hqueryHead`, `hbEpoch`, `hqueryHeadWalk`, `hqueryWalk` — query-store geometry
  at `q'`; `hqueryHead` is the one genuinely call-specific fact and is already
  proved at the crossing producer (`strictSelectedResult_below_head` →
  `hbelowResult`, `AcceptedHistoricalA32Crossing.lean:128-132`), so it must be
  **carried in the payload**;
* the five `hvoter*`/`hagree` families are ambient store facts at any honest
  store, derivable from `hT`/`hA` — no carrying needed;
* conclusion: `HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q'`
  — **the proviso itself, at `q'`**.

That object feeds the *unchanged* producers
`AcceptedCurrentTargetA32GateRealizationProducerAt` /
`certifiedCurrentTarget_of_gate_and_stateSemantics`
(`CurrentTargetCertificateRealization.lean:512-543`), which is B2's manufacture
site, and therefore reconstructs **both** `certified` and the deferred
`support_branch`. So the redesign is:

> **replace `certified` and `support_branch` by the origin-call data, and
> re-derive both at the consumption site from the origin's safety.**

D1's `EndpointOriginOrPinnedAt`-valued field is a strictly weaker object that
requires the *same* input; it would still need a bespoke repair lemma for arm 2
and would still leave `support_branch` unserved. Keep D1's transport idea, drop
its disjunction.

---

## 3. D2 — included-evidence extraction for the A1 quorum

**Verdict: fails, on two independent grounds.**

### 3.1 What A1 actually needs the quorum for

`AcceptedHistoricalA32LineageAt.lateVisibleSeedAt`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:715-794`) consumes
`hpayload.support_branch w hw m hmH hlate` (`:748`) and, in the non-anchor arm,
hands the `ConcreteA32QuorumBefore` to
`accepted_paperA32IncludedAtTip_of_concreteQuorum`
(`:786-791`, `PaperA32SupportRealization.lean:411`). Its conclusion is **not** a
justification fact: it is `∃ seed`, known at `(w,m)`, ancestor of `selected`,
with `SourceVisibleAtTip (E.store w m) seed`
(`SelectedFFGRealization.lean:77-80`: `store.justified_checkpoint.epoch ≤
(get_voting_source cfg store seed).epoch`).

The route is quorum → `paperA32SupportThroughoutEpoch_of_concreteQuorum`
(`PaperA32SupportRealization.lean:350-375`) → `PaperA32SupportThroughoutEpochCore`
(`Model/FFGStateSemantics.lean:1115-1127`) → **the paper's liveness assumption**
`PaperA32InclusionCore.included` (`:1136-1151`) → AU inclusion of `C(b,e)` in a
pre-boundary descendant at `(w,m)`.

### 3.2 Ground 1 — there is no realized epoch-`e` justification to extract

`lateVisibleSeedAt` carries `hjustifiedEpoch : (E.store cfg ext w m).justified_checkpoint.epoch ≤ e`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:738`) as a **hypothesis**, and the
same hypothesis is threaded verbatim by
`acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage` (`:1167-1200`).
So in the very branch where the quorum is read, the endpoint's justified
checkpoint is **at most** epoch `e` and may be far older. There is nothing of
epoch `e` realized at `(w,m)`; the branch's whole job is to show the endpoint's
(old) justified epoch does not exceed the seed's voting source. `hDelay`
(`AcceptedRealizedFinalizationDelay`) bounds *finalization* lag, not epoch-`e`
justification realization; `AcceptedFFGGlobalCheckpointTrajectory.lean:624-635`
(`AcceptedSelectorAUCarrier`) only certifies the endpoint's **own**
`justified_checkpoint`. D2's premise ("epoch `e`'s justification should be
REALIZED/included in the endpoint store by then") is therefore **false as a
derivable fact** — it is precisely what `PaperA32Inclusion` *assumes*.

### 3.3 Ground 2 — the span structure included evidence cannot carry

Even granting a realized epoch-`e` justification, `PaperA32LinkSupportAtCore`
(`Model/FFGStateSemantics.lean:1073-1098`) demands, per signer and **per honest
view `(w', m')` throughout epoch `e+1`**:

| conjunct | source in `ConcreteA32QuorumBefore` | available from `EndpointJustifiedQuorumAt` / `IncludedCertifiedJustified`? |
|---|---|---|
| `E.AttestationReceivedBy w' m'` for each signer | synchrony/delivery from the concrete honest vote (`ConcreteA32QuorumScheduledDelivery`, `CurrentTargetA32Support.lean:543-566`) | **no** — included evidence gives `AttestationIncludedOnChain` at *one* carrier, not receipt in *every* honest view |
| `i ∉ V.slashableOnChain cfg b'` for the chosen `b'` | honest voter + `not_slashable` | **no** |
| validity against `(store w' m').checkpoint_states target` | `target_state_keyed` from the one-confirmed key path | **no** |
| `a.data.source = source` for a **single common** source | `Q.source_agreement` (`CurrentTargetA32Support.lean:534`) | **no** — N1 carries no source field at all |
| `i ∈ E.committee a.data.slot`, `epoch_at_slot a.data.slot = target.epoch` | per-vote | **yes** (`EndpointQuorumCausality.lean`, N1 signer conjuncts) |
| `2 * total ≤ 3 * weight signers` | `Q.supermajority` | **yes**, but for the *endpoint's* checkpoint, not `C(selected,e)` |

So the two conjuncts N1 *does* supply are exactly the two D2 hoped were the hard
ones, and every remaining one is unavailable. And the target is wrong: N1's
quorum certifies `(store w m).justified_checkpoint`, while A1 needs a quorum for
`B.state.C selected e`.

**D2 verdict: fails.** The A1 branch's residual is the same as §2's: the
deferred `support_branch` must be discharged from the proviso at `q'`, and the
only proviso-free source of that proviso is `SafeFrom origin` from `q'`.
Fortunately, at A1 the guard `e+2 ≤ currentEpoch(store w m)` places **all** of
epoch `e` in the past, so the discharge is the *uncapped*
`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate` with no prediction —
i.e. R3's §9.2 content, but **lazily**, at the consuming call.

---

## 4. Step-by-step verdict table

| # | Step | Verdict |
|---|---|---|
| **D1a** | `currentHistorical` arms extract only `Nonempty (CertifiedJustified anchor T)` → `justified_unique` → arm 3 | **holds** (`AcceptedSelectedJustifiedOrientation.lean:211-218`, `WeakSelectedJustifiedOrientation.lean:138-147`, `AcceptedHistoricalA32Payload.lean:344-354`) |
| **D1a′** | no gate boolean is in scope in that configuration | **holds** — gates come only from a crossing edge (`SelectedFilterBridge.lean:206-211`) or a previous-epoch non-start result (`:298-310`) |
| **D1b** | target constancy `T(q) = B.state.C origin e` | **holds**, via the producer type (`AcceptedHistoricalA32Payload.lean:331-341`) + `transport_sameEpoch`'s `hcheckpoint` (`:203-211`); field must be indexed by `B.state.C · e` |
| **D1b′** | the new field transports/extends without touching the write-back | **holds** — `rw [hcheckpoint]` (`:225-226`), `extend` copies verbatim (`:279-297`) |
| **D1c** | arm-2-at-`q'` transports to `q` | **fails** — anti-monotone; consumers need `q`- *and* `glc`-matching `hIH`/`hglcKnown` (`SelectedJustifiedCompatibility.lean:275-286`, `CausalCheckpointEpochBound.lean:87`, `CausalCheckpointCompatibility.lean:37`) |
| **D1c′** | repair arm-2@`q'` → arm 3 by boundary geometry | **needs-new-lemma**, and the lemma needs `SafeFrom origin (slot_start (slot_at q'))` — the same input as the *full* proviso, so the disjunction buys nothing |
| **D1c″** | "origin safe from `q'`" in scope at the arm bodies | **fails today** — only `hbase` at `q` (`AcceptedSelectedJustifiedOrientation.lean:299-300`) and `hIH` from `slot_start (slot_at q)` (`:325-332`); the A3.2 payload is safety-free by design (`AcceptedHistoricalA32Payload.lean:14-18`) |
| **D1★** | **eager payload field is same-step circular; lazy origin-call data is not** | **new finding — holds**; this is the precise repair of §10.3 obstacle 1/2 |
| **D1†** | lazy origin-call data + origin safety ⟹ the full proviso at `q'` | **holds**, via `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate` (`HonestTargetAgreement.lean:244-286`), which gains its first consumer |
| **D2a** | epoch `e` is realized/justified in the endpoint store under the `e+2` guard | **fails** — `hjustifiedEpoch : J.epoch ≤ e` is a hypothesis of the branch (`AcceptedSelectedStrictEdgeFilterSupply.lean:738`) |
| **D2b** | included evidence supplies A1's quorum content | **fails** — missing `AttestationReceivedBy` per honest view, `slashableOnChain` exclusion, `checkpoint_states` validity, and common-source agreement (`Model/FFGStateSemantics.lean:1073-1098`, `1115-1127`) |
| **D2c** | A1's quorum needs span structure | **yes** — `Q.source_agreement`, per-slot committee seats and delivery; N1 supplies only committee+epoch |
| **D2†** | A1 is dischargeable lazily from origin safety | **holds** — under `e+2` the whole of epoch `e` is past, so no prediction is involved |
| **D3a** | strong side: all required safety derivable in-repo | **holds, threading** — `AcceptedActualFCRNextSlotSafetyAssumptions.confirmed_safeFromFollowingSlot` (`AcceptedActualFCRNextSlotSafetyFacade.lean:54-66`) is a *theorem* of the record for all honest `v`, all `n` |
| **D3a′** | but inside the fold it must come from the motive, not the record | **needs-work** — the accepted fold must be strengthened to the all-`k ≤ n` motive, mirroring wave 3's `weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le` (`WeakTrajectorySafety.lean:400`) |
| **D3b** | weak side: `observer_helper_provisos` removable | **fails, structurally** — all four weak witness families are one-shot (`hbase` at the call's own second) and the observer is `∉ E.honest` (`WeakOneShotSafety.lean:245`) |
| **D3c** | `selectedPreviousResult_noConflict_gate_and_support` + `selected_previous_result_no_conflict` deletion is free | **holds** (§5.1) |
| **D3d** | audit witness *signatures* change | **no** — only two witness premise *bundles* weaken; see §5.4 |

---

## 5. The endgame accounting — D3

### 5.1 The free win (confirmed, and larger than claimed)

`rg` over the tree:

* `selectedPreviousResult_noConflict_gate_and_support` (`SelectedA32Support.lean:54-72`)
  — **zero consumers**; only its own definition line matches.
* `SelectedHelperProvisosAt.selected_previous_result_no_conflict`
  (`SelectedTraceFilterPipeline.lean:50-58`) — read **only** at
  `SelectedA32Support.lean:71`, i.e. inside the dead lemma.
* `Weak.SelectedHelperProvisosAt.selected_previous_result_no_conflict`
  (`WeakSelectedStrictEdgeFilterSupply.lean:220-228`) — **zero readers already**
  (there is no weak twin of the `gate_and_support` lemma).
* Supply side: `AcceptedActualFCRJointNonVacuityFinal.lean:285` (inside
  `witnessSelectedHelperProvisos`, `:271-292`). Deleting the field deletes that
  bullet **and orphans** `no_selectedPreviousResult_under_selector` (`:236-260`)
  and its `decide`-heavy companion `bounded_no_selectedPreviousResult_under_selector`
  — a build-time saving as well as a line saving.

Also free, and already flagged by `trunkB-two-case-discharge.md` §7 but still
present at HEAD: `certifiedCurrentTarget_of_crossing`
(`SelectedPreQueryHistoricalSIR.lean:774-784`, zero consumers, and the **only**
remaining strong consumer of `currentTargetAcceptedEdge_gate_and_support` that
is not a payload producer) and `noConflict_certifiedJustified_root_eq_currentTarget`
(`NoConflictCertificatePinning.lean:757-…`, zero consumers, still carrying an
`hsupport` premise at `:778`).

### 5.2 What stands between D1†/D2† and deleting the fields

The dependency chain that must be rewired, bottom-up:

1. `certifiedCurrentTarget_of_gate_and_stateSemantics`
   (`CurrentTargetCertificateRealization.lean:512-543`) and
   `fixedSourceCurrentTargetA32GateRealizationProducerAt_of_stateSemantics`
   (`:1156-…`) — take `hsupport` explicitly. **Unchanged** under the lazy design;
   they are simply *called later*.
2. `AcceptedCurrentTargetA32GateRealizationProducerAt` — its antecedent is
   `(hgate) (hsupport)`; the payload constructor
   `of_fixedSourceCurrentTarget` (`AcceptedHistoricalA32Payload.lean:123-167`)
   would stop taking a realization and start taking origin-call data.
3. The **two hubs**:
   * `Execution.currentTargetAcceptedEdge_gate_and_support`
     (`SelectedA32Support.lean:38-48`) — becomes
     `currentTargetAcceptedEdge_gate`, returning only
     `will_current_target_be_justified … = true`, dropping `hprovisos`.
     Consumers to update: `AcceptedHistoricalA32Crossing.lean:151`, `:153`,
     `:481`; `AcceptedHistoricalA32Step.lean:354`, `:443`;
     `AcceptedHistoricalA32GlobalTrajectory.lean:398`
     (+ `SelectedPreQueryHistoricalSIR.lean:783`, deleted by §5.1).
   * `Weak.currentTargetAcceptedEdge_gate_and_support`
     (`WeakHistoricalA32Step.lean:280-294`) — same, consumers
     `WeakHistoricalA32Step.lean:668`, `:761`. **Cannot be landed** (§5.5).
4. `AcceptedHistoricalA32CallInterfaceAt.helper_provisos`
   (`AcceptedHistoricalA32Induction.lean:51-58`) and its use at `:270`;
   weak twin `WeakHistoricalA32Induction.lean:117`, used at `:336` and `:475`.
5. `AcceptedHistoricalA32CompletedPrefixCallAssumptions.helper_provisos`
   (`AcceptedHistoricalA32CallSupplier.lean:341`), discharged at `:441`.
6. `Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`
   (`WeakSelectedStrictEdgeFilterSupply.lean:239-245`).
7. `SelectedHelperProvisosAt` (`SelectedTraceFilterPipeline.lean:37-58`) and
   `Weak.SelectedHelperProvisosAt` (`WeakSelectedStrictEdgeFilterSupply.lean:209-228`)
   — deletable once 3–6 are done.

### 5.3 The safety supply — the one architectural item

The consuming call needs, for each *earlier* call second `k ≤ n`:

```lean
E.SafeFrom cfg ext (E.confirmed cfg ext v (k+1)) (k+1)
```

(the **unweakened** one-shot conclusion, not the `followingSlotStart`-mono'd
`ConfirmedSafeFromFollowingSlot`; at a call `slot_start (slot_at (k+1)) = k+1`
by `slot_start_eq_succ_of_advance_minimal`, and that equality is what the repair
consumes).

* At the **facade** `findLatestConfirmedDescendant_safeFrom_of_actualCall`
  (`AcceptedActualFCRNextSlotSafetyFacade.lean:75-…`) the all-`n` version is
  already in hand — `h.confirmed_safeFromFollowingSlot` is used there at `:113-118`.
* Inside the **accepted fold** (`confirmed_safeFromFollowingSlot_of_acceptedActualFCRFold`,
  `AcceptedActualFCRNextSlotSafetyFold.lean`) it is **not**; the motive must be
  strengthened to `∀ k ≤ n` exactly as wave 3 did for the weak fold
  (`WeakTrajectorySafety.lean:400-415`, and its docstring at `:376-397` already
  states this demand verbatim: "the write-back recursion … replays **every
  earlier call second `k < n`** … needs an input-safety witness at each of those
  earlier seconds").
* Well-foundedness: lineage(`n+1`) is consumed at the call's own second
  (`AcceptedSelectedStrictEdgeFilterSupply.lean:1869-1875`), and under laziness
  its `currentHistorical` consumption needs safety only at origin calls `k+1 ≤ n`
  — strictly below the step being proved. ✔ (The *eager* variant would need it at
  `n+1` and is circular. ✘)

### 5.4 Audit witnesses — **no signature changes**

`scripts/Audit.lean:22-47` lists the 23 frozen witnesses. Checked one by one:

* `findLatestConfirmedDescendant_safeFrom_of_actualCall` — mentions only
  `E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext`. Deleting
  `helper_provisos` from `completed_calls` changes that record's *fields*, i.e.
  **weakens** a premise. Statement text unchanged; strength strictly improved.
* `witnessJointNonvacuity` (`AcceptedActualFCRJointNonVacuityFinal.lean:773`) and
  `acceptedActualFCRNextSlotSafetyAssumptions_nonvacuous` (`:803-808`) — mention
  the record only; **proofs** change (`:682` `helper_provisos := …`, `:271-292`
  `witnessSelectedHelperProvisos`). No signature change.
* `acceptedSpec_safety_next_slot`, the LMDGhost/HFC witnesses — untouched.
* The ten weak witnesses mention `Weak.ObserverHistoricalA32CallAssumptions`
  (e.g. `WeakOneShotSafetyClosed.lean:131`, `:197`). Deleting
  `observer_helper_provisos` would likewise only weaken them — but §5.5 says it
  cannot be done.

**So no audit witness signature changes; only internal lemmas move.** ✔

### 5.5 The residual that still needs the proviso — stated exactly

> **Residual.** `Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`
> (`WeakSelectedStrictEdgeFilterSupply.lean:239-245`) cannot be deleted while the
> weak public witnesses keep their statements.

Proof sketch of the obstruction, in three steps:

1. *The content is genuinely needed.* The `currentHistorical` pin at a `q` inside
   epoch `e` asserts that the endpoint's epoch-`e` justified checkpoint agrees
   with `C(origin,e)`. At the crossing call `q'` the gate contributes only
   `3·(observed + projected) ≥ 2·total`, and `observed` alone is near-zero early
   in an epoch (`Model/FFGHelpers.lean:73-90`; the same arithmetic that
   `epoch-indexed-restructure.md` §7 analyses). The claim is therefore *equivalent*
   to honest epoch-`e` voters after `q'` targeting `C(origin,e)`, whose only
   non-assumed source is head agreement, i.e. `SafeFrom origin` from `q'`.
2. *That fact is a fold output.* The observer's own confirmed-root safety is
   `E.WeakConfirmedSafeFromFollowingSlot cfg ext obs k`, produced only by
   `weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`
   (`WeakTrajectorySafety.lean:400`), which *consumes* the witness
   `weak_safeFrom_observerCall_closed` at each step (`:366-368`).
3. *The witness cannot receive it.* Every weak witness is one-shot: its only
   safety input is `hbase` at its own second
   (`WeakOneShotSafety.lean:1123`, `WeakOneShotSafetyNative.lean:207`,
   `WeakOneShotSafetyClosed.lean:138-140`, `:204`). Putting the missing fact into
   `hC` is circular (the fold would have to prove, for **all** `n`, the very thing
   it is inducting on) and would in any case *strengthen* a premise bundle.
   Bounding `hC` by the witness's own second is a signature change. And no
   honest-behaviour substitute exists: `WeakObserverAssumptions.observer :
   obs ∉ E.honest` (`WeakOneShotSafety.lean:245`), so the strong
   `AcceptedActualFCRNextSlotSafetyAssumptions.confirmed_safeFromFollowingSlot`
   — which *is* constructible inside the weak witness, since `B, hT, hC.base,
   hfit, hanchor, hboundary, hDelay, hpaper, P, V` are all in its signature
   (`WeakOneShotSafetyClosed.lean:115-132`) — covers only honest validators, not
   the observer.

**In one line: `observer_helper_provisos` is the price of the weak theorems
being one-shot.** Removing it requires promoting one weak witness to an
all-seconds form, which is a change to the audited statement set and therefore
out of scope here.

---

## 6. New lemmas, with signatures and sizes

All `Execution`-namespace, all on the **strong/accepted** path.

**A1 — the origin-call record (replaces `certified`/`support_branch`).**
```lean
structure AcceptedHistoricalA32OriginCallAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (target : Checkpoint Root) : Prop where
  node            : ValidatorIndex
  node_honest     : node ∈ E.honest
  second          : ℕ                       -- the crossing call's `n`
  second_horizon  : E.WithinHorizon cfg (second + 1)
  is_call         : E.IsFCRCallAt cfg ext node second
  origin          : Root
  origin_known    : origin ∈ (E.fcrStep cfg ext node second).store.block_roots
  origin_current  : get_block_epoch cfg (E.fcrStep cfg ext node second).store origin
                      = get_current_store_epoch cfg (E.fcrStep cfg ext node second).store
  head_descends   : is_ancestor (E.fcrStep cfg ext node second).store
                      (get_head cfg (E.fcrStep cfg ext node second).store)
                      (get_node_for_root origin) = true
  gate            : will_current_target_be_justified cfg ext
                      (E.fcrStep cfg ext node second).store = true
  target_eq       : get_current_target cfg (E.fcrStep cfg ext node second).store = target
```
New payload field: `origin_call : B.state.C origin e = B.anchor ∨
E.AcceptedHistoricalA32OriginCallAt cfg ext B (B.state.C origin e)`.
Transports by `rw [hcheckpoint]` in `transport_sameEpoch`. **~25 lines**
(structure + the three constructor discharges).

**A2 — the lazy proviso reconstruction (the only real new proof).**
```lean
theorem AcceptedHistoricalA32OriginCallAt.honestVotesSupportTarget
    (hA : SelectedMarginAssumptions cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    {T : Checkpoint Root} (h : E.AcceptedHistoricalA32OriginCallAt cfg ext B T)
    (hsafe : E.SafeFrom cfg ext h.origin (h.second + 1)) :
    HonestVotesSupportTarget cfg E T (h.second + 1)
```
Body: `slot_start_eq_succ_of_advance_minimal` for `hqStart`, the store-geometry
plumbing for `hqueryParent`/`hqueryHeadWalk`/`hqueryWalk` (precedent:
`AcceptedHistoricalA32Crossing.lean:100-160`, `SelectedA32Semantics.lean:118-190`),
the ambient voter-side families from `hT`/`hA`, then
`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`. **~90 lines**, of
which ~70 is geometry with line-for-line precedent.

**A3 — the two re-derivations at the consumption site.**
```lean
theorem AcceptedHistoricalA32GatePayloadAt.certified_of_originSafety
    (…) (hpayload : E.AcceptedHistoricalA32GatePayloadAt cfg ext B origin e)
    (hsafe : <A2's hsafe for hpayload.origin_call>) :
    Nonempty (CertifiedJustified cfg E B.anchor (B.state.C origin e))

theorem AcceptedHistoricalA32GatePayloadAt.deferredSupport_of_originSafety
    (…) : E.AcceptedHistoricalA32DeferredSupportAt cfg ext B origin e
```
Each is A2 plus the unchanged
`certifiedCurrentTarget_of_gate_and_stateSemantics` /
`fixedSourceCurrentTargetA32GateRealizationProducerAt_of_stateSemantics`
pipeline. **~40 lines each.**

**A4 — the all-`k ≤ n` accepted fold motive.** Mirror of
`weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`
(`WeakTrajectorySafety.lean:400`), but retaining the *unweakened*
`E.SafeFrom cfg ext (E.confirmed cfg ext v (k+1)) (k+1)`. **~60 lines**, purely
enabling (single-second form recovered by `k := n`).

**A5 — threading.** A new hypothesis
`hprior : ∀ k ≤ n, ∀ v ∈ E.honest, E.SafeFrom cfg ext (E.confirmed cfg ext v (k+1)) (k+1)`
on the internal chain
facade → `AcceptedActualFCRStrictHelperIntegration` →
`AcceptedSelectedStrictEdgeFilterSupply.fcrStep_endpointFilterOutcome` →
`strictSelected_result_and_child_ancestor_of_endpointJustified_accepted` →
`epochStart_or_endpointOriginOrPinned_of_acceptedCallSite`. **~0 new proof, ~10
files touched.**

*Not needed* (contrary to the brief): any `EndpointOriginOrPinnedAt`
re-indexing lemma, any capped `HonestVotesSupportTargetUpTo`, any new
`CausalCheckpointEpochBound`/`HonestTargetAgreement` geometry, any change to
N1–N6.

---

## 7. Wave plan and blast radius

| Wave | Content | Files | Risk |
|---|---|---|---|
| **T0** | Free deletions (§5.1): `selectedPreviousResult_noConflict_gate_and_support`, both `selected_previous_result_no_conflict` fields, `witnessSelectedHelperProvisos`'s second bullet + `no_selectedPreviousResult_under_selector` + `bounded_…`, `certifiedCurrentTarget_of_crossing`, `noConflict_certifiedJustified_root_eq_currentTarget` | `SelectedA32Support`, `SelectedTraceFilterPipeline`, `WeakSelectedStrictEdgeFilterSupply`, `AcceptedActualFCRJointNonVacuityFinal`, `SelectedPreQueryHistoricalSIR`, `NoConflictCertificatePinning` — **6** | none; build gets faster |
| **T1** | A1 + A2 + A3, all **additive** (payload keeps `certified`/`support_branch`; the new field and the three theorems sit beside them) | `AcceptedHistoricalA32Payload` + 1 new file — **2** | low; green throughout |
| **T2** | A4: strengthen the accepted fold motive | `AcceptedActualFCRNextSlotSafetyFold` (+ `…Facade`) — **2** | medium (induction surgery, but wave 3's weak twin is the template) |
| **T3** | A5: thread `hprior` down the strong call chain | `AcceptedActualFCRNextSlotSafetyFacade`, `AcceptedActualFCRStrictHelperIntegration`, `AcceptedSelectedStrictEdgeFilterSupply`, `AcceptedSelectedJustifiedOrientation`, `AcceptedActualSelectedJustifiedOrientation`, `SelectedJustifiedCompatibility` — **~8-10** | medium; mechanical but wide |
| **T4** | Flip the payload: `certified`/`support_branch` → `origin_call`; rewire the strong `currentHistorical` arm (`AcceptedSelectedJustifiedOrientation.lean:211`) and A1 (`lateVisibleSeedAt`) to A3 | `AcceptedHistoricalA32Payload`, `…Crossing`, `…Step`, `…OneStep`, `…Induction`, `…CallSupplier`, `…GlobalTrajectory`, `AcceptedSelectedJustifiedOrientation`, `AcceptedSelectedStrictEdgeFilterSupply` — **~9** | high |
| **T5** | Drop the support half of the strong hub; delete `SelectedHelperProvisosAt.current_target`, `AcceptedHistoricalA32CallInterfaceAt.helper_provisos`, `AcceptedHistoricalA32CompletedPrefixCallAssumptions.helper_provisos`, then `SelectedHelperProvisosAt` itself | `SelectedA32Support`, `SelectedTraceFilterPipeline`, `AcceptedHistoricalA32Induction`, `AcceptedHistoricalA32CallSupplier`, `AcceptedActualFCRJointNonVacuityFinal` — **5** | low, once T4 is green |
| **T6** | **Blocked** (§5.5): the weak twin of T4/T5 and `observer_helper_provisos` | — | — |

Cumulative strong-path blast radius ≈ **20 files**; no audit witness signature
changes. The weak-path blast radius is 0 because the weak path does not move:
`Weak.currentTargetAcceptedEdge_gate_and_support` (`WeakHistoricalA32Step.lean:280`),
`Weak.SelectedHelperProvisosAt.current_target` and `observer_helper_provisos`
survive T0–T5 intact.

---

## 8. Residual statement

After T0–T5, `HonestVotesSupportTarget` is projected at **one** site:
`Weak.currentTargetAcceptedEdge_gate_and_support`
(`WeakHistoricalA32Step.lean:280-294`), reading
`Weak.SelectedHelperProvisosAt.current_target` (`:293`), supplied by
`Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`
(`WeakSelectedStrictEdgeFilterSupply.lean:239-245`), and it feeds the weak
crossing-lineage producers (`WeakHistoricalA32Step.lean:668`, `:761`) and hence
the weak `currentHistorical` arm (`WeakSelectedJustifiedOrientation.lean:136-147`)
and the weak A1 site. It is required because the weak observer is not honest and
the weak public theorems are one-shot; discharging it needs the observer's own
earlier-call safety, which only the weak fold produces and which a one-shot
statement cannot receive. Removing it is not a proof problem — it is a change to
the audited statement set (promote one weak witness to an all-seconds form), and
should be raised as such rather than attempted as a refactor.
