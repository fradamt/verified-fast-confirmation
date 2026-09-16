# The crossing-call `support_branch` residue — what actually closes it

Analysis only; **nothing under `FastConfirmation/` was modified**, no build was
run, no commit was made. Branch `centaur/discharge-helper-provisos-202609161`,
`HEAD 36df8c7`. Paths relative to the repo root (`/home/agent/workspace/vfc`).
Companions: [`trunkA-final-discharge.md`](trunkA-final-discharge.md) (esp. §9),
[`trunkB-two-case-discharge.md`](trunkB-two-case-discharge.md) §6,
[`epoch-indexed-restructure.md`](epoch-indexed-restructure.md) §10,
[`justification-causality-contract.md`](justification-causality-contract.md) §6.

---

## 0. Headline verdict

1. **The reordering crux (question 2) fails as literally posed, and §9.3's
   Correction 2 is confirmed.** `fcrStep_endpointFilterOutcome` at call second
   `n` consumes the **post-call** lineage, at index `n + 1`, whose tip is
   `E.confirmed v (n+1) = trace.result`
   (`AcceptedSelectedStrictEdgeFilterSupply.lean:1861-1876`). That lineage is
   built by the `succ` step of `acceptedHistoricalA32CurrentLineageAt_all`
   (`AcceptedHistoricalA32Induction.lean:259-273`) from `hcall.helper_provisos`
   **at second `n`**, and in the crossing branch
   (`getLatestConfirmedTraceAt_currentLineage_step`'s `hcrossingLineage`,
   `AcceptedHistoricalA32OneStep.lean:78-100`, used at `:136-140`, `:180-184`,
   `:226-229`) the payload's own origin **is** `trace.result`. There is no
   reordering that lets the filter outcome consume the pre-call lineage: the
   outcome it must produce is
   `AcceptedSelectedResultFilterOutcomeAt B (store w m) trace.result`, i.e. it
   is *about* the new root, and the previous lineage's tip is a different
   block (`StrictSelectorAdvanceAt.result_ne_input`).

2. **But the residue is not irreducible, and the fix is much cheaper than
   §9.3's.** The safety input the A1 site needs is *not* the full step-`n`
   conclusion. The endpoint-filter supply is a Π-type whose binder `hIH`
   (`SelectedCoveredMarginConstruction.lean:58-66`,
   `AcceptedSelectedStrictEdgeFilterSupply.lean:1765-1766`) is exactly the
   **capped** form of that conclusion — canonicity of `trace.result` at every
   honest endpoint with `slot_at m' < slot_at m` — supplied by the *inner
   endpoint induction of the same step*, and therefore strictly earlier in a
   well-founded order. Under the A1 guard `e + 2 ≤ currentEpoch(store w m)`
   that cap **clears the whole of epoch `e`**, which is the entire vote span
   the A3.2 quorum consumes. So the manufacture goes through with a capped
   safety input.

3. **No capped `HonestVotesSupportTargetUpTo` is required, and
   `CurrentTargetA32Support.lean:504` is untouched.** `HonestVotesSupportTarget`
   (`TheoremStatements.lean:68-74`) already restricts its quantifier to slots
   `s` with `compute_epoch_at_slot s = T.epoch`, and its only consumer of
   `hsafe` is at cast seconds `k` with `E.slot_at cfg k = s`
   (`HonestTargetAgreement.lean:197`, via `honest_vote_eq_honestAttestation`'s
   `E.slot_at cfg k = s`, `:103`). Capping the *safety input* at a slot above
   `start(e+1)` therefore yields the **uncapped** support predicate. §9.3's
   item (2) — "a capped variant of the quorum manufacture …
   `currentTargetFutureHonestSeat_vote`", "the expensive one" — is **not
   needed**. §6's "*Not needed* … any capped `HonestVotesSupportTargetUpTo`"
   was right for the wrong reason and should be *re-instated*, not reversed;
   what must be reversed is §5.3's well-foundedness bullet (already done by
   §9.3) and §9.3's cost estimate.

4. **What *is* required, and §9.3's last paragraph is right about it:** the
   payload must know that its origin call is not in the consumer's future.
   The minimal recording is a *threaded, capped, node-and-second-indexed
   safety antecedent* on the support field (§4.3). It is not an extra index on
   the record — it is a closure inside the `Supp` parameter of the §9.1 shim.

5. **The §9.1 `abbrev` shim is confirmed sound** for all five shared
   constructor sites (three strong, plus the four weak ones named in §9.2),
   and the repo already uses this exact pattern (`PaperA32Inclusion` is an
   `abbrev` over `PaperA32InclusionCore`, `FFGStateSemantics.lean:1188-1190`,
   `:1212-1215`). It must be extended from `Cert` to a second parameter
   `Supp`, because the A1 site is shared between the trunks too (§5.2).

6. **Nothing reduces to paper A3.2.** The residue is not, and never was, a
   restatement of Assumption 3.2 (§6). Had it been irreducible it would have
   been a *strictly different* normative prediction — the antecedent of A3.2's
   antecedent — and saying "it is paper A3.2, which is floor" would have been
   wrong. It is moot, because it closes.

---

## 1. What the guarded `support_branch` is consumed for, transitively

### 1.1 The single consumer and the chain

`AcceptedHistoricalA32GatePayloadAt.support_branch`
(`AcceptedHistoricalA32Payload.lean:88`, type
`AcceptedHistoricalA32DeferredSupportAt`, `:58-64`) is read at exactly two
places in the tree:

* `AcceptedHistoricalA32Payload.lean:222` — `transport_sameEpoch` re-indexing
  it along a same-epoch segment (not a consumption);
* `AcceptedSelectedStrictEdgeFilterSupply.lean:748` — inside
  `AcceptedHistoricalA32LineageAt.lateVisibleSeedAt` (`:716-794`). **This is
  A1, and it is the only consumer.** §10.1 of `epoch-indexed-restructure.md`
  is confirmed at HEAD by `rg`.

The chain from `:748` is:

| step | site | object |
|---|---|---|
| 1 | `:748` | `B.state.C origin e = B.anchor ∨ Nonempty (AcceptedHistoricalA32QuorumAt B origin e)` |
| 2 | `:765-773` | unpack: `deadline = start(e+1)`, `target = C origin e`, `Q : ConcreteA32QuorumBefore … deadline target` (`CurrentTargetA32Support.lean:528-538`), `Q.source = GJ origin` |
| 3 | `:785-791` | `accepted_paperA32IncludedAtTip_of_concreteQuorum` (`PaperA32SupportRealization.lean:411`) |
| 4 | — | `accepted_paperA32SupportThroughoutEpoch_of_concreteQuorum` (`:379-406`) → `PaperA32SupportThroughoutEpochCore` (`Model/FFGStateSemantics.lean:1115-1127`) |
| 5 | — | `PaperA32InclusionCore.included` (`:1136-1151`), the **paper assumption**, supplied as `hpaper` |
| 6 | `:792-794` | `∃ seed`, known at `(w,m)`, ancestor of `selected`, `SourceVisibleAtTip (store w m) seed` |

### 1.2 Everything in it is past at the `e+2` endpoint — **yes**

Unpacked:

* every quorum vote is a `ConcreteHonestTargetVoteBefore`
  (`CurrentTargetA32Support.lean:178-194`) with `before_deadline : slot < deadline`
  and `deadline = compute_start_slot_at_epoch cfg (e+1)`, plus
  `slot_epoch : compute_epoch_at_slot slot = target.epoch = e` and
  `slot_at_time : E.slot_at cfg time = slot`. So **every vote is cast at a
  second whose slot lies in epoch `e`**.
* `PaperA32SupportThroughoutEpochCore` (`FFGStateSemantics.lean:1115-1127`)
  quantifies honest views `(w', m')` with
  `compute_epoch_at_slot (slot_at m') = e + 1` and, per signer, demands
  `E.AttestationReceivedBy w' m'` and `a.data.slot ≤ E.slot_at cfg m'`
  (`PaperA32LinkSupportAtCore`, `:1073-1098`). Those receipts are of epoch-`e`
  votes in epoch-`(e+1)` views; the delivery is
  `ConcreteA32QuorumScheduledDelivery` (`CurrentTargetA32Support.lean:543-566`)
  plus ordinary synchrony.
* `PaperA32InclusionCore.included`'s conclusion is read at `(w,m)` with
  `compute_start_slot_at_epoch cfg (e+2) ≤ E.slot_at cfg m`
  (`lateVisibleSeedAt:777-784` derives exactly this from `hlate`).

**So the answer to the brief's question is yes.** At the `e+2` endpoint every
object in the chain is about votes already cast and already delivered. The
"future span" of `currentTargetFutureSpan` is future *relative to the origin
call's slot*, never relative to the consuming endpoint — and the whole span is
bounded above by `currentTargetEpochEnd`, the last slot of epoch `e`
(`CurrentTargetFutureSupport.lean:28`, `:41`), which under `hlate` is strictly
below `slot_at m`.

This is the reconciliation with `justification-causality-contract.md` §6 (§3.2
below): §6's negative finding is about an endpoint `m` *inside* the target's
epoch; the A1 site is never that.

---

## 2. The reordering crux (question 2) — verdict: **the order is wrong, but
the capped input rescues it**

### 2.1 The write-back order, verified line by line

`fcrStep_endpointFilterOutcome` (`AcceptedSelectedStrictEdgeFilterSupply.lean:1712`),
current-epoch late branch:

```
:1861  hwrite : E.confirmed v (n+1) = trace.result
:1870  acceptedHistoricalA32CurrentLineage_of_completedPrefixes … hv hn1H hcurrentConfirmed
:1874  hlineage : AcceptedHistoricalA32LineageAt B trace.result e
:1894  acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage …
:1222      → AcceptedHistoricalA32LineageAt.lateVisibleSeedAt
:748           → hpayload.support_branch
```

`acceptedHistoricalA32CurrentLineage_of_completedPrefixes` is the projection of
`AcceptedHistoricalA32CurrentLineageAt B v (n+1)`
(`AcceptedHistoricalA32Induction.lean:31-40`, `:337-355`), whose `succ` case
(`:243-273`) is the call case: it calls
`getLatestConfirmedTraceAt_currentLineage_step` with `hcall.helper_provisos`
(`:270`) — the proviso **at second `n`**. In that transformer, when the call
*is* a crossing (`hcrossing` true, `AcceptedHistoricalA32OneStep.lean:136-140`,
`:180-184`, `:226-229`), the `hcrossingLineage` branch (`:78-100`) runs
`selectedCurrentCrossingLineage_of_fixedSourceProducer`, whose body ends in
`AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget` +
`AcceptedHistoricalA32LineageAt.refl` (`AcceptedHistoricalA32Crossing.lean:156-158`;
`AcceptedHistoricalA32Step.lean:365-367`, `:446-448`). `refl` sets
`origin := trace.result` (`AcceptedHistoricalA32Payload.lean:265-273`).

**Therefore:** the lineage consumed at the call's own second is the lineage the
call just built, and at a crossing its payload's origin call is that same call
at second `n`. §9.3 Correction 2 is confirmed. The proposed restructure ((i)
prove `SafeFrom` from the previous lineage, (ii) then build this call's
lineage) is impossible: the filter outcome's *conclusion* is indexed by
`trace.result`, so it cannot be produced from `confirmed v n`'s lineage at all.

The `currentHistorical` arm is unaffected, exactly as §9.3 says: it fires under
`hnone`, so `getLatestConfirmedTraceAt_currentLineage_step` took its
`hnoCrossingLineage` branch (`AcceptedHistoricalA32OneStep.lean:101-113`,
`:152-157`, `:197-202`) and the origin call is strictly earlier. **D1† stands.**

### 2.2 …but the consumption-time derivation exists, because `hIH` *is* the
capped step-`n` conclusion

The decisive fact §9.3 states but does not exploit: the A1 branch carries

```lean
hIH : E.SelectedCanonicalBeforeEndpointAt cfg ext (n+1)
        (E.getLatestConfirmedTraceAt cfg ext v n).result m
```
(`AcceptedSelectedStrictEdgeFilterSupply.lean:1765-1766`), unfolded
(`SelectedTraceFFGRealizationPipeline.lean:42-49`) to

```lean
∀ w' ∈ E.honest, ∀ m', slot_start (slot_at (n+1)) ≤ m' → slot_at m' < slot_at m →
  WithinHorizon m' → is_ancestor (store w' m') (get_head (store w' m')) (node trace.result) = true
```

Compare `EngineInv` (`EngineInduction.lean:52-56`), which the repo already
documents as "`SafeFrom` capped at cutoff slot `k`" (`L4Fold.lean:50-58`):

```lean
EngineInv b n₀ k := ∀ w ∈ E.honest, ∀ m, n₀ ≤ m → slot_at m ≤ k → WithinHorizon m → …
```

`hIH` **is** `EngineInv trace.result (n+1) (slot_at m − 1)` modulo two trivial
conversions: `slot_start (slot_at (n+1)) ≤ n+1 ≤ m'` by
`Clock.lean:158` (`slot_start_le_of_slot_at`), and the strict/non-strict cap.
`hIH` is not a fold output of step `n`; it is the **binder** of
`SelectedStrictEdgeFilterSupplyAt` (`SelectedCoveredMarginConstruction.lean:58-66`),
discharged by the endpoint induction in
`selectedCoveredMarginSupplyAt_of_filterSupply_minimal` (`:126`) — i.e. the
inner induction of the *same* step, well-founded on `slot_at m`.

So the well-founded input the lazy manufacture needs **does exist at the A1
site**, one induction level down rather than one fold step back.

### 2.3 Why the cap suffices — the epoch arithmetic

`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
(`HonestTargetAgreement.lean:244-329`) consumes `hsafe` in exactly one place:
inside `honestVoteTarget_eq_checkpoint_of_head_ancestor` at
`HonestTargetAgreement.lean:197` (`have hanc := hsafe v hv k hqk hkH`), where
`k` is the honest voter's *cast second* for slot `s`, and
`honest_vote_eq_honestAttestation` (`:97-104`) gives `E.slot_at cfg k = s`.
The conclusion's own quantifier (`TheoremStatements.lean:70-74`) restricts `s`
to `compute_epoch_at_slot cfg s = T.epoch`, and at the crossing call
`T.epoch = get_current_store_epoch (query.store) = e`. Hence

```
slot_at k = s   and   compute_epoch_at_slot s = e
  ⟹ s < compute_start_slot_at_epoch cfg (e+1)         (slot_lt_next_epoch_start, CurrentTargetA32Support.lean:204-211)
  ⟹ slot_at k ≤ compute_start_slot_at_epoch cfg (e+1)
```

and under `hlate` (`e + 2 ≤ compute_epoch_at_slot (slot_at m)`, i.e.
`start(e+2) ≤ slot_at m` — the derivation is already in
`lateVisibleSeedAt:777-784`) we get `start(e+1) < start(e+2) ≤ slot_at m`.

**So `EngineInv b (second+1) (start(e+1))` is enough to prove the *uncapped*
`HonestVotesSupportTarget T (second+1)`, and `hIH` supplies it.**

This is precisely the pattern already mechanized one level up:
`canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch`
(`SelectedA32Semantics.lean:118-172`) converts the same `hIH` plus the same
`hlate` into `CanonicalThroughoutEpoch selected (e+1)` — full head-descent at
every honest view of epoch `e+1` — and is consumed at
`AcceptedSelectedStrictEdgeFilterSupply.lean:1888-1893`. The new lemma is its
sibling for epoch `e` in `EngineInv` form; the arithmetic (`hslotUpper` at
`SelectedA32Semantics.lean:150-163`) is line-for-line reusable.

**Verdict on question 2.** The reordering *as posed* is impossible (§2.1). But
the crux question behind it — "can the construction-time obligation be replaced
by a consumption-time derivation?" — is **yes**, using the endpoint induction's
own hypothesis rather than a fold step. The residue closes, and closes without
any new assumption.

---

## 3. Question 3 — the §9.3 capped repair, evaluated honestly

### 3.1 The span question

Does `PaperA32SupportThroughoutEpochCore`'s consumer at the `e+2` endpoint need
the full epoch-`e` span, or only votes below some slot a capped manufacture
covers?

**It needs the full epoch-`e` span** — `currentTargetA32Signers`
(`CurrentTargetA32Support.lean:197-201`) is
`observedHonest ∪ (currentTargetFutureSpan).filter honest`, and
`currentTargetFutureSpan store = span_committee (get_current_slot store)
(currentTargetEpochEnd store)` (`CurrentTargetFutureSupport.lean:28`, `:41`),
committee seats through the **last slot of epoch `e`**. That is
`justification-causality-contract.md` §6's finding, and it is correct.

**But the full epoch-`e` span is entirely below `slot_at m` at the A1 site.**
That is the conjunct §6 could not have, because §6 was analysing the generic
Trunk-A/Trunk-B consumption at an endpoint `m` constrained only by
`hslotQM : slot_at (n+1) ≤ slot_at m`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:1792-1795`), which permits `m`
inside epoch `e`. Its sentence — "**yes** — the quorum needs honest votes at
slots `≥ slot_at m` whenever `m` lies inside the target's epoch, the normal
case" — is *true and remains true*, and it is simply **not the A1 case**: A1 is
guarded by `hlate`, which is precisely the negation of "`m` lies inside the
target's epoch (or the next one)".

So the two documents are consistent, and the reconciliation is one line:

> §6's cap failure is about endpoints inside epoch `e`. `support_branch`'s only
> consumer is `e+2`-guarded, so its endpoints are never inside epoch `e`, and
> there the derived cap `slot_at m` strictly dominates `currentTargetEpochEnd`.

### 3.2 What predicate/cap actually suffices

**Not** a capped `HonestVotesSupportTargetUpTo`. The cap belongs on the
*safety* side, where the repo already has the predicate:

```lean
-- EngineInduction.lean:52 — already exists, already has `.mono` (:62)
EngineInv cfg ext E b n₀ k
```

Concretely, three small additions (sizes in §4.4):

* **C1.** `honestVoteTarget_eq_checkpoint_of_head_ancestor_capped`
  — `HonestTargetAgreement.lean:168-213` with `hsafe : SafeFrom b q` replaced
  by `heng : EngineInv b q cap` and one new hypothesis `hscap : s ≤ cap`; the
  single use site `:197` becomes `heng v hv k hqk (hkSlot ▸ hscap) hkH`.
  (`hkSlot : slot_at k = s` is already produced at `:194`, currently discarded
  as `_`.)
* **C2.** `honestVotesSupportTarget_of_engineInv_currentEpochCandidate`
  — `HonestTargetAgreement.lean:244-329` with the same swap plus
  `hcap : compute_start_slot_at_epoch cfg (get_current_store_epoch cfg query.store + 1) ≤ cap`;
  `hscap` is discharged inside by `slot_lt_next_epoch_start` from `heq`
  (`:293-295`). **Conclusion unchanged** — the full
  `HonestVotesSupportTarget (get_current_target query.store) q`.
* **C3.** `engineInv_of_selectedCanonical_lateEndpoint`
  — the epoch-`e` sibling of
  `canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch`
  (`SelectedA32Semantics.lean:118-172`):
  `SelectedCanonicalBeforeEndpointAt (n+1) b m` + `hlate` ⟹
  `EngineInv b (n+1) (compute_start_slot_at_epoch cfg (e+1))`.

Downstream of C2 **nothing changes**:
`AcceptedHistoricalA32OriginCallAt.honestVotesSupportTarget`
(`AcceptedHistoricalA32OriginCall.lean:167-297`) passes `hsafe` straight
through at `:293`, so it gains a capped twin by a two-token edit; `.gateRealization`
(`:324-341`), `.certified` (`:351-367`),
`certifiedCurrentTarget_of_gate_and_stateSemantics`
(`CurrentTargetCertificateRealization.lean:512-543`),
`currentTargetFutureHonestSeat_vote` (`CurrentTargetA32Support.lean:457-508`)
and the unfolding at `:504` are **untouched**.

### 3.3 What breaks

Only one thing, and it is §9.3's final paragraph: **the payload must know its
origin call is not in the consumer's future.** See §4.

---

## 4. The design that closes it

### 4.1 The obligation, stated exactly

At the A1 site, for a payload whose origin call is `(node, second, origin)`,
the manufacture needs

```lean
EngineInv cfg ext E origin (second + 1) (compute_start_slot_at_epoch cfg (e + 1))
```

and the consumer can produce it in two ways:

* **`second < n`** — `hprior : PriorStrictCallWriteBackSafe n`
  (`AcceptedHistoricalA32OriginCall.lean:129-134`, supplied by
  `priorStrictCallWriteBackSafe_of_acceptedActualFCRFold`,
  `AcceptedActualFCRNextSlotSafetyFold.lean:485-501`, and bundle-facing at
  `AcceptedActualFCRNextSlotSafetyFacade.lean:100-108`) gives the *uncapped*
  `SafeFrom origin (second+1)`; weaken to `EngineInv` at any cap. This is the
  landed `safeFrom_of_prior` (`AcceptedHistoricalA32OriginCall.lean:304-313`).
* **`second = n`** — then `origin = trace.result` (crossing branch), and C3
  converts `hIH` directly.

`second > n` cannot occur for the payload in `v`'s lineage at `n+1`, but the
*type* does not know it, and the origin root is existentially quantified after
transport (`AcceptedHistoricalA32OriginCallFor`,
`AcceptedHistoricalA32OriginCall.lean:111-113` — necessarily so, because
`transport_sameEpoch` re-indexes by the checkpoint, not the root,
`AcceptedHistoricalA32Payload.lean:196-207`). So the disjunction must be
recorded.

### 4.2 Why it cannot be recorded as a plain field

Three shapes were checked and all fail:

| candidate antecedent | fails because |
|---|---|
| `CanonicalThroughoutEpoch origin e` (unconditional) | false before the origin call: honest heads need not descend `origin` at epoch-`e` seconds `< second+1` |
| `∀ i k, confirmed i (k+1) = origin → EngineInv origin (k+1) cap` (origin-keyed, uniform) | consumer cannot discharge it for a *later* call `k > n` that also writes back `origin` |
| `EpochCallWriteBackEngineSafe e` (uniform over all epoch-`e` calls) | same: includes calls at seconds `> n`, not yet proved by the fold at step `n` |

### 4.3 The shape that works — a *closure* inside the `Supp` parameter

Extend §9.1's shim by a second parameter, a predicate on `(origin, e)`:

```lean
structure AcceptedHistoricalA32GatePayloadCoreAt
    (B) (origin : Root) (e : Epoch)
    (Cert : Checkpoint Root → Prop) (Supp : Root → Epoch → Prop) where
  origin_block  : BeaconBlock Root
  origin_at     : E.AcceptedBlockAt cfg ext origin origin_block
  origin_epoch  : compute_epoch_at_slot cfg origin_block.slot = e
  anchor_epoch_le : B.anchor.epoch ≤ e
  certified     : Cert (B.state.C origin e)
  support_branch : Supp origin e
```

with the **eager** instantiation (weak trunk, zero diff)

```lean
abbrev AcceptedHistoricalA32GatePayloadAt (B) (origin) (e) :=
  AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
    (fun c => Nonempty (CertifiedJustified cfg E B.anchor c))
    (fun o ee => E.AcceptedHistoricalA32DeferredSupportAt cfg ext B o ee)
```

and the **lazy** instantiation (strong trunk), parameterized by the owning
validator `v` and the write-back second `N`:

```lean
/-- Capped, node-and-second-bounded call-safety supply. -/
def CallWriteBackEngineSafeUpTo (v : ValidatorIndex) (N : ℕ) (cap : Slot) : Prop :=
  ∀ k : ℕ, k + 1 ≤ N → E.WithinHorizon cfg (k+1) → E.IsFCRCallAt cfg ext v k →
    E.confirmed cfg ext v (k+1) ≠
      (E.getLatestConfirmedTraceAt cfg ext v k).afterObserved →
      EngineInv cfg ext E (E.confirmed cfg ext v (k+1)) (k+1) cap

def LazySupportAt (B) (v : ValidatorIndex) (N : ℕ) (origin : Root) (e : Epoch) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
    E.CallWriteBackEngineSafeUpTo cfg ext v N (E.slot_at cfg m) →
      B.state.C origin e = B.anchor ∨
        Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)
```

Key properties, each checked:

* **Not circular.** `of_fixedSourceCurrentTarget`'s lazy twin, at the crossing
  call `(v, n)` with `N := n+1`, receives the antecedent *hypothetically*,
  instantiates it at `k := n` (side condition `origin_strict`, already a field
  of the landed record, `AcceptedHistoricalA32OriginCall.lean:97-98`), obtains
  `EngineInv origin (n+1) (slot_at m)`, weakens the cap to `start(e+1) ≤ slot_at m`
  (from the `hlate` binder, which the field already has), runs C2 and then the
  unchanged manufacture. Nothing is proved about the fold at step `n`.
* **Transports.** `transport_sameEpoch` re-indexes via `hcheckpoint`
  (`AcceptedHistoricalA32Payload.lean:196-207`, `:222-232`); `LazySupportAt`'s
  antecedent does not mention `origin`, so only the disjunction moves — exactly
  the two-line rebuild already there.
* **Extends.** The write-back induction moves a lineage from `N = n` to
  `N = n+1`; `CallWriteBackEngineSafeUpTo v (n+1) cap → CallWriteBackEngineSafeUpTo v n cap`
  is anti-monotone in `N`, so
  `LazySupportAt v n o e → LazySupportAt v (n+1) o e`. One `mapSupp` lemma on
  the lineage (`Supp → Supp'` pointwise) covers `refl`/`extend`/`payloadAtTip`.
* **Consumer dischargeable.** At `fcrStep_endpointFilterOutcome` step `n`,
  endpoint `m`, prove `CallWriteBackEngineSafeUpTo v (n+1) (slot_at m)`:
  `k < n` → `hprior` (uncapped → `EngineInv`); `k = n` → `hwrite`
  (`:1861-1863`) makes it `trace.result`, and C3 converts `hIH`. The
  previous-epoch-start late branch (`:1966`) only ever needs `k < n`, because
  its payload's epoch `e` was current at a strictly earlier slot.

### 4.4 Sizes

| item | content | size |
|---|---|---|
| C1/C2 | `EngineInv`-capped twins in `HonestTargetAgreement` | ~15 lines delta (two hypothesis swaps + one `slot_lt_next_epoch_start`) |
| C3 | `engineInv_of_selectedCanonical_lateEndpoint`, sibling of `SelectedA32Semantics.lean:118` | ~45 lines, arithmetic copied from `:139-163` |
| C4 | `CallWriteBackEngineSafeUpTo` + `.mono` (`N`, `cap`) | ~15 lines |
| C5 | capped twin of `AcceptedHistoricalA32OriginCallAt.honestVotesSupportTarget` / `.gateRealization` / `.certified` / new `.deferredSupport` | ~30 lines (the landed proof is reused verbatim; only `hsafe` at `:293` changes) |
| S1 | `Cert`+`Supp` Core/abbrev shim for payload **and** lineage, + `mapSupp` | ~90 lines, additive, weak side zero diff |
| S2 | eager/lazy wrappers for `lateVisibleSeedAt` and `…retainedVisible_of_lateLineage` (§5.2) | ~40 lines |
| S3 | write-back induction instantiates `Supp := LazySupportAt v n`, `mapSupp` at the step | ~25 lines |
| S4 | discharge `CallWriteBackEngineSafeUpTo` at the two strong late branches | ~40 lines |
| T3 | thread `hprior` down the strong chain (unchanged from §9.4 item 4) | ~10 files, ~0 new proof |

Nothing in `CurrentTargetA32Support`, `CurrentTargetFutureSupport`,
`CurrentTargetCertificateRealization`, `AcceptedCurrentTargetGateBridge`, or
`NoConflictCertificatePinning` moves. That is the whole of §9.3's item (2),
deleted from the plan.

---

## 5. The §9.1 Cert shim — confirmation and spec (question 5)

### 5.1 It works, and the pattern is already in the repo

`PaperA32Inclusion` is *already* an `abbrev` over `PaperA32InclusionCore`
(`FFGStateSemantics.lean:1188-1190`, `:1212-1215`) and is consumed by dot
notation (`hpaper.included`) and by full-name application throughout. So the
mechanism is proven in-tree.

Resolution rules relied on, each load-bearing:

* `abbrev` is `@[reducible]`; Lean 4 dot notation resolves the namespace from
  the head constant after `whnfR`, so `hpayload.certified`,
  `hpayload.support_branch`, `hpayload.anchor_epoch_le`, `hlineage.payload`,
  `hlineage.origin`, `hlineage.descends`, `hlineage.tip_epoch`,
  `hlineage.payloadAtTip`, `hlineage.tip_epoch_eq_of_causal_known` all keep
  resolving.
* Anonymous-constructor notation `{ … }` and `refine { … }` elaborate against a
  reducible abbreviation of a structure. Both forms are used
  (`AcceptedHistoricalA32Payload.lean:107-117` `of_anchor`, `:132-139`
  `of_fixedSourceCurrentTarget`, `:210-226` `transport_sameEpoch`,
  `:265-273` `refl`, `:283-297` `extend`).
* Declarations may be added in the namespace `Foo` when `Foo` is an `abbrev`;
  the existing constructor names therefore survive unchanged as thin wrappers
  at the eager instantiation.

### 5.2 The five shared constructor/consumer sites — all confirmed

| site | call | under the shim |
|---|---|---|
| `WeakHistoricalA32Step.lean:679` | `Execution.AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget cfg ext B hstore hresultKnown hresultCurrent htarget hfixed` then `LineageAt.refl` (`:680`) | unchanged: eager `Cert`/`Supp` |
| `WeakHistoricalA32Step.lean:764` | identical | unchanged |
| `WeakHistoricalA32Induction.lean:265` | `…GatePayloadAt.of_anchor cfg ext B hat horiginEpoch (…)` then `LineageAt.refl` (`:270`) | unchanged |
| `WeakSelectedStrictEdgeFilterSupply.lean:1285` | `…of_anchor` + `refl` + `Weak.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual` | unchanged |
| strong: `AcceptedHistoricalA32Crossing.lean:156`, `AcceptedHistoricalA32Step.lean:365`, `:446` | `of_fixedSourceCurrentTarget` | flipped to the lazy instantiation in the flip wave |

**One correction to §9.2's scope.** §9.2 names only `certified` as shared. The
**A1 consumption is shared too**:
`acceptedSelectedResultFilterOutcome_retainedVisible_of_lateLineage`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:1160`) is called from the weak
dispatcher at `WeakSelectedStrictEdgeFilterSupply.lean:2247` and `:2315`, and
`lateVisibleSeedAt` has exactly one caller
(`AcceptedSelectedStrictEdgeFilterSupply.lean:1222`) inside it. So the shim must
cover `Supp`, and `lateVisibleSeedAt` / `…_of_lateLineage` each need an
eager wrapper (weak, unchanged signature) and a lazy twin (strong, extra
`CallWriteBackEngineSafeUpTo` argument). Without that, the flip breaks the weak
trunk at two more sites than §9.2 accounts for.

### 5.3 Shim spec (T4a, revised)

1. `AcceptedHistoricalA32GatePayloadCoreAt … (Cert) (Supp)` as in §4.3;
   `abbrev AcceptedHistoricalA32GatePayloadAt := Core … eagerCert eagerSupp`.
2. `AcceptedHistoricalA32LineageCoreAt … (Cert) (Supp)` with the same field set
   (`origin`, `payload`, `tip_block`, `tip_at`, `tip_epoch`, `descends`,
   `same_epoch_segment`, `AcceptedHistoricalA32Payload.lean:251-263`);
   `abbrev AcceptedHistoricalA32LineageAt := Core … eagerCert eagerSupp`.
3. `refl`, `extend`, `payloadAtTip`, `transport_sameEpoch`,
   `tip_epoch_eq_of_causal_known`, `payloadAtQuery_nonempty` become
   `Cert`/`Supp`-polymorphic; the existing names stay as the eager wrappers.
4. New `mapCert` / `mapSupp` on both records.
5. `of_anchor` discharges `Supp` from a supplied
   `hanchorSupp : ∀ o e, C o e = anchor → Supp o e` (eager and lazy both
   satisfy it trivially).
6. **Zero diff** for `WeakHistoricalA32Step`, `WeakHistoricalA32Induction`,
   `WeakSelectedStrictEdgeFilterSupply`, `WeakSelectedJustifiedOrientation`,
   `WeakPreQuerySIR`. Verify with `git diff --stat -- '*Weak*'` = empty after
   T4a.
7. No audit witness changes: `scripts/Audit.lean:22-47` lists 23 names and none
   mentions the payload, the lineage, or `HonestVotesSupportTarget`.

---

## 6. Question 4 — the classification, for the record

The residue closes (§2-§4), so this section is contingency. But the proposed
classification should be rejected on its merits even as a fallback:

* **Paper A3.2 in the repo** is `PaperA32InclusionCore`
  (`Model/FFGStateSemantics.lean:1136-1151`), an *implication*:
  canonical `b` + `PaperA32SupportThroughoutEpochCore V b e` ⟹ by `st(e+2)`
  every honest view has a pre-boundary descendant carrying `C(b,e)` in AU. It
  is supplied as the premise `hpaper : B.state.PaperA32Inclusion cfg ext`
  (`AcceptedSelectedStrictEdgeFilterSupply.lean:1724`).
* **The proviso** is `HonestVotesSupportTarget`
  (`TheoremStatements.lean:68-74`): every honest vote at a slot of `T.epoch`
  at or after `slot_at n` has target `T`.

These are *not* the same shape, and the proviso is not weaker:

| | paper A3.2 | `HonestVotesSupportTarget` |
|---|---|---|
| logical form | implication (support ⟹ inclusion) | bare universal |
| quantifies | honest *views* in epoch `e+1` over *already-cast* votes | honest *votes* in epoch `e` **from `slot_at n` onward**, i.e. future conduct |
| what it asserts | delivery/inclusion of an existing quorum | that a quorum will *exist* |
| repo's own note | "the paper's separate liveness assumption" (`FFGStateSemantics.lean:24`) | "prediction-shaped … gated … avoiding circularity" (`TheoremStatements.lean:55-67`); the spec text quoted there is "*assumes that all honest validators will be voting in support of the current epoch target starting from the current moment in time*" |

`justification-causality-contract.md` §3 makes the same distinction and is
right: the proviso "predicts future honest conduct", A3.2 does not.
`HonestVotesSupportTarget` is the antecedent *of* A3.2's antecedent
(it manufactures `ConcreteA32QuorumBefore` →
`PaperA32SupportThroughoutEpochCore` → `PaperA32InclusionCore.included`), so
assuming it is strictly more than assuming A3.2.

**Therefore "the observer-indexed proviso reduces to paper A3.2 at crossing
calls, which is floor" would have been a false statement**, and should not be
written even as a fallback. The honest irreducible, had §2.2 failed, would have
been: *a normative prediction about honest voting from the crossing call to the
end of its epoch, not implied by A3.2, and dischargeable only by the safety
fold.* It does not arise.

(The genuinely irreducible item in this area remains the one
`trunkA-final-discharge.md` §5.5 identifies —
`Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`,
`WeakSelectedStrictEdgeFilterSupply.lean:239-245` — and that one is a
consequence of the weak theorems being one-shot with a non-honest observer
(`WeakOneShotSafety.lean:245`), not of anything in this note.)

---

## 7. Revised wave plan (supersedes §9.4)

| wave | content | files | risk |
|---|---|---|---|
| **T4a** | §5.3 shim: `Cert` **and** `Supp` parameterization of payload + lineage, eager `abbrev`s, `mapCert`/`mapSupp`; eager wrappers for `lateVisibleSeedAt` and `…retainedVisible_of_lateLineage` | `AcceptedHistoricalA32Payload`, `AcceptedSelectedStrictEdgeFilterSupply` — **2** | low; weak diff must be empty |
| **T4b** | C1-C4: `EngineInv`-capped `HonestTargetAgreement` twins, `engineInv_of_selectedCanonical_lateEndpoint`, `CallWriteBackEngineSafeUpTo` + monos | `HonestTargetAgreement`, `SelectedA32Semantics`, `AcceptedHistoricalA32OriginCall` — **3** | low; all additive |
| **T4c** | C5: capped twins of the four landed `AcceptedHistoricalA32OriginCallAt` theorems, incl. the missing `deferredSupport_of_originSafety` | `AcceptedHistoricalA32OriginCall` — **1** | low |
| **T3** | thread `hprior` (`PriorStrictCallWriteBackSafe`, already defined and supplied) down `…Facade → AcceptedActualFCRStrictHelperIntegration → AcceptedSelectedStrictEdgeFilterSupply → strictSelected_result_and_child_ancestor_… → epochStart_or_endpointOriginOrPinned_of_acceptedCallSite` | ~8-10 | medium; mechanical, wide |
| **T4d** | flip the strong payload: `of_fixedSourceCurrentTarget` lazy twin at `AcceptedHistoricalA32Crossing:156`, `AcceptedHistoricalA32Step:365`, `:446`; write-back induction instantiates `Supp := LazySupportAt v n`; lazy twins of the A1 consumers; discharge `CallWriteBackEngineSafeUpTo` at `AcceptedSelectedStrictEdgeFilterSupply:1894` (hIH+hprior) and `:1966` (hprior) | `…Crossing`, `…Step`, `…OneStep`, `…Induction`, `…CallSupplier`, `…GlobalTrajectory`, `AcceptedSelectedJustifiedOrientation`, `AcceptedSelectedStrictEdgeFilterSupply` — **~8** | high |
| **T5** | drop the support half of the strong hub and delete `SelectedHelperProvisosAt.current_target`, `AcceptedHistoricalA32CallInterfaceAt.helper_provisos`, `AcceptedHistoricalA32CompletedPrefixCallAssumptions.helper_provisos`, then `SelectedHelperProvisosAt` | **5** | low once T4d is green |
| **T6** | blocked, §5.5 of `trunkA-final-discharge.md`: weak twin + `observer_helper_provisos` | — | — |

§9.4's T4c ("capped `HonestVotesSupportTargetUpTo` and the capped quorum
manufacture … This is the real cost") is **deleted**; T4b/T4c above replace it
at roughly a fifth of the blast radius and touch none of the
`CurrentTarget*`/`AcceptedCurrentTargetGateBridge` cluster.

---

## 8. Verdict table

| # | claim | verdict |
|---|---|---|
| 1 | `support_branch`'s only consumer is A1, `e+2`-guarded | **holds** (`AcceptedSelectedStrictEdgeFilterSupply.lean:748`; `rg` finds no other reader) |
| 2 | A1's conclusion is entirely about already-cast, already-delivered epoch-`e` votes | **holds** (`CurrentTargetA32Support.lean:178-194` `before_deadline`; `FFGStateSemantics.lean:1115-1127`, `:1146-1151`) |
| 3 | the filter outcome at second `n` consumes the **post-call** lineage (index `n+1`, tip `trace.result`) | **holds** — §9.3 Correction 2 confirmed (`:1870-1876`; `AcceptedHistoricalA32Induction.lean:259-273`; `AcceptedHistoricalA32OneStep.lean:78-100`) |
| 4 | reordering to consume the pre-call lineage | **fails, structurally** — the outcome is indexed by `trace.result` |
| 5 | `hIH` is the capped step-`n` safety conclusion, supplied by the endpoint induction | **holds** (`SelectedCoveredMarginConstruction.lean:58-66`, `:126`; cf. `L4Fold.lean:50-58`, `EngineInduction.lean:52`) |
| 6 | under `hlate` the cap clears the whole epoch-`e` vote span | **holds** (`lateVisibleSeedAt:777-784`; `slot_lt_next_epoch_start`, `CurrentTargetA32Support.lean:204`) |
| 7 | `hsafe` is consumed only at cast seconds with `slot_at k = s`, `epoch s = T.epoch` | **holds** (`HonestTargetAgreement.lean:197`, `:103`, `TheoremStatements.lean:70-74`) |
| 8 | hence capped safety ⟹ **uncapped** `HonestVotesSupportTarget`; no capped support predicate, no change at `CurrentTargetA32Support.lean:504` | **holds** — reverses §9.3's item (2) |
| 9 | `justification-causality-contract.md` §6's negative finding | **holds, and does not apply to A1** — it concerns endpoints inside epoch `e`; A1's are `≥ e+2` |
| 10 | the origin-second/node bound must still be recorded | **holds** — §9.3's last paragraph; but as a `Supp` closure, not a record index (§4.3) |
| 11 | `abbrev` shim works at all five shared constructor sites | **holds**; in-tree precedent `PaperA32Inclusion` (`FFGStateSemantics.lean:1188`) |
| 12 | §9.2's shared-surface list is complete | **fails** — the A1 *consumption* is shared too (`WeakSelectedStrictEdgeFilterSupply.lean:2247`, `:2315`) |
| 13 | the residue is paper A3.2 | **fails** — it is the antecedent of A3.2's antecedent, and prediction-shaped (§6) |
| 14 | no audit witness signature changes | **holds** (`scripts/Audit.lean:22-47`) |
