# Trunk B's residue: adversarial verification of the two-case argument

Analysis only; **nothing under `FastConfirmation/` was modified**. Branch
`centaur/discharge-helper-provisos-202609161`, `HEAD a4f9bf1`. Paths relative to
the repo root (`/home/agent/workspace/vfc`). Companions:
[`proviso-discharge-map.md`](proviso-discharge-map.md),
[`justification-causality-contract.md`](justification-causality-contract.md),
[`epoch-indexed-restructure.md`](epoch-indexed-restructure.md).

---

## 0. Headline verdict

**The two-case argument is sound, and it is stronger than proposed: the
"causality field" it needs is not a new assumption — it is *derivable* from
machinery already in the repo.**

Three corrections to the brief, all in the favourable direction:

1. **Case α does not need the SIR bracket at all.** Both Trunk-B consumers
   (`…endpointJustifiedEpoch_le_result`, `…result_and_child_ancestor_…`) already
   contain a *proviso-free* post-query branch keyed on exactly the H2 predicate
   — `Execution.endpoint_justified_epoch_le_of_causal_honest_target_minimal`
   (`Proof/CausalCheckpointEpochBound.lean:87`) and
   `…endpoint_justified_ancestor_of_causal_honest_target_minimal`
   (`Proof/CausalCheckpointCompatibility.lean:37`), both consuming `hIH` and
   `hselectedKnown` and nothing else. Case α's job is only to *supply an H2
   witness*; the geometry is already mechanized. (The brief's literal route —
   feeding `above_selected` / `inside_selected_segment` — also holds
   geometrically, see §3.4, but costs two new transport lemmas for no gain.)
2. **Case β is the existing arithmetic branch with one seat-argument swapped.**
   `Execution.noConflict_arithmeticBranch_oneThird_of_prefixEvidence`
   (`Proof/WeakHistoricalA32CallSupplier.lean:385`) already proves
   `total_active < 3 · weight(observedHonest ∪ futureHonest)` **without the
   proviso and without node honesty**. The proviso is consumed *only* at
   `WeakHistoricalA32CallSupplier.lean:664` (`currentTargetFutureHonestSeat_vote`)
   to turn a future seat into a `T`-voter. Case β replaces that by "a future seat
   cannot be in `J`'s quorum at all", which is a committee-assignment argument.
   This **bypasses** `epoch-indexed-restructure.md` §7's objection (that the
   elapsed prefix carries no weight bound): no bound on the prefix is needed.
3. **The causality conjunct is derivable.** `SupermajorityLink` carries no slot
   data (`Model/FFGCertificates.lean:51-69`), but the endpoint's justified
   checkpoint is not certified by a bare `SupermajorityLink` — it is certified by
   an `IncludedCertifiedJustified` over a carrier known in the endpoint store
   (`AcceptedSelectedJustifiedOrientation.lean:163-172`,
   `AcceptedFFGGlobalCheckpointTrajectory.lean:624-635`), whose
   `IncludedAttestationEvidence` (`Model/FFGStateSemantics.lean:90-115`) supplies
   `slot_before_carrier`, `target_epoch`, `slot_within_horizon` and
   `attesters_in_committee` for **every** signer. §4 derives
   `a.data.slot + 1 ≤ E.slot_at cfg m` from these.

**Consequence.** `observer_helper_provisos` can be deleted with **no replacement
assumption whatsoever**, *for Trunk B*. The residual blocker for actually
deleting the field is Trunk A (`current_target`'s positive quorum use at
`WeakHistoricalA32Step.lean:280`), which is `epoch-indexed-restructure.md`'s
R0–R4 and is independent of this note.

---

## 1. Where the proviso actually enters Trunk B, exactly

`Weak.SelectedHelperProvisosAt` (`WeakSelectedStrictEdgeFilterSupply.lean:209-233`)
supplies only `HonestVotesSupportTarget`; **both executable gate booleans are
derived, not assumed**:

* `CurrentTargetAcceptedEdge.current_target_gate` — `SelectedFilterBridge.lean:203-209`;
* `selected_previous_result_no_conflict_gate` — `SelectedFilterBridge.lean:~180-193`.

See `Execution.currentTargetAcceptedEdge_gate_and_support`
(`SelectedA32Support.lean:38-49`) and
`…selectedPreviousResult_noConflict_gate_and_support` (`:54-72`): each returns
`⟨derived gate, hprovisos.<field>⟩`.

The support halves are then stored in two constructors of the call-site
inductive `StrictSelectedHistoricalSIRCallSite`
(`SelectedPreQueryHistoricalSIR.lean:62-90`; weak twin `WeakPreQuerySIR.lean:290-323`):
`currentCrossing.support` (`:70-71`) and `previousNoConflict.support` (`:89-90`),
and consumed in `epochStart_or_endpointCurrentTargetPinned_of_callSite`
(`:825-861`; weak `WeakSelectedJustifiedOrientation.lean:112-167`) at:

| Arm | Weak line | Uses `support` for |
|---|---|---|
| `currentCrossing` | `:143-149` | `CurrentTargetCertificateProducerAt` → `Nonempty (CertifiedJustified anchor T)` → `hacc.justified_unique` |
| `currentHistorical` | `:150-158` | — (payload `certified`, Trunk A) |
| `previousEpochStart` | `:159-160` | — (short circuit) |
| `previousNoConflict` | `:161-167` | `NoConflictCertificatePinningProducerAt` → `…_at_observer` (`WeakHistoricalA32CallSupplier.lean:522`) |

Both live arms produce the **same** conclusion: `J.root = T.root` where
`J = (E.store cfg ext w m).justified_checkpoint`,
`T = get_current_target cfg query.store`. That equality is the only thing Trunk B
needs from the proviso, and it is consumed as `hJT : J = T` at
`SelectedPreQueryHistoricalSIR.lean:1196` / `:1267`.

**Verdict on the brief's setup facts.**

* `J` materialized at `(w,m)`: **holds**. `WeakSelectedJustifiedOrientation.lean:139-141`
  obtains `hJ` from `ExactPrefixAcceptedFFGSemantics.endpointJustified_certificate`
  (`AcceptedSelectedJustifiedOrientation.lean:154-172`) applied to
  `E.store_causal cfg ext w m` (`:220`). Strong twin
  `SelectedFilterBridge.lean:403-404` at `:1318`/`:1373`. ✔
* `hIH` shape (`AcceptedSelectedStrictEdgeFilterSupply.lean:152-159`): **holds**,
  and the weak twin carries it verbatim
  (`WeakSelectedJustifiedOrientation.lean:493-500`, `:322-329`). ✔
* `votes_assigned` / `votes_head` (`Model/Assumptions.lean:88-96`): **holds**, and
  `no_forgery` (`:101-105`) — not mentioned in the brief — is the field that makes
  the whole argument possible: *every* attestation naming an honest validator
  carries that validator's own recorded vote **for `a.data.slot`**. ✔

---

## 2. Does quorum membership pin the signer's target to `J`? — **holds**

The brief asks this explicitly. Answer: yes, and by a better route than
`JustificationInterface.justified_requires_targets` (`TheoremStatements.lean:144-158`),
which is **not in the accepted premise bundle**
(`AcceptedActualFCRNextSlotSafetyAssumptions`,
`AcceptedActualFCRNextSlotSafetyFacade.lean:33-48`, contains no
`JustificationInterface`). Using it would be a genuine new premise.

Instead, `J`'s own certificate carries the quorum:

* `SupermajorityLink.signer_attestation` (`Model/FFGCertificates.lean:64-68`):
  `∀ i ∈ signers, ∃ w n a fb, Event.attestation a fb ∈ E.schedule w n ∧
   i ∈ a.attesting_indices ∧ a.data.source = source ∧ a.data.target = target`.
* `signers_in_epoch` (`:61-63`) and `supermajority` (`:69`) are the same shape as
  `justified_requires_targets`'s.
* For honest `i`, `HonestBehavior.no_forgery` (`Model/Assumptions.lean:101-105`)
  converts `i ∈ a.attesting_indices` into `E.vote i a.data.slot = some (m', a')`
  with `a'.data = a.data`, hence `a'.data.target = J`.

This is exactly the pattern already used at `NoConflictCertificatePinning.lean:831-834`
and `WeakHistoricalA32CallSupplier.lean:719-723`. **Holds, no new lemma.**

---

## 3. Case α — H2 non-empty

### 3.1 The witness feeds an existing, proviso-free consumer

`Execution.endpoint_justified_epoch_le_of_causal_honest_target_minimal`
(`CausalCheckpointEpochBound.lean:87-208`) takes precisely

```
{i} (hi : i ∈ E.honest) {s} (hqs : E.slot_at cfg q ≤ s) (hsm : s < E.slot_at cfg m)
(hsH : E.SlotWithinHorizon cfg s) (hvote₀ : E.vote i s = some (k₀, a₀))
(htarget₀ : a₀.data.target = (E.store cfg ext w m).justified_checkpoint)
(hnotJGlc : ¬ is_ancestor … J.root … glc)
```

plus `hglcKnown` and `hIH` — i.e. **an H2 member, verbatim** — and concludes
`J.epoch ≤ get_block_epoch cfg (E.store w m) glc`. Internally (`:170-179`) it
derives `hkLower : slot_start (slot_at q) ≤ k` from `hqs` via
`query_slot_start_le_of_slot_ge_minimal` and applies `hIH i hi k hkLower hkSlotLt hHk`.

The compatibility twin `endpoint_justified_ancestor_of_causal_honest_target_minimal`
(`CausalCheckpointCompatibility.lean:37`) has the same premise shape and is
consumed at `SelectedJustifiedCompatibility.lean:311-317`.

Both are already reached today whenever `EndpointJustificationOriginAt`'s *single*
origin vote happens to satisfy `slot_at q ≤ s`
(`WeakSelectedJustifiedOrientation.lean:717-722`;
`SelectedJustifiedCompatibility.lean:310-323`). **The proviso is needed only when
that one vote is pre-query.** Case α's content is: *look at the whole quorum, not
just the origin vote.*

**Verdict: holds. New content is the witness supplier (§4), not the geometry.**

### 3.2 Side conditions of the witness

| Conjunct needed | Source | Verdict |
|---|---|---|
| `i ∈ E.honest` | case split | holds |
| `E.vote i s = some (k₀,a₀)`, `a₀.data.target = J` | `no_forgery` | holds |
| `E.SlotWithinHorizon cfg s` | `IncludedAttestationEvidence.slot_within_horizon` (`FFGStateSemantics.lean:100`) | holds |
| `E.slot_at cfg 0 ≤ s` | free from `slot_at q ≤ s` + `slot_at_mono` | holds |
| `slot_at q ≤ s` | case-α hypothesis | holds |
| `s < E.slot_at cfg m` | §4 (derived causality) | holds, **derived** |

### 3.3 The brief's boundary-block reasoning — cross-check

The brief's α reasoning ("the epoch-`e` boundary block of a chain through
`result` lies at-or-above `result`") is the content of
`checkpointTarget_epoch_le_of_head_descent_and_reverse_exclusion`
(`CausalCheckpointEpochBound.lean:36-72`), which is proved by `get_ancestor_comp`
exactly as the brief describes. **Holds** — and is already in the repo, so it need
not be re-derived.

### 3.4 The brief's literal bracket route (for the record)

If one insisted on feeding the bracket instead:

* Region selection is **forced by epoch arithmetic**, not chosen. At the
  `previousNoConflict` configuration (`epoch(result)+1 = e`, `J.epoch = e` by
  `aboveSelectedRegion_forces_previous`, `SelectedPreQueryHistoricalSIR.lean:1243`)
  `below_input` and `inside_selected_segment` are **vacuous** and only
  `above_selected` is live. At `currentCrossing`/`currentHistorical`
  (`epoch(result) = e`) `above_selected` is vacuous (it would need
  `e < J.epoch ≤ e`, contradicting `htargetUpper` at `:1147-1150`) and only
  `inside_selected_segment` is live. **The brief's guess is correct.**
* `is_ancestor store (node X) (node Y) = true` means *`X` descends from `Y`*
  (read off `compatible_of_selected_descends_input`,
  `SelectedPreQuerySIR.lean:70-100`). So `above_selected`
  (`SelectedPreQuerySIR.lean:57-61`) demands `J.root ⪰ result` and
  `inside_selected_segment` (`:48-56`) demands `result ⪰ J.root ∧ J.root ⪰ input`.
  **Both are exactly what an H2 voter's head chain yields**, with the direction
  flip the brief predicts. ✔
* **But** the bracket lives in the *endpoint* store
  (`SelectedPreQueryHistoricalSIR.lean:1090-1092`), while case α's ancestry is
  born in the *voter's* store at the cast second `k`. Transport is available —
  `E.rootDescends_of_store_ancestor` (`FFGEndpointRealization.lean:140`) then
  `E.store_known_ancestor_of_rootDescends_for_storeReflection`
  (`ExecutionRootReflection.lean:208`), with `J.root ∈ (store w m).block_roots`
  from `SelectedMarginDomain.justified_root_known` — but it is **two new lemmas
  for nothing**, because the bracket producer
  (`selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning`, `:1057`) does not
  take `hIH` and would have to be re-plumbed, whereas the two orientation
  theorems that call it (`WeakSelectedJustifiedOrientation.lean:581`, `:455`)
  already hold `hIH`. **Route (b) of §3.1 strictly dominates.**

---

## 4. The causality premise is **derivable** — the decisive finding

`justification-causality-contract.md` §1 proposes adding
`a.data.slot + 1 ≤ E.slot_at cfg m` to `justified_requires_targets`. For the
Trunk-B object (`J = (E.store w m).justified_checkpoint`) this is **unnecessary**.

Chain, every step cited:

1. `B.globalJustified_anchor_or_AUEvidence hgen hanchor (E.store_causal cfg ext w m)`
   gives `J = B.anchor` or `Nonempty (AcceptedSelectorAUCarrier B.state (E.store w m) J)`
   (`AcceptedSelectedJustifiedOrientation.lean:70`, `:163`;
   `AcceptedFFGGlobalCheckpointTrajectory.lean:683-695`).
2. `AcceptedSelectorAUCarrier` (`AcceptedFFGGlobalCheckpointTrajectory.lean:624-635`)
   carries `tip`, `carrier`, `tip_carrier.known : tip ∈ store.block_roots`,
   `tip_descends_carrier : E.RootDescends tip carrier`, and
   `formed_evidence : AcceptedFormedCheckpointEvidence … carrier J`.
3. `hcarrier.carrier ∈ (E.store cfg ext w m).block_roots` — **already proved**, at
   `AcceptedSelectedJustifiedOrientation.lean:117-132` (`hcarrierRoot` +
   `store_known_ancestor_of_rootDescends_for_storeReflection`).
4. `formed_evidence.certified : Nonempty (IncludedCertifiedJustified cfg E
   B.state.includedAttestations.Included B.anchor hcarrier.carrier J)`
   (`Model/FFGStateSemantics.lean:354-355`). `cases` on it: either `J = B.anchor`
   (excluded by `hanchorBefore`, `WeakHistoricalA32CallSupplier.lean:637-643`) or a
   terminal `IncludedSupermajorityLink cfg E Included hcarrier.carrier source J`
   (`Model/FFGStateSemantics.lean:206-226`).
5. For each `i ∈ L.signers`, `L.signer_attestation` (`:220-225`) gives `a` with
   `AttestationIncludedOnChain E Included hcarrier.carrier a`, i.e.
   `∃ b, E.RootDescends hcarrier.carrier b ∧ Included b a` (`:173-176`), plus
   `i ∈ a.attesting_indices` and `a.data.target = J`.
6. `B.state.includedAttestations.evidence` on `Included b a` yields an
   `AcceptedIncludedAttestationEvidence` (`:133-147`) whose base
   (`IncludedAttestationEvidence`, `:90-115`) gives
   * `slot_before_carrier : a.data.slot < carrier_message.slot` (`:101`),
   * `target_epoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot` (`:102-103`),
   * `slot_within_horizon` (`:100`), `attesters_in_committee` (`:112-113`),
   and whose `carrier_accepted : E.AcceptedBlockAt cfg ext b carrier_message` (`:137-138`)
   supplies `E.ExecutionRoot b`.
7. `b ∈ (E.store w m).block_roots` by
   `store_known_ancestor_of_rootDescends_for_storeReflection` (`ExecutionRootReflection.lean:208`)
   with `tip := hcarrier.carrier` (known by step 3) and `hdesc` from step 5.
8. `(E.store w m).blocks b = carrier_message` by `BlockAt.unique` +
   `acceptedBlockAt_of_causal_known` (pattern:
   `AcceptedSelectedJustifiedOrientation.lean:133-136`), then
   `E.store_blocks_slot_le_current` + `E.store_current_slot` give
   `carrier_message.slot ≤ E.slot_at cfg m` (pattern: `:137-145`).
9. Therefore **`a.data.slot + 1 ≤ E.slot_at cfg m`**, and additionally
   **`compute_epoch_at_slot cfg a.data.slot = J.epoch`** (step 6) and
   **`i ∈ E.committee a.data.slot`** (step 6) — the two *extra* facts case β needs
   and which the contract note's field does **not** supply.
10. `E.slot_at cfg 0 ≤ a.data.slot` follows from `TrustedAnchorBoundaryAligned`
    exactly as at `AcceptedSelectedJustifiedOrientation.lean:97-116`, using
    step 9's epoch identity and `anchor.epoch < J.epoch`.

This is the same argument the repo already runs for the *origin* vote
(`hvoteBeforeEndpoint`, `AcceptedSelectedJustifiedOrientation.lean:137-145`); §4
merely runs it for the whole quorum instead of one vote.

**Verdict: the causality premise holds and is derivable. The proposed
`justified_targets_before_endpoint` interface field is not required, and
`justification-causality-contract.md` §1 should be superseded.** (The field
remains of independent use for `Nucleus.honest_member_vote_indexed`, whose
`hanchor0 : ablk.message.slot = GENESIS_SLOT` premise is stronger than
`TrustedAnchorBoundaryAligned` and is *not* discharged anywhere.)

---

## 5. Case β — H2 empty

### 5.1 The gate arithmetic — **holds, already proved, proviso-free**

`Execution.noConflict_arithmeticBranch_oneThird_of_prefixEvidence`
(`WeakHistoricalA32CallSupplier.lean:385-477`) proves

```
E.total_active cfg < 3 * E.weight (currentTargetA32Signers cfg store state)
```

from `hgate` alone. Reading its body against
`compute_honest_ffg_support_for_current_target` (`Model/FFGHelpers.lean:73-90`):

| Spec term | Soundness step | Line | Verdict |
|---|---|---|---|
| `ffg_support_for_checkpoint` split | `current_target_score_eq_honest_add_nonhonest_weight` | `:430-436` | holds |
| `min(adversarial_weight, score)` subtraction | `hbyz : weight(observedNonhonest) ≤ adversarial` via `currentTarget_nonhonest_weight_le_adversarial_of_prefix` | `:439-451` | holds — **direction is sound** (observed score may contain adversarial weight; the model subtracts an upper bound on it) |
| `remaining_honest_ffg_weight` | `hfuture : remaining ≤ weight(futureHonest)` via `currentTarget_remaining_honest_le_future_weight` (`CurrentTargetFutureSupport.lean:237`) | `:452-455` | holds |
| elapsed/future disjointness | `currentTarget_observed_future_disjoint` | `:456-458` | holds |
| `estimate_committee_weight_between_slots` | modelled **exactly** as written; soundness enters only via `ByzantineBound.estimate_sound` (`Model/Assumptions.lean:382-385`) inside `currentTarget_remaining_honest_le_future_weight`; the `//100 * (100 − β)` rounding is handled in `Proof/EconomicRounding.lean` | — | holds; no adjustment factor is assumed away |
| `3 * honest_ffg_support > 1 * total` | `hgateArithmetic'` | `:459-467` | holds |

So the brief's `(β1)`/`(β2)` — "observed-minus-adversarial ≤ actual honest elapsed
`T`-weight" and "projected remainder ≤ actual future honest weight" — are both
**already theorems**, and the composed bound `weight(elapsedHonestT) +
weight(futureHonest) > total/3` is already `honeThird`. The brief's worry about the
observer's *observed* support including adversarial weight is answered by `hbyz`.

The remaining model lemmas the brief asks about all exist:
`current_epoch_span_eq_anchorActive` (`CurrentTargetFutureSupport.lean:119`),
`total_active_eq_anchorActive_weight` (`:107`),
`ExternalsCoherence.committee_assignment_unique` / `committee_coverage` /
`committee_members_active` (`Model/Assumptions.lean:300-319`),
`StaticValidatorSet.activity_constant` (`:334-337`),
`ByzantineBound.span_fraction` / `estimate_sound` (`:382-398`),
`one_third_honest_intersects_two_thirds` (`FFGQuorum.lean:89-96`).
**No new model lemma is needed.**

### 5.2 Where the proviso is consumed inside the pinning proof

`completedPrefix_noConflict_certifiedJustified_root_eq_currentTarget_at_observer`
(`WeakHistoricalA32CallSupplier.lean:522-…`; strong twin
`NoConflictCertificatePinning.lean:698-864`) uses `hsupport` at **one** place:
`hvotes`'s `hiFuture` branch, `:663-666` (`currentTargetFutureHonestSeat_vote`,
`CurrentTargetA32Support.lean:457-508`, proviso unfolded at `:504`). `hvotes` is then
used three times:

1. `hsignersHonest` (`:667-670`) — replaceable: `futureHonest` is
   `(currentTargetFutureSpan).filter (· ∈ E.honest)`
   (`CurrentTargetA32Support.lean:197-201`), so honesty is `Finset.mem_filter`.
2. `hsignersEpoch` (`:671-678`) — replaceable: `currentTargetFutureSpan =
   span_committee (get_current_slot store) (currentTargetEpochEnd store)`
   (`CurrentTargetFutureSupport.lean:41-42`) `⊆ span_committee (epochStart) (epochEnd) = U`
   by `current_slot_epoch_bounds` (`:82-102`).
3. the intersection contradiction (`:718-…`) — **this is where case β does new work.**

### 5.3 The intersection contradiction, case β

`one_third_honest_intersects_two_thirds` is applied with `S := signers` (honest,
`> 1/3`), `T := link.signers` (`2/3`), `U := span_committee(e)`, `W := total_active`.
Replace `T` by the §4 quorum (same `U`, same `2/3` bound via
`IncludedSupermajorityLink.supermajority`), obtaining honest
`i ∈ signers ∩ quorum`.

* **`i ∈ observedHonest`.** Unchanged, verbatim existing proof
  (`WeakHistoricalA32CallSupplier.lean:718-…`, strong `NoConflictCertificatePinning.lean:830-864`):
  `i` has a real `T`-vote (`currentTargetObservedHonestSupporter_vote_of_prefix`,
  proviso-free) and a quorum attestation targeting `J`; `no_forgery` +
  `HonestBehavior.not_slashable` (`Model/Assumptions.lean:111-114`) force
  `J.root = T.root`. **Holds.**
* **`i ∈ futureHonest`.** New. `i ∈ currentTargetFutureSpan` gives `s'' ∈ [current_slot,
  epochEnd]` with `i ∈ E.committee s''` and `compute_epoch_at_slot s'' = e`
  (`epoch_eq_of_epoch_bounds`, `CurrentTargetFutureSupport.lean:65-77`; the same
  unpacking as `currentTargetFutureHonestSeat_vote:472-491`). §4 gives
  `i ∈ E.committee a.data.slot` and `compute_epoch_at_slot a.data.slot = J.epoch = T.epoch = e`.
  `ExternalsCoherence.committee_assignment_unique` (`Model/Assumptions.lean:300-302`)
  gives `a.data.slot = s'' ≥ get_current_slot query.store = E.slot_at cfg q`
  (`store_current_slot`). Case β says `a.data.slot < E.slot_at cfg q`. **Contradiction.**

### 5.4 Where causality is load-bearing — confirmed

Case β's hypothesis is `¬∃` H2 member, i.e. no honest quorum member has
`slot ∈ [slot_at q, slot_at m)`. Turning that into `slot < slot_at q` requires
excluding `slot ≥ slot_at m`, which is exactly §4's derived bound. Without it a
future seat could sit in `J`'s quorum with a vote *after* the endpoint, and
`hIH` (strict in `slot_at m`) could not reach it. **The brief's diagnosis is
correct; the premise is just cheaper than it thought.**

Note the second requirement the brief did not flag: `compute_epoch_at_slot
a.data.slot = J.epoch`. It is *not* implied by `justified_requires_targets` even
with the contract note's conjunct, and it is *not* derivable via
`honest_attestation_data_target_epoch` without first knowing
`E.slot_at cfg 0 ≤ a.data.slot` (circular — `votes_head`,
`Model/Assumptions.lean:88-93`, demands it). §4 step 6 supplies it directly.
**Had the contract-note route been taken, this would have been a second missing
conjunct.**

### 5.5 The `currentCrossing` arm

There the true gate is `will_current_target_be_justified`
(`Model/FFGHelpers.lean:121-125`), `3·support ≥ 2·total`, which implies the
no-conflict arithmetic `total < 3·support` provided `0 < total_active` —
available from `hC.balance_floor` + `total_active_eq_anchorActive_weight`
(`CurrentTargetFutureSupport.lean:107-114`) + `Config.effective_balance_increment_pos`
(`Model/Config.lean:46`). The `get_current_target = unrealized_justified`
short-circuit of the no-conflict gate is irrelevant: that branch is closed
proviso-free by `certified_justified_unique` (`NoConflictCertificatePinning.lean:751-768`).
So **one arithmetic-only refactor** (expose `noConflict_arithmeticBranch_oneThird…`
over the raw inequality rather than over the `will_no_conflicting…` boolean)
serves both live arms. **Holds.**

---

## 6. Verdict table

| # | Step | Verdict |
|---|---|---|
| A1 | `J` materialized at `(w,m)`; endpoint certificate available | **holds** (`AcceptedSelectedJustifiedOrientation.lean:154-172`) |
| A2 | Quorum membership pins signer's target to `J` | **holds** via `SupermajorityLink.signer_attestation` + `no_forgery`; do **not** use `justified_requires_targets` (absent from the accepted bundle) |
| A3 | H2 member ⟹ honest own vote at `a.data.slot` with target `J` | **holds** (`Model/Assumptions.lean:101-105`) |
| A4 | H2 member's head contains `result` at its cast second | **holds** (`hIH`, via `query_slot_start_le_of_slot_ge_minimal`) |
| A5 | boundary-block geometry (prev-epoch `result`: `J.root ⪰ result`) | **holds**, already mechanized (`CausalCheckpointEpochBound.lean:36-72`) |
| A6 | crossing site: direction flips to `result ⪰ J.root ⪰ input` | **holds**; feeds `inside_selected_segment` as the brief predicts |
| A7 | bracket region is *forced* by epoch arithmetic, not chosen | **holds** (`:1172`, `:1243`) |
| A8 | transporting voter-store ancestry into the bracket's endpoint store | **holds but unnecessary**; needs 2 new lemmas (`rootDescends_of_store_ancestor` / `store_known_ancestor_of_rootDescends_for_storeReflection` wrappers). Superseded by A9 |
| A9 | H2 witness feeds the *existing* post-query consumers instead | **holds — recommended route**, zero new geometry (`CausalCheckpointEpochBound.lean:87`, `CausalCheckpointCompatibility.lean:37`) |
| C1 | causality `a.data.slot + 1 ≤ slot_at m` for the whole quorum | **holds, DERIVABLE** (§4); no interface field needed |
| C2 | `compute_epoch_at_slot a.data.slot = J.epoch` | **holds, DERIVABLE** (`FFGStateSemantics.lean:102-103`); *needed*, and not supplied by the contract note's proposal |
| B1 | gate ⟹ `weight(elapsedHonestT) + weight(futureHonest) > total/3` | **holds, already proved proviso-free** (`WeakHistoricalA32CallSupplier.lean:385`) |
| B2 | adversarial-correction direction is sound | **holds** (`hbyz`, `:439-451`) |
| B3 | remaining-committee weight spans `[current_slot, epochEnd]` | **holds** (`CurrentTargetFutureSupport.lean:41`) — the brief's requirement is met |
| B4 | estimation modelled exactly; adjustment factor not assumed away | **holds** (`Model/FFGHelpers.lean:79-84`; soundness only via `estimate_sound`) |
| B5 | `signers ⊆ honest` / `⊆ U` without the proviso | **holds**, trivial re-derivation |
| B6 | observed-honest ∩ quorum ⟹ `J = T` | **holds**, existing proof verbatim |
| B7 | future-seat ∩ quorum ⟹ `False` | **holds**, needs C1+C2+`committee_assignment_unique` |
| B8 | crossing arm reuses the same `>1/3` bound | **holds**, needs a raw-inequality refactor |
| B9 | §7 of `epoch-indexed-restructure.md` (prefix weight-coverage gap) | **does not apply** — the argument never bounds prefix weight |
| D1 | Trunk A (`current_target` positive quorum) | **fails here** — out of scope; still needs restructure R0–R4 |

Nothing in the chain **fails on its merits**. The only "fails" is D1, which the
brief already excludes from Trunk B.

---

## 7. New lemmas required, with signatures

All in the `Execution` / `Weak` namespaces; all additive except N5–N7.

**Status (landed).** N1–N4 are implemented and green. N1/N2 live in the new
module `FastConfirmation/Spec/Proof/EndpointQuorumCausality.lean`; N3/N4 in
`FastConfirmation/Spec/Proof/WeakHistoricalA32CallSupplier.lean`. Three
signature refinements relative to the sketches below, all *weakenings of the
premise surface* — none weakens a conclusion, and no hypothesis had to be
added:

* **N2** is split in two, because "the chosen slot of `i`" is not expressible
  as a hypothesis about an existential witness. The case-split predicate
  `EndpointJustifiedQuorumAt.PostQueryHonestSigner Q q` names the signer *and*
  its attestation (with exactly the conjuncts `signer_attestation` supplies);
  `causalHonestTargetAt_of_postQuerySigner` turns it into the existing
  `Execution.CausalHonestTargetAt cfg ext q w m`, which is precisely what
  `EndpointJustificationCausalityAt` (`SelectedJustifiedCompatibility.lean:131`)
  must produce. Case β's hypothesis is the negation of the same predicate, so
  the two cases are literally complementary. The raw witness shape (including
  `E.slot_at cfg 0 ≤ s`, which `CausalHonestTargetAt` drops) is available from
  `honestTargetVote_of_scheduledAttestation`.
* **N3** needs neither `hw : w ∈ E.honest` nor `hHm : E.WithinHorizon cfg m`:
  the endpoint certificate it opposes comes from
  `endpointJustified_certificate` at the *causal* store `E.store cfg ext w m`,
  which requires no honesty and no horizon bound. Its arithmetic premise is the
  raw helper inequality (N4's form) rather than the already-converted signer
  weight, so the caller never has to mention `currentTargetA32Signers`.
* **N4**'s `hraw` is stated over `compute_honest_ffg_support_for_current_target`
  itself rather than over its unfolded body; the two are definitionally equal,
  and the folded form is what both executable gates reduce to.

**N1 — the endpoint quorum with slot data (the §4 derivation).**
```lean
structure EndpointJustifiedQuorumAt (E : Execution Root)
    (anchor : Checkpoint Root) (w : ValidatorIndex) (m : ℕ) : Type where
  signers      : Finset ValidatorIndex
  signers_in_epoch : signers ⊆ E.span_committee
      ((E.store cfg ext w m).justified_checkpoint.epoch * cfg.slots_per_epoch)
      ((E.store cfg ext w m).justified_checkpoint.epoch * cfg.slots_per_epoch
        + (cfg.slots_per_epoch - 1))
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers
  signer_attestation : ∀ i ∈ signers,
    ∃ (u n' : ℕ) (a : Attestation Root) (fb : Bool),
      Event.attestation a fb ∈ E.schedule u n' ∧ i ∈ a.attesting_indices ∧
      a.data.target = (E.store cfg ext w m).justified_checkpoint ∧
      E.SlotWithinHorizon cfg a.data.slot ∧
      E.slot_at cfg 0 ≤ a.data.slot ∧
      compute_epoch_at_slot cfg a.data.slot =
        (E.store cfg ext w m).justified_checkpoint.epoch ∧
      i ∈ E.committee a.data.slot ∧
      a.data.slot + 1 ≤ E.slot_at cfg m

theorem ExactPrefixAcceptedFFGSemantics.endpointJustified_quorumAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    {w : ValidatorIndex} {m : ℕ}
    (hne : (E.store cfg ext w m).justified_checkpoint ≠ B.anchor) :
    Nonempty (E.EndpointJustifiedQuorumAt cfg ext B.anchor w m)
```
*Proof:* §4 steps 1–10. ~120 lines; every sub-step has a citable precedent in
`AcceptedSelectedJustifiedOrientation.lean:48-148`.
*Landed* as `Execution.EndpointJustifiedQuorumAt` /
`Execution.ExactPrefixAcceptedFFGSemantics.endpointJustified_quorumAt`
(`EndpointQuorumCausality.lean`), verbatim in this shape.

**N2 — case-α witness extraction.**
```lean
theorem EndpointJustifiedQuorumAt.postQueryHonestTarget_of_mem
    (hhb : HonestBehavior cfg ext E)
    (Q : E.EndpointJustifiedQuorumAt cfg ext anchor w m)
    {i : ValidatorIndex} (hiQ : i ∈ Q.signers) (hi : i ∈ E.honest)
    {q : ℕ} (hq : E.slot_at cfg q ≤ (chosen slot of i)) :
    ∃ (s : Slot) (k : ℕ) (a : Attestation Root),
      E.slot_at cfg 0 ≤ s ∧ E.slot_at cfg q ≤ s ∧ s < E.slot_at cfg m ∧
      E.SlotWithinHorizon cfg s ∧ E.vote i s = some (k, a) ∧
      a.data.target = (E.store cfg ext w m).justified_checkpoint
```
*Proof:* `no_forgery` + N1's conjuncts. ~15 lines.
*Landed* as `Execution.honestTargetVote_of_scheduledAttestation` plus
`EndpointJustifiedQuorumAt.PostQueryHonestSigner` /
`…causalHonestTargetAt_of_postQuerySigner` (see the status note above).

**N3 — case-β pinning (the replacement for the proviso'd producer).**
```lean
theorem noConflict_endpointJustified_root_eq_currentTarget_at_observer
    (hA : NoConflictPinningAssumptions cfg ext E)
    (B) (hT) (hfit) (hanchor) (hboundary) (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgateArith : E.total_active cfg <
      3 * E.weight (E.currentTargetA32Signers cfg
        (E.store cfg ext obs (n+1)) state) ∨
      get_current_target cfg (E.store cfg ext obs (n+1)) =
        (E.store cfg ext obs (n+1)).unrealized_justified_checkpoint)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hHm : E.WithinHorizon cfg m)
    (Q : E.EndpointJustifiedQuorumAt cfg ext B.anchor w m)
    (hnoPostQuery : ¬ ∃ i ∈ Q.signers, i ∈ E.honest ∧
      E.slot_at cfg (n+1) ≤ (chosen slot of i))
    (hepoch : (E.store cfg ext w m).justified_checkpoint.epoch =
      (get_current_target cfg (E.store cfg ext obs (n+1))).epoch) :
    (E.store cfg ext w m).justified_checkpoint.root =
      (get_current_target cfg (E.store cfg ext obs (n+1))).root
```
*Proof:* §5.3; ~90 lines, of which ~60 are the existing
`WeakHistoricalA32CallSupplier.lean:644-760` with the `hiFuture` arm rewritten.
*Landed* as
`Execution.noConflict_endpointJustifiedQuorum_root_eq_currentTarget_at_observer`
(`WeakHistoricalA32CallSupplier.lean`), without `hw`/`hHm` and over the raw
gate; the proviso-free re-derivation of `signers ⊆ E.honest` and
`signers ⊆ span_committee(e)` (§5.2 items 1–2) went through as described.

**N4 — raw-inequality form of the arithmetic branch (refactor, no new content).**
```lean
theorem noConflict_arithmeticBranch_oneThird_of_rawGate
    … (hraw : E.total_active cfg <
        3 * (get_current_target_score cfg ext store
             - min (compute_adversarial_weight …) (get_current_target_score …)
             + (E.total_active cfg - estimate_committee_weight_between_slots …) / 100
                 * (100 - cfg.confirmation_byzantine_threshold))) :
      E.total_active cfg < 3 * E.weight (E.currentTargetA32Signers cfg store state)
```
plus two 5-line corollaries deriving `hraw` from `will_no_conflicting_checkpoint_be_justified`
and from `will_current_target_be_justified` (the latter needs `0 < E.total_active`).
*Landed* as `Execution.noConflict_arithmeticBranch_oneThird_of_rawGate`; the
old `…_of_prefixEvidence` is now a wrapper with its **signature unchanged**, and
`…_of_currentTargetGate` is the crossing-arm corollary.

**N5 — drop `support` from the call-site inductive (signature change).**
`StrictSelectedHistoricalSIRCallSite` (`SelectedPreQueryHistoricalSIR.lean:62-90`)
and `Weak.StrictSelectedHistoricalSIRCallSite` (`WeakPreQuerySIR.lean:290-323`):
delete the `support` fields; `strictSelectedHistoricalSIRCallSite` (`:98-137`) and
its weak twin then drop `hprovisos` (the gates are already derived, §1).

*Landed.* Both inductives also lose their `E` parameter — the two `support`
fields were their only mention of an execution, so the classification is now
purely executable. The proviso'd pinning interface
`NoConflictCertificatePinningProducerAt` and both of its dischargers are
deleted, together with the two `completedPrefix_noConflict_certifiedJustified_*`
proofs they wrapped and the pre-accepted legacy island
(`currentEpochCertificatePinned_of_previousNoConflict`,
`endpointJustified_root_eq_currentTarget_of_certificates`,
`epochStart_or_endpointCurrentTargetPinned_of_callSite`, and the two
`…_of_historicalCertificateProducers` wrappers), which had no callers outside
their own module and could not survive the interface change.

**N6 — three-way endpoint origin (signature change).**
```lean
def EndpointOriginOrPinnedAt (anchor) (q) (w m) (T : Checkpoint Root) : Prop :=
  (E.store cfg ext w m).justified_checkpoint = anchor ∨
  (∃ i ∈ E.honest, ∃ s k a, E.slot_at cfg 0 ≤ s ∧ E.slot_at cfg q ≤ s ∧
     s < E.slot_at cfg m ∧ E.SlotWithinHorizon cfg s ∧ E.vote i s = some (k,a) ∧
     a.data.target = (E.store cfg ext w m).justified_checkpoint) ∨
  ((E.store cfg ext w m).justified_checkpoint.epoch = T.epoch →
     (E.store cfg ext w m).justified_checkpoint.root = T.root)
```
built by `by_cases` on case α from N1/N2/N3, and consumed by re-cased variants of
`selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal`
(`SelectedJustifiedCompatibility.lean:238`) and
`observerCall_strictSelected_endpointJustifiedEpoch_le_result`
(`WeakSelectedJustifiedOrientation.lean:581`): arm 2 → the existing post-query
lemmas; arm 3 → the existing bracket route with the pin in place of
`epochStart_or_endpointCurrentTargetPinned_of_observerCallSite`'s output.

*Landed* as `Execution.EndpointOriginOrPinnedAt` with arm 2 stated as the
existing `Execution.CausalHonestTargetAt` (N2 produces exactly that shape, so
the raw vote conjuncts are not repeated), and with the producer interface
`Execution.EndpointOriginOrPinnedProducerAt` taking *either* executable gate
boolean — the crossing arm's `will_current_target_be_justified` and the
no-conflict arm's `will_no_conflicting_checkpoint_be_justified` both reduce to
the raw helper inequality (§5.5), so one interface serves both live arms and
the accepted live-gate certificate producer leaves the Trunk-B path entirely.

Three shared consumers were factored out rather than duplicating the case
split four times: `preQueryVoteSelectedSIRBracketAt_of_startOrPin` (arm 3 and
the epoch-start short circuit), `…_of_trustedAnchorEndpoint` (arm 1) and
`selected_result_and_child_ancestor_of_causalHonestTarget` (arm 2). The
epoch-start short circuit stays outside the disjunction, so the call-site
dispatcher's conclusion is `is_start_slot ∨ EndpointOriginOrPinnedAt`.

**N7 — delete the field.** `Weak.SelectedHelperProvisosAt.selected_previous_result_no_conflict`
and the Trunk-B half of `current_target` become unused;
`observer_helper_provisos` (`WeakSelectedStrictEdgeFilterSupply.lean:236-245`) can
go once Trunk A is handled.

*Orphaned by N5/N6, for the N7 sweep* (all still compile; none is reachable
from a public witness):

| Declaration | Module | Why it is now dead |
|---|---|---|
| `selected_previous_result_no_conflict` field | `SelectedTraceFilterPipeline.lean`, `WeakSelectedStrictEdgeFilterSupply.lean` | supplied, never read |
| `selectedPreviousResult_noConflict_gate_and_support` | `SelectedA32Support.lean` | last consumer was the call-site classifier |
| `certifiedCurrentTarget_of_crossing` | `SelectedPreQueryHistoricalSIR.lean` | already dead before this wave |
| `CurrentTargetCertificateProducerAt` + `acceptedCurrentTargetCertificateProducerAt_of_gateProducer` | `SelectedPreQueryHistoricalSIR.lean`, `CurrentTargetCertificateRealization.lean` | crossing arm no longer takes the certificate route |
| `noConflict_certifiedJustified_root_eq_currentTarget` | `NoConflictCertificatePinning.lean` | already dead before this wave |
| `noConflict_arithmeticBranch_oneThird_of_prefixEvidence`, `…_of_currentTargetGate` | `WeakHistoricalA32CallSupplier.lean` | N4 wrappers; the producers now call `…_of_rawGate` / `rawGate_of_executableGate` directly |

`currentTargetAcceptedEdge_gate_and_support` (`SelectedA32Support.lean:38`) and
its weak twin (`WeakHistoricalA32Step.lean:280`) stay: they are Trunk A's
crossing-lineage hubs, and `SelectedHelperProvisosAt.current_target` is still
read through them.

**Blast radius:** `SelectedPreQueryHistoricalSIR.lean`, `WeakPreQuerySIR.lean`,
`SelectedJustifiedCompatibility.lean`, `AcceptedSelectedJustifiedOrientation.lean`,
`AcceptedActualSelectedJustifiedOrientation.lean`,
`WeakSelectedJustifiedOrientation.lean`, `NoConflictCertificatePinning.lean`,
`WeakHistoricalA32CallSupplier.lean`, `AcceptedSelectedStrictEdgeFilterSupply.lean`,
`SelectedA32Support.lean`, `SelectedTraceFilterPipeline.lean`,
`WeakSelectedStrictEdgeFilterSupply.lean`, plus one new file. ~12 files — an order
of magnitude below map §6 wave 5's 29.

---

## 8. Overall verdict

* **Trunk B's residue closes.** The two-case argument is correct, and every step
  either already exists in the repo or is a short additive lemma. `hbase`, `hIH`
  and `hselectedKnown` are all in scope at both consumption sites.
* **No new assumption is needed — not even the causality field.** The endpoint's
  own `IncludedCertifiedJustified` evidence already bounds every quorum
  attestation's slot below the endpoint slot and pins its epoch. This supersedes
  `justification-causality-contract.md` §1 for this purpose and removes Wave 4's
  decision point.
* **`epoch-indexed-restructure.md` §7's obstruction is not binding.** It assumed
  the replacement argument must bound conflicting weight in the epoch-`e` prefix.
  The two-case argument instead excludes the *future* span from the conflicting
  quorum by committee assignment plus causality, and keeps the existing `>1/3`
  bound whole. §7 should be amended.
* **`observer_helper_provisos` cannot be deleted by this argument alone.** It also
  carries Trunk A's `current_target`, consumed positively at
  `WeakHistoricalA32Step.lean:280` → `AcceptedCurrentTargetA32GateRealizationProducerAt`.
  That half is `epoch-indexed-restructure.md` R0–R4 (judged clean there). With
  **both** landed, the field is deletable with **no replacement assumption**.
* **Recommended order:** N4 → N1 → N2 → N3 (all additive, build stays green) →
  N5/N6 (signature moves, Trunk B only) → restructure R0–R4 (Trunk A) → N7.
