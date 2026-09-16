# Proviso discharge map — `HonestVotesSupportTarget` on the WEAK path

Analysis only; nothing in `FastConfirmation/` was modified. All line numbers are
from branch `centaur/discharge-helper-provisos-202609161` at commit `9afcddc`.
Paths are relative to the repo root (`/home/agent/workspace/vfc`).

**Headline verdict.** Two of the three proviso fields are *live*; one
(`no_conflict`) is **dead** and can be deleted today. The two live fields are
consumed in exactly **six** projection sites, all funnelling through one hub
(`StrictSelectedHistoricalSIRCallSite` / its weak twin) plus the A3.2 crossing
lineage. The proposed discharge (a)/(b) from the trajectory invariant
**does not go through as stated**: at every live site the proviso is demanded
precisely in the configuration where the `SafeFrom` root is a *previous-epoch*
block, so the current-epoch boundary block that determines `get_current_target`
sits strictly **above** the safe candidate, and the block whose ancestry would
determine it is the selector's own result — whose safety is the conclusion of
the very call. Details and the two narrow escapes are in §5.

---

## 1. Consumption graph of `Weak.ObserverHistoricalA32CallAssumptions`

Definition: `FastConfirmation/Spec/Proof/WeakSelectedStrictEdgeFilterSupply.lean:236-245`

```lean
structure ObserverHistoricalA32CallAssumptions (E) (obs) : Prop where
  base : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext
  observer_helper_provisos : ∀ n, E.IsFCRCallAt cfg ext obs n →
    E.WithinHorizon cfg (n+1) →
      getLatestSelectorGuard cfg (E.weakFcrStep …) (E.weakGetLatestConfirmedTraceAt …).afterObserved →
        Weak.SelectedHelperProvisosAt cfg ext E obs (n+1) (E.weakFcrStep …) (… .afterObserved)
```

`base` is `Execution.AcceptedHistoricalA32CompletedPrefixCallAssumptions`
(`FastConfirmation/Spec/Proof/AcceptedHistoricalA32CallSupplier.lean:332-347`,
8 fields: `synchrony`, `static_validators`, `byzantine_bound`, `phase0_source`,
`phase0_boundary_source`, `balance_floor`, `delivery_lookahead`,
`helper_provisos`).

### 1.1 Every binder of the record (`hC : Weak.ObserverHistoricalA32CallAssumptions …`)

| # | File:line | Declaration | Role |
|---|---|---|---|
| 1 | `WeakSelectedJustifiedOrientation.lean:381` | `Weak.observerCall_orientation_inputs` | **eats `observer_helper_provisos` at `n`** (`:432`) and `base` (`:434`, `:437`) |
| 2 | `WeakSelectedJustifiedOrientation.lean:459` | `Weak.observerCall_strictSelected_result_and_child_ancestor_of_endpointJustified` | obtains provisos via #1 at `:524`; `base.synchrony/static_validators/byzantine_bound` at `:517-520` |
| 3 | `WeakSelectedJustifiedOrientation.lean:585` | `Weak.observerCall_strictSelected_endpointJustifiedEpoch_le_result` | as #2; `base.*` at `:639-642`, provisos at `:652` |
| 4 | `WeakHistoricalA32Induction.lean:139` | `Weak.observerHistoricalA32CallInterfaceAt_of_callAssumptions` | **eats `observer_helper_provisos n hcall hHn1` (`:148`)**; `base` → `Execution.observerCall_acceptedTargetGateProducerAt` (`:150`) |
| 5 | `WeakHistoricalA32Induction.lean:395` | `Weak.observerHistoricalA32CurrentLineage_invariant` | eta-expands #4 over **all** call seconds (`:403-407`); `base.phase0_source`, `base.phase0_boundary_source` at `:404` |
| 6 | `WeakHistoricalA32Induction.lean:418` | `Weak.observerHistoricalA32CurrentLineage` | via #5 (`:430-431`) |
| 7 | `WeakHistoricalA32Induction.lean:453` | `Weak.observerCall_currentLineage` | via #5/#6; `base.phase0_*` at `:474`; interface at `n` `:471-475` |
| 8 | `WeakHistoricalA32Induction.lean:500` | `Weak.observerCall_previousCarried_epochStartLineage` | via #5/#6 |
| 9 | `WeakHistoricalA32Induction.lean:726` | `Weak.observerCall_currentTargetHistoricalA32Payload` | via #5; `base.phase0_source` at `:774` |
| 10 | `WeakHistoricalA32Induction.lean:839` | (payload wrapper) | via #9 |
| 11 | `WeakHistoricalA32PayloadProducer.lean:54` | `Weak.observerCall_historicalA32PayloadProducerAt` | via #9/#10 |
| 12 | `WeakObserverStrictCallFilterInputs.lean:51` | `Weak.observerStrictCallFilterInputsAt_of_observerCall` | all four residual fields: `:73-74` (#11), `:79-80` (#7), `:82-83` (#8), `:87` (#2), `:92` (#3) |
| 13 | `WeakObserverStrictCallFilterInputs.lean:124` | `…observerCall_selectedStrictEdgeFilterSupplyAt_closed` | via #12 (`:147-148`) |
| 14 | `WeakOneShotSafetyClosed.lean:125` | **`Execution.weak_safeFrom_observerCall_closed`** (headline, one call) | via #13, only in the `strictSelected` branch (`:161-164`) |
| 15 | `WeakOneShotSafetyClosed.lean:187` | `Execution.weak_confirmed_head_closed` | via #14 |
| 16 | `WeakOneShotSafetyClosed.lean:236` | `Execution.weak_safeFrom_observerCall_closed_from_finalized` | via #14 |
| 17 | `WeakOneShotSafetyClosed.lean:283` | `Execution.weak_confirmed_head_closed_from_finalized` | via #16 |
| 18 | `WeakTrajectorySafety.lean:333` | `Execution.weakConfirmedSafeFromFollowingSlot_succ_of_call` | passes `hC` whole to #14 (`:348`) |
| 19 | `WeakTrajectorySafety.lean:394` | **`Execution.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold`** | passes whole (`:415`) |
| 20 | `WeakTrajectorySafety.lean:443` | `Execution.weakConfirmed_head_of_weakFullRuleFold_nextSlot` | passes whole (`:456`) |
| 21 | `WeakObservedResetSeedSafety.lean:158` | **`Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`** | passes whole to #19 |
| 22 | `WeakObservedResetSeedSafety.lean:191` | **`Execution.weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot`** | passes whole to #20 |

Correction to the brief: `Weak.observedResetSeedSafety_of_acceptedDynamics`
does **not** take `hC`; it is proved from `hW.base`, `B`, `hT`, `hji`,
`hanchor`, `hboundary`, `hW.committees_agree`
(`WeakObservedResetSeedSafety.lean:165-167`, `:205-207`). The two `hC` binders
in that file belong to the two unconditional fold corollaries (#21, #22).

### 1.2 Which fields are actually used, and at which index

* **`observer_helper_provisos` (observer-indexed)** is projected at exactly
  **two** places:
  * `WeakSelectedJustifiedOrientation.lean:432` — `hC.observer_helper_provisos n hcall hHn1 hselector.guard_true`, at the **current** call second `n`, conclusion indexed at `n+1`;
  * `WeakHistoricalA32Induction.lean:148` — same shape, but that interface is
    eta-closed over **all** call seconds at `WeakHistoricalA32Induction.lean:403-407`
    (`fun _k hk hkH => observerHistoricalA32CallInterfaceAt_of_callAssumptions … hk hkH`)
    and instantiated at every `k` with `E.IsFCRCallAt cfg ext obs k` reached by
    the write-back recursion `observerHistoricalA32CurrentLineageAt_all`
    (`:280`, `hcalls n hadv hHn1` at `:311`). So it is demanded at **`n` and
    every earlier call second `k < n`**, never at a second `> n`.

* **`base.helper_provisos` (honest-validator-indexed)** is **never**
  instantiated on the weak path. Verified by grep: the only eliminations are
  `AcceptedHistoricalA32CallSupplier.lean:441`,
  `AcceptedSelectedStrictEdgeFilterSupply.lean:215`,
  `AcceptedActualSelectedJustifiedOrientation.lean:705`, and the non-vacuity
  witness `AcceptedActualFCRJointNonVacuityFinal.lean:687` — all strong-path.
  The weak producers in `WeakHistoricalA32CallSupplier.lean:282` / `:764` read
  only `static_validators`, `byzantine_bound`, `delivery_lookahead`,
  `phase0_*`, `balance_floor` (documented at
  `WeakHistoricalA32CallSupplier.lean:32-36`).

* **`base`'s other fields on the weak path**: `synchrony`,
  `static_validators`, `byzantine_bound` (`WeakSelectedJustifiedOrientation.lean:517-520`,
  `:639-642`), `phase0_source`, `phase0_boundary_source`
  (`WeakHistoricalA32Induction.lean:404`, `:474`, `:774`), plus `balance_floor`
  and `delivery_lookahead` inside the two call suppliers.

**Consequence.** If `helper_provisos` were dropped from
`Execution.AcceptedHistoricalA32CompletedPrefixCallAssumptions`, the weak path
would not notice; the weak surface's *only* proviso carrier is
`observer_helper_provisos`. Conversely, dropping `observer_helper_provisos`
alone removes the proviso from every weak headline theorem (#14–#22).

---

## 2. Per-field consumption, exhaustively

Record (weak): `WeakSelectedStrictEdgeFilterSupply.lean:203-233`;
strong twin: `SelectedTraceFilterPipeline.lean:29-56`.

### 2.1 `no_conflict` — **DEAD**

* Declared: `SelectedTraceFilterPipeline.lean:37-42` (strong),
  `WeakSelectedStrictEdgeFilterSupply.lean:214-219` (weak).
* **Zero projections anywhere in the repo** (`rg '\.no_conflict\b'` → empty).
* Only construction: `AcceptedActualFCRJointNonVacuityFinal.lean:285`
  (vacuous, via `no_previousAcceptedEdge_away_from_epoch_start`).
* The mid-epoch `PreviousAcceptedEdge` case it was meant to serve is reached
  through the *result-level* field instead
  (`StrictSelectedHistoricalSIRCallSite.previousNoConflict`). The only other
  `PreviousAcceptedEdge` no-conflict consumer,
  `SelectedFilterBridge.lean:679 filterTipCertificate_of_previous_no_conflict_result`,
  is unreferenced legacy API (as is its sibling at `:640`,
  `filterTipCertificate_of_current_accepted_edge`). **Both are now deleted;**
  the `SelectedFilterFFGPipeline` fields `current_target_tip_source` (`:515`)
  and `no_conflict_tip_source` (`:534`), plus
  `selected_strict_current_balance_checkpoint_key` (`:299`), were orphaned by
  that deletion and are **also deleted** (R0 follow-up sweep). Note
  `SelectedFilterFFGPipeline` itself now has zero consumers repo-wide; its two
  surviving fields (`accountability_assumptions`, `endpoint`) are carried by no
  theorem, so the whole record is a further deletion candidate.
* **Immediately deletable** from both records; the only edit needed is the
  witness at `AcceptedActualFCRJointNonVacuityFinal.lean:285-296`.

### 2.2 `current_target` — 4 projections (3 live; S2 deleted)

| Site | File:line | Enclosing declaration |
|---|---|---|
| S1 | `SelectedA32Support.lean:48` | `Execution.currentTargetAcceptedEdge_gate_and_support` (`:38`) |
| S2 | ~~`SelectedA32Support.lean:170`~~ | ~~`Execution.currentTargetAcceptedEdge_honest_vote_before_next_epoch` (`:147`)~~ — **dead lemma, no callers; deleted.** Its callee `Execution.honest_target_vote_before_next_epoch` (`:111`) was orphaned by the deletion and is **also deleted** (R0 follow-up sweep) |
| W1 | `WeakHistoricalA32Step.lean:293` | `Weak.currentTargetAcceptedEdge_gate_and_support` (`:280`) |
| W2 | `WeakPreQuerySIR.lean:368` | `Weak.strictSelectedHistoricalSIRCallSite` (`:339`) |

Both live hubs produce
`will_current_target_be_justified … = true ∧ HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q`.
From there two trunks:

**Trunk A — A3.2 crossing lineage (positive certification).**
`SelectedA32Support.lean:38` / `WeakHistoricalA32Step.lean:280` →
`AcceptedHistoricalA32Step.lean:354` (`selectedCurrentCrossingLineage`) /
`:443` (fixed-source) and weak twins `WeakHistoricalA32Step.lean:668`, `:761`
→ `AcceptedCurrentTargetA32GateRealizationProducerAt`
(`CurrentTargetA32Support.lean:701`, core at `:627`) applied to gate+support
→ `CurrentTargetA32GateRealizationCore` (`CurrentTargetA32Support.lean:607`),
whose `certified` field is
`Nonempty (CertifiedJustified cfg E anchor (get_current_target cfg store))`
plus a `ConcreteA32QuorumBefore` with a fixed source
→ `AcceptedHistoricalA32LineageAt` → `current_lineage` /
`previous_epochStart_carried_lineage` of
`Weak.ObserverStrictCallFilterInputsAt`.
The producer is discharged, and `HonestVotesSupportTarget` genuinely
**unfolded**, at
`AcceptedCurrentTargetGateBridge.lean:769` (`hsupport.2 i hi s …` inside
`currentTargetFutureHonestSeat_vote_of_currentSlot`, `:717`) and
`CurrentTargetA32Support.lean:504` (inside `currentTargetFutureHonestSeat_vote`,
`:457`). **What it buys: the honest *future* committee seats of the current
epoch are counted as target-`T` voters, giving the two-thirds weight bound.**

**Trunk B — pre-query SIR pinning.**
→ `StrictSelectedHistoricalSIRCallSite.currentCrossing`
(`SelectedPreQueryHistoricalSIR.lean:62-71`, built at `:122`; weak twin
`WeakPreQuerySIR.lean:290`, built at `:368`)
→ `epochStart_or_endpointCurrentTargetPinned_of_callSite`
(`SelectedPreQueryHistoricalSIR.lean:825`, `currentCrossing` arm `:843-848`;
accepted twin `AcceptedSelectedJustifiedOrientation.lean:182`; weak twin
`WeakSelectedJustifiedOrientation.lean:112`), conclusion:

```
is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
  (endpointStore.justified_checkpoint.epoch = (get_current_target cfg query.store).epoch →
   endpointStore.justified_checkpoint.root = (get_current_target cfg query.store).root)
```

→ `selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning`
(`SelectedPreQueryHistoricalSIR.lean:1057`; equality eaten at `:1180-1197`
and `:1245-1262` as `hJT : J = T`; weak twin `WeakPreQuerySIR.lean:545`)
→ `SelectedSIRThreeRegionBracket` (`SelectedPreQuerySIR.lean:41-61`)
→ `PreQueryVoteSelectedSIRBracketAt` → `PreQuerySelectedJustifiedCompatibilityAt`
(`SelectedJustifiedCompatibility.lean:88-99`)
→ `…strictSelected_result_and_child_ancestor_of_endpointJustified`
(`AcceptedActualSelectedJustifiedOrientation.lean:602`; weak
`WeakSelectedJustifiedOrientation.lean:455`, `:581`)
→ `Weak.ObserverStrictCallFilterInputsAt.result_descends_endpoint_justified` /
`…endpoint_justified_epoch_le_result`.

### 2.3 `selected_previous_result_no_conflict` — 2 projections

| Site | File:line | Enclosing declaration |
|---|---|---|
| S3 | `SelectedA32Support.lean:71` | `Execution.selectedPreviousResult_noConflict_gate_and_support` (`:54`) |
| W3 | `WeakPreQuerySIR.lean:385` | `Weak.strictSelectedHistoricalSIRCallSite` (`:339`) |

Both go into `StrictSelectedHistoricalSIRCallSite.previousNoConflict`
(`SelectedPreQueryHistoricalSIR.lean:82-90`; weak `WeakPreQuerySIR.lean:315-323`),
then `epochStart_or_endpointCurrentTargetPinned_of_callSite`'s
`previousNoConflict` arm (`SelectedPreQueryHistoricalSIR.lean:857-861`:
`hnoConflict hgate hsupport store.justified_checkpoint hJ hepoch`), and then the
identical Trunk B tail as above.

The producer `NoConflictCertificatePinningProducerAt`
(`SelectedPreQueryHistoricalSIR.lean:753-762`) is discharged by
`AcceptedActualSelectedJustifiedOrientation.lean:361` and, weakly,
`WeakHistoricalA32CallSupplier.lean:764`, both delegating to
**`noConflict_certifiedJustified_root_eq_currentTarget`**
(`NoConflictCertificatePinning.lean:698`, `hsupport` premise `:719-720`,
conclusion `c.root = (get_current_target …).root` at `:724-725`). Its two
branches:
* equality branch `:766` → `Execution.certified_justified_unique`
  (`FFGAccountability.lean:179`);
* arithmetic branch `:782` → `currentTargetFutureHonestSeat_vote`
  (`CurrentTargetA32Support.lean:457`, unfolds `hsupport.2` at `:504`) +
  `noConflict_arithmeticBranch_oneThird` (`:91`) → **strictly more than 1/3 of
  the epoch's committee weight is honest and targets `T`**, so no other
  checkpoint of that epoch can gather 2/3.

### 2.4 Final downstream conclusion of both chains

`Execution.SelectedStrictEdgeFilterSupplyAt`
(`SelectedCoveredMarginConstruction.lean:44`) — *the selected edge's child
survives the endpoint's filtered block tree* — produced by
`StrictSelectorAdvanceAt.actualCall_selectedStrictEdgeFilterSupplyAt`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:2129`) / weak
`…observerCall_selectedStrictEdgeFilterSupplyAt_closed`
(`WeakObserverStrictCallFilterInputs.lean:104`);
then `selectedCoveredMarginSupplyAt_of_filterSupply_minimal`
(`SelectedCoveredMarginConstruction.lean:80`) → `SafeFrom result`
(`WeakOneShotSafetyClosed.lean:107`) → the fold (`WeakTrajectorySafety.lean:376`).

### 2.5 Two dead interface fields worth recording

`JustificationInterface.gate_sound` (`FastConfirmation/Spec/TheoremStatements.lean:86-101`)
and `target_justified_sound` (`:162-169`) — the two fields gated on
`HonestVotesSupportTarget` — are **never applied anywhere** (only prose mention
at `ResidualMechanical.lean:33`). The mechanized replacement of `gate_sound` is
the certificate-level pinning of §2.3, which delivers *exact root equality*,
not `gate_sound`'s disjunctive comparability. So the plan's phrase
"`gate_sound`-style conclusion" does **not** describe what the safety proof
actually consumes.

---

## 3. Machinery already present for a discharge

**(i) Chain-intrinsic `get_current_target`.**
`get_current_target` = `get_checkpoint_for_block store (get_head store).root (get_current_store_epoch store)`
(`FastConfirmation/Spec/Model/FCRStore.lean:86`; `get_checkpoint_for_block` `:76`;
`get_checkpoint_block` `FastConfirmation/Spec/Model/ForkChoice.lean:121`).
* `Execution.current_target_eq_checkpoint_of_current_epoch_ancestor` —
  `SelectedA32Support.lean:80`. **The workhorse**: head ⪰ `c`, `c` in the current
  epoch, boundary walk known ⟹ `get_current_target store = get_checkpoint_for_block store c (get_block_epoch store c)`.
* `currentTarget_eq_selectedCheckpoint_of_currentEpochAncestor` — `SelectedA32Semantics.lean:58`.
* `currentTarget_descends_previousEpochBlock` — `SelectedPreQueryHistoricalSIR.lean:930`
  (`b` previous-epoch and head-descended ⟹ `T.root ⪰ b`).
* `currentEpochBoundaryWalk_of_knownEarlierEpochBlock` — `SelectedPreQueryHistoricalSIR.lean:984`.

**(ii) Boundary block determined by ancestry.**
* `get_checkpoint_block_of_ancestor` — `FilterViability.lean:25` (exactly
  "the epoch-`e` boundary block of any chain through `b` equals `b`'s, when
  `start_slot e ≤ b.slot`").
* `get_ancestor_comp` — `AncestryRoots.lean:60`; `get_ancestor_stop/step/spec` —
  `Ancestry.lean:83/93/110`; `get_ancestor_aux_fuel_eq` — `Ancestry.lean:46`.
* Cross-store: `get_checkpoint_block_eq_of_paired_walks` —
  `AcceptedPathLocalFinalizedTransport.lean:79`.
* `start_slot_at_block_epoch_le` — `HonestWeight.lean:380`;
  `is_ancestor_comparable` — `CertExtract.lean:77`.

**(iii) `SafeFrom` at vote-cast seconds.**
* `Execution.SafeFrom` — `L4Fold.lean:60`: literally "ancestor of every honest
  head at every second `≥ n`". No converter needed.
* `HonestBehavior.votes_head` — `FastConfirmation/Spec/Model/Assumptions.lean:88`:
  the cast second `k` satisfies `E.slot_at cfg k = s`. Combined with
  `votes_assigned` (`:95`) this gives, for *any* honest vote,
  `slot_at (castSecond) = voteSlot`.
* `honest_attestation_data` — `FastConfirmation/Spec/Model/Validator.lean:35-48`:
  `target = Checkpoint.mk (get_current_epoch head_state) (get_checkpoint_block store head.root …)`;
  projections `Delivery.honest_attestation_data_target_root` (`Delivery.lean:266`)
  and `…_target_epoch` (`:277`).
* **Useful positive finding:** at a genuine FCR call,
  `E.slot_start cfg (E.slot_at cfg (n+1)) = n+1`
  (`Execution.slot_start_eq_succ_of_advance_minimal`, used at
  `WeakTrajectorySafety.lean:285-286`), i.e. `n+1` is the *first second of its
  slot*. With `votes_head`'s `slot_at k = s`, every honest vote relevant to
  `HonestVotesSupportTarget … (n+1)` has `k ≥ n+1`. So the
  `PreexistingRelevantHonestVotesSupportTarget` half
  (`CausalQueryEvidence.lean:39`) is **vacuous at call sites**, and the
  unresolved `PreexistingVoteActionCoverage` obligation
  (`CausalQueryEvidence.lean:84`, explicitly flagged as not implied by
  `GlobalRuntime`) is *not* an obstacle here. A three-line lemma
  `honest_vote_castSecond_ge_of_slotStart` closes this gap.
* `Execution.honest_target_vote_before_next_epoch` — was
  `SelectedA32Support.lean:111` (the per-seat unfolding; **deleted** as dead by
  the R0 sweep, but the shape a constructor would mirror is recoverable from
  git history).
* **No lemma anywhere constructs `HonestVotesSupportTarget`.** Every occurrence
  is a hypothesis or a record field. That is the hole.

**(iv) Accountability floor.**
* `Execution.certified_justified_unique` — `FFGAccountability.lean:179`.
* `links_intersect_honest` — `FFGAccountability.lean:152`;
  `certified_links_not_surround` — `:217`.
* `CheckpointCertificateAccountability` — `ExactCheckpointLinks.lean:300`,
  realizer `:313`.
* `head_ge_of_justified_ge_K` — `E5Filter.lean:449` (unprimed `EngineStore.lean:307`).
* `Execution.globalJustified_honestTarget` — `AcceptedCurrentSameEndpointSource.lean:71`:
  a non-anchor endpoint justified checkpoint *was* an honest attestation target,
  with `target_walk : WalkKnown store (start_slot justified.epoch) (get_head store).root`.
* `noConflict_certifiedJustified_root_eq_currentTarget` — `NoConflictCertificatePinning.lean:698`.

---

## 4. Does the fold's induction dominate the demand seconds?

**Fold structure.** `Execution.WeakConfirmedSafeFromFollowingSlot`
(`WeakTrajectorySafety.lean:180`) = `SafeFrom (E.weakConfirmed obs n) (E.followingSlotStart n)`.
Fold: `weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold`
(`WeakTrajectorySafety.lean:376`), plain `induction n` at `:403-419`, motive
`WithinHorizon n → invariant n`, IH used once at `:412`. Call step
`weakConfirmedSafeFromFollowingSlot_succ_of_call` (`:315`); idle step (`:216`).

**Where the call step stands.** At a call, `followingSlotStart n = n+1`
(`:296`), so `hprev` is exactly `SafeFrom (weakConfirmed n) (n+1)`, which is fed
as `hbase : SafeFrom input (slot_start (slot_at (n+1)))` into
`weak_safeFrom_observerCall_closed` (`:345-349`). Note that `hbase` is
**already a hypothesis at the very sites where the provisos are consumed**
(`WeakObserverStrictCallFilterInputs.lean:62-64`,
`WeakSelectedJustifiedOrientation.lean:459-…`,
`SelectedPreQueryHistoricalSIR.lean:1070-1071`). So no *new* co-induction is
needed for the Trunk-B (orientation) sites — the invariant is already in scope.

**Indexing of the demands.**
* Trunk B / `observerCall_orientation_inputs`: `hC.observer_helper_provisos`
  instantiated at the current call second only
  (`WeakSelectedJustifiedOrientation.lean:432`). *Well-founded.*
* Trunk A / historical A3.2 write-back: the interface is eta-closed over all
  call seconds (`WeakHistoricalA32Induction.lean:403-407`) and the recursion
  `observerHistoricalA32CurrentLineageAt_all` (`:280`, use at `:311`) replays
  **every** earlier call second `k < n`. Never a second `> n`, so no future
  demand — but `hbase` for those past calls is *not* passed down
  (`WeakObserverStrictCallFilterInputs.lean:78-83` supplies `current_lineage`
  and `previous_epochStart_carried_lineage` without `hbase`).
* Consequence: a co-induction is well-founded **in index**, but the fold's
  single-second IH is too weak. The fix is mechanical: strengthen the fold's
  motive to `∀ k ≤ n, WithinHorizon k → invariant k` (or prove a separate
  "proviso supply at all call seconds ≤ n" accumulator), so that the A3.2 replay
  at call `n` has an input-safety witness at every `k < n`. This is a
  restructuring of `WeakTrajectorySafety.lean:403-419` only.

**A note correcting a common misreading:** `HonestVotesSupportTarget … (n+1)`
*is* forward-looking, but so is `SafeFrom … (n+1)` (`∀ m ≥ n+1`). The forward
quantifier is therefore **not** the obstruction. The obstruction is spatial
(which root is safe), not temporal — see §5.

---

## 5. Obstructions

### 5.1 The decisive one: the proviso is demanded exactly where the safe root is a *previous-epoch* block

At a call, `hinputEpoch`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:199-207`,
`SelectedPreQueryHistoricalSIR.lean:1065-1069`) says the candidate input is
either a current-epoch block or exactly one epoch old.

* **`current_target` site.** A `CurrentTargetAcceptedEdge`
  (`SelectedFilterBridge.lean:199-202`; weak `WeakHistoricalA32Step.lean:88-92`)
  is a *tentative-trace* edge `(a,c)` with
  `get_block_epoch a < get_block_epoch c`. Every trace edge lies at or above the
  input, and no block exceeds the store's current epoch, so a crossing edge can
  exist **only when `epoch(input) + 1 = currentEpoch`** — i.e. precisely when the
  input is a previous-epoch block. (If the input were current-epoch, the
  `currentHistorical` branch applies and needs **no** proviso.)
  So `SafeFrom input` never determines the current-epoch boundary block: honest
  heads all contain `input`, but may fork anywhere above it and below the epoch
  boundary, so their `get_checkpoint_block(·, currentEpoch)` values may differ.
  The block that *would* determine the target is `c` (current-epoch), and
  `SafeFrom c` is the conclusion of this very call ⇒ **circular**.

* **`selected_previous_result_no_conflict` site.** Here `result` is a
  previous-epoch block and `epoch(input) = epoch(result) = currentEpoch - 1`.
  `T = get_current_target` is a *current*-epoch checkpoint, strictly above both.
  Same conclusion: `SafeFrom input` is one epoch too low.

In both cases the missing fact is `SafeFrom T.root (n+1)` with
`input ⪯ T.root ⪯ result` (crossing case: `input ⪯ T.root ⪯ c`); no invariant
in the development supplies it.

### 5.2 The consumers genuinely need exact agreement, not comparability

The plan hoped to replace the proviso by "all honest targets descend from the
candidate ⟹ any justified checkpoint is comparable with it". Three facts block
that literal substitution:

1. The comparability form (`JustificationInterface.gate_sound`,
   `TheoremStatements.lean:86-101`) is **dead code**. The live consumer is
   `epochStart_or_endpointCurrentTargetPinned_of_callSite`
   (`SelectedPreQueryHistoricalSIR.lean:825`) whose conclusion is an
   **equality** `J.epoch = T.epoch → J.root = T.root`, used at
   `:1195` and `:1260` in the strictly stronger form `hJT : J = T` to transport
   query-store ancestry facts (`result ⪰ T`, `T ⪰ input`) onto `J`.
2. Comparability of `J.root` with the *input* is already free (both are
   ancestors of the endpoint head: `head ⪰ J.root` by fork-choice,
   `head ⪰ input` by `hbase`; then `is_ancestor_comparable`, `CertExtract.lean:77`).
   The bracket needs `J.root ⪰ result` (region `above_selected`,
   `SelectedPreQuerySIR.lean:57-61`) or `result ⪰ J.root ⪰ input` (region
   `inside_selected_segment`, `:48-56`) — strictly stronger than comparability
   with the input.
3. `J`'s formation vote is a **pre-query** vote: the bracket quantifies over
   `s < E.slot_at cfg q` (`SelectedPreQueryHistoricalSIR.lean:1078`,
   `PreQueryVoteSelectedSIRBracketAt` at `SelectedPreQueryAnchor.lean:267`).
   No `SafeFrom` indexed at or after the query second constrains the honest head
   at those slots. This is exactly the region the FFG gate exists to cover, and
   is the second, independent reason the trajectory invariant cannot reach it.

Trunk A is worse still: its use is *positively constructive* — the proviso
supplies the honest **future** committee seats that make up the two-thirds
weight of `ConcreteA32QuorumBefore`
(`CurrentTargetA32Support.lean:528`, `currentTargetFutureHonestSeat_vote`
`:457`, unfold at `:504`; accepted route `AcceptedCurrentTargetGateBridge.lean:769`).
Nothing weaker than "these seats will vote `T`" produces that quorum, and the
quorum is what yields `CertifiedJustified (get_current_target …)` — the payload
of the whole A3.2 lineage. This is the "exact-target quorum used positively"
case the brief asked about, and it is real.

### 5.3 Two narrow escapes (both substantial)

* **(E1) Endpoint-slot-capped proviso.** The strict-edge supplier's own
  induction already provides
  `hIH : ∀ w' m', slot_start (slot_at (n+1)) ≤ m' → slot_at m' < slot_at m → head(w',m') ⪰ result`
  (`AcceptedSelectedStrictEdgeFilterSupply.lean:152-159`). Together with
  `votes_head` and `get_checkpoint_block_of_ancestor`, that *does* give
  "every honest vote at a slot in `[slot(q), slot(m))` targets `T`" whenever
  `result` is a current-epoch block — i.e. a `HonestVotesSupportTarget`
  **capped at the endpoint slot**, derived rather than assumed, for the
  `current_target` site. To exploit it one must re-prove
  `noConflict_certifiedJustified_root_eq_currentTarget` (`NoConflictCertificatePinning.lean:698`)
  and the quorum construction (`AcceptedCurrentTargetGateBridge.lean:1042`)
  under the capped hypothesis. Blocker inside the blocker:
  `JustificationInterface.justified_requires_targets`
  (`TheoremStatements.lean:144-158`) does **not** bound the target-vote slots by
  the endpoint second, so "justified at `(w,m)` ⟹ formed from votes at slots
  `< slot(m)`" is not currently available and would itself have to be added to
  the interface (i.e. traded for a different floor assumption).
* **(E2) Boundary-block safety invariant.** Strengthen the trajectory invariant
  from `SafeFrom (weakConfirmed n)` to
  `SafeFrom (get_checkpoint_block store (weakConfirmed n) currentEpoch)` — i.e.
  carry safety of the *current-epoch boundary block above* the confirmed root.
  That is exactly the fact the provisos encode, so it would have to be
  established by its own argument (presumably from the previous epoch's
  finalized/justified checkpoint plus the gate), and is very likely a
  reformulation of the assumption rather than a discharge.

### 5.4 Things that are *not* obstructions (good news)

* The same-slot-earlier-cast problem is vacuous at call sites (§3(iii)); no
  `PreexistingVoteActionCoverage` is needed.
* `hbase` (input safety) is already in scope at every Trunk-B proviso site.
* No demand is ever at a second the fold has not reached (§4).
* `base.helper_provisos` is never touched on the weak path, so the weak and
  strong provisos can be decoupled cleanly.

---

## 6. A concrete wave plan

The plan below is ordered so the build stays green after each wave. Waves 1–3
are unconditional wins independent of §5; waves 4–6 are the actual discharge and
should only start after the §5.3 decision.

### Wave 0 — measurement only (no edits)
Record the current premise surfaces of the five weak headline theorems
(`WeakOneShotSafetyClosed.lean:107/169/236/283`,
`WeakTrajectorySafety.lean:376/425`,
`WeakObservedResetSeedSafety.lean:140/174`).

### Wave 1 — delete the dead `no_conflict` field — **LANDED** (`0e9b8be`)
*Edits:* `SelectedTraceFilterPipeline.lean:37-42`,
`WeakSelectedStrictEdgeFilterSupply.lean:214-219`,
`AcceptedActualFCRJointNonVacuityFinal.lean:285-296` (drop the vacuous branch;
`no_previousAcceptedEdge_away_from_epoch_start` may become unused).
*Blast radius:* 3 files. Zero proof changes elsewhere (field has no projections).
*Green after:* yes.

### Wave 2 — the missing constructor lemmas (additive only) — **LANDED** (`5f274ed`)
New file `FastConfirmation/Spec/Proof/HonestTargetAgreement.lean` (imports
`SelectedA32Support`, `Delivery`, `L4Fold`):
1. `honest_vote_castSecond_slot` — `v ∈ E.honest → E.vote v s = some (k,a) → E.slot_at cfg k = s`
   (from `votes_assigned` + `votes_head`, `Assumptions.lean:88/95`).
2. `honest_vote_castSecond_ge_of_slotStart` — with
   `E.slot_start cfg (E.slot_at cfg q) = q` and `E.slot_at cfg q ≤ s`, `q ≤ k`.
3. `honestVoteTarget_eq_checkpoint_of_head_ancestor` — `SafeFrom b q` +
   `get_block_epoch (store v k) b = compute_epoch_at_slot s` +
   domain side-conditions ⟹ `a.data.target = get_checkpoint_for_block (store v k) b …`
   (via `Delivery.lean:266/277` + `FilterViability.lean:25`).
4. `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate` —
   the packaging: `SafeFrom b q`, `q` a slot start, `b` a current-epoch block of
   the query store, cross-store block agreement ⟹
   `HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q`
   (via `current_target_eq_checkpoint_of_current_epoch_ancestor`,
   `SelectedA32Support.lean:80`, and
   `get_checkpoint_block_eq_of_paired_walks`,
   `AcceptedPathLocalFinalizedTransport.lean:79`).
*Blast radius:* 1 new file (`HonestTargetAgreement.lean`, wired into
`FastConfirmation/Spec.lean` so the trust audit covers it), nothing changes
signature.  As landed, lemma 4
(`Execution.honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`) carries
the current-epoch placement of `b` as the explicit hypothesis `hbEpoch :
get_block_epoch query.store b = get_current_store_epoch query.store` — which is
exactly what §5.1 says the live sites cannot supply — plus the usual per-voter
walk/agreement transport premises.  See the module docstring for the full list.
*Green after:* yes. **This wave is worth doing regardless** — it is the first
constructor for `HonestVotesSupportTarget` in the repo and it makes the
remaining gap precise and checkable.

### Wave 3 — strengthen the fold's IH (enabling, no signature change) — **LANDED**
Rewrite `WeakTrajectorySafety.lean:403-419` so the induction motive is
`∀ k ≤ n, E.WithinHorizon cfg k → E.WeakConfirmedSafeFromFollowingSlot cfg ext obs k`,
exposing a new lemma
`weakConfirmedSafeFromFollowingSlot_of_weakFullRuleFold_all_le`. Keep the
existing statement as a corollary.
*Blast radius:* 1 file. *Green after:* yes.
As landed: the new lemma is stated `∀ n, ∀ k ≤ n, WithinHorizon k → invariant k`
and the headline fold is its `k := n` instance; no downstream signature moved.

### Wave 4 — decision point (§5.3)
Choose (E1) or (E2), or accept that `observer_helper_provisos` stays. If (E1):
add `justified_requires_targets_before_endpoint` to `JustificationInterface`
(`TheoremStatements.lean`) — note this *trades* one floor assumption for
another and must be argued explicitly in `docs/`.

### Wave 5 — capped proviso plumbing (only under (E1))
1. New predicate `HonestVotesSupportTargetUpTo cfg E T q endSlot` next to
   `HonestVotesSupportTarget` (`TheoremStatements.lean:68`).
2. Re-prove `currentTargetFutureHonestSeat_vote` (`CurrentTargetA32Support.lean:457`)
   and `currentTargetFutureHonestSeat_vote_of_currentSlot`
   (`AcceptedCurrentTargetGateBridge.lean:717`) against it.
3. Re-prove `noConflict_certifiedJustified_root_eq_currentTarget`
   (`NoConflictCertificatePinning.lean:698`) and the quorum builder
   (`AcceptedCurrentTargetGateBridge.lean:1042`).
*Blast radius (files whose proofs must change):*
`TheoremStatements.lean`, `CurrentTargetA32Support.lean`,
`AcceptedCurrentTargetGateBridge.lean`, `CurrentTargetCertificateRealization.lean`,
`NoConflictCertificatePinning.lean`, `SelectedA32Support.lean`,
`SelectedA32Semantics.lean`, `SelectedPreQueryHistoricalSIR.lean`,
`SelectedTraceFilterPipeline.lean`, `AcceptedHistoricalA32Step.lean`,
`AcceptedHistoricalA32Crossing.lean`, `AcceptedHistoricalA32GlobalTrajectory.lean`,
`AcceptedSelectedJustifiedOrientation.lean`,
`AcceptedActualSelectedJustifiedOrientation.lean`,
`AcceptedSelectedStrictEdgeFilterSupply.lean`,
`AcceptedHistoricalA32CallSupplier.lean`, `AcceptedHistoricalA32Induction.lean`,
`AcceptedHistoricalA32OneStep.lean`, `SelectedCoveredMarginConstruction.lean`,
`SelectedTraceFFGRealizationPipeline.lean`,
`AcceptedActualFCRJointNonVacuityFinal.lean` (21 strong-path files) plus the
weak twins `WeakPreQuerySIR.lean`, `WeakHistoricalA32Step.lean`,
`WeakHistoricalA32OneStep.lean`, `WeakHistoricalA32Induction.lean`,
`WeakSelectedJustifiedOrientation.lean`, `WeakHistoricalA32CallSupplier.lean`,
`WeakObserverStrictCallFilterInputs.lean`,
`WeakSelectedStrictEdgeFilterSupply.lean` (8 weak files).

### Wave 6 — drop the field and the binder
1. Replace `Weak.SelectedHelperProvisosAt`'s two remaining fields by derived
   lemmas at `WeakPreQuerySIR.lean:339` and `WeakHistoricalA32Step.lean:280`,
   fed from wave 2's constructor plus wave 5's capped supply.
2. Delete `observer_helper_provisos` from
   `WeakSelectedStrictEdgeFilterSupply.lean:236-245`; `Weak.ObserverHistoricalA32CallAssumptions`
   collapses to `base`, so the 22 binders of §1.1 can be replaced by
   `E.AcceptedHistoricalA32CompletedPrefixCallAssumptions` directly (or the
   record kept as a one-field alias for a wave, to keep diffs local).
3. Only then consider dropping `helper_provisos` from the strong record.
*Green after each sub-step:* keep the record with a `True`-valued field for one
wave if necessary, so downstream call sites never break in the same commit as
the proof rewrites.

### Safe ordering summary
Wave 1 → Wave 2 → Wave 3 are independent and each leaves the build green with
no signature change beyond the dead-field deletion. Wave 4 is a design decision
that should be written up before any code moves. Waves 5–6 are the only ones
with a large blast radius (≈29 files) and should be split by trunk: Trunk B
(pinning / SIR) first, Trunk A (quorum / A3.2 lineage) second, since Trunk A is
where the positive-quorum use lives and is the more likely to fail.
