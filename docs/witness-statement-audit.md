# Witness statement & assumption audit

**Scope.** This document audits the **statements** and the **assumptions** of the
declarations in `scripts/Audit.lean`'s `publicWitnesses` array, as of
`centaur/weak-synchrony-202609150824` @ `0be68f6` (working tree clean at audit time),
when the array held 23 names.

> **Post-audit status (2026-09-16).** Flags **F1, F2, F3 and F7 are RESOLVED**, plus the
> bonus deletion of the two dead `JustificationInterface` fields. Every fix was a
> deletion, a premise weakening or a doc correction; no conclusion changed by a byte.
> * `fbb3ec1` — **F3**: the `observer : obs ∉ E.honest` field is deleted from both weak
>   observer records; all ten weak witnesses now cover an *arbitrary* observer.
> * `28a9bd6` — **F2**: `hT`, `hphase0`, `hboundaryPhase` are gone from the four
>   trajectory headlines (derived internally), and the 7-field call contract `hCbase` is
>   replaced there by the 4-field
>   `Execution.AcceptedHistoricalA32CompletedPrefixCallSupplement`, its other three
>   fields being read off `hW.base`. `Weak.observedResetSeedSafety_of_acceptedDynamics`
>   also lost its `hT`.
> * `47c3984` — **F1**: W20/W21 (the *conditional* fold pair) are **deregistered**; the
>   witness count is now **21** and `scripts/Audit.lean` asserts 21. They remain internal
>   theorems used by W22/W23's proof chain. The W-numbering below is left as audited;
>   the registered set is W1–W19, W22, W23.
> * `8b05b67` — **bonus**: `JustificationInterface.gate_sound` and
>   `.target_justified_sound` deleted (13 fields left), weakening `hji` on W20–W23.
> * `28a9bd6` + `5ec6441` — **F7**: both docstring discrepancies fixed.
> * **single-synchrony refactor** — the model now carries **one** synchrony assumption.
>   `HorizonVoteDeliveryLookahead` is deleted; its clause is the delivery field of
>   `Synchrony`/`PaperSafetySynchrony`, now phrased without a horizon gate on the
>   *receipt* second (the vote's slot and cast second stay horizon-scoped). The merged
>   field is provably the same proposition as the old pair
>   (`Spec.attestation_delivery_pair_iff`), and both old forms are recovered as derived
>   lemmas (`toHorizonScopedDelivery`, `toDeliveryLookahead`) — **the boundary delivery
>   case is now a derived lemma, not an assumption.** Records shrink: O 7 → 6 fields,
>   O′ 4 → 3. On the witnesses that carried **both** old forms (W1, W2, W20–W23, and the
>   non-vacuity pair W3/W4 through `completed_calls`) the premise content is *equal* and
>   the surface shrank by one field, because the removed content sits in the `synchrony`
>   field they already carry. On the witnesses that carried only the horizon-gated half
>   and no `delivery_lookahead` (**W14–W19**, via `M.synchrony`), the `synchrony` field
>   is now the merged clause, i.e. their delivery premise gained the boundary case: that
>   is the unavoidable arithmetic of having *one* synchrony assumption instead of two —
>   the model's assumption content is unchanged (the merged field **is** the old pair),
>   but those six witnesses now assume the pair where they previously assumed one half.
>   Conclusions are unchanged: W5/W6's environment `def` loses the
>   `HorizonVoteDeliveryLookahead` conjunct, which the retained `Synchrony` conjunct now
>   asserts — the same proposition, one conjunct shorter.
>
> Rows and sections below are annotated in place; nothing else was re-audited.
For each witness: what it claims in protocol language, and every hypothesis it carries,
unfolded through record premises, each classified.

**Explicitly out of scope: the proofs.** Proof integrity is gate-checked mechanically by
`scripts/Audit.lean` itself (no `sorry`, no project axiom/opaque/partial/extern/
`implemented_by`, axiom closure ⊆ `{propext, Classical.choice, Quot.sound}`, all
witnesses present and theorems — 23 at audit time, **21** since `47c3984`). Nothing below depends on reading a proof body; every
statement and premise list was read off the Lean signature, not the docstring. Where a
docstring disagrees with its signature, that is recorded in §8.

**Classification key.**
- **[S]** security assumption — the ratified standard set: honest-to-honest Δ-synchrony,
  β corrupt-or-eclipse bound, honest behaviour/BLS, static registry & committee ground
  truth, synchronized clocks, accountable-safety statements, finalization spacing.
- **[P]** model-plumbing contract — pins an abstract/uninterpreted model function
  (`Externals`, the FFG selector state) against the pinned consensus spec.
- **[B]** bookkeeping/technical — anchor alignment, horizon/config arithmetic,
  nondegeneracy, call-local data.
- **[D]** derived-but-carried — provable from other premises of the same witness.
- **[!]** does not fit the above.

**Conventions used below.** `E.honest` is a *static, global* validator set (not
time-indexed). `E.WithinHorizon n` = `time_at n ≤ UINT64_MAX ∧ slot_at n ≤ UINT64_MAX ∧
epoch(slot_at n) < E.verification_horizon` (`Spec/Model/Execution.lean:78`).
`E.SafeFrom b n` = `∀ w ∈ E.honest, ∀ m ≥ n, WithinHorizon m → b` is an ancestor of
`get_head (store w m)` (`Spec/Proof/L4Fold.lean:60`). A "call at second `n`"
(`IsFCRCallAt`, `Spec/Proof/FCRCallContracts.lean:56`) means the store's `get_current_slot`
strictly advances from `n` to `n+1`; the call's write-back lands at second `n+1`.
`followingSlotStart n = slot_start (slot_at n + 1)`.

---

## 1. Master assumption table

Spec-layer records are unfolded to their fields here; per-witness sections reference them
by name. Witness IDs are Audit.lean order (W1…W23), listed in §2.

| # | Assumption (Lean) | Content (one line) | Class | Witnesses |
|---|---|---|---|---|
| A | `ExactPrefixAcceptedFFGSemantics` (`Model/FFGStateSemantics.lean:926`) — `anchor`, `state : AcceptedChainFFGState`, `coherence : AcceptedFFGTransitionCoherence` | one globally-chosen FFG semantic state (`C/GJ/GU/GF/GUF` selectors + included-attestation relation) interpreting every *accepted* root, with maximality/evidence laws | [P] | W1,W2,W16–W23 |
| A1 | `AcceptedChainFFGState` fields (26) | `checkpoint_epoch`, `formed_*` evidence, `gj/gu/gf/guf_mem`, `gj_max`/`gu_max` maximality, `gj_anchor_or_before`, `au_epoch_le_block`, `gf/guf_evidence`, epoch-ordering `gf ≤ gj`, `guf ≤ gu`, `gf ≤ guf` | [P] | as A |
| A2 | `AcceptedFFGSelectorCoherence` (11 fields) | selectors agree with `ext.is_valid_indexed_attestation`, with the genesis store's block states, and with every *accepted* `on_block` post-state (`transition_gj/gf/gu/guf`) | [P] mirrors `state_transition` + `process_justification_and_finalization` | as A |
| A3 | `AcceptedFFGTransitionCoherence` extra (2) | `checkpoint_of_known`, `au_checkpoint_of_known`: `C`/AU agree with `get_checkpoint_for_block` on every causal store | [P] | as A |
| B | `ScheduledPrefixTrajectoryAssumptions` (`Proof/CausalQueryTraceAdapter.lean:112`) | 5 fields: `whole_seconds` (`1000 ∣ slot_duration_ms`) [B]; `wellFormed` (roots commit to blocks) [P]; `externals_coherence` [S]+[P]; `honest_behavior` [S]; `genesis` (store = `get_forkchoice_store` of an anchor pair) [B] | mixed | binder on W1,W2; **derived from M** on W16–W23 (since `28a9bd6` it is a binder nowhere on the weak side — F2) |
| C | `JustificationInterface` (`Spec/TheoremStatements.lean:80`) — **13 fields** (was 15; `gate_sound` and `target_justified_sound`, the soundness of the two `will_*` gates, were never applied anywhere and were deleted in `8b05b67`) | FFG exports consumed by the FCR: `justified_unique` (**accountable safety**), `justified_requires_targets` (2/3 target weight), `observed_justified`, `unrealized_justified`, `finalized_justified_ancestry`, `justified_ancestry`, `finalized_descent`, `checkpoint_known`, and 5 checkpoint-state-cached fields | [S] (accountable-safety + ≥2/3 justification) with [P] cache fields | W20–W23 |
| D | `hanchor : B.anchor = genesis_store.justified_checkpoint` | the FFG state's anchor is the store's trusted checkpoint-sync anchor | [B] | W1,W2,W16–W23 |
| E | `TrustedAnchorBoundaryAligned` (`Proof/FFGGlobalCheckpointTrajectory.lean:623`) | anchor block's slot ≤ start slot of the anchor's epoch | [B] | W1,W2,W16–W23 |
| F | `AcceptedRealizedFinalizationDelay` (`Proof/AcceptedFinalizationTiming.lean:211`) | every accepted block's realized finalized checkpoint is the anchor or ≥2 epochs behind the block | [P] (phase0 process-epoch-before-slot order), also the **finalization spacing** [S] | W1,W2,W20–W23 |
| G | `Phase0SourceCoherence` (`Proof/FFGSourceCoherence.lean:64`) | same-epoch `process_slots` / `state_transition` preserve `current_justified_checkpoint` | [P] | W1,W2,W16,W17; on W20–W23 no longer a standalone binder — supplied once by O′ (`28a9bd6`) |
| H | `Phase0BoundarySourceCoherence` (`Proof/CurrentTargetCertificateRealization.lean:57`) | epoch-crossing `process_slots` / `state_transition` install the eager `process_justification_and_finalization` value | [P] | W1,W2,W16,W17; on W20–W23 supplied once by O′ (`28a9bd6`) |
| I | `PaperA32Inclusion` (`Model/FFGStateSemantics.lean:1188` → `…Core:1136`) | paper Assumption 3.2: canonical-throughout-epoch `b` with fixed `vs(b,e)→C(b,e)` 2/3 link support in every honest view throughout epoch `e+1` ⇒ by `st(e+2)` every honest view holds a pre-boundary descendant carrying `C(b,e)` in AU | [S] | W1,W2,W20–W23 |
| J | `AcceptedEpochCheckpointProjection` (`Model/ExactCheckpointLinks.lean:31`) | `C` is closed on accepted roots and composes at/above the anchor epoch | [B] | W1,W2,W20–W23 |
| K | `ExactLinkValidity` = `ExactIncludedLinkValidity` (`:153`/`…:~120`) | a link that *extends* an included certificate has an accepted carrier and both endpoints equal to that carrier's `C` at their epochs | [P] | W1,W2,W20–W23 |
| L | `hanchorExact : B.anchor = B.state.C anchor.root anchor.epoch` | the anchor is its own exact projection | [B] | W20–W23 |
| M | `SelectedMarginAssumptions` (`Proof/MinimalSelectedDomain.lean:39`) | 9 fields: `genesis` [B], `wellFormed` [P], `whole_seconds` [B], `honest_behavior` [S], `synchrony : PaperSafetySynchrony` [S], `externals_coherence` [S]+[P], `static_validators` [S], `byzantine_bound` [S], `domain : SelectedMarginDomain` [P] | mixed | W14–W23 (via M1/M2) |
| M-a | `HonestBehavior` (`Model/Assumptions.lean:84`) | vote-your-head at the assigned slot, votes only when assigned, no forgery (BLS) / no equivocation, honest votes pairwise non-slashable, honest unslashed in the registry | [S] | as M |
| M-b | `PaperSafetySynchrony` (`Model/Assumptions.lean:~183`) | 3 fields: honest slot-`s` attestations are in every honest node's schedule at `slot_start(s+1)`; blocks known to an honest node are known to every honest node by the end of the same slot; equivocation evidence relays by the next slot. **Honest-to-honest only; no delivery to the observer is assumed.** Since the single-synchrony refactor the delivery clause is *not* horizon-gated on the receipt side (the vote's slot and cast second still are), so it also covers the boundary vote whose receipt second is the first second past the exclusive cutoff: it is exactly the old receipt-gated clause **plus** the old separate `HorizonVoteDeliveryLookahead` record, and `attestation_delivery_pair_iff` proves the two are the same proposition. The old pair is recovered by `toHorizonScopedDelivery` / `toDeliveryLookahead` — **the boundary case is now a derived lemma, not an assumption.** | [S] (Δ-synchrony, GST-0 specialization) | as M |
| M-c | `ExternalsCoherence` (`Model/Assumptions.lean:233`) | 14 fields pinning `process_slots`/`state_transition`/`process_justification_and_finalization` (slot targeting, registry preservation, pre-slot ordering, checkpoint-epoch bounds), committee readback = ground truth on honest stores, BLS validity both directions, committee confinement, per-epoch assignment uniqueness/coverage/activity | [P] for the state functions; [S] for committee ground truth and BLS | as M |
| M-d | `StaticValidatorSet` (`Model/Assumptions.lean:325`) | genesis second is in-horizon; active-validator set constant below the horizon (paper Assumption 1) | [S] | as M |
| M-e | `ByzantineBound` (`Model/Assumptions.lean:371`) | effective balances quantized; `estimate_committee_weight_between_slots` is an upper bound (the spec's own 5‰ high-probability claim); per-span `100·byz ≤ CONFIRMATION_BYZANTINE_THRESHOLD · W` (paper Assumption 2 at β = threshold/100) | [S] | as M |
| M-f | `SelectedMarginDomain` (`:27`) | honest stores keep their justified root known and their justified checkpoint state cached | [P] | as M |
| M1 | `WeakObserverMarginAssumptions` (`Proof/WeakOneShotSafety.lean:~225`) | `base : M` + `coherence : ObserverCoherence` (committee readback **and** justified-root knownness at the observer's own store). The `observer : obs ∉ E.honest` field was deleted in `fbb3ec1` (§8 F3, RESOLVED): `obs` is now arbitrary and may be honest | [P] | W14,W15,W18,W19 |
| M2 | `WeakObserverAssumptions` (`Proof/WeakOneShotSafety.lean:~243`) | `base : M` + `committees_agree` at the observer's store only; `justified_root_known` is *derived* from A/B/D/E. The `observer : obs ∉ E.honest` field was deleted in `fbb3ec1` (§8 F3, RESOLVED) | [P] | W16,W17,W20–W23 |
| N | `PostAnchorHonestVoteTargetWalkDomain` (`Proof/Bridge.lean:72`) | for an actual post-anchor honest vote, the walk from the source head down to the vote's target-epoch boundary stays inside that store's block domain | [P] (domain adequacy of the totalized walk) | W18–W23 |
| O | `AcceptedHistoricalA32CompletedPrefixCallAssumptions` (`Proof/AcceptedHistoricalA32CallSupplier.lean:~342`) — **6 fields, no `helper_provisos`, no `delivery_lookahead`** (was 7; `delivery_lookahead` was deleted by the single-synchrony refactor — the boundary delivery case is now derived from `synchrony` via `PaperSafetySynchrony.toDeliveryLookahead`, so the content moved into a field the record already carried) | `synchrony : PaperSafetySynchrony` [S] (its delivery clause now also covers the boundary vote); `static_validators` [S]; `byzantine_bound` [S]; `phase0_source` [P]; `phase0_boundary_source` [P]; `balance_floor : effective_balance_increment ≤ weight(currentTargetAnchorActive)` [B] (excludes the empty-active-set helper branch) | mixed | W1,W2,W20–W23 |
| O′ | `Execution.AcceptedHistoricalA32CompletedPrefixCallSupplement` (`Proof/WeakTrajectorySafety.lean`, added `28a9bd6`) — **3 fields** (was 4; `delivery_lookahead` [S] dropped by the single-synchrony refactor — its content is now the boundary case of `hW.base.synchrony`, a premise these witnesses already carried, so dropping the field is a premise **weakening**) | O minus its `SelectedMarginAssumptions`-duplicating fields: `phase0_source` = G [P], `phase0_boundary_source` = H [P], `balance_floor` [B]. The full 6-field O is rebuilt internally from O′ + `hW.base` | mixed | W20–W23 (replaces O there) |
| P | `EpochEndsFitUint64` (`Model/Config.lean:97`) | `slots_per_epoch ∣ UINT64_MAX + 1` | [B] | W1,W2,W20–W23 |
| Q | `1 < cfg.slots_per_epoch` | config nondegeneracy | [B] | W1,W2 (strong only) |
| R | `Weak.ObservedResetSeedSafety` (`Proof/WeakTrajectorySafety.lean:~148`) | at a weak call whose candidate came from the epoch-start restart branch, the restarted-from root is `SafeFrom` at `n+1` | **[D]** — proved by `Weak.observedResetSeedSafety_of_acceptedDynamics` from premises already present. §8 F1 RESOLVED (`47c3984`): W20/W21 are **no longer registered witnesses**, so no *witness* carries R | W20,W21 (internal only) |
| S | `SelectedCoveredMarginSupplyAt` / `Weak.SelectedCoveredMarginSupplyAt` (`Proof/CoveredMargin.lean:203`, `Proof/WeakSelectedMarginInputs.lean:209`) | per strict selected edge at each honest endpoint: either the edge is already covered by that endpoint's justified root, or the caller supplies the exact LMD margin record | **[!]** residual per-call proof obligation, not an environmental assumption | W14–W17 |
| T | `Weak.SelectedStrictEdgeFilterSupplyAt` (`Proof/WeakCoveredMarginConstruction.lean:45`) | per strict selected edge with the strict-edge geometry: the child node is in the endpoint's filtered block tree | **[!]** residual per-call proof obligation (S discharged into it) | W18,W19 |
| U | call-local data: `hqH : WithinHorizon q`, `hstore : fcr_store.store = E.store obs q`, `hlcr`, `hbase : SafeFrom lcr (slot_start (slot_at q))`, `hcall`, `hselector : getLatestSelectorGuard …` | the query is in-horizon, reads the node's own store, the seed root is known and already safe from the query slot's start, the call actually happened / the helper actually ran | [B] | W2,W14–W19 |

### Paper-layer (arXiv:2405.00549 model) assumptions

| # | Assumption (Lean) | Content | Class | Witnesses |
|---|---|---|---|---|
| a | `Synchrony` (`Paper/Core/Model/View.lean:82`) | view monotonicity; `honestVoteUbiq` (honest cast in slot ≤ s′ is in every honest view by `st(s′+1)` once slot `s′` is post-GST); votes carry blocks; blocks ancestor-closed; `blockRelay`; `noFutureMessages`; `messageRelay` | [S] (Δ-synchrony after GST) | W7–W13 |
| b | `HonestNoForgery` (`:162`) | an honest-attributed vote in any honest view was genuinely cast (BLS unforgeability) | [S] | W7–W13 |
| c | `HonestBehavior` (`Paper/Core/Model/Honest.lean:22`) | honest committee members vote their own fork-choice head; vote only in their committee's slots; never equivocate | [S] | W7–W13 |
| d | `ViewsValid` (`:152`) | every message is from a committee member of its slot for a well-formed block of not-greater slot | [S]/[B] | W7–W13 |
| e | `CommitteeHonestMajority` (`Paper/LMDGhost/Model/Assumptions.lean:21`) | over every committee union, honest weight ≥ `(1-β)` of total (paper Assumption 2) | [S] | W7–W13 |
| f | `WellFormedBoost` (`Paper/Core/Model/ForkChoice.lean:84`) | the proposer boost applies only to a current-slot, well-formed, in-view proposal | [B] | W8,W9,W10,W11 |
| g | `StaticBalances` (`:46`) | all `gj` anchors assign identical balances (paper Assumption 1) | [S] | W8–W11 |
| h | `AnchorsCoincide` (`:72`) | every honest voter's `gj`-anchor equals the engine anchor `C` | [S] (implied by g; g is not a premise of W7, so not [D] there) | W7 |
| i | `fm.β < 1/3` (`FaultModel` field) | global Byzantine fraction bound | [S] | W7–W13 |
| j | `fm.β < (1-pb)/4` | paper Assumption 4 (LMD monotonicity) | [S] | W9 |
| k | `fm.β < min(1/6, (1-pb)/4)` | Assumption 6.2 FFG-closure `1/6` ⊓ Assumption 4; the `(1-pb)/4` **stands in for the paper's `1/3 − d` safety-decay bound** (documented substitution) | [S] w/ note §8 F6 | W11,W13 |
| l | `CommitteeCoversEpoch` (`:62`) | the epoch's committee union is the whole validator set (Assumption-1 corollary) | [S] | W9,W11,W13 |
| m | `GlobalByzantineBound` (`Paper/Core/Model/Validators.lean:66`) | non-honest weight ≤ `β·W` at anchor `C` | [S] | W10–W13 |
| n | `FFG_AccountableSafety` (`Paper/HFC/TheoremStatements.lean:262`) | three Casper consequences: finalized non-conflicting; one justified block per epoch; finalized prefix of justified | [S] (accountable safety, consumed) | W10–W13 |
| o | `HonestFFGNoEquivocation` (`Paper/HFC/Model/HonestFFG.lean:46`) | an honest FFG cast targets its own head's checkpoint with the rule's voting source | [S] (definitional honest behaviour) | W10–W13 |
| p | `SafeGreatestJustifiedAnchorInputs` (`:194`) | every honest-view-safe block satisfies the semantic no-conflicting-justification gate + GU-anchor well-formedness/realization inputs | [!] see §8 F5 | W10,W11 |
| q | `SlotCommitteeMinority` (`:40`) | a single slot's committee controls `< (2/3 − β)` of stake — **docstring states it is an added assumption, not a consequence of the paper's set** | [S]+ / flagged §8 F5 | W12,W13 |
| r | `Alg1SelectorSafetyInterface` → `Alg1SafetyInterface` (`:474`/`:452`) | per-confirmation: on-chain AU vote payload interfaces, greatest-finalized realization + selector agreement, epoch committee partition, `P-link` common source, and `AfterGST(st(s'-1))` at the witness slot | [S]+[P] mix, partly [!] §8 F5 | W12 |
| s | `SafeConfirmedAlg1Inputs` (`:557`) | for **every** honest-view-safe block: rule confirmation + the same four interface conjuncts | [!] — docstring self-discloses it is *stronger and more direct* than paper Assumption 6 | W13 |
| t | `0 ≤ pb`, `0 ≤ we`, `sg τ b t` guard, `1 ≤ s`, `b.WellFormed`, `b.slot ≤ s` | scalar nonnegativity / recency-and-GST guard / block well-formedness | [B] | W7–W13 |

**Bucket counts (as audited; distinct assumptions, spec + paper layers, counting the 21
spec-layer rows A–U — row O′ was added later as a projection of O, not a new assumption —
and the 20 paper-layer rows a–t = 41 entries):** [S] 19 · [P] 12 · [B] 8 · [D] 1 · [!] 3
(rows S, T, s; with q, p, r flagged as [S]-with-caveat). Several rows are mixed-class
records; the count assigns each row its dominant class and §8 records the exceptions.

---

## 2. Strong one-shot / fold statements

### W1 `FastConfirmation.Spec.acceptedSpec_safety_next_slot`
`Spec/Proof/AcceptedActualFCRNextSlotSafetyFacade.lean:269` (statement
`AcceptedSpec_Safety_next_slot`, `:257`). **Headline (strong side).**

*Statement.* For every execution `E` satisfying the accepted bundle, every honest node `v`,
every second `n`, and every honest node `w` at every second `m ≥ n` that is in-horizon and
whose slot is at least `slot(n)+1`: the root `v`'s FCR store holds at second `n`
(`E.confirmed v n`) is an ancestor of `w`'s fork-choice head at `m`. Note `n` itself is
**not** required to be in-horizon — only the endpoint second `m` is; `n ≤ m` plus
horizon-monotonicity makes this harmless.

*Hypotheses.* One record, `E.AcceptedActualFCRNextSlotSafetyAssumptions` (`:33`), 11 fields:
`semantics` = A [P]; `trajectory` = B [mixed]; `completed_calls` = O (7 fields) [mixed];
`epoch_ends_fit` = P [B]; `anchor_eq` = D [B]; `anchor_boundary` = E [B];
`finalization_delay` = F [P/S]; `slots_per_epoch_gt_one` = Q [B]; `paper_a32` = I [S];
`checkpoint_projection` = J [B]; `exact_link_validity` = K [P].
No `JustificationInterface`, no `PostAnchorHonestVoteTargetWalkDomain`, no reset/adoption/
head-ancestry/safety field. **No [D], no [!].** Field-level overlap check: B's five fields
and O's seven fields are disjoint; the bundle is non-redundant.

### W2 `…AcceptedActualFCRNextSlotSafetyAssumptions.findLatestConfirmedDescendant_safeFrom_of_actualCall`
`…Facade.lean:122`. **Supporting public statement (strong side).**

*Statement.* At an actual boundary call by honest `v` at second `n` (slot advances `n → n+1`),
with `n+1` in-horizon, and given that the executable selector guard
`getLatestSelectorGuard` fired on the call's post-observed candidate: the literal return
value of `find_latest_confirmed_descendant` on the call's own store and candidate is
`SafeFrom` at second `n+1` — i.e. an ancestor of every in-horizon honest node's head from
the write-back second onward. Covers the case where the helper runs and returns its input
unchanged.

*Hypotheses.* The same bundle as W1 (all 11 fields), plus call-local `hv : v ∈ E.honest`
[B/scope], `hcall : IsFCRCallAt v n` [B], `hHn1 : WithinHorizon (n+1)` [B],
`hselector : getLatestSelectorGuard …` [B]. **No [D], no [!].**

---

## 3. Weak trajectory headlines (the audited weak statements)

All four share one premise list modulo `hOR`; differences from the strong twins are in §3.5.

> **Post-audit (`28a9bd6`, `47c3984`).** The four premise lists below were audited at 17
> items (W20/W21) and 16 (W22/W23). They are now 14 and 13: `hT`, `hphase0` and
> `hboundaryPhase` are gone (derived internally / read off the call supplement), and
> `hCbase` is O′ rather than O (4 fields then; 3 since the single-synchrony refactor
> deleted `delivery_lookahead`, O itself dropping 7 → 6). W20/W21 are also no longer
> registered witnesses. Conclusions are byte-identical.

### W20 `Execution.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold`
`Spec/Proof/WeakTrajectorySafety.lean:~572`. **Conditional form — since `47c3984` an
internal theorem, not a registered witness (§8 F1).**

*Statement.* Fix an observer `obs` that is **not** honest and to which no delivery is
assumed. For **every** in-horizon second `n`, the root the observer's weak FCR trajectory
holds at `n` (`E.weakConfirmed obs n`, produced by rule-delta-5
`Weak.on_fast_confirmation` at each slot advance) is an ancestor of the fork-choice head of
**every** honest node `w` at **every** in-horizon second `m ≥ followingSlotStart n`
(= the first second of the slot after `slot(n)`). Quantifier order: `∀ n, WithinHorizon n →
∀ w ∈ honest, ∀ m ≥ followingSlotStart n, WithinHorizon m → is_ancestor(…)`.

*Hypotheses* (17 as audited; **14 now**, see the annotations):
1. `B` = A [P] — accepted FFG semantic state.
2. ~~`hT` = B~~ — **F2 RESOLVED (`28a9bd6`): removed**, derived from `hW.base` via
   `ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions`.
3. `hji` = C [S] — justification interface (accountable safety, ≥2/3
   justification, checkpoint caches); **13 fields since `8b05b67`**, the two gate-soundness
   fields having been deleted as dead, which weakens this premise.
4. `hanchor` = D [B]. 5. `hboundary` = E [B]. 6. `hDelay` = F [P/S].
7. ~~`hphase0` = G~~ — **F2 RESOLVED: removed**, read off `hCbase.phase0_source`.
8. ~~`hboundaryPhase` = H~~ — **F2 RESOLVED: removed**, read off
   `hCbase.phase0_boundary_source`.
9. `hpaper` = I [S] — paper A3.2.
10. `P` = J [B]. 11. `V` = K [P]. 12. `hanchorExact` = L [B].
13. `hW` = M2 — unfolds to `base : SelectedMarginAssumptions` (M-a…M-f: honest behaviour
    [S], honest-to-honest Δ-synchrony [S], externals coherence [P]+[S], static registry
    [S], β bound + weight-estimation soundness [S], honest-store domain [P], genesis /
    whole-seconds [B]) and `committees_agree` at the observer's own store [S]/[P]. The
    `observer : obs ∉ E.honest` field is **gone (F3 RESOLVED, `fbb3ec1`)**: the statement
    now also covers an honest observer.
14. `hwalkDomain` = N [P]. 15. `hCbase` = **O′** [mixed] since `28a9bd6` — now the 3-field
    supplement (`phase0_source`, `phase0_boundary_source`, `balance_floor` [B]); the
    fields of O that duplicated `hW.base` (`synchrony`, `static_validators`,
    `byzantine_bound`) are taken once, from `hW.base`, when the full record is rebuilt
    internally, and `delivery_lookahead` [S] is gone entirely — the single-synchrony
    refactor moved its content into `hW.base.synchrony`'s delivery clause, where the
    boundary case is now the derived lemma `PaperSafetySynchrony.toDeliveryLookahead`.
    The premise surface therefore shrank again; the conclusion is unchanged byte for
    byte. **F2 RESOLVED.**
16. `hfit` = P [B]. 17. `hOR` = R — **[D], §8 F1 RESOLVED by deregistration**.

No honesty *or* non-honesty binder at `obs`; no delivery to `obs`;
`ObserverCoherence.justified_root_known` is derived inside the induction, not assumed.

### W21 `Execution.weakConfirmed_head_of_weakFullRuleFold_nextSlot`
`WeakTrajectorySafety.lean:~641`. **Endpoint form of W20; likewise internal since
`47c3984`.**

*Statement.* Same premises as W20 plus `w ∈ E.honest`, `n ≤ m`,
`slot(n) + 1 ≤ slot(m)`, `WithinHorizon m`. Conclusion: `is_ancestor (store w m)
(get_head (store w m)) (get_node_for_root (E.weakConfirmed obs n)) = true` — i.e. the paper's
timing: canonical at every in-horizon honest endpoint in a strictly later slot. The
`followingSlotStart` deadline of W20 is converted to the slot inequality internally.

*Hypotheses.* Identical to W20 (17), plus the three endpoint binders [B]. Same [D]/[!] as W20.

### W22 `Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
`Spec/Proof/WeakObservedResetSeedSafety.lean:~163`. **The unconditional weak headline.**

*Statement.* Identical to W20's conclusion, verbatim.

*Hypotheses.* W20's list **minus** `hOR`: audited at 16 premises, **13 now**. The
discharge (`Weak.observedResetSeedSafety_of_acceptedDynamics`, `:~81`) consumes only
`hW.base`, `B`, `hji`, `hanchor`, `hboundary`, `hW.committees_agree` — all already
present (it lost its own `hT` in `28a9bd6`), so the premise surface is strictly smaller
than W20's, as the docstring claims. The exact list is now:

> `B` [A], `hji` [C, 13 fields], `hanchor` [D], `hboundary` [E], `hDelay` [F],
> `hpaper` [I], `P` [J], `V` [K], `hanchorExact` [L], `hW` [M2, no honesty field],
> `hwalkDomain` [N], `hCbase` [O′, 4 fields], `hfit` [P].

All former [D]/[!] flags on this witness are cleared: `hT`, `hphase0`, `hboundaryPhase`
are no longer carried (F2) and `hW.observer` no longer exists (F3). Every remaining
premise is [S]/[P]/[B].

### W23 `Execution.weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot`
`WeakObservedResetSeedSafety.lean:~196`. **The unconditional endpoint headline.**
Statement = W21's; hypotheses = W22's 13 plus the three endpoint binders [B]
(`hw : w ∈ E.honest`, `n ≤ m`, `slot(n)+1 ≤ slot(m)`, `WithinHorizon m`). Same cleared
flags as W22.

### 3.5 Strong ↔ weak premise differences

| | strong fold (W1/W2, via `AcceptedActualFCRNextSlotSafetyAssumptions`) | weak trajectory headlines (W20–W23) |
|---|---|---|
| observer | `hv : v ∈ E.honest` | **nothing** — `obs` is an arbitrary index. (As audited this was `hW.observer : obs ∉ E.honest`, unused and domain-narrowing; deleted in `fbb3ec1`, §8 F3. The weak headlines now also speak about honest observers, though the *conclusion object* still differs: see the last row.) |
| observer-store facts | none (honesty supplies them) | `committees_agree` at `obs`'s store; `justified_root_known` derived |
| `JustificationInterface` | **absent** (deliberately replaced by `SelectedMarginDomain`) | **present** (`hji`, **13** fields since `8b05b67`) — a materially larger FFG export surface on the weak side |
| `PostAnchorHonestVoteTargetWalkDomain` | absent | present (`hwalkDomain`) |
| `SelectedMarginAssumptions` | absent as a premise (rebuilt internally from `trajectory` + `completed_calls` + derived domain) | present inside `hW.base` — which is why `hT` was redundant and is now **derived from it** (§8 F2, `28a9bd6`) |
| `1 < cfg.slots_per_epoch` | present | **absent** |
| `Phase0*SourceCoherence` | only inside `completed_calls` | only inside the call supplement O′ — the standalone duplicates are gone (§8 F2, `28a9bd6`) |
| conclusion object | `E.confirmed v n` (strong handler) | `E.weakConfirmed obs n` (rule-delta-5 handler) |
| deadline | `followingSlotStart n` | `followingSlotStart n` (identical) |

---

## 4. Weak one-shot floor statements

These carry no `B`/`hT`; they are the per-call floor, with the margin/filter obligation on
the caller. All six are **supporting public statements**, not headlines.

### W14 `Execution.weak_safeFrom_find_latest_confirmed_descendant` — `Proof/WeakOneShotSafety.lean:1116`
*Statement.* For a not-necessarily-honest observer `obs`, an in-horizon query second `q`, an
FCR store whose `store` field is exactly `E.store obs q`, and a seed root `lcr` known in it
and already `SafeFrom` from the start of `q`'s slot: the weak selector's output
`Weak.find_latest_confirmed_descendant` is `SafeFrom` at second `q` itself — an ancestor of
every in-horizon honest node's head from `q` on.
*Hypotheses.* `hW` = M1 [P] (no honesty field since `fbb3ec1`), `hqH`/`hstore`/`hlcr`/
`hbase` = U [B], `hmargin` = S **[!]** (conditional on the selector strictly advancing).

### W15 `Execution.weak_confirmed_head` — `:1175`
Endpoint form of W14: same premises plus `w ∈ E.honest`, `q ≤ m`, `WithinHorizon m`;
conclusion is the literal `is_ancestor` equation. Same classes.

### W16 `Execution.weak_safeFrom_find_latest_confirmed_descendant_from_finalized` — `Proof/WeakFinalizedInput.lean:679`
*Statement.* As W14 but **seeded at the observer's own finalized checkpoint root** rather
than at a caller-supplied safe root: `hlcr`/`hbase` are discharged from the accepted FFG
bundle. Conclusion: the selector output from that seed is `SafeFrom` at `q`.
*Hypotheses.* `hW` = M2, `B` = A, `hanchor` = D, `hboundary` = E, `hphase` = G,
`hboundaryPhase` = H, `hqH`/`hstore` = U, `hmargin` = S **[!]**. `hT` is derived from
`hW.base` inside the proof, **not carried** — contrast §8 F2.

### W17 `Execution.weak_confirmed_head_from_finalized` — `:726`
Endpoint form of W16; premises identical plus `hw`, `hqm`, `hHm` [B].

### W18 `Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged` — `Proof/WeakOneShotSafetyNative.lean:199`
*Statement.* W14 with the margin obligation `hmargin` (S) discharged into the narrower
`hfilter` (T) via the weak supplier; `hwalkDomain` (N) appears in its place.
*Hypotheses.* `hW` = M1 (no honesty field since `fbb3ec1`), `hwalkDomain` = N [P], U [B],
`hfilter` = T **[!]**.

### W19 `Execution.weak_confirmed_head_discharged` — `:223`
Endpoint form of W18; same premises plus `hw`, `hqm`, `hHm` [B].

---

## 5. Paper-layer statements

All seven are *strong-side* statements in the paper model (`FastConfirmation/Paper`), each a
facade theorem discharging a proof-free `Prop` in `TheoremStatements.lean`. Hypotheses are
the `Prop`'s own binders — the facade adds none.

### W7 `LMDGhost.HeadFutureAgreement_proved` — `Paper/LMDGhost/ProvenTheorems.lean:18`
(statement `LMDGhost/TheoremStatements.lean:88`). **Reusable engine, Lemma 6.**
*Statement.* For any anchor `C` and any block filter: if honest `v` sees `b` as
`isLMDGHOSTSafe` at `t`, `b` is well-formed with `b.slot ≤ slot(t)`, `1 ≤ slot(t)`,
`AfterGST(st(slot(t)-1))`, and `b` is `NeverFiltered`, then for every honest `w` and every
`t' ≥ st(slot(t))`, `b ≼ forkChoiceHead τ C boost pb flt (𝒱 w t') t'`.
*Hypotheses.* a [S], b [S], c [S], d [S]/[B], e [S], `0 ≤ pb` [B], h `AnchorsCoincide` [S],
plus the per-instance guards in t [B], plus the two semantic antecedents
(`isLMDGHOSTSafe`, `NeverFiltered`) which are *data of the statement*, not assumptions.
No [D] (note: `StaticBalances` is **not** a premise here, so `AnchorsCoincide` is not derivable).

### W8 `LMDGhost.Theorem1_Safety_proved` — `:24` (statement `:109`)
*Statement.* Under the §3.1 bundle, if honest `v` has `isConfirmed` (Algorithm 4: `b` is an
ancestor of the highest LMD-safe block since the second slot of the previous epoch) for `b`
at `t` with the security guard `sg τ b t`, then there is a time `t₀` from which `b` is on
every honest validator's LMD-GHOST head.
*Hypotheses.* a, b, c, d, e (per-view form), f, g, `0 ≤ pb`, `sg` [all as tabled]. No [D]/[!].

### W9 `LMDGhost.Theorem1_Monotonicity_proved` — `:32` (statement `:138`)
*Statement.* Same bundle plus `β < (1-pb)/4` (Assumption 4) and `CommitteeCoversEpoch` at
`epoch(slot(t'))-1`: `isConfirmed … b t → isConfirmed … b t'` for every `t' ≥ t`.
*Hypotheses.* W8's + j + l. No [D]/[!].

### W10 `HFC.HFC_Safety_proved` — `Paper/HFC/ProvenTheorems.lean:44` (statement `HFC/TheoremStatements.lean:353`)
*Statement.* W8 at `flt := ffgFilter bal₀ τ`, `gj := gjFFG bal₀`, `C := bal₀`, with the
confirmation predicate `isHFCConfirmed` = `isConfirmed ∧ WillNoConflictingChkpBeJustified`.
Conclusion: `∃ t₀`, from which `b` is on every honest LMD-GHOST-HFC head.
*Hypotheses.* a,b,c,d,e,f,g,`0 ≤ pb`,`sg` + n `FFG_AccountableSafety` [S] + o [S] + m [S] +
p `SafeGreatestJustifiedAnchorInputs` **[!]** (§8 F5).

### W11 `HFC.HFC_Monotonicity_proved` — `:54` (statement `:403`)
*Statement.* `isHFCConfirmed … b t → isHFCConfirmed … b t'` for `t' ≥ t`.
*Hypotheses.* W10's + k (`β < min(1/6,(1-pb)/4)`) + l. Flags: p **[!]**, k documented
substitution (§8 F6).

### W12 `HFC.HFC_Safety_Alg1_proved` — `:63` (statement `:498`)
*Statement.* The gate-free form: confirmation hypothesis is `isConfirmedAlg1` (the wrapper
over the *local, computable* `isConfirmedNoCaching`), the semantic gate
`WillNoConflictingChkpBeJustified` is **gone**, replaced by the selector witness's own local
rule proof plus `Alg1SelectorSafetyInterface` at the selected block `B`. Precondition is
slot-boundary (`1 ≤ s`, `b.slot ≤ s`, `AfterGST(st(s-1))`) rather than `sg`.
*Hypotheses.* a,b,c,d,e,`0 ≤ pb`,`0 ≤ we` + n + o + m + q `SlotCommitteeMinority` [S]+ +
r `Alg1SelectorSafetyInterface` [S]+[P], flagged §8 F5. Note `WellFormedBoost` and
`StaticBalances` are **not** premises here.

### W13 `HFC.HFC_Monotonicity_Alg1_proved` — `:71` (statement `:568`)
*Statement.* `isConfirmedAlg1 … b t → isConfirmedAlg1 … b t'` for `t' ≥ t`, under `sg` and
`CommitteeCoversEpoch`.
*Hypotheses.* a,b,c,d,e,`0 ≤ pb`,`0 ≤ we`, k, n, o, m, q, l, and s
`SafeConfirmedAlg1Inputs` **[!]** (§8 F5).

---

## 6. Closed finite witnesses (no hypotheses)

### W3 `Spec.AcceptedActualFCRJointNonVacuityFinal.witnessJointNonvacuity` — `Proof/AcceptedActualFCRJointNonVacuityFinal.lean:682`
*Statement.* A **closed** theorem (zero hypotheses) exhibiting one concrete 16-second,
4-validator, all-honest execution and asserting `JointWitnessFacts` (`:645`): the full
`AcceptedActualFCRNextSlotSafetyAssumptions` bundle is inhabited for it; there is a genuine
FCR call at second 1 whose selector strictly advances anchor → child (`confirmed 0 1 =
anchor`, `confirmed 0 2 = child`, `child ≠ anchor`, and the exact selector equation); paper
A3.2's support antecedent *and* its conclusion hold substantively at second 12; a slot-15
honest vote is delivered only at second 16, which is outside the horizon; and the public
safety conclusion holds at second 15. This is the anti-vacuity evidence for W1: the bundle
is satisfiable **and** the theorem's hypotheses are met non-trivially.
*Hypotheses.* None. No [D]/[!].

### W4 `Spec.AcceptedActualFCRJointNonVacuityFinal.acceptedActualFCRNextSlotSafetyAssumptions_nonvacuous` — `:712`
*Statement.* Closed: `∃ cfg ext E, Nonempty (E.AcceptedActualFCRNextSlotSafetyAssumptions
cfg ext)`. Hypotheses: none.

### W5 `Spec.AcceptedStrictPrefixExtraQueryCounterexample.strict_prefix_extra_query_counterexample` — `Proof/AcceptedStrictPrefixExtraQueryCounterexample.lean:930`
*Statement.* Closed **negative** result. In a concrete 4-root, 4-validator, all-honest,
fully synchronous execution satisfying `StrictPrefixWitnessEnvironment` (genesis
initialization, `WellFormedExecution`, whole seconds, `HonestBehavior`, full `Synchrony`,
`ExternalsCoherence`, `StaticValidatorSet`, `ByzantineBound`,
plus exact clock/committee/schedule/vote equations), the global action interpreter reaches a
genuine query snapshot in which node 0 and node 1 are two *different action prefixes of the
same second*; node 0's source-permitted pre-update extra query returns `candidate`, while
node 1's simultaneously-represented fork-choice head is `sibling` and `candidate` is **not**
its ancestor. The scope claim: this refutes exact-current, all-runtime-prefix helper safety;
it does **not** refute any theorem quantified over completed `Execution.store` boundaries.
*Hypotheses.* None (all assumptions are conclusions of the statement). No [D]/[!].

### W6 `Spec.AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample.pinned_economics_strict_prefix_extra_query_counterexample` — `…PinnedEconomics…:930`
*Statement.* The same negative result at the **pinned FCR economic constants**
(`proposer_score_boost = 40`, `confirmation_byzantine_threshold = 25`, both exported as
explicit conjuncts of the environment), on a 5-root chain anchor→parent→{candidate,sibling},
so the race is not an artifact of the `100`/`0` toy economics of W5. Still a four-slot
one-second-per-slot preset: a pinned-**economics** witness, not `mainnet_config`.
*Hypotheses.* None.

---

## 7. Statement-scope caveats (not defects; read them before ratifying)

1. **Horizon.** Every spec-layer conclusion is scoped to `WithinHorizon` endpoints:
   `epoch(slot m) < E.verification_horizon` plus uint64 bounds. Safety is silent beyond it.
   `StaticValidatorSet.genesis_within_horizon` keeps the domain non-empty.
2. **Honesty is static.** `E.honest : Finset ValidatorIndex` is fixed for the whole
   execution; there is no adaptive-corruption model. β is a *weight fraction per committee
   span*, cross-multiplied.
3. **GST-0.** `PaperSafetySynchrony` is global over the horizon, i.e. the spec layer is the
   GST-0 specialization; the paper layer carries an explicit `AfterGST` guard instead.
4. **"Accepted" ≠ "all".** `ExactPrefixAcceptedFFGSemantics` is explicit that it does not
   claim coverage of delayed queues or arbitrary global action traces (`:923`); W5/W6 are
   the matching negative result for in-second prefixes.
5. **The weak conclusion is about the observer's own trajectory**, `E.weakConfirmed obs n`,
   which is the rule-delta-5 handler's output; it is not `E.confirmed`. The two handlers are
   different functions (`Weak.update_fast_confirmation_variables` additionally takes `ext`
   for the certificate gate).

---

## 8. Flags

**F1 — RESOLVED (`47c3984`) — [D] on a trajectory headline:
`hOR : Weak.ObservedResetSeedSafety` (W20, W21).**
`WeakTrajectorySafety.lean:552`/`:621` carry `hOR` as a premise, yet
`Weak.observedResetSeedSafety_of_acceptedDynamics` (`WeakObservedResetSeedSafety.lean:81`)
proves exactly that `Prop` from `hW.base`, `B`, `hT`, `hji`, `hanchor`, `hboundary`,
`hW.committees_agree` — every one of which W20/W21 already carry. So on W20/W21 `hOR` is
derived-but-carried. It is *deliberate* (the docstring says the `Prop` is kept
"so the one-call-at-a-time reading remains available"), and W22/W23 are the same statements
with it discharged. Ratification consequence: **W20/W21 are strictly weaker restatements of
W22/W23 and add nothing; only W22/W23 should be read as headlines.**
*Resolution:* W20/W21 were removed from `publicWitnesses` (count 23 → **21**; the
`Audit.lean` size assertion was updated to 21). They remain internal theorems — W22/W23's
proof chain goes through them — and their docstring now says so.

**F2 — RESOLVED (`28a9bd6`) — [D] on all four trajectory headlines: three redundant
premises.**
(i) `hT : ScheduledPrefixTrajectoryAssumptions` is derivable from `hW.base` via
`ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions`
(`CausalQueryTraceAdapter.lean:~125`) — all five of `hT`'s fields are fields of
`SelectedMarginAssumptions`. W16/W17 do exactly this derivation internally and do *not*
carry `hT`; W20–W23 carry it anyway.
(ii) `hphase0 : Phase0SourceCoherence cfg ext` is literally the field
`hCbase.phase0_source`.
(iii) `hboundaryPhase : Phase0BoundarySourceCoherence cfg ext` is literally
`hCbase.phase0_boundary_source`.
Additionally, three of `hCbase`'s seven fields (`synchrony`, `static_validators`,
`byzantine_bound`) are already supplied by `hW.base`; only `balance_floor` and
`delivery_lookahead` are new content (and since the single-synchrony refactor
`delivery_lookahead` no longer exists: its content is the boundary case of
`hW.base.synchrony`, leaving `balance_floor` as the only new content). None of this changes the *assumption set* — it is
double-counting on the premise **surface**, so the four headlines look heavier than they
are.
*Resolution:* all four collapsed. `hT` is derived inside each headline from `hW.base`
(as W16/W17 already did) and `hphase0`/`hboundaryPhase` are read off the call contract;
the call contract itself is now the 3-field
`Execution.AcceptedHistoricalA32CompletedPrefixCallSupplement` (row O′; 4 fields when F2
was resolved, 3 since the single-synchrony refactor), from which —
together with `hW.base` — the full record is rebuilt internally
(`…CallSupplement.toCompletedPrefixCallAssumptions`). No field was left behind: all three
duplications were literal (same `Prop`), so the de-duplication was mechanical.
`Weak.observedResetSeedSafety_of_acceptedDynamics` lost its own `hT` for the same reason.
Premise counts: W20/W21 17 → 14, W22/W23 16 → 13. Conclusions unchanged byte for byte.

**F3 — RESOLVED (`fbb3ec1`) — [!] an unused premise that narrowed the weak statements:
`observer : obs ∉ E.honest`.**
Field of both `WeakObserverAssumptions` (`WeakOneShotSafety.lean:246`) and
`WeakObserverMarginAssumptions` (`:227`). A repository-wide search finds exactly **one**
occurrence of the projection, `WeakOneShotSafety.lean:265`, which merely copies it from one
record to the other; no proof, no lemma, and no destructuring of either record consumes it.
So on W14–W23 it is a dead hypothesis that nonetheless **restricts the conclusion's domain**:
as stated, the weak theorems say nothing about a *honest* observer, and therefore do not
subsume the strong fold. If it is genuinely unused the field should be deleted, which would
strictly generalize all ten weak witnesses; if it is intended as documentation it should not
be a hypothesis. (Finding is signature/grep-level; a `lake env`-side unused-argument check
would confirm it mechanically — not run here per the read-only constraint.)
*Resolution:* the field was deleted from **both** records; the only consumption (the copy
inside `WeakObserverAssumptions.toMarginAssumptions`) went with it and the build confirms
nothing else used it. Every weak witness is thereby strictly generalized: they now hold for
an arbitrary observer, honest or not. The records' docstrings state that the observer MAY be
honest and that the model simply grants it nothing.

**F4 — [!] residual per-call proof obligations on the premise surface: `hmargin`/`hfilter`.**
W14–W17 carry `(Weak.)SelectedCoveredMarginSupplyAt` and W18/W19 carry
`Weak.SelectedStrictEdgeFilterSupplyAt`. These are neither security assumptions nor model
plumbing: they are per-edge fork-choice-weight obligations that the *caller* must prove at
each strict selected edge at each honest endpoint. They are fully discharged on the
trajectory headlines (W20–W23 carry neither). Reading W14–W19 as "safety of the weak
selector" without that qualification would overstate them.

**F5 — [!] paper-layer premises the paper does not state in this form.**
(i) `SafeGreatestJustifiedAnchorInputs` (W10, W11) requires the semantic no-conflicting-
justification gate **for every honest-view-safe block**, not only for the confirmed one.
(ii) `SafeConfirmedAlg1Inputs` (W13) — the docstring itself discloses: *"this is stronger
and more direct than paper Assumption 6's conditional-eventual FFG-closure premise."*
(iii) `SlotCommitteeMinority` (W12, W13) — docstring: *"a genuine added hypothesis, NOT a
consequence of the model's existing assumptions."* True of real Ethereum, but it is outside
the paper's assumption list.
(iv) `Alg1SelectorSafetyInterface`/`Alg1SafetyInterface` (W12) bundle four per-confirmation
facts (on-chain AU vote payloads, greatest-finalized realization + selector agreement,
committee partition, `P-link` common source); the first two are model plumbing for the
block-contained-vote abstraction rather than paper assumptions.
All four are self-disclosed in their own docstrings; they are flagged here because they are
premise content a reader of the theorem *names* alone would not expect.

**F6 — documented substitution in the β-bound (W11, W13).** The Lean statements carry
`β < min(1/6, (1-pb)/4)`. The `1/6` is paper Assumption 6.2's FFG-closure constant verbatim;
the `(1-pb)/4` **stands in for** the paper's `1/3 − d` safety-decay bound (Assumption 5.1) —
the Lean abstracts `d` away and instead demands the LMD-GHOST monotonicity bound. Disclosed
in the docstring at `HFC/TheoremStatements.lean:~410`; recorded here so ratification is of
the substituted bound, not the paper's.

**F7 — RESOLVED (`28a9bd6`, `5ec6441`) — docstring/signature discrepancies found.** Two,
both minor, both in the weak layer:
(i) `WeakObservedResetSeedSafety.lean:38-41` enumerates
`observedResetSeedSafety_of_acceptedDynamics`'s premises as "the selected-margin
assumptions, the accepted FFG semantic bundle and its anchor alignment, the justification
interface, and the observer's own committee agreement" — the signature (`:81`) *also* takes
`hT : ScheduledPrefixTrajectoryAssumptions`. Harmless (it is derivable from `hA`), but the
enumeration is incomplete. *Resolution (`28a9bd6`):* `hT` was removed from that signature
and is derived from `hA` in the body, so the enumeration is now exact; the paragraph says
so explicitly.
(ii) `WeakOneShotSafety.lean:1109-1115` says W14 matches the strong original's hypothesis
list with "no further hypothesis added or dropped". The substitution `(v, hv : v ∈ honest)
↦ (obs, hW)` does replace one binder by a three-field record containing two genuinely new
observer-store facts (`committees_agree`, `justified_root_known`) plus the unused
non-honesty field of F3. The sentence is defensible as written but reads as stronger than
the signature warrants. *Resolution (`5ec6441`):* the docstring now states the exchange —
the honesty binder is dropped and two observer-store facts (`committees_agree`,
`justified_root_known`) are taken in its place, with the reason this one-shot floor form
cannot derive the second one.
No other docstring claim checked against a signature was found to disagree. In particular
the following were verified **accurate**: `AcceptedActualFCRNextSlotSafetyAssumptions`'s
"no finalized-reset, observed-adoption, observed-lock, head-ancestry, filter-result, or
safety field"; `AcceptedHistoricalA32CompletedPrefixCallAssumptions`'s "there is no
`helper_provisos` field" (7 fields at audit time, confirmed; 6 since the single-synchrony
refactor dropped `delivery_lookahead`); W22's "strictly smaller premise surface than
the conditional one … nothing is added"; W20's "premise surface is that of
`weak_safeFrom_observerCall_closed_lazy` together with `hboundaryPhase` and `hOR`"; and the
claim across the weak layer that `ObserverCoherence.justified_root_known` is derived rather
than assumed.

**Trajectory-headline verdict (as audited).** The premise surfaces of W20–W23 contain,
besides [S]/[P]/[B] items, exactly: **[D]** `hT`, `hphase0`, `hboundaryPhase` (all four) and
`hOR` (W20/W21 only); and **[!]** the unused, domain-narrowing `hW.observer`. No other
premise falls outside [S]/[P]/[B].

**Trajectory-headline verdict (after `fbb3ec1`/`28a9bd6`/`47c3984`/`8b05b67`).** The two
registered weak headlines W22/W23 carry **13 premises** (plus W23's four endpoint binders),
every one of them [S]/[P]/[B]: no [D], no [!]. The single-synchrony refactor kept the count
at 13 while shrinking one of them (`hCbase` 4 → 3 fields). The conditional pair W20/W21 keeps the single
[D] `hOR` and is no longer a registered witness. `#print axioms` on both headlines:
`[propext, Classical.choice, Quot.sound]`.
