# Plumbing-layer spec-citation audit

**What this is.** `docs/witness-statement-audit.md` classified every premise of the
registered witnesses and tagged a set of them **[P] model-plumbing contract** — fields that
pin an abstract or uninterpreted model function (`Externals`, the FFG selector state, the
FCR store caches) against the pinned consensus spec. That audit did *not* ground them in
spec text. This document does: for each [P] field on the weak trajectory headlines'
premise surface it gives the Lean statement, the pinned-spec origin verbatim, and a
faithfulness verdict.

**Read `docs/witness-statement-audit.md` first** for the inventory and the [S]/[P]/[B]/[D]
key. Rows A, A1, A2, A3, G, H, J, K, M-c, M-f, N, O, O′ there are the subject matter.

> **Post-audit status (2026-09-16).** Every flag of §13 except **P-6** is now
> **RESOLVED**; P-6 awaits the owner. Each fix was a deletion, a premise weakening or a
> docstring disclosure — no witness conclusion changed by a byte and no premise surface
> grew anywhere.
> * `ed9af80` — **P-2**: the duplicate field `justified_checkpoint_cached` is deleted;
>   `justified_cached` is kept and absorbs its provenance paragraph.
>   `JustificationInterface` 15 → **14** fields.
> * `3fc11bc` — **P-5**: `checkpoint_known` gains the `WithinHorizon` guard every other
>   field of the record carries (a strict weakening); ~25 consumers rewired mechanically.
> * `445d63d` — **P-10**: `hanchorExact` (row L) is *derived* from `hboundary` (row E) on
>   the weak headlines by the pre-existing `acceptedAnchorExact_of_trajectory`, the same
>   route the strong fold already used. Rows E and L are now demonstrably not independent.
> * `bfc03a3` — **P-3, P-4, P-7, P-8**: docstring disclosures, no semantic change.
> * `dab205e` — **bonus, row N**: `PostAnchorHonestVoteTargetWalkDomain` is derived from
>   `SelectedMarginAssumptions` + `hanchor` + `hboundary` and dropped from the weak
>   headlines. See §14.
> * The **P-9** Lean docstring was already corrected by `edf357f` (the single-synchrony
>   refactor): `AcceptedHistoricalA32CallSupplier.lean:~323` now reads "the first five
>   fields" of a six-field record and states outright that there is no `delivery_lookahead`
>   field. Only the **P-1** count drift in `witness-statement-audit.md` remained, and is
>   fixed there.
>
> Rows and sections below are annotated in place; nothing else was re-audited.

## 0. Sources, snapshot, and method

**Pinned spec.** consensus-specs `30aa65fc21cf7f7c7dd1f7d6b686d0250462d04f`, via the blob
SHAs in `spec_source/manifest.json`. All four files were extracted by blob SHA and their
sha256 digests verified byte-for-byte against the manifest:

| file | blob | sha256 verified |
|---|---|---|
| `specs/phase0/fast-confirmation.md` | `5d85a380…` | ✅ `1c3a9839…` |
| `specs/phase0/fork-choice.md` | `275b3699…` | ✅ `050733d8…` |
| `specs/phase0/beacon-chain.md` | `3c8de972…` | ✅ `88958710…` |
| `specs/phase0/validator.md` | `c53cc215…` | ✅ `cd40680c…` |

Line numbers below are 1-based into those exact blobs.

**Lean snapshot.** Read-only, at `centaur/weak-synchrony-202609150824` @ `18d6eab`
**plus the uncommitted working-tree edits present at 2026-09-16 20:16:48 UTC**. Another
agent is mid-refactor (the `HorizonVoteDeliveryLookahead`→`Synchrony.attestation_delivery`
merge), touching thirteen files. Every Lean line number here is against that snapshot;
where a record differs from what `witness-statement-audit.md` records, §12 says so.
Audited-file digests: `Assumptions.lean` `78acfc3e…`, `FFGStateSemantics.lean`
`ada28d60…`, `TheoremStatements.lean` `9c19d9c0…`, `ExactCheckpointLinks.lean`
`39698f39…`, `WeakTrajectorySafety.lean` `9e11694e…`, `Handlers.lean` `2a98cf52…`.

**Verdict key.**
- **FAITHFUL** — direct transcription of the quoted spec text; reading the quote is
  reading the field.
- **FAITHFUL-WITH-NOTE** — transcription plus an abstraction, summarization or
  idealization step, spelled out in the row.
- **UNMOTIVATED/CANNOT-LOCATE** — no spec text grounds it. Flagged in §12.
- **DELTA** — a rule change we introduced (certificates, certified banking). Motivated by
  the thread-agreed design, not by transcription; said so explicitly.

---

## 1. `ExactPrefixAcceptedFFGSemantics` (row A) — `Model/FFGStateSemantics.lean:926`

Three fields: `anchor` (`:927`), `state` (`:928`), `coherence` (`:929`). `anchor` and
`state` are *data*; the contracts are the state's 24 fields and the coherence's 12.

### 1.1 `state : AcceptedChainFFGState` — `:686`–`:734`, **24 fields**

Eight of the 24 fields are data — the validity oracle, the inclusion relation, the
`formed` predicate and the five selectors, which are the model's names for five
beacon-state / store reads:

| field | Lean (`:line`) | pinned-spec origin | verdict |
|---|---|---|---|
| `attestationValidity` | `:688` | oracle slot; pinned by `coherence.attestation_validity` (§1.2) | FAITHFUL |
| `includedAttestations` | `:689` | block bodies are projected out of the model `BeaconBlock`, so inclusion is re-supplied as a relation with evidence (`IncludedAttestationEvidence`, `:90`). That evidence is a near-verbatim transcription of `process_attestation` (beacon-chain.md:2004): `assert data.target.epoch == compute_epoch_at_slot(data.slot)` → `target_epoch` (`:102`); `assert data.slot + MIN_ATTESTATION_INCLUSION_DELAY <= state.slot` → `slot_before_carrier` (`:101`); `committee = get_beacon_committee(state, data.slot, data.index)` + `assert len(attestation.aggregation_bits) == len(committee)` → `attesters_in_committee` (`:112`); `assert is_valid_indexed_attestation(state, get_indexed_attestation(state, attestation))` → `valid` (`:99`); `assert data.source == state.current_justified_checkpoint` → `target_descends_source` (`:110`) | FAITHFUL-WITH-NOTE (block-body projection restored as a relation) |
| `formed` | `:692` | see §1.3 — the certificate **DELTA** | DELTA |
| `C` | `:693` | fast-confirmation.md:170 `def get_checkpoint_for_block(store, block_root, epoch) -> Checkpoint: return Checkpoint(epoch=epoch, root=get_checkpoint_block(store, block_root, epoch))` | FAITHFUL |
| `GJ` | `:694` | `state.current_justified_checkpoint`, the value `on_block` hands to `update_checkpoints` (fork-choice.md:941) | FAITHFUL |
| `GU` | `:695` | `compute_pulled_up_tip` (fork-choice.md:726): `state = store.block_states[block_root].copy(); process_justification_and_finalization(state); store.unrealized_justifications[block_root] = state.current_justified_checkpoint` | FAITHFUL |
| `GF` | `:696` | `state.finalized_checkpoint` in the same `update_checkpoints` call | FAITHFUL |
| `GUF` | `:697` | `compute_pulled_up_tip`'s `update_unrealized_checkpoints(store, …, state.finalized_checkpoint)` | FAITHFUL |

The 16 laws:

- `checkpoint_epoch` (`:698`) `(C r e).epoch = e`. Literally the constructor
  `Checkpoint(epoch=epoch, root=…)` of `get_checkpoint_for_block`. **FAITHFUL.**
- `formed_carrier_accepted` (`:699`), `formed_evidence` (`:701`) — domain scoping and
  evidence packaging for the accepted-prefix restriction. No spec analogue is claimed;
  they *narrow* the relation. **FAITHFUL-WITH-NOTE** (model-internal scoping, not a claim
  about a pinned function).
- `gj_mem`/`gu_mem`/`gf_mem`/`guf_mem` (`:704`,`:706`,`:708`,`:710`) — every selector value
  at an accepted root is carried by some ancestor. Origin: `weigh_justification_and_finalization`
  (beacon-chain.md:1509) only ever assigns `Checkpoint(epoch=…, root=get_block_root(state, …))`,
  i.e. a checkpoint on the state's *own* chain. **FAITHFUL-WITH-NOTE** (chain-locality of
  `get_block_root` summarized as an ancestor-carrier existential).
- `gj_anchor_or_before` (`:712`) `GJ r = anchor ∨ (GJ r).epoch < epoch(b.slot)`. This is
  the process-epoch-before-slot-increment order, quoted:
  ```python
  while state.slot < slot:
      process_slot(state)
      # Process epoch on the start slot of the next epoch
      if (state.slot + 1) % SLOTS_PER_EPOCH == 0:
          process_epoch(state)
      state.slot = Slot(state.slot + 1)
  ```
  (beacon-chain.md:1396). The last `process_epoch` before a block at slot `s` runs with
  `state.slot = compute_start_slot_at_epoch(epoch(s)) - 1`, so `get_current_epoch(state) =
  epoch(s) - 1`, and `weigh_…` can only justify `previous_epoch` or `current_epoch` of
  *that* state — both `< epoch(s)`. `process_block` (beacon-chain.md:1876) never writes
  `current_justified_checkpoint`. The `= anchor` disjunct covers the no-boundary-crossed
  case, where the value is inherited from `get_forkchoice_store`. **FAITHFUL-WITH-NOTE**
  (two-step derivation, not one quoted line).
- `gj_max` (`:714`), `gu_max` (`:717`) — maximality. Origin: `weigh_…` tests previous then
  current, the later assignment overwriting; `update_checkpoints` (fork-choice.md:490) then
  keeps the max: `if justified_checkpoint.epoch > store.justified_checkpoint.epoch:`.
  **FAITHFUL-WITH-NOTE** (sequential-overwrite semantics stated as a `≤` law).
- `au_epoch_le_block` (`:720`) — no formed checkpoint on an accepted block's chain exceeds
  the block's epoch. Origin: `assert data.target.epoch in (get_previous_epoch(state),
  get_current_epoch(state))` and `assert data.slot + MIN_ATTESTATION_INCLUSION_DELAY <=
  state.slot` in `process_attestation`. **FAITHFUL-WITH-NOTE.**
- `gf_evidence` (`:723`), `guf_evidence` (`:726`) — `GF`/`GUF` is the anchor or carries an
  `IncludedCertifiedFinalized` (`:242`), whose `child_epoch : child.epoch = c.epoch + 1`
  admits only a **consecutive** finalizing link. Checked against all four branches of
  `weigh_justification_and_finalization`: `bits[1:4]`/`bits[1:3]`/`bits[0:3]`/`bits[0:2]`
  each finalize a checkpoint that has a justified checkpoint at epoch+1 using it as source
  — the spec states the source relation only in its inline comments ("the 2nd using the
  4th as source"), the `justification_bits` carry it. **FAITHFUL-WITH-NOTE** (k-finality
  collapsed to its gap-1 witness; correct in every branch, but read off comments).
- `gf_epoch_le_gj` (`:729`), `guf_epoch_le_gu` (`:731`), `gf_epoch_le_guf` (`:733`).
  Origin: every finalization branch assigns `state.finalized_checkpoint` from
  `old_previous_justified_checkpoint`/`old_current_justified_checkpoint`, which the same
  function has already superseded on the justification side.
  **FAITHFUL-WITH-NOTE** (ordering read off the assignment order).

### 1.2 `coherence : AcceptedFFGTransitionCoherence` — `:870`, extending `:836`, **12 fields**

| field | Lean (`:line`) | pinned-spec origin | verdict |
|---|---|---|---|
| `attestation_validity` | `:839` | `ext.is_valid_indexed_attestation` = the `is_valid_indexed_attestation` of on_attestation's `assert is_valid_indexed_attestation(target_state, indexed_attestation)` (fork-choice.md:964) | FAITHFUL |
| `genesis_gj` | `:841` | `get_forkchoice_store` (fork-choice.md:215): `block_states={anchor_root: copy(anchor_state)}` | FAITHFUL |
| `genesis_gf` | `:843` | same line | FAITHFUL |
| `genesis_gu`, `genesis_guf` | `:845`,`:848` | `compute_pulled_up_tip` applied to the anchor state | FAITHFUL |
| `genesis_unrealized_justification` | `:851` | `get_forkchoice_store`: `unrealized_justifications={anchor_root: justified_checkpoint}` | **FAITHFUL-WITH-NOTE — §13 P-3, disclosed in the field docstring by `bfc03a3`.** The pinned initializer stores the *un-pulled* checkpoint; combined with `genesis_gu` this field demands `pjf(anchor_state).current_justified_checkpoint = Checkpoint(anchor_epoch, anchor_root)`, which `get_forkchoice_store` does not establish |
| `transition_gj`, `transition_gf` | `:853`,`:856` | `on_block` (fork-choice.md:905): `state_transition(state, signed_block, …)` then `store.block_states[block_root] = state` | FAITHFUL |
| `transition_gu`, `transition_guf` | `:859`,`:863` | `compute_pulled_up_tip(store, block_root)`, the last line of `on_block` | FAITHFUL |
| `checkpoint_of_known` | `:874` | `get_checkpoint_for_block` → `get_checkpoint_block` (fork-choice.md:295) → `get_ancestor` (`:269`) | FAITHFUL-WITH-NOTE: the semantic `C` is a global function of (root, epoch) while `get_checkpoint_block` is store-relative; the field asserts store-independence over causal stores. Sound because `get_ancestor` is a pure walk over `store.blocks`, which is monotone along the execution |
| `au_checkpoint_of_known` | `:877` | same | FAITHFUL-WITH-NOTE (same abstraction) |

### 1.3 The certificate machinery — **DELTA**

`IncludedSupermajorityLink` (`:206`), `IncludedCertifiedJustified` (`:230`),
`IncludedCertifiedFinalized` (`:242`), `AcceptedFormedCheckpointEvidence` (`:350`) and the
`formed` field they support are **not** transcriptions of a pinned function. The pinned
spec carries justification in `state.justification_bits` + `current_justified_checkpoint`;
we re-present the same content as an inductive chain of ≥2/3 links from the trusted anchor,
carrier-local (votes must be *included in block bodies on this chain*, not merely gossiped).
The arithmetic is the spec's: `supermajority : 2 * E.total_active ≤ 3 * E.weight signers`
(`:226`) is `weigh_justification_and_finalization`'s
`if current_epoch_target_balance * 3 >= total_active_balance * 2` cross-multiplied.
**Motivation is design, agreed in-thread (certificates / certified banking), not
transcription.** The transcription obligation lands on `AcceptedFFGSelectorCoherence`
(§1.2), which ties the certificate-side selectors back to the actual post-states.

---

## 2. `JustificationInterface` — `Spec/TheoremStatements.lean:82`, **15 fields**

> **Count correction.** The statement audit records 13 (from 15). The record had **15** at
> audit time; `8b05b67` deleted two fields from **17**. Verified: `git show 8b05b67^:…`
> yields 17 fields, the audited snapshot 15. §13 P-1.
>
> **Since `ed9af80` (P-2) the record has 14 fields**: `justified_checkpoint_cached` is
> gone. Row 12 below is struck; row 3 `justified_cached` carries its content.

| # | field (`:line`) | pinned-spec origin | verdict |
|---|---|---|---|
| 1 | `justified_unique` `:86` | Casper accountable safety. **Not in the pinned markdown.** The four files define the slashing *conditions* (`is_slashable_attestation_data`, `process_attester_slashing`, fork-choice.md:977 `on_attester_slashing`) and the `CONFIRMATION_BYZANTINE_THRESHOLD = 25` budget (fast-confirmation.md:80) that make the theorem's hypothesis hold, but never state the theorem | FAITHFUL-WITH-NOTE ([S] consumed theorem; grounded in the slashing rules, not transcribed) |
| 2 | `observed_justified_cached` `:95` | fast-confirmation.md:272 / :280 — `get_previous_balance_source`/`get_current_balance_source` do the unguarded dict read `store.checkpoint_states[fcr_store.*_observed_justified_checkpoint]`; the keys are written only by `on_attestation`'s `store_target_checkpoint_state` (fork-choice.md:817) | FAITHFUL-WITH-NOTE (python `KeyError`-freedom made an explicit premise) |
| 3 | `justified_cached` `:105` | fork-choice.md:358 `def get_weight(store, node): state = store.checkpoint_states[store.justified_checkpoint]` | FAITHFUL-WITH-NOTE (same) |
| 4 | `finalized_justified_ancestry` `:113` | `weigh_…` assigns `finalized_checkpoint` from `old_*_justified_checkpoint`, on the same chain; consumed by `filter_block_tree`'s `correct_finalized` (fork-choice.md:430) | FAITHFUL-WITH-NOTE ([S] Casper) |
| 5 | `justified_requires_targets` `:126` | `if previous_epoch_target_balance * 3 >= total_active_balance * 2` / `if current_epoch_target_balance * 3 >= …` (beacon-chain.md:1509ff) | FAITHFUL-WITH-NOTE: the spec's inequality is over balances **recorded in the state**; the Lean quantifies over attestations **observable in honest schedules**, adding the network-observability half |
| 6 | `observed_justified` `:144` | fast-confirmation.md:94 — verbatim field doc: *"`current_epoch_observed_justified_checkpoint`: a justified checkpoint that has been observed by all honest nodes at the beginning of the current epoch assuming synchrony"* | **FAITHFUL** (direct transcription of normative field documentation) |
| 7 | `unrealized_justified` `:156` (disclosed in-docstring by `bfc03a3`, §13 P-4) | fast-confirmation.md:97 — but that field's doc reads *"`previous_epoch_greatest_unrealized_checkpoint`: a greatest unrealized justified checkpoint at the start of the last slot of the previous epoch **according to a local view**"* | FAITHFUL-WITH-NOTE — **§13 P-4**: the spec documents cross-view propagation only for the *observed* fields; this asserts it one rotation upstream, where the spec says "local view" |
| 8 | `greatest_unrealized_cached` `:170` | `update_fast_confirmation_variables` (fast-confirmation.md:805) rotates the checkpoint into `*_observed_*` **without re-keying** `checkpoint_states`; `get_previous_balance_source` then reads it as a key | FAITHFUL-WITH-NOTE (gap the pinned rotation leaves open, supplied explicitly; the docstring says exactly this) |
| 9 | `checkpoint_known` `:179` | `on_block`'s `finalized_checkpoint_block = get_checkpoint_block(store, block.parent_root, store.finalized_checkpoint.epoch)` + `assert store.finalized_checkpoint.root == finalized_checkpoint_block`; `get_filtered_block_tree`'s `base = store.justified_checkpoint.root` (fork-choice.md:448) | FAITHFUL-WITH-NOTE — **§13 P-5 RESOLVED (`3fc11bc`)**: it was the one field of the fifteen with no `WithinHorizon` guard; it now carries one, like every other field |
| 10 | `justified_ancestry` `:188` | as #1 | FAITHFUL-WITH-NOTE ([S]) |
| 11 | `finalized_descent` `:201` | fork-choice.md:171 Store doc: *"`finalized_checkpoint`: the highest known finalized checkpoint"*, + `update_checkpoints`' monotone guard | FAITHFUL-WITH-NOTE ([S] cross-store; the spec's monotonicity is per-store only) |
| ~~12~~ | ~~`justified_checkpoint_cached` `:214`~~ | — | **DELETED (`ed9af80`, §13 P-2)**: it was mechanically α-equal to field #3 `justified_cached` (`:105`), which now carries its docstring content |
| 13 | `observed_checkpoint_known` `:224` | fast-confirmation.md:94 for the third conjunct; `compute_pulled_up_tip` writes `unrealized_justifications` only for known `block_root`s for the first two | FAITHFUL-WITH-NOTE (cross-store knownness is a synchrony consequence; the spec asserts nothing cross-store) |
| 14 | `justified_descends` `:245` | fork-choice.md:394 `filter_block_tree` keeps a branch when `voting_source.epoch == store.justified_checkpoint.epoch or voting_source.epoch + 2 >= current_epoch`; `get_head` (`:473`) then walks `get_filtered_block_tree` from `store.justified_checkpoint.root` | **UNMOTIVATED/CANNOT-LOCATE** as stated — §13 P-6. The field asserts the head *descends every checkpoint justified above the store's realized justified epoch*. `filter_block_tree` prunes branches whose voting source is stale, but nothing in the pinned fork choice makes the head descend a checkpoint that is not the filter base. The docstring calls it "the justification-friendliness of LMD-GHOST the fork-choice design guarantees" — a design intuition, not spec text |
| 15 | `justified_block_boundary` `:259` | `get_checkpoint_block`: `epoch_first_slot = compute_start_slot_at_epoch(epoch); return get_ancestor(store, node, epoch_first_slot).root`, and `get_ancestor` (`:269`) returns a node with `block.slot <= slot` | FAITHFUL-WITH-NOTE (the "honest targets never trail the justified epoch" half comes from validator.md's FFG-vote construction, not from the walk) |

---

## 3. `Phase0SourceCoherence` (row G) — `Proof/FFGSourceCoherence.lean:64`

| field | Lean | origin | verdict |
|---|---|---|---|
| `process_slots_current_justified` | `:65` | `process_slots`' loop: `if (state.slot + 1) % SLOTS_PER_EPOCH == 0: process_epoch(state)`. Within one epoch the boundary test never fires, and `process_slot` (beacon-chain.md:1407) writes only `state_roots`/`block_roots`/`latest_block_header` | **FAITHFUL** |
| `state_transition_current_justified` | `:71` | `state_transition` = `process_slots` then `process_block`; `process_block(state, block)` = `process_block_header`, `process_randao`, `process_eth1_data`, `process_operations` (beacon-chain.md:1447) — none writes `current_justified_checkpoint`; `process_attestation` only appends `PendingAttestation`s | FAITHFUL-WITH-NOTE (neutrality of `process_block` is by inspection of the call list, not a quoted assertion) |

## 4. `Phase0BoundarySourceCoherence` (row H) — `Proof/CurrentTargetCertificateRealization.lean:57`

| field | Lean | origin | verdict |
|---|---|---|---|
| `process_slots_current_justified` | `:59` | first boundary crossed: `process_epoch(state)` runs with `state.slot = last slot of the starting epoch`, so `get_current_epoch(state)` equals `st`'s epoch and the attestation pools `process_slot` leaves untouched are `st`'s — hence `pjf` at the boundary = `pjf(st)` on the justification fields | FAITHFUL-WITH-NOTE, two-part: (i) the first-boundary equality above; (ii) **later empty boundaries are idempotent** — with no new blocks `process_participation_record_updates` rotates current→previous, so the next `weigh_…` re-justifies the *same* checkpoint `Checkpoint(epoch=previous_epoch, root=get_block_root(state, previous_epoch))`. The docstring states (ii) as "Additional empty epochs cannot create a new justified checkpoint"; the spec does not state it |
| `state_transition_current_justified` | `:66` | same, plus `process_block` neutrality as in §3 | FAITHFUL-WITH-NOTE (same) |

Together these two records are, as their docstrings say, the phase0 content of the paper's
Definition 7 source selector — which the pinned spec also computes, in
`get_voting_source` (fork-choice.md:378): `if current_epoch > block_epoch: return
store.unrealized_justifications[block_root] else: return
head_state.current_justified_checkpoint`. That is the `GU`/`GJ` split verbatim.

---

## 5. `PaperA32Inclusion` (row I) — `Model/FFGStateSemantics.lean:1188` → `…Core:1136`

Paper Assumption 3.2 of arXiv:2405.00549, instantiated over the executable model. The
pinned spec incorporates the paper by reference (fast-confirmation.md:57): *"The research
paper for this rule can be found [here](https://arxiv.org/abs/2405.00549)."*
**FAITHFUL-WITH-NOTE**: motivated by the paper the spec cites, not by any spec function; it
is [S] in the statement audit and is correctly classified there.

## 6. `AcceptedEpochCheckpointProjection` (row J) — `Model/ExactCheckpointLinks.lean:31`

| field | Lean | origin | verdict |
|---|---|---|---|
| `checkpoint_root_accepted` | `:35` | `get_checkpoint_block` returns `get_ancestor(store, node, epoch_first_slot).root` — an ancestor of a known block | FAITHFUL |
| `checkpoint_comp` | `:37` | `get_ancestor` is the recursive walk `if block.slot > slot: return get_ancestor(store, parent, slot); return node` — so `get_ancestor(get_ancestor(r, t), s) = get_ancestor(r, s)` for `s ≤ t` | FAITHFUL (composition is the walk's transitivity) |

The `anchor.epoch ≤ e` guard on both fields is [B] scoping: below the trusted anchor the
store holds no blocks, so the walk is undefined. **FAITHFUL-WITH-NOTE** for the guard.

## 7. `ExactLinkValidity` (row K) — `Model/ExactCheckpointLinks.lean:153` → `:128`

| field | Lean | origin | verdict |
|---|---|---|---|
| `carrier_accepted` | `:134` | domain scoping onto accepted roots | FAITHFUL-WITH-NOTE (model-internal) |
| `endpoints_on_carrier` | `:139` | **target half**: `validate_on_attestation`'s `assert target.root == get_checkpoint_block(store, attestation.data.beacon_block_root, target.epoch)` (fork-choice.md:786ff) — the LMD/FFG consistency gate. **source half**: `process_attestation`'s `assert data.source == state.current_justified_checkpoint` / `== state.previous_justified_checkpoint` (beacon-chain.md) — the source is the carrier chain's own justified checkpoint | FAITHFUL-WITH-NOTE: two distinct asserts in two different files, on two different objects (fork-choice store vs. block-processing state), combined into one carrier-local equation |

## 8. `AcceptedRealizedFinalizationDelay` (row F) — `Proof/AcceptedFinalizationTiming.lean:211`

*Statement.* For every accepted block transition, the post-state's `finalized_checkpoint`
is the anchor or `finalized.epoch + 2 ≤ compute_epoch_at_slot(block.slot)`.

*Origin.* The tightest of the four finalization branches is
`if all(bits[0:2]) and old_current_justified_checkpoint.epoch + 1 == current_epoch:
state.finalized_checkpoint = old_current_justified_checkpoint`, i.e. `finalized.epoch =
current_epoch - 1` at the boundary where `process_epoch` runs. By the `process_slots`
loop quoted in §1.1 that boundary has `get_current_epoch(state) = epoch(block.slot) - 1`,
so `finalized.epoch ≤ epoch(block.slot) - 2`. **FAITHFUL-WITH-NOTE** — arithmetic over two
quoted fragments; the docstring's "exactly the reachable-post-state consequence of Phase0's
process-epoch-before-slot-increment order" is accurate.

---

## 9. `ExternalsCoherence` (row M-c) — `Model/Assumptions.lean:329`, **14 fields**

| field | Lean | origin | verdict |
|---|---|---|---|
| `process_slots_slot` | `:331` | `while state.slot < slot: … state.slot = Slot(state.slot + 1)` | FAITHFUL |
| `process_slots_registry` | `:332` | — | **FAITHFUL-WITH-NOTE / §13 P-7, disclosed in the field's own docstring by `bfc03a3`**: *false* of the pinned function across an epoch boundary. `process_epoch` calls `process_registry_updates`, `process_slashings` and `process_effective_balance_updates`, all of which mutate `state.validators`. Motivated only by the static-set idealization ([S] `StaticValidatorSet`), which this field's docstring — unlike `state_transition_registry`'s — does not mention |
| `state_transition_registry` | `:338` | same idealization; **disclosed** in the docstring ("no deposits/exits in the window — the static-set idealization") | FAITHFUL-WITH-NOTE |
| `state_transition_slot` | `:336` | `state_transition` calls `process_slots(state, block.slot)`; `process_block` does not move the slot | FAITHFUL |
| `state_transition_pre_slot_lt` | `:344` | `def process_slots(state, slot): assert state.slot < slot` | **FAITHFUL** (single quoted assert) |
| `state_transition_checkpoint_epoch` | `:351` | `weigh_…` assigns checkpoints at `previous_epoch`/`current_epoch` of the processing state, all `≤ epoch(block.slot)`; `finalized` from the older justified values | FAITHFUL-WITH-NOTE (needs the pre-state invariant on the no-boundary path) |
| `pjf_checkpoint_epoch` | `:360` | same; plus the early return `if get_current_epoch(state) <= GENESIS_EPOCH + 1: return` preserves whatever the pre-state carried | FAITHFUL-WITH-NOTE (same) |
| `committees_agree` | `:366` (disclosed in-docstring by `bfc03a3`, §13 P-8) | fast-confirmation.md:230 normative note on `get_slot_committee`: *"This function returns the committee for a specific slot. It MUST support committees of epochs starting from `current_epoch - 2`."*, over `shuffling_source = store.block_states[head]`; validator.md:257 `MAX_SEED_LOOKAHEAD` and validator.md:325 "Lookahead" | FAITHFUL-WITH-NOTE — **§13 P-8**: the spec bounds the guarantee to `current_epoch - 2`; the Lean asserts exact ground-truth agreement for **every** in-horizon slot, with no window |
| `honest_attestation_valid` | `:374` | `is_valid_indexed_attestation` (beacon-chain.md:765): sorted-unique non-empty indices + `bls.FastAggregateVerify` | FAITHFUL-WITH-NOTE (singleton indices are trivially sorted-unique; BLS completeness on honestly-signed data. The restriction to actually-signed data is a deliberate weakening, disclosed) |
| `valid_attestation_honest` | `:381` | the same function's `bls.FastAggregateVerify` read as unforgeable | FAITHFUL-WITH-NOTE ([S]; cryptographic soundness, not spec text) |
| `valid_attestation_committee` | `:390` | `def get_attesting_indices(state, attestation): committee = get_beacon_committee(state, attestation.data.slot, attestation.data.index); return {index for i, index in enumerate(committee) if attestation.aggregation_bits[i]}` (beacon-chain.md:1192) | **FAITHFUL** — the constraint `get_indexed_attestation` imposes, restored as a field because the model absorbed the indexed projection into the wire object (docstring says so) |
| `committee_assignment_unique` | `:396` | `get_beacon_committee` calls `compute_committee(indices=get_active_validator_indices(state, epoch), …, index=(slot % SLOTS_PER_EPOCH) * committees_per_slot + index, count=committees_per_slot * SLOTS_PER_EPOCH)` — one partition of the epoch's active set across all `slots × committees`; `get_committee_assignment` (validator.md:283) correspondingly returns a single slot | FAITHFUL-WITH-NOTE (disjointness is a property of `compute_committee`'s partition, never asserted) |
| `committee_coverage` | `:403` | same partition, over `get_active_validator_indices(state, epoch)`; `get_committee_assignment` returns `None` only for non-members | FAITHFUL-WITH-NOTE (same) |
| `committee_members_active` | `:411` | `indices=get_active_validator_indices(state, epoch)` with `epoch = compute_epoch_at_slot(slot)` | FAITHFUL |

## 10. Handler contracts inside the floor

These are **definitions**, not premises: `E.store` is the fold of these handlers over the
schedule, so they are discharged by construction and appear on the premise surface only as
the meaning of the store. They are nonetheless part of the plumbing layer's faithfulness.

- **The parent-known contract** (the one cited in-thread as correct) — `Model/Handlers.lean:354`:
  ```lean
  if block.parent_root ∉ store.block_roots then none
  ```
  transcribing fork-choice.md:908:
  ```python
  # Parent block must be known
  assert block.parent_root in store.block_states
  ```
  The `block_states` → `block_roots` substitution is disclosed at `Handlers.lean:326-328`
  ("`blocks` and `block_states` share their key set by construction — design decision 14"),
  and holds of `get_forkchoice_store` (`Handlers.lean:470`, both maps keyed at
  `anchor_root`) and of `on_block`'s paired writes. **FAITHFUL.**
- `on_block`'s remaining asserts — `get_current_slot(store) >= block.slot` (`:358`),
  `block.slot > finalized_slot` (`:362`), `store.finalized_checkpoint.root ==
  finalized_checkpoint_block` (`:367`), `state_transition` (`:371`), then the
  `blocks`/`block_states` writes, `record_block_timeliness`, `update_proposer_boost_root`,
  `update_checkpoints`, `compute_pulled_up_tip` (`:384`–`:391`) — line-for-line against
  fork-choice.md:905–946. **FAITHFUL.**
- `validate_on_attestation` (`:186`) — all seven asserts of fork-choice.md:786 transcribed,
  in order. **FAITHFUL.**
- `on_attestation` (`:410`) — `validate` → `store_target_checkpoint_state` → validity →
  `update_latest_messages`, matching fork-choice.md:950. One **documented deviation**: on
  the validity-failure path the model discards `store_target_checkpoint_state`'s write,
  which the reference python leaves in place. Motivated by normative text, fork-choice.md:94:
  *"Invalid calls to handlers must not modify `store`."* **FAITHFUL-WITH-NOTE** (deviation
  from the reference implementation *towards* the normative sentence; disclosed at
  `Handlers.lean:393-401`).
- `balance_floor` — `Proof/WeakTrajectorySafety.lean:199`,
  `cfg.effective_balance_increment ≤ E.weight (E.currentTargetAnchorActive cfg)`. Origin:
  `get_total_balance` (beacon-chain.md:1130-1133): *"``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum
  to avoid divisions by zero"* — `max(EFFECTIVE_BALANCE_INCREMENT, sum(...))`. The model's
  ground-truth `E.weight` is a plain sum, so this field says the `max` is not on its
  artificial branch. **FAITHFUL-WITH-NOTE** ([B]; excludes a spec-artifact branch).
- **The call supplement** `Execution.AcceptedHistoricalA32CompletedPrefixCallSupplement`
  (`WeakTrajectorySafety.lean:196`) now carries **3** fields — `phase0_source` (§3),
  `phase0_boundary_source` (§4), `balance_floor` — not the 4 the statement audit records.
  `delivery_lookahead` was absorbed into `PaperSafetySynchrony.attestation_delivery` by the
  concurrent working-tree edit. §13 P-9.
- The full contract `AcceptedHistoricalA32CompletedPrefixCallAssumptions`
  (`AcceptedHistoricalA32CallSupplier.lean:344`) is correspondingly **6** fields; its
  docstring at `:326` still describes a `delivery_lookahead` field that no longer exists.

## 11. `TrustedAnchorBoundaryAligned` and the anchor equalities

**Classification: the checkpoint-sync trust boundary.** The spec object mirrored is
`get_forkchoice_store(anchor_state, anchor_block)` (fork-choice.md:215) and its docstring:
*"The provided anchor-state will be regarded as a trusted state, to not roll back beyond.
This should be the genesis state for a full client."*

- `hanchor : B.anchor = E.genesis_store.justified_checkpoint` (row D, [B]). Mirrors
  `anchor_epoch = get_current_epoch(anchor_state)`;
  `justified_checkpoint = Checkpoint(epoch=anchor_epoch, root=anchor_root)`. **FAITHFUL.**
- `TrustedAnchorBoundaryAligned` (row E) — `Proof/FFGGlobalCheckpointTrajectory.lean:623`:
  `(E.genesis_store.blocks anchor.root).slot ≤ compute_start_slot_at_epoch cfg anchor.epoch`.
  **FAITHFUL-WITH-NOTE / §13 P-10 — RESOLVED (`445d63d`).** `get_forkchoice_store` sets `anchor_epoch =
  get_current_epoch(anchor_state)`, which gives the *converse* inequality
  `compute_start_slot_at_epoch(anchor.epoch) ≤ anchor_block.slot`. The two together force
  the anchor block to sit exactly at its epoch boundary — a real restriction on
  checkpoint-sync anchors, which the pinned initializer explicitly permits to be any
  trusted state.
- ~~`hanchorExact : B.anchor = B.state.C anchor.root anchor.epoch` (row L, [B]).~~ Given
  §1.1's `C` ≙ `get_checkpoint_for_block`, this is `get_ancestor(anchor_root,
  start_slot(anchor.epoch)) = anchor_root`, i.e. the same boundary-alignment fact expressed
  through the walk. **RESOLVED (`445d63d`): no longer a premise anywhere.** It is *derived*
  from `B` + trajectory + `hanchor` + `hboundary` by
  `Execution.acceptedAnchorExact_of_trajectory` (`Proof/AcceptedActualFCRCommon.lean:26`),
  which reflects the semantic `C` through `AcceptedFFGTransitionCoherence.checkpoint_of_known`
  at the genesis store. The strong headlines already did this; the weak headlines now do
  too. Rows E and L are therefore demonstrably one premise, not two.

---

## 12. Summary table

| field / record | spec anchor | verdict |
|---|---|---|
| `…FFGSemantics.state` selectors `C/GJ/GU/GF/GUF`, `checkpoint_epoch` | `get_checkpoint_for_block`; `on_block`'s `update_checkpoints`; `compute_pulled_up_tip` | FAITHFUL ×6 |
| `attestationValidity`, `includedAttestations` | `process_attestation` asserts; `is_valid_indexed_attestation` | 1 FAITHFUL, 1 NOTE |
| `formed` + certificate machinery | — | DELTA |
| `formed_carrier_accepted`, `formed_evidence` | scoping | NOTE ×2 |
| `gj/gu/gf/guf_mem`, `gj_anchor_or_before`, `gj_max`, `gu_max`, `au_epoch_le_block`, `gf/guf_evidence`, 3 epoch orderings | `process_slots` loop; `weigh_justification_and_finalization`; `update_checkpoints` | NOTE ×13 |
| `AcceptedFFGSelectorCoherence` (10) | `get_forkchoice_store`; `on_block`; `compute_pulled_up_tip` | 9 FAITHFUL, 1 NOTE (P-3) |
| `checkpoint_of_known`, `au_checkpoint_of_known` | `get_checkpoint_block`/`get_ancestor` | NOTE ×2 |
| `JustificationInterface` (15 → **14** since `ed9af80`) | `get_weight`; balance-source reads; `weigh_…`; FCR store field docs | 1 FAITHFUL, 12 NOTE, 1 UNMOTIVATED (P-6); the duplicate (P-2) is deleted |
| `Phase0SourceCoherence` (2) | `process_slots` boundary test; `process_block` call list | 1 FAITHFUL, 1 NOTE |
| `Phase0BoundarySourceCoherence` (2) | same + participation-record rotation | NOTE ×2 |
| `PaperA32Inclusion` | arXiv:2405.00549, cited by fast-confirmation.md:57 | NOTE |
| `AcceptedEpochCheckpointProjection` (2) | `get_ancestor` transitivity | 2 FAITHFUL (+ NOTE on the anchor guard) |
| `ExactLinkValidity` (2) | `validate_on_attestation` target assert + `process_attestation` source assert | NOTE ×2 |
| `AcceptedRealizedFinalizationDelay` | `weigh_…` gap-1 branch + `process_slots` order | NOTE |
| `ExternalsCoherence` (14) | `process_slots`; `state_transition`; `get_attesting_indices`; `get_beacon_committee`; `get_slot_committee` note | 4 FAITHFUL, 10 NOTE (2 flagged: P-7, P-8) |
| handler contracts (`on_block` parent-known + 4 asserts, `validate_on_attestation`, `on_attestation`) | fork-choice.md:905/950/786 | 3 FAITHFUL, 1 NOTE |
| `balance_floor` | `get_total_balance` minimum | NOTE |
| `TrustedAnchorBoundaryAligned`, `hanchor`, ~~`hanchorExact`~~ | `get_forkchoice_store` | 1 FAITHFUL, 1 NOTE; `hanchorExact` derived and dropped (P-10, `445d63d`) |

**Counts as audited (fields, not records): FAITHFUL 28 · FAITHFUL-WITH-NOTE 52 · DELTA 1 ·
UNMOTIVATED/CANNOT-LOCATE 2** (`justified_descends`; `justified_checkpoint_cached` as a
distinct field). Total 83 plumbing fields examined.

**Counts after the fixes:** the duplicate is gone (`ed9af80`) and `hanchorExact` is derived
rather than assumed (`445d63d`), so **81** plumbing fields remain on the surface, with
exactly **one** UNMOTIVATED — `justified_descends`, P-6, which awaits the owner.

## 13. Flags

**P-1 — RESOLVED (doc-only, this commit) — field-count drift in `witness-statement-audit.md`.** `JustificationInterface` has
**15** fields, not 13 (`8b05b67` went 17 → 15). `AcceptedChainFFGState` has **24**, not 26.
`AcceptedFFGSelectorCoherence` has **10**, not 11. Documentation only; no premise changed.
*Resolution:* the rows in `witness-statement-audit.md` are corrected, and the counts are
re-verified mechanically against the environment (`getStructureFields`) rather than by
eye: `JustificationInterface` **14** (after P-2), `AcceptedChainFFGState` **24**,
`AcceptedFFGSelectorCoherence` **10**, `AcceptedFFGTransitionCoherence` **+2**,
`ExternalsCoherence` **14**, `SelectedMarginAssumptions` **9**,
`AcceptedHistoricalA32CompletedPrefixCallAssumptions` **6**, its supplement **3**,
`AcceptedActualFCRNextSlotSafetyAssumptions` **11**.

**P-2 — RESOLVED (`ed9af80`) — a literally duplicated premise field.** `JustificationInterface.justified_cached`
(`TheoremStatements.lean:105`) and `.justified_checkpoint_cached` (`:214`) are the **same
proposition** up to bound-variable renaming (verified mechanically: both normalize to
`∀ X ∈ E.honest, ∀ X : ℕ, E.WithinHorizon cfg X → (E.store cfg ext X X).justified_checkpoint
∈ (E.store cfg ext X X).checkpoint_state_keys`). One of the two should go; the premise
surface of W20–W23 currently carries it twice under different docstrings.
*Resolution:* `justified_checkpoint_cached` deleted; `justified_cached` kept and its
docstring extended with the deleted field's provenance paragraph and the fork-choice.md:358
`get_weight` citation. Three consumers rewired by renaming the projection
(`EdgeDynamics` ×2, `SpecAssumptions.toSelectedMarginAssumptions`). Record 15 → 14.

**P-3 — RESOLVED as a disclosure (`bfc03a3`) — the genesis unrealized-justification field over-constrains the pinned initializer.**
`AcceptedFFGSelectorCoherence.genesis_unrealized_justification` (`:851`) plus `genesis_gu`
(`:845`) jointly demand `pjf(anchor_state).current_justified_checkpoint =
Checkpoint(anchor_epoch, anchor_root)`. The pinned `get_forkchoice_store` stores the
**un-pulled** value: `unrealized_justifications={anchor_root: justified_checkpoint}`. The
conjunction is therefore an extra contract on `ext.process_justification_and_finalization`
at the anchor state, not a transcription of the initializer.
*Resolution:* no strict weakening was available (the field is read at the anchor root, which
is where the extra content lives), so the field's own docstring now states the over-constraint
verbatim and names it a companion of the checkpoint-sync trust boundary rather than a
transcription. No semantic change.

**P-4 — RESOLVED as a disclosure (`bfc03a3`) — cross-view propagation asserted where the spec says "local view".**
`JustificationInterface.unrealized_justified` (`:156`) asserts that an honest store's
unrealized justified checkpoint *and* its FCR store's
`previous_epoch_greatest_unrealized_checkpoint` are justified in every honest view from the
same slot on. fast-confirmation.md documents the all-honest-nodes property only for the two
`*_observed_justified_checkpoint` fields; the greatest-unrealized field's own documentation
says *"according to a local view"*.
*Resolution:* disclosed in the field's docstring, with both quotations (fast-confirmation.md:94
for the observed fields, :97 for the greatest-unrealized field) and the statement that the
cross-view step is taken one rotation upstream of the spec's own. No semantic change; the
field is consumed as a whole, so dropping either conjunct is not available as a weakening.

**P-5 — RESOLVED (`3fc11bc`) — one unguarded field.** `JustificationInterface.checkpoint_known` (`:179`) is the
only field of the fifteen stated without a `WithinHorizon` hypothesis; it claims
justified/finalized-root knownness at **every** second, including beyond the verification
horizon every other conclusion is scoped to.
*Resolution:* the field now reads `∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m → …`,
which is a strict weakening (the new field follows from the old by discarding a hypothesis).
Every consumer already had the horizon witness in context or derived it one line earlier;
`InterfaceRewire.justified_known_of_interface` / `.finalized_known_of_interface` gained the
same guard, four legacy `SpecAssumptions`-path lemmas took the horizon second they were
implicitly relying on, and `FindLatestSafety.safeFrom_find_latest_confirmed_descendant` kept
its signature by entering `safeFrom_of_headStep` first. No witness signature changed.

**P-6 — UNMOTIVATED: `JustificationInterface.justified_descends` (`:245`).** It asserts
that an honest store's `get_head` descends *every* checkpoint justified above that store's
realized justified epoch. No text in the four pinned files grounds this. `filter_block_tree`
(fork-choice.md:394) prunes branches by `voting_source.epoch + 2 >= current_epoch`, and
`get_filtered_block_tree` roots the walk at `store.justified_checkpoint.root` — neither
makes the head descend a *different, higher* justified checkpoint. The docstring's
justification is "the justification-friendliness of LMD-GHOST the fork-choice design
guarantees", which is a design intuition. This is the largest single unsupported step in
the plumbing layer and it sits on all four weak headlines via `hji`.

**P-7 — RESOLVED as a disclosure (`bfc03a3`) — `ExternalsCoherence.process_slots_registry` (`:332`) is false of the pinned
function.** `process_slots` calls `process_epoch`, which calls `process_registry_updates`,
`process_slashings` and `process_effective_balance_updates` — all of which write
`state.validators`. The field is the static-set idealization at the function level. Its
sibling `state_transition_registry` (`:338`) discloses exactly this in its docstring;
`process_slots_registry` does not, and says only "preserves the registry".
*Resolution:* the field now has its own docstring naming it the static-validator-set
idealization at the function level, listing the three `process_epoch` calls that falsify it
across a boundary, noting that it is exact within one epoch, and pointing at the [S]
assumption that licenses it. `process_slots_slot` keeps the transcription half with its
beacon-chain.md:1396 citation. No faithful weakening was trivially available (the model calls
`process_slots` across boundaries), so none was made.

**P-8 — RESOLVED as a disclosure (`bfc03a3`) — `ExternalsCoherence.committees_agree` (`:366`) exceeds the spec's own window.**
fast-confirmation.md:230 states the requirement as *"It MUST support committees of epochs
starting from `current_epoch - 2`"*. The Lean field asserts exact agreement with the
ground-truth committee for every in-horizon slot with no two-epoch window and no
`MAX_SEED_LOOKAHEAD` qualification. Sound under the static-registry idealization, but it is
a strengthening, not a transcription, of the quoted MUST.
*Resolution:* disclosed in the field's docstring, quoting fast-confirmation.md:230 verbatim
and stating that the extra window is licensed by the same static-set idealization (a fixed
active set makes the shuffling registry-determined, so `current_epoch - 2` stops binding).
No semantic change.

**P-9 — RESOLVED (`edf357f` for the Lean docstring; doc rows here) — the record moved under this audit.** `AcceptedHistoricalA32CompletedPrefixCall
Supplement` has **3** fields in the snapshot read (`WeakTrajectorySafety.lean:196`, md5
`9e11694e…`), not the 4 the *committed* statement audit records: `delivery_lookahead` was
merged into `PaperSafetySynchrony.attestation_delivery` by the concurrent uncommitted edit.
The working-tree `witness-statement-audit.md` has since been updated to 3 (row O′) and 6
(row O), so the two documents agree; but **the Lean docstring at
`AcceptedHistoricalA32CallSupplier.lean:326` still documents a `delivery_lookahead` field
that no longer exists** ("`delivery_lookahead` is the paper-synchrony boundary closure for
honest votes created inside the prefix", and "the first five fields" of a now-six-field
record). *Resolution:* re-read at `bfc03a3`. The docstring the audit flagged was in fact already
corrected by `edf357f` itself: `AcceptedHistoricalA32CallSupplier.lean:~323` now reads *"The
first five fields are direct protocol/model contracts"* of a six-field record and states
outright *"There is no `delivery_lookahead` field either."* A repository sweep for
`delivery_lookahead` / `HorizonVoteDeliveryLookahead` finds only deliberate historical notes.
The remaining half of this flag was the P-1 count drift, fixed in
`witness-statement-audit.md`.

**P-10 — RESOLVED as a de-duplication (`445d63d`) — the trust boundary is narrower than checkpoint sync.** `TrustedAnchorBoundary
Aligned` (`FFGGlobalCheckpointTrajectory.lean:623`) together with `get_forkchoice_store`'s
`anchor_epoch = get_current_epoch(anchor_state)` pins the anchor block to *exactly* its
epoch's start slot. The pinned initializer permits any trusted anchor state, including a
mid-epoch one. `hanchorExact` (row L) is the same fact restated through the checkpoint
walk, so rows E and L are not independent premises.
*Resolution:* the redundancy is **total**, not partial, and it is mechanical: the derivation
`Execution.acceptedAnchorExact_of_trajectory` (`Proof/AcceptedActualFCRCommon.lean:26`)
already existed — the strong fold used it, which is why W1/W2 never carried `hanchorExact` —
and every one of its inputs (`B`, the trajectory record, `hanchor`, `hboundary`) was already
a premise of the weak headlines. `hanchorExact` is therefore deleted from all four weak
trajectory theorems and supplied internally. The *narrowness* of the trust boundary itself
(anchor block pinned to its epoch's start slot) is unchanged and remains an honest
restriction relative to `get_forkchoice_store`, now carried by exactly one premise, row E.

**P-6 — still open (owner).** Untouched by this pass, as instructed.

**Overall judgement (as audited).** The plumbing layer is a faithful transcription: 28 fields are
line-for-line, 52 are transcriptions with an abstraction step that this document names, one
is a declared design delta, and only two are unsupported — one of them (P-2) a duplicate
rather than a claim. Everything that touches `on_block`, `on_attestation`,
`update_checkpoints`, `compute_pulled_up_tip`, `get_forkchoice_store` and
`get_checkpoint_block` is verbatim. The concentration of notes is in three places, all of
them the same phenomenon: the reduced model erases `process_epoch`'s internals, block
bodies, and the `checkpoint_states` cache's provenance, so what the spec computes the model
must assume. P-6 is the one genuine hole.

**Overall judgement (after the fixes).** Unchanged in substance, sharper on the surface: the
duplicate is gone, the one unguarded field is guarded, the one redundant anchor row is
derived, the four idealizations are disclosed at the point of definition, and P-6 is the
single remaining unsupported step.

---

## 14. Bonus: row N, `PostAnchorHonestVoteTargetWalkDomain`, derived (`dab205e`)

Not a flag of this document — it is row N of `witness-statement-audit.md`, classified [P]
"domain adequacy of the totalized walk" — but it is grounded by the same store-closure
machinery this audit traces, so it is recorded here.

The predicate says: for every actual post-anchor honest vote, `WalkKnown` holds from the
voter's own head down to the boundary slot of the vote's target epoch. It is now **derived**,
by

```
Execution.postAnchorHonestVoteTargetWalkDomain_of_selectedMarginAssumptions
  (hA : SelectedMarginAssumptions cfg ext E)
  (hanchor : anchor = E.genesis_store.justified_checkpoint)
  (hboundary : TrustedAnchorBoundaryAligned … anchor) :
  E.PostAnchorHonestVoteTargetWalkDomain cfg ext
```

from three facts this audit has already grounded:

1. the voter's head is a known block — `get_head_root_mem_or`, with
   `SelectedMarginDomain.justified_root_known` covering the totalized fallback;
2. every known block walks down to the retained trusted anchor's slot —
   `Execution.store_walkKnownK`, which is proved for arbitrary nodes out of the handler
   contract of §10: `on_block` admits only parent-known blocks (`Model/Handlers.lean:354`
   ← fork-choice.md:908 `assert block.parent_root in store.block_states`). The owner's
   justification — "we have parent-known for `on_block`, which is correct" — is exactly
   this step, and it suffices;
3. `TrustedAnchorBoundaryAligned` (§11) lifts that anchor-slot walk to the target boundary,
   because the predicate's own post-anchor hypothesis (`E.slot_at cfg 0 ≤ s`) puts the
   vote's target epoch at or above the anchor epoch.

Step 3 is where the boundary subtlety lands, and it is handled by the post-anchor hypothesis
alone: a vote whose target epoch *preceded* the anchor epoch would demand a walk below the
retained anchor, which no store can support — and the predicate never quantifies over one.

`hwalkDomain` is dropped from the four weak trajectory theorems. It is **kept** on the weak
one-shot floor pair (`weak_safeFrom_find_latest_confirmed_descendant_discharged` /
`weak_confirmed_head_discharged`, W18/W19): those carry `hW.base` but neither an anchor
identification nor `TrustedAnchorBoundaryAligned`, so dropping the binder there would be a
premise *exchange* (one [P] adequacy statement for one [B] anchor inequality), not a shrink.
That is an owner call, not a mechanical one.
