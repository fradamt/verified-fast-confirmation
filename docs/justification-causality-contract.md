# The justification-causality contract

Wave 4 of [`proviso-discharge-map.md`](proviso-discharge-map.md) §6 is a design
decision: escape **E1** (endpoint-slot-capped proviso) or **E2** (boundary-block
safety invariant). This note states E1's single premise-surface addition — a
justification-causality field on `JustificationInterface`
(`FastConfirmation/Spec/TheoremStatements.lean:80`) — in its weakest sufficient
form, grounds it in the pinned spec, classifies it, and reports one negative
finding (§6). Line numbers: branch `centaur/discharge-helper-provisos-202609161`;
spec quotes: `spec_source/manifest.json`, consensus-specs `30aa65fc`.

## 1. The field

It is `justified_requires_targets` (`TheoremStatements.lean:144-158`) verbatim
plus **one conjunct**, marked below:

```lean
  /-- Justification causality (the time half of `justified_requires_targets`):
      a post-anchor checkpoint justified in an honest view at second `m` was
      formed from target attestations whose slots are strictly in the past of
      `m`'s slot — the store admits an attestation only once its slot is over
      (`validate_on_attestation`'s no-future gate) and a block's attestations
      are older than the block (`MIN_ATTESTATION_INCLUSION_DELAY`). -/
  justified_targets_before_endpoint : ∀ w ∈ E.honest, ∀ m : ℕ,
    ∀ c : Checkpoint Root,
    E.WithinHorizon cfg m →
    JustifiedIn (E.store cfg ext w m) c →
    E.genesis_store.justified_checkpoint.epoch < c.epoch →
    c.epoch < E.verification_horizon →
      ∃ S : Finset ValidatorIndex,
        S ⊆ E.span_committee (c.epoch * cfg.slots_per_epoch)
          (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) ∧
        (∀ i ∈ S, ∃ (w' : ValidatorIndex) (n' : ℕ) (a : Attestation Root)
            (ifb : Bool),
          E.WithinHorizon cfg n' ∧
          E.SlotWithinHorizon cfg a.data.slot ∧
          Event.attestation a ifb ∈ E.schedule w' n' ∧
          i ∈ a.attesting_indices ∧ a.data.target = c ∧
          a.data.slot + 1 ≤ E.slot_at cfg m) ∧          -- ← the only addition
        2 * E.total_active cfg ≤ 3 * E.weight S
```

Weakest-form notes. The bound is on the **attestation slot**, not the schedule
second `n'` and not the voter's cast second: consumers key on the vote slot
(`HonestVotesSupportTarget`, `:68-74`, quantifies `∀ s : Slot`), and
`Nucleus.honest_member_vote_indexed` (`Proof/Nucleus.lean:77`) already converts
`a.data.slot + 1 ≤ E.slot_at cfg m` — its premise `hprocessed`, `:90` — into
`slot_at k < slot_at m` for the member's cast second. That lemma exists, is
unapplied, and its docstring (`:72-76`) names the gap verbatim: *"the upper
bound uses the exact `validate_on_attestation` no-future gate, which is not
carried by `justified_requires_targets`"*; `Nucleus.lean:235` records it again
for `CurrentEpochCoveringBridge`. No delivery, relay or processing claim is
made, and no uniqueness of `S`; the anchor is excluded by the existing field's
own `genesis_store.justified_checkpoint.epoch < c.epoch` guard. Adding the
conjunct in place beats a second field (no duplicated realizer obligation);
either way the premise surface grows by one inequality.

**Boundary case — strict is needed, and strict is what the spec gives.** The
capped support E1 derives from `hIH`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:152-159`) covers honest heads only
at seconds `m'` with `slot_at m' < slot_at m`; `slot_at m` is the slot whose
safety is under proof. So `a.data.slot ≤ slot_at m` is **insufficient**: a
quorum attestation of slot exactly `slot_at m`, cast at an earlier second inside
that slot, escapes `hIH`. Unlike at a call second, where `slot_start (slot_at
(n+1)) = n+1` makes the same-slot-earlier-cast case vacuous (map §5.4,
`HonestTargetAgreement.lean` lemma 2), `m` need not be a slot start.

## 2. Why it holds of the pinned spec, by construction

`Execution.store_current_slot` (`Proof/Trajectory.lean:137`) gives
`get_current_slot (E.store cfg ext w m) = E.slot_at cfg m`, so every quote below
about `get_current_slot(store)` is a statement about `slot_at m`.

1. **Fork-choice admission is strict.** `fork-choice.md`'s
   `validate_on_attestation` ends with
   > ```python
   > # Attestations can only affect the fork choice of subsequent slots.
   > # Delay consideration in the fork choice until their slot is in the past.
   > assert get_current_slot(store) >= attestation.data.slot + 1
   > ```
   It is **not** gated on `is_from_block` (only
   `validate_target_epoch_against_current_time` is), so block-carried
   attestations obey it too; `on_attestation` runs it before
   `update_latest_messages`.
2. **State-level justification is strict too.**
   `process_justification_and_finalization` reads only
   `state.current/previous_epoch_attestations` (`beacon-chain.md`), appended
   solely by `process_attestation`, which asserts `data.slot +
   MIN_ATTESTATION_INCLUSION_DELAY <= state.slot <= data.slot + SLOTS_PER_EPOCH`
   with `MIN_ATTESTATION_INCLUSION_DELAY = 1`; `on_block` admits a block only
   under `assert get_current_slot(store) >= block.slot`.
3. **Every `JustifiedIn` disjunct routes through 1 or 2.**
   `justified_checkpoint`/`finalized_checkpoint` are written by
   `update_checkpoints` from an accepted block's post-state (`on_block`) or by
   `on_tick_per_slot`'s epoch pull-up; the unrealized fields and
   `unrealized_justifications[r]` are written by `compute_pulled_up_tip`, which
   copies `store.block_states[block_root]` and runs
   `process_justification_and_finalization` on it.
4. **Time only moves forward.** `on_tick_per_slot` assigns `store.time = time`
   and `on_tick` catches up slot by slot (`while get_current_slot(store) <
   tick_slot`), so a fact admitted at `m' ≤ m` was admissible at `m'`.

Together: a store at time `m` cannot have realized a justification whose quorum
includes votes not yet cast at `m`. The field transcribes an `assert`.

## 3. Classification: an export, not a proviso

It joins the fields that pin what the abstract `ext`-parameterized functions do
in the real spec — checkable line by line against the pinned markdown, each
about what has **already happened**. Comparators: `justified_requires_targets`
(`:144-158`), the same FFG export's weight half from the same call graph;
`justified_cached` (`:123-128`) and `observed_justified_cached` (`:113-121`),
transcriptions of `store_target_checkpoint_state`'s keying; and
`checkpoint_known` (`:208-214`), whose docstring already reads
"`justified_requires_targets`' knownness half ... the abstract state transition
cannot deliver it per-handler" — the proposed field is that sentence with *slot*
for *knownness*. It is emphatically not in the class of
`HonestVotesSupportTarget` (`:68-74`), the proviso being removed: that predicate
quantifies honest votes at slots `≥ slot_at n`, i.e. **predicts future honest
conduct** under cross-validator head agreement the algorithm's own checks are
mid-way through establishing (hence its non-circularity docstring, and the
spec's *"This function assumes that all honest validators will be voting in
support of the current epoch target starting from the current moment in time"*).
The new field has no future quantifier: it bounds a past event set by a past
clock read.

## 4. What it buys (the E1 route end to end)

At a call second `n+1`, `hIH`
(`AcceptedSelectedStrictEdgeFilterSupply.lean:152-159`) — every honest head at
slots in `[slot(n+1), slot(m))` descends from the selector's result — composed
with the wave-2 constructor
`honestVotesSupportTarget_of_safeFrom_currentEpochCandidate`
(`Proof/HonestTargetAgreement.lean`: `votes_head` +
`get_checkpoint_block_of_ancestor` + paired-walk transport) yields a **capped**
`HonestVotesSupportTargetUpTo … (slot_at m)`, derived rather than assumed (map
§5.3 E1, wave 5 step 1). §1's field makes that cap co-extensive with the
adversary's opportunity: any `c` justified at `(w,m)` was built from slots
`< slot_at m`, exactly the region the capped support governs. Under it the
Trunk-B pinning lemma `noConflict_certifiedJustified_root_eq_currentTarget`
(`NoConflictCertificatePinning.lean:698`, `hsupport` `:719-720`) and the Trunk-A
quorum builder (`AcceptedCurrentTargetGateBridge.lean:1042`) are re-proved (wave
5 steps 2-3); the two live fields of `Weak.SelectedHelperProvisosAt` become
derived lemmas at `WeakPreQuerySIR.lean:339` / `WeakHistoricalA32Step.lean:280`,
and `observer_helper_provisos`
(`WeakSelectedStrictEdgeFilterSupply.lean:236-245`) is deleted, collapsing the
22 binders of map §1.1 and unconditionalising theorems #14-#22 (wave 6).
**Caveat: §6 shows the Trunk-A leg does not close at cap `slot_at m`** — the
field removes the *time* obstruction, not the weight arithmetic.

## 5. Why not E2

E2 strengthens the invariant from `SafeFrom (weakConfirmed n)` to `SafeFrom
(get_checkpoint_block store (weakConfirmed n) currentEpoch)`. But map §5.1 shows
"all honest heads agree on the current-epoch boundary block above the candidate"
is precisely what the two proviso fields encode — it is what turns per-validator
honest voting into support for *this* target. Carrying it in the invariant
relocates the assumption rather than discharging it, and it would still need its
own argument (previous epoch's justified checkpoint plus the gate) at the fold's
base and step. Only E1 replaces a normative prediction with a transcription.

## 6. Open risk: Trunk A's positive quorum — the cap does not reach

The map flags Trunk A as "most likely to fail" (§5.2, §6); reading the
consumption confirms it and locates the failure. The signer set whose weight
must reach two-thirds is definitionally `currentTargetA32Signers =
observedHonest ∪ (currentTargetFutureSpan).filter honest`
(`CurrentTargetA32Support.lean:197-201`), and `currentTargetFutureSpan store =
span_committee (get_current_slot store) (currentTargetEpochEnd store)`
(`CurrentTargetFutureSupport.lean:41`, `:28`) — the committee union from the
query slot **through the last slot of the current epoch**. The proviso is
unfolded per seat at `CurrentTargetA32Support.lean:504` (in
`currentTargetFutureHonestSeat_vote`, `:457`, seat binder `:466-472`) and at
`AcceptedCurrentTargetGateBridge.lean:769` (in `…_of_currentSlot`, `:717`,
applied at `:1117`/`:1286` inside the quorum builder `:1042`). So **yes — the
quorum needs honest votes at slots `≥ slot_at m` whenever `m` lies inside the
target's epoch**, the normal case: safety is asserted from the following slot
on, and `hslotQM` (`AcceptedSelectedStrictEdgeFilterSupply.lean:140`) constrains
`m` only by `slot_at (n+1) ≤ slot_at m`.

Truncating the span at `slot_at m` does not weaken the bound, it deletes it:
`will_current_target_be_justified_honest_quorum`
(`CurrentTargetFutureSupport.lean:372-399`) runs through
`current_epoch_span_eq_anchorActive` (`:119`) — full-epoch committee coverage
identifies `span(epochStart, epochEnd)` with the static active set — and
`currentTarget_remaining_honest_le_future_weight` (`:237`), which lower-bounds
only the **full** future span, by `total_active − estimate(elapsed)` scaled by
the per-span honest fraction. A partial span is not complementary to the elapsed
estimate, so it carries no lower bound at all. The same objection hits Trunk B's
arithmetic branch, which reaches `>1/3` through the identical union
(`noConflict_arithmeticBranch_oneThird`, `NoConflictCertificatePinning.lean:91`,
used at `:782`): wave 5 step 2 is not a literal re-proof in either trunk. Nor
does the obvious repair close it — bounding a conflicting quorum by elapsed-
estimate soundness gives `weight(S) ≤ estimate + byzantine`, while the gate
guarantees only `estimate < 5/9 · total`, compatible with `weight(S) ≥ 2/3`.

So: the cap E1 derives is `slot_at m`; the cap both trunks consume is
`currentTargetEpochEnd`, a fixed slot that does not move with the endpoint.
Options, in order of appeal: (i) prove head agreement for the remainder of the
target's epoch in one step (epoch-indexed rather than slot-indexed induction),
supplying the epoch-end cap directly and making E1 complete; (ii) split the
trunks — E1 for Trunk B if a purely intersection-based pinning argument can
replace the `>1/3` counting, residual proviso for Trunk A; (iii) accept
`observer_helper_provisos`. §1's field is worth adding under (i) and (ii) alike,
and independently arms `Nucleus.honest_member_vote_indexed` and the gap
`CurrentEpochCoveringBridge` (`Nucleus.lean:235`) names.
