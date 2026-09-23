# Weak synchrony: model delta and proof-migration plan

## Premises added by the main merge

The caller-facing `Execution.WeakObserverAssumptions` adds these fields:

```lean
genesis : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
  E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
  anchorState.slot = anchorBlock.message.slot ∧
  ext.AnchorCommitsToState anchorBlock.message anchorState ∧
  anchorBlock.message.parent_root ≠ anchorBlock.root
validity : E.ObserverValidity cfg ext obs
```

The validity record is verbatim:

```lean
structure ObserverValidity (E : Execution Root) (obs : ValidatorIndex) : Prop where
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      ext.is_valid_indexed_attestation state a = true
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  valid_attestation_committee : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot
```

`ObserverValidationState` is a keyed block or checkpoint state from genesis
or from the observer's validated handler prefixes. It restricts the old
unconditional attestation laws to the states this observer run produces.
The observer may be outside the honest set. Its non-equivocation and
latest-message provenance now follow from these scoped laws. The anchor
commitment supplies the new strong adapter requirement; it is the same
commitment already carried by `ScheduledPrefixTrajectoryAssumptions` on main.

Companion to `FastConfirmation/Spec/Model/WeakSynchrony.lean`. Source
discussion: the Ethlabs working note "Weakening the synchrony assumptions of
FCR" (September 2026).

## Gloas payload status — 23 September 2026

The merge of `main` brings the Gloas fork-choice nodes into the weak model.
A block node is PENDING; its payload children are FULL and EMPTY. A vote
from a slot after the block slot supports FULL or EMPTY, as its payload bit
sets.

### Payload-aware duty-fresh discount

The weak empty-slot discount of a block `c` with parent `a` counts only
the parent votes that agree with the payload status that `c` requires:

```lean
Weak.get_duty_fresh_parent_payload_support_between_slots cfg ext store bs
  block.parent_root (get_parent_payload_status store block)
  (parent_block.slot + 1) (block.slot - 1)
```

A counted cell must satisfy all of these conditions:

- its root is `a`;
- it is duty-fresh (rule delta 3);
- its validator is not in `store.equivocating_indices`;
- `get_supported_node` of the cell selects the payload status of `a` that
  `c` requires.

A parent vote for the opposite payload status is not discounted. It stays
in the weight that opposes `c`. The Python twin is branch
`fcr-weak-synchrony-gloas` in `consensus-specs-weak`, commit `4a6b336ec`.

`Weak.has_broadcast_certificate` returns `false` when the current slot is
zero. This matches Python commit `353eb0dc4`, where `current_slot - 1`
would be out of range for `Slot`. The guard can only make the rule stricter.

### Weak G2-004: the pending parent selects the status of `c`

At an edge `a → c` that an arbitrary weak observer confirms, each later
honest endpoint must select the payload status that `c` requires at the
pending node of `a` (`PendingStatusMargin`). The proof is in
`FastConfirmation/Spec/Proof/WeakStatusMarginConstruction.lean`:

```text
┌──────────────────────────────────────────────────────┬──────────────────────────────┐
│ Declaration                                          │ Content                      │
├──────────────────────────────────────────────────────┼──────────────────────────────┤
│ support_discount_le_fresh_parent_payload_stuck_      │ discount ≤ honest matching   │
│   of_prefix                                          │ fresh parent support         │
│ endpoint_opposite_not_freshParentPayloadStuck        │ an old honest opposite voter │
│                                                      │ does not fund the discount   │
│ endpoint_opposite_honest_classification_at_observer  │ honest opposite supporters:  │
│                                                      │ Xclass, or Aclass \ discount │
│ endpoint_status_strip_lo_at_observer                 │ strip with debt O            │
│ statusMargin_loWindow_at_observer                    │ direct-window, same-epoch    │
│ statusMargin_crossing_at_observer                    │ both crossing regimes        │
└──────────────────────────────────────────────────────┴──────────────────────────────┘
```

The call sites are in `WeakCoveredMarginConstruction.lean`
(`selectedCoveredMarginSupplyAt_of_filterSupply_at_observer`).

The proof follows the strong construction (`StatusMarginConstruction.lean`)
with these changes:

1. All classes are read at the honest endpoint `(w, m)`. The observer
   supplies only its recorded cells.
2. An honest endpoint supporter of the opposite status of `a` is in
   `Xclass(W, lo, σ)`, or it is an old voter in `Aclass(W, lo, es)`. For an
   old voter, the observer cell is duty-fresh, so its epoch dominates each
   completed duty (`epoch_le_of_duty_fresh_cell`). The honest endpoint has
   the recorded-epoch bound (`windowRecordedEpochMax_at_query_minimal`).
   `old_window_latest_messages_agree` then gives the same message at both
   stores. That message selects the opposite status, so it is not in
   `FreshParentPayloadStuck`. This replaces the strong argument, which uses
   an honest query owner.
3. The confirmation strip keeps the debt
   `O = w(Aclass(W, lo, es) \ FreshParentPayloadStuck)`. The discount is at
   most `w(FreshParentPayloadStuck)`.
4. The crossing arms use `reanchored_endpoint_of_fullSpan_certificate_opp`
   with `eqSub = eqExtra = 0`. The weak budget has no equivocation
   subtraction, so both crossing regimes use one construction.
5. FULL availability comes from `Execution.full_parent_payload_verified`
   (`required_parent_status_mem_pending_minimal`), as on `main`.

### Premises

The weak bundle carries one new premise from `main`:
`PaperSafetySynchrony.payload_envelope_relay`, through
`SelectedMarginAssumptions.synchrony`. The weak G2-004 proof adds no
premise. It uses `WeakObserverAssumptions.validity` (observer provenance),
the observer committee readback, and `PostAnchorHonestVoteTargetWalkDomain`
at the honest endpoint. All three were already in the weak premise surface.

## Current carrier rule — 21 September 2026

The current implementation uses the newest certified ancestor of the actual
fork-choice head. It does not require the actual head to have a completed-slot
certificate. See [certified-head.md](certified-head.md) for the rule, proof
changes, and validation scope. Later sections retain the original development
history; references there to head-only certificates describe the earlier rule.

## Greatest-unrealized reset — 22 September 2026

The weak FCR store has a separate
`current_epoch_greatest_unrealized_checkpoint` field. Initialization sets it to
finalized. At each epoch start, weak bookkeeping copies
`previous_epoch_greatest_unrealized_checkpoint` into it. This value stays fixed
when the previous snapshot changes at the last slot of the epoch. The certified
observed checkpoint still supplies positive confirmation and the balance source.
The frozen strong rule does not read or write the new field.

The weak getter applies this last reset gate **after the certified restart**
and immediately before descendant search:

```text
if greatest != get_checkpoint_for_block(confirmed_root, greatest.epoch):
    confirmed_root = finalized.root
```

The test compares the full checkpoint. An ancestor root alone does not suffice
when the chain skips an epoch boundary. A test before restart is insufficient:
the restart can restore the rejected root. Schema 2 of the trace harness carries
the new field. Legacy schema 1 defaults it to finalized and cannot reconstruct
an earlier epoch-start snapshot for an independent record.

The proposed containment principle is that weak confirmation is an ancestor
of strong confirmation on the same fork-choice store, across handler calls.
`FastConfirmation/Spec/Proof/Containment.lean` defines `Dominates` with this root
order, equal fork-choice stores, equal previous snapshots and slot heads, and
strong current observed checkpoint equal to weak current greatest checkpoint.
`dominates_init` proves initialization without extra premises. The requested
handler preservation and one-shot containment are false under this relation.
`Negative.not_handler_preservation` and `Negative.not_one_shot_containment` are
kernel-checked audit witnesses. The chain is `1@0 → 2@8 → 3@9`; at slot 16,
weak starts at 2 and strong at 3. Their banks and balance sources agree. Strong
fails to reconfirm its extra suffix and resets to 1. Its actual head has a
different unrealized checkpoint, so restart fails. Weak retains 2, which passes
the new reset. The outputs reverse the initial ancestor order.

This finite store is not claimed to have an accepted execution history.
An accepted-history theorem would need further hypotheses and proofs; there
is no proved trajectory containment corollary here. Work on the positive
containment theorem stopped at this counterexample. Native trace counts are
separate diagnostics and do not prove containment.

Three obsolete complete-evidence audit witnesses were removed, together with
their positive theorem declarations:

- `CompleteEvidence.banking_eq`: weak banking writes the new field; strong
  banking retains it, so whole-record equality is false.
- `CompleteEvidence.get_latest_confirmed_eq_of_head_eq`: complete prior-slot
  evidence and aligned heads do not prevent the added checkpoint reset.
- `CompleteEvidence.on_fast_confirmation_eq_of_head_eq`: the dependent handler
  equality also fails; the new reset can change the confirmed root.

The audit has 54 witnesses: 55 old witnesses minus the three removed equalities,
plus two negative containment witnesses. The other complete-evidence helper
statements and concrete witnesses remain.
Their evidence contract has no added premise. The existing weak safety proof
now has an explicit greatest-checkpoint reset case. Both reset locations use
the same finalized-root safety argument; certified restart safety is unchanged.

Rationale and zk scope (22 September 2026). The gate is the first check of
the strong `is_confirmed_chain_safe`, applied to the same checkpoint: the
strong rule banks the greatest-unrealized snapshot as its observed checkpoint.
At the epoch transition, fork choice pulls this checkpoint up to
`store.justified_checkpoint`, so the gate keeps the confirmed chain consistent
with the observer's own justified checkpoint. The gate can only reset, so it
cannot weaken safety. Its only input is the replayed store, so the replay
theorems are unchanged. The snapshot is a maximum over all processed blocks,
orphans included. A zk prover chooses the log and can lower the snapshot by
omitting blocks, so the gate is not enforceable against a hostile prover. No
safety argument depends on it. A third party cannot force the gate on a prover.
The gate fires only if a checkpoint that conflicts with the confirmed chain has
an unrealized justification: two thirds of the stake voted for it. A verifier
must keep the highest accepted confirmed root and must not treat a later lower
output as a revert. Any prover can already produce a lower output by omitting votes.

Trajectory containment (weak confirmed root is an ancestor of the strong one) is
not a target. Python probes on consensus-specs branch `fcr-containment-probe`
(e58edbbf3, 3e2a87558) reach weak-above-strong with 5 of 64 validators faulty:
strong fails its epoch-start re-check on a block that weak never confirmed, and
its restart cannot fire (skipped checkpoint slot, or a head whose unrealized
checkpoint is behind the store maximum).

## Network model

The adversary controls **or eclipses** up to `CONFIRMATION_BYZANTINE_THRESHOLD`
of the stake. Eclipsing is weaker than controlling, so eclipsed validators are
accounted inside the same budget and "honest" continues to mean *honest and
not eclipsed*. Synchrony is constrained to honest validators: a message
produced by an honest validator is received by every honest validator within
the delay bound. Non-validator relay nodes need no separate treatment — honest
to honest delivery is a property of the network as a whole, and the fields of
`Synchrony`/`PaperSafetySynchrony` already quantify holders/senders and
receivers over `E.honest`, so the records are reused **verbatim**.

The single change is the observer running the FCR:

- Strong model (current accepted theorem): the observer is a member of
  `E.honest`, so `block_relay` treats its store contents as network-known and
  `attester_slashing_relay` treats its equivocation evidence as shared.
- Weak model: the observer is an arbitrary node — an inbox that is granted
  nothing. No law guarantees delivery to it, and nothing it holds propagates
  from it. (Since `refactor!: drop the unused obs-not-honest field` the
  records no longer even assume `obs ∉ E.honest`: non-honesty was never used,
  so the weak statements cover honest observers too.)
  Its inbox stays authentic (`WellFormedExecution`, `HonestBehavior.no_forgery`
  range over every node's schedule) and its clock stays synchronized (a base
  assumption of the protocol, kept).

Kept as-is: `ExternalsCoherence`/`StaticValidatorSet` (ground-truth committees
and registry) and clock synchronization. Scope: one-shot confirmation safety.
Observer liveness is explicitly out of scope. Stored-state maintenance
(`get_latest_confirmed`'s revert-to-finalized and epoch-start restart branches,
`is_confirmed_chain_safe`) is deferred.

## Broadcast certificates

`Weak.has_broadcast_certificate store bs r a b`: the weight of unslashed,
active, non-equivocating members of the committees of `[a, b]` whose latest
message was cast for a slot in the span and votes for `r` or a descendant,
strictly exceeds `Weak.compute_adversarial_weight` over the same span. The
surplus is honest; **one** surplus honest attester suffices (no majority):
casting such a vote presupposes possession of `r`'s chain by the vote's slot,
and honest-to-honest synchrony disseminates it from that sender. The evidence
may reach the observer late — it certifies dissemination that already
happened by `end_slot + 1`.

Uses:

1. **Confirmed blocks — automatic.** `is_one_confirmed`'s threshold already
   exceeds the span's adversarial budget, so a one-confirmed block carries a
   certificate implicitly. No rule change; the proofs must route synchrony
   applications through the vote surplus instead of the observer's receipt.
2. **Justification witness — rule change.** The previous-epoch advancement of
   `Weak.find_latest_confirmed_descendant` additionally requires
   `Weak.has_justification_witness_certificate` for
   `fcr_store.previous_slot_head` (the block carrying the previous epoch's
   justification), over `[witness block slot, current_slot − 1]`. Certified
   votes end before the current slot, so every honest validator holds the
   witness chain before casting any vote the FFG projections count.
3. **Fork-choice head — rule delta 4.** `Weak.has_head_broadcast_certificate`
   certifies the fork-choice head over `[head slot, current_slot − 1]`.
   Possessing a block implies possessing its ancestry, so a certificate on the
   head dominates the deeper carrier that actually formed the
   `unrealized_justifications` entry the rule reads — no certificate on that
   carrier is required. See "Rule delta 4" below.

## Equivocation discount

`Weak.compute_adversarial_weight` drops the `get_equivocation_score` subtraction.
Its soundness rested on `attester_slashing_relay` applied to the observer's
evidence (everyone must exclude the same equivocators, or the subtracted weight
reappears as competing support outside the budget). Dropping it is monotonically
stricter, hence safety-free; in-model it also costs no liveness beyond the free
adversarial baseline, since honest validators are never slashable and a detected
equivocator's margin effect without the discount equals abstention. Equivocators'
votes remain excluded from support sums (also stricter). A later improvement may
re-enable the discount for slashings carried in a broadcast-certified block.

## Rule delta 3 — duty-based freshness

`Weak.is_one_confirmed` and its empty-slot support discount count only cells
accepted by `Weak.is_duty_fresh_message cfg ext store i lm`. The check uses
`cutoff = epoch(current_slot - 1)` and accepts either:

- a cell with `lm.epoch >= cutoff`; or
- a cell with `lm.epoch + 1 == cutoff` whose validator has no assigned duty in
  `[start_slot(cutoff), current_slot - 1]`.

The second arm scans only the completed part of one epoch. A client can cache
that committee union once per query instead of recomputing it per validator.
Thus a previous
vote remains usable until a newer duty has completed. At the first slot of an
epoch the cutoff remains the previous epoch. The rule adds no delivery
assumption for the observer. The observer's existing committee-readback contract
is used when connecting this executable check to the ground-truth vote schedule.

This replaces the original weak branch's epoch-wide cutoff, introduced in
`cf46f95`. That cutoff discarded all remaining previous-epoch cells at the
second slot of an epoch, even when a validator's next duty was still ahead.

`WeakDutyFreshness.lean` proves the local contract:

- `epoch_le_of_duty_fresh_cell`: the recorded epoch dominates every completed
  assigned duty of its validator;
- `duty_fresh_of_epoch_fresh`: every cell admitted by the old cutoff is retained;
- `duty_fresh_of_no_completed_duty`: a previous vote is retained before its next duty;
- `duty_fresh_of_completed_duty_domination`: a recent cell that already covers
  all completed duties is retained;
- `duty_fresh_false_of_newer_completed_duty`: a newer completed duty excludes
  the old cell.

The endpoint support and parent-support proofs use the first lemma together
with honest duty assignment and the existing `PrefixCommitteeAgreement`.
They do not use delivery to the observer. The public assumption records and
headline theorem statements are unchanged.

**The empty-slot discount is retained.** Honest votes for the parent in the gap
are neutral between its children. They can reduce the potential competing
weight. A hidden newer vote for a competing child invalidates that use of the
old parent vote, so the discount uses the same duty check as positive support.
A timely replacement that still votes for the parent can keep funding the
discount; a replacement on the candidate branch contributes positive support.
The rule does not add the parent discount and positive support for one recorded
message: these root conditions are disjoint.

This filter changes weight accounting, not the stored message history. The
broadcast-certificate helpers are unchanged: an old honest vote can still prove
past receipt of a block even after a newer vote replaces its LMD contribution.
The current-target FFG scorer is also unchanged; its checkpoint comparison
already requires a vote for the current target epoch.

The lossless-retention lemma is a local statement about a recent recorded cell,
not a full FCR liveness theorem. It does not assume an offline validator will
cast its next vote. Without that vote, exclusion after its duty can still cost
liveness compared with retaining an actually-unsuperseded old cell.

## Rule delta 4 — certificate-gated justification short-circuit

Every place `find_latest_confirmed_descendant` reads an *unrealized*
justification at the fork-choice `head` (as opposed to the already-witness-
certified `previous_slot_head`) now additionally requires
`Weak.has_head_broadcast_certificate` on `head`:

- the previous-epoch guard's `(unrealized_justifications head).epoch + 1 ≥
  current_epoch` disjunct;
- the tentative loop's entry gate, same condition;
- `Weak.will_no_conflicting_checkpoint_be_justified`'s short-circuit
  (`get_current_target = unrealized_justified_checkpoint ⟹ true`), which now
  additionally requires the head certificate before trusting the
  short-circuit, using the balance source `get_current_balance_source
  fcr_store` (the same one every other weak certificate in the call already
  uses).

The voting-source read of `previous_slot_head` and the `unrealized_justifications
previous_slot_head` disjunct are already gated (they sit behind the witness
certificate conjunct); they are unchanged.

**Site sweep (all sites `find_latest_confirmed_descendant` touches that read
an unrealized/tentative justification or voting source):**

| site | status |
| --- | --- |
| voting-source read of `previous_slot_head` | already gated by the witness certificate |
| `unrealized_justifications previous_slot_head` | already gated |
| `unrealized_justifications head` (prev-epoch guard) | gated this delta |
| `unrealized_justifications head` (tentative entry) | gated this delta |
| `will_no_conflicting_checkpoint_be_justified` short-circuit | gated this delta |
| voting-source read of `tentative_confirmed_root` (finding 7) | gated *implicitly* — see below |
| `filter_block_tree` inside `get_head` (finding 8-adjacent) | out of scope |
| `is_head_unrealized_justified_ok` in `get_latest_confirmed` | out of scope |
| balance-source key from `unrealized_justified_checkpoint` (finding 8) | **closed** by rule delta 5, see below |

**Finding 7 — the tentative loop's voting-source read is gated implicitly.**
`find_latest_confirmed_descendant`'s final `if` reads `(get_voting_source
cfg store tentative_confirmed_root).epoch + 2 ≥ current_epoch` — a read at a
candidate root that is *not* separately wrapped in a certificate conjunct.
This is sound without one: `tentative_confirmed_root` is only ever a value
that already passed `Weak.is_one_confirmed`
(`Weak.find_latest_confirmed_descendant_tentative_loop`'s only advance case,
`weak_tentative_loop_spec` in `WeakSelectorInversion.lean`), and a `true`
`Weak.is_one_confirmed` result is itself a broadcast certificate for that
root (its support already exceeds the span's adversarial budget — see
`is_one_confirmed`'s own docstring). So this site is gated through the loop
invariant rather than an explicit conjunct; recorded explicitly
(`WeakSelectorInversion.lean`'s module docstring) since it is easy to mistake
for an ungated read.

**Finding 8 — the balance source itself descends from an ungated read —
CLOSED by rule delta 5.** `get_current_balance_source`/every weak certificate
in this call keys off `fcr_store.current_epoch_observed_justified_checkpoint`,
which in turn derives from `unrealized_justified_checkpoint` bookkeeping in
`Confirmation.lean` (around `:46-50`) that rule delta 4 did not touch and
that was not itself broadcast-certified. Rule delta 5 (below) gates exactly
this installation on `Weak.has_head_broadcast_certificate` **and re-points it
at the certified head's own `unrealized_justifications` entry**, so the key
every weak certificate in the call is evaluated against is now itself
certificate-backed — by a certificate that provably covers it — or the trusted
anchor value. See "Rule delta 5" for the gate, the input invariant it
establishes (`Weak.CertifiedBankedJustification`, maintained along the whole
trajectory), and the liveness cost of closing this gap.

**Finding 6 — head-certificate non-inertness depends on call placement, not
just the rule.** `has_head_broadcast_certificate`'s span is `[get_block_slot
store head, current_slot − 1]`; this is **empty** (hence the certificate is
vacuously false, never able to fire) exactly when `head` *is* a block for
`current_slot` itself. Verified against the actual call-trace model
(`AllowedFCRCallTrace.lean`): the canonical schedule updates the cached
variables "at the first whole second of a slot" (module docstring, `:6-8`),
i.e. before a same-slot proposal could plausibly have been produced and
processed, so `head` is ordinarily the *previous* slot's block and the span is
non-empty. But this is a scheduling expectation, not a proved invariant of
the interpreter: `canUpdate` (`:170-177`) gates on clock alignment,
per-slot uniqueness, the attestation-deadline window, and past-attestations
having landed — it does not check, and nothing else in `step?`/`run?` rules
out, whether a block for the *current* slot has already been received and
processed (via `.receive`/`.processNext`) before `.updateVariables`/
`.query .mandatory` fire. The source explicitly "permits the update to happen
later" in the slot, and separately permits `.query .extra` calls "at any
other point in the slot" (`QueryKind` docstring, `:54-56`) — at either of
those, if the current slot's own block has already landed, `head` can equal
it, the span degenerates to empty, and the head certificate is inert at that
call. This is not a bug in this delta: the re-anchored variant (certifying a
span that stays non-empty regardless of where `head` lands, e.g. anchored one
slot back) is a distinct rule shape, deferred as a future rule delta, out of
scope for this wave. (Rule delta 5, below, closes finding 8 by *gating* the
existing span rather than re-anchoring it — the re-anchored variant remains
future work, and is in fact the strongest argument delta 5's own liveness
note makes for scheduling it next.)

## Rule delta 5 — certified bookkeeping

`Weak.update_fast_confirmation_variables` (`Spec/Model/WeakSynchrony.lean`)
is identical to the strong rule except for **one** write: the epoch-start
installation of the current-epoch observed justified checkpoint — the key
`get_current_balance_source` reads, and hence the key every other weak
certificate in the call is evaluated against — happens only when the
fork-choice head at update time is broadcast-certified
(`Weak.has_head_broadcast_certificate`, evaluated against the pre-write
balance source `bs`, read before any field is rewritten), **and what it banks
is that head's own unrealized justification**:

```lean
    current_epoch_observed_justified_checkpoint :=
      if has_head_broadcast_certificate cfg ext store bs then
        store.unrealized_justifications (get_head cfg store).root
      else fcr_store.current_epoch_observed_justified_checkpoint
```

*Bank only a justification observed in a certified block.* The value banked is
the justification observed **through** the certified block, not the
store-global running maximum `previous_epoch_greatest_unrealized_checkpoint`.
That is the whole point of the design: coverage of the banked checkpoint by
the head certificate becomes **chain-intrinsic**. The accepted FFG contracts
tie `store.unrealized_justifications b` to `b`'s own ancestry
(`AcceptedFFGTransitionCoherence.au_checkpoint_of_known` identifies the
checkpoint root with `get_checkpoint_block store b c.epoch`, i.e. with the
block the store's own ancestor walk from `b` lands on), so "the banked root is
on the certified head's chain" is a *theorem about the rule* rather than a
field of the input invariant or an extra executable conjunct.

If the gate fails, the field keeps its previous value: stale-but-certified
beats fresh-but-uncertified. Every other write (slot-head cache,
`previous_epoch_greatest_unrealized_checkpoint`,
`previous_epoch_observed_justified_checkpoint`) stays unconditional, exactly
as in the strong rule; see the definition's docstring for the field-by-field
argument. `Weak.get_latest_confirmed` and `Weak.on_fast_confirmation` are
minimal clones of the strong definitions with the weak selector/bookkeeping
substituted (picked up by namespace shadowing); `is_confirmed_chain_safe` and
the revert-to-finalized branch stay the strong/deferred versions, per the
module docstring's standing scope.

**`previous_epoch_greatest_unrealized_checkpoint` is now vestigial in the weak
bookkeeping.** It keeps its strong, ungated writes verbatim — the last-slot
refresh from `store.unrealized_justified_checkpoint` — purely for
field-for-field parity with the strong rule (and for any future consumer of
the strong-side rotation lemmas). Rule delta 5 no longer reads it. The weak
rotation lemmas about it (`Weak.weakFcr_previousGreatest_succ_exact`,
`Weak.weakFcr_previousGreatest_origin`, `Weak.weakFcr_previousGreatest_known`
in `WeakBankedJustification.lean`) are retained and marked as parity-only;
`Weak.update_fcv_observed_exact` no longer mentions the field at all (the
ordered write through it has disappeared from the exact-source statement).

**Safety and liveness of the deviation.** When a *side* branch carried a
higher justification than the head chain, the revised rule banks the
head-chain one — a lower epoch. Lower is strictly stricter in every recency
guard that reads the banked value (`is_observed_justified_block_epoch_ok`,
`get_block_epoch confirmed_root + 1 ≥ current_epoch`, the voting-source
recency tests), so the deviation is safety-free by the same monotonicity
argument that licensed dropping the equivocation discount; it costs liveness
only in the case where a side branch was ahead, which is exactly the case in
which trusting the side branch's justification would have been the uncertified
step. The balance-source deviation (a possibly different, always
head-chain-observed checkpoint state) is benign in-model under
`StaticValidatorSet`, where all keyed checkpoint states agree on the registry
and the total active balance; in practice it means the FCR may run on slightly
staler effective balances.

**Epoch shape at the consumers — unchanged, and one guard improves.**
`Weak.get_latest_confirmed`'s epoch-start restart branch reads the banked
value through three tests. (i) `is_observed_justified_block_epoch_ok` asks
`compute_epoch_at_slot (get_block_slot store banked.root) + 1 = current_epoch`
— a constraint on the epoch of the *block* the banked checkpoint points at.
Under both the old and the revised write the banked root is the boundary block
of its own checkpoint epoch (`banked.root = get_checkpoint_block store b
banked.epoch`, whose slot is at or below `compute_start_slot_at_epoch
banked.epoch`), so no epoch index moves. (ii) `is_head_unrealized_justified_ok`
asks `banked = store.unrealized_justifications head` — under the revised rule
this is *true by construction* at a gate-passing epoch-start call, since
`update_fast_confirmation_variables` and `get_latest_confirmed` run on the same
store in the same `on_fast_confirmation` invocation, hence on the same head.
Under the old write it compared a store-global value captured one slot earlier
against `UJ[head]`, an unrelated runtime coincidence. So the revision makes the
restart branch *more* able to fire, not less. (iii) `is_confirmed_block_stale`
is a slot comparison and is unaffected. The previous/current rotation
(`previous_epoch_observed_justified_checkpoint := current_epoch_observed_
justified_checkpoint`) is untouched. No downstream consumer lemma needed
adjusting, and none was adjusted.

**Free bonus** (`Weak.has_broadcast_certificate_span_nonempty`,
`WeakBankedJustification.lean`): a true certificate forces non-empty support,
hence a non-empty `Finset.Icc start end`, hence (composed with the store's
current slot being at least `1`) `get_block_slot store head <
get_current_slot store` — the certified head is a pre-boundary block whenever
the gate fires at an epoch start.

**The input invariant.** `Weak.BankedJustificationCertificate` packages the
certified-arm evidence: the second the gate fired, the supplier (the
fork-choice head at that second) and its knownness, the banked root's
knownness, the **raw banking equation** `banked_eq : banked =
(E.store obs second).unrealized_justifications supplier`, and the balance
source with its two economic facts (registry/total-active-balance) plus the
gate itself and its span side conditions. The structure deliberately carries
the equation rather than an ancestry field: the equation is executable, is
discharged by `rfl`-shaped rewriting at construction, and the ancestry is
derived where it is used. `Weak.CertifiedBankedJustification` is the one-shot
invariant: `fcr_store`'s banked observed justified checkpoint is either the
trusted anchor/initialisation value (globally known, hence disseminated for
free by `Execution.store_storeLE`) or a gate-passing rotation with a
certificate. `Weak.checkpoint_state_key_of_broadcast_certificate` supplies the
certificate's own economic side conditions self-containedly (same route as
`Execution.checkpoint_state_key_of_one_confirmed`: an unkeyed balance source is
the default `BeaconState`, whose empty registry makes every candidate inactive,
so a true certificate forces a keyed source).

**The chain-intrinsic ancestry, as a lemma.**
`Weak.auCheckpoint_known_and_below_tip` is the new load-bearing fact: a
checkpoint with accepted AU evidence at a known tip is not only known in the
observer's own store — that half is
`AcceptedSelectorAUCarrier.checkpointRoot_known`, which the repo already had —
but sits *on that tip's chain*. The ancestry half is the `get_ancestor_comp`
step the knownness proof derives and discards: `au_checkpoint_of_known` gives
`c.root = get_checkpoint_block store tip c.epoch`, and walking from `tip` down
to that landed block's own slot lands on it, which is exactly `is_ancestor`.
`Weak.headUnrealizedJustification_known_and_below` specialises it to the rule's
actual read, `store.unrealized_justifications (get_head store).root`, via
`Execution.accepted_unrealized_justification_eq` (`UJ[b] = GU b`) and `gu_AU`.
Everything on this route is causal-store quantified and honesty-free, so it
restates at a possibly-Byzantine observer exactly as
`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory` did;
`Weak.head_known_at_observer` supplies the head's own knownness from
`get_head_root_mem_or` plus `Weak.justifiedRoot_known_at_observer`.

**Consumption.** `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`
is the banked twin of `Execution.confirmed_known_at_all_honest_endpoints_at_observer`:
given a certificate and a "same-slot-capable" timing gate (`E.slot_at
cfg second ≤ E.slot_at cfg m`, equality not required — exactly like
`weak_finalized_epoch_le_remoteJustified`), both the supplier and the banked
root are known at every honest endpoint from the gate on. It routes through
`Execution.certificate_dissemination` (obligation 2) for the supplier, and for
the banked root through `banked_eq` +
`Weak.headUnrealizedJustification_known_and_below` +
`Execution.is_ancestor_transport_closed` — not
`Weak.certificate_chain_dissemination`, whose extra `WalkKnown` premises are
not derivable from the certificate's own fields.

**The amendment — no residual corner.** An earlier draft of this rule left a
"residual corner" open at the anchor arm: the banked root globally known but
the query head not certified, addressed only by scoping S8 to a candidate
arm that never relays an observer-store seed, or by an explicit side
condition. The landed design instead handles the anchor arm by a **symmetric
two-arm consumption**: `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`
is stated over the *invariant* (`CertifiedBankedJustification`, not just the
certificate structure) and concludes banked-root possession at every honest
endpoint in **both** arms — the anchor arm via genesis membership and
`Execution.store_storeLE` (globally known by initialisation; there is no
supplier in this arm, so only the banked-root conjunct applies), the
certified arm via the lemma above. No scoping and no side condition: the
anchor arm is handled by global knownness, not an exception.

> **When the gate fails to bank.** `has_head_broadcast_certificate` is inert
> at an epoch-start update in three situations. First, Finding 6's
> degeneracy, which is *worst* exactly here: if the epoch's first-slot
> proposal has already been received and processed before `.updateVariables`
> fires, `head` is a current-slot block, the span `[head.slot, current_slot −
> 1]` is empty, and the certificate is vacuously false. Second, genuine
> evidence shortfall: the observer's inbox does not contain enough attesting
> weight for the head chain over that span to exceed the span's adversarial
> budget — recall the weak budget carries no equivocation discount (delta 1)
> and grows with span length, and that the observer is an inbox with no
> delivery guarantee, so the votes may exist without reaching it. Third, an
> unkeyed or degenerate balance source, which makes the certificate false by
> construction (this is the self-certification hole the gate is designed to
> close). In every case the rule keeps the previous banked value:
> `current_epoch_observed_justified_checkpoint` is only ever *replaced* by a
> certified, head-chain-observed value, never cleared, so a missed boundary
> costs exactly one epoch of freshness and does not cascade. A fourth,
> *non*-inert liveness case is specific to the revision: the gate fires but a
> side branch carried a higher justification than the head chain, so the
> banked value is lower than the strong rule's would have been — the
> confirmation restart then anchors one justification further back. The
> consequences are: the FCR runs the epoch on the previous epoch's (or a
> head-chain) balance source (harmless in-model under `StaticValidatorSet`; in
> practice, stale effective balances), and `get_latest_confirmed`'s epoch-start
> restart branch cannot fire when the gate failed, since
> `is_observed_justified_block_epoch_ok` demands a banked root exactly one
> epoch back. Safety is unaffected — the gated write only ever installs a
> certified justification observed on the head's own chain, which is a
> sub-behaviour of the strong write in every recency guard, so the delta is
> safety-free by the same monotonicity argument that licensed dropping the
> equivocation discount. This is the price of certified bookkeeping, and it is
> the strongest remaining argument for scheduling the re-anchored-span variant
> (a certificate whose span stays non-empty regardless of where `head` lands)
> next.

**Maintenance along the trajectory — closed.** Both maintenance lemmas are
proved in `WeakBankedJustification.lean`.
`Weak.certifiedBankedJustification_update` has three cases: not an epoch start,
or the gate false ⇒ the banked field is unchanged and the incoming witness
re-indexes (`BankedJustificationCertificate.transport`); the gate true ⇒ the
certified arm at `second := n + 1` with `supplier :=` the boundary head,
`banked_eq` read straight off the revised write via
`Weak.update_fcv_observed_exact`, `supplier_known` from
`Weak.head_known_at_observer`, `banked_known` from
`Weak.headUnrealizedJustification_known_and_below`, `second_pos` from the
call's own slot advance (`E.IsFCRCallAt`), and the two economic facts
*produced* rather than assumed — the gate being true forces its key to be
keyed (`Weak.checkpoint_state_key_of_broadcast_certificate`), after which
`Execution.registryConstant` and
`Execution.checkpoint_states_total_active_balance` apply.
`Weak.weakFcr_certifiedBankedJustification` is the trajectory induction: the
seed is the genesis initializer, which banks the anchor store's
`finalized_checkpoint` — in `E.genesis_store.block_roots`, hence the anchor arm
— and every step is either the update lemma at a real slot advance or a pure
re-index. No honesty hypothesis appears anywhere.

*The honesty was dead.* The strong installation-provenance machinery is
honesty-free throughout: `ExactPrefixAcceptedFFGSemantics.causalStoreGlobalProjection`,
`globalJustified_anchor_or_AUEvidence`,
`Execution.accepted_unrealized_justification_eq`,
`AcceptedSelectorAUCarrier.checkpointRoot_known` and the accepted bundle's
`AcceptedFFGTransitionCoherence.au_checkpoint_of_known` carry **no** honesty
binder (the last is quantified over `E.CausalStore`), and the store geometry
they call (`store_causal`, `store_parentSlotLt`, `store_walkKnownK`,
`store_storeLE`, `store_anchor_block`, `store_anchor_min_slot`) is
node-generic. The one honesty-quantified route,
`ActualResetCheckpointRealization.lean`'s `ResetCheckpointHistoryAt` family,
goes through the **legacy** `FFGTransitionCoherence.au_checkpoint_of_known`
(`∀ w ∈ E.honest, …`) and is simply bypassed in favour of the accepted bundle.

**The branch-switch finding, and how the revision resolves it.** The previous
landing of this delta banked the store-global running maximum
`previous_epoch_greatest_unrealized_checkpoint`, and its input invariant
therefore had to carry a field `banked_below_supplier` asserting that the
banked root lies on the certified head's chain. That field was found to be
**false in general**, and not merely unproved. The running maximum is captured
at the *end of the previous epoch*
(`Weak.weakFcr_previousGreatest_origin` identifies it with `(E.store obs k)
.unrealized_justified_checkpoint` for an exact earlier second `k`), while the
gate certifies the head at the *boundary*. Between those two moments the
store's checkpoints can move branch: `update_unrealized_checkpoints` replaces
the unrealized-justified field on any strictly higher epoch, from any accepted
carrier on any branch, and `on_tick_per_slot`'s epoch pull-up installs whatever
that field holds at the tick. An observer holding `C_A` (epoch `e−1`, branch A)
at second `k`, then receiving a branch-B block whose pulled-up state justifies
`C_B` at epoch `e`, enters epoch `e` with a branch-B head: the gate passes and
banks `C_A`, which the head's certificate does not cover. Placing `C_A` and
`C_B` on one chain is an FFG-safety-grade claim about conflicting certified
justifications at *different* epochs; it does not follow from the store
definitions, the accepted bundle gives only `anchor ∨ GU carrier`, and
`JustificationInterface.justified_descends` covered only the strictly-ahead case
(and was honest-quantified besides). That field has since been deleted outright
(`fe724fd`, P-6): it was an LMD-GHOST weight claim, not an FFG export, and it is
not derivable from the 2/3-target export at `CONFIRMATION_BYZANTINE_THRESHOLD =
25`. So the reasoning here stands a fortiori — see
`docs/p6-justified-descends-derivation.md`, whose §7.2 cites *this* branch-switch
finding as the reason the strong path cannot borrow rule delta 5's chain-intrinsic
banking.

That cross-reference is no longer a live residual in either direction. The named premise
`fe724fd` left behind on the legacy `SpecAssumptions` observed-anchor route, and the whole
observed-anchor cone that threaded it, are deleted (P-6 §8): nothing in the development ever
produced the premise, and the accepted route does not need it — it proves
`obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`, so the strictly-ahead case the deleted
field covered never arises there. The branch-switch finding recorded here is what ruled out
repairing the strong path instead.

An earlier proposal was to close the hole with an extra executable conjunct on
the gate (`is_ancestor store (get_head store) (get_node_for_root
previous_epoch_greatest.root)`). The ratified design does better: by banking
the head's own `unrealized_justifications` entry, the rule never produces a
banked value the head certificate fails to cover, so the hole is closed **at
the source** and no ancestry conjunct, ancestry field, or ancestry obligation
exists at all. `Weak.bankedBelowHead_of_bankedBelowJustified` — the fork-choice
reduction from the head to the store's justified root — is retained as a true
and reusable observer-side fact, but it is no longer on rule delta 5's path.

## Proof migration map

| Strong-model use | Weak-model replacement |
| --- | --- |
| `Synchrony.block_relay` with the **observer** as holder (justification witness / Case-4-style previous-slot receipt, `OnChainAnchorBlockAvailable.of_blockRelay`) | `Weak.CertificateDissemination` applied to the rule-required `has_justification_witness_certificate` |
| `Synchrony.block_relay` with the observer as holder for the **selected block** | `Weak.CertificateDissemination` applied to the certificate implicit in `Weak.is_one_confirmed` |
| `Synchrony.attestation_delivery` (honest votes land at honest nodes) | unchanged — already honest-to-honest; the observer is no longer a guaranteed recipient, which safety does not need |
| `Synchrony.attester_slashing_relay` (observer's equivocation evidence is shared) | removed together with the equivocation discount |
| Paper Assumption 3.2 (vote inclusion) | restated: enough votes reach an **honest** proposer whose block stays canonical; honest-to-honest delivery covers transport, the proposer-honesty budget joins the fault accounting |
| Observer-as-honest instantiation of the accepted theorem | `ObserverContext` with `obs ∉ E.honest`; observer store facts used only via certificates |

Obligations 1 and 2 are stated as named `Prop`s in `WeakSynchrony.lean` and
**both are proved** (no `sorry`s anywhere; the build enforces `-E hasSorry`;
both dischargers depend only on `propext, Classical.choice, Quot.sound`):

- **Obligation 1** (`CertificateHonestSupporter`), discharged by
  `Execution.certificate_honest_supporter` in
  `FastConfirmation/Spec/Proof/WeakCertificateSupporter.lean` from
  `WellFormedExecution + HonestBehavior + ExternalsCoherence + ByzantineBound`
  and a `get_forkchoice_store` genesis. Route: the certificate support sum,
  rewritten onto the ground-truth span committee, is bounded by the weak
  budget whenever no counted validator is honest (`ByzantineBound.span_bound`
  + `weight_mono`), so the certificate inequality forces an honest counted
  supporter; `schedLMProv`/`no_forgery`/`votes_assigned`/
  `committee_assignment_unique` turn its recorded latest message into its
  genuine vote at its assigned slot in the span, and
  `latestMessageProvenance` places the vote root in the observing store.
- **Obligation 2** (`CertificateDissemination`), discharged by
  `Execution.certificate_dissemination` in
  `FastConfirmation/Spec/Proof/WeakCertificateDissemination.lean` (adding
  `PaperSafetySynchrony + JustificationInterface` and the anchor-shape
  genesis facts). Route: Obligation 1's supporter `u`; `votes_head` makes its
  vote the validator-spec attestation over `u`'s own store, whose head root is
  known (`head_root_known`); the observer-store ancestry fact transports into
  `u`'s store via `Execution.is_ancestor_transport_closed`
  (`FastConfirmation/Spec/Proof/WeakAncestryTransport.lean`) — a
  **containment-free** replay of the `get_ancestor` walk using only
  root-injectivity agreement at commonly-known roots plus parent-closure above
  the anchor slot (`get_ancestor_aux_congr_closed`); `block_relay` from `u`
  then delivers `block_root` to every honest store from `end_slot + 1`.

The transport file is the weak model's one genuinely new argument: the
existing `Knownness.mem_of_honest_past_descendant` transports ancestry via
`block_relay` *into* the confirming node, which is illegal for a non-honest
observer. `get_ancestor_aux_congr_closed` needs no store containment in
either direction.

Instance premises of the two `Prop`s (balance source reads the ground
registry; store-computed committees read back the ground-truth assignment)
are discharged at real call sites by `registryConstant`,
`checkpoint_states_total_active_balance` (their honesty hypotheses are
vacuous), and an `ObserverContext`-level committee-readback assumption
mirroring `ExternalsCoherence.committees_agree`.

## The one-shot weak safety theorem (proved)

`Execution.weak_safeFrom_find_latest_confirmed_descendant` and its endpoint
corollary `Execution.weak_confirmed_head`
(`FastConfirmation/Spec/Proof/WeakOneShotSafety.lean`): for an **arbitrary**
observer `obs` (honest or not — nothing is assumed in its favour), at any
within-horizon second, under
`WeakObserverMarginAssumptions` (the strong `SelectedMarginAssumptions`
verbatim — synchrony stays honest-to-honest — plus `ObserverCoherence`:
committee readback and justified-root knownness at the observer's own store),
with a safe canonical input and the covered-margin supply as an explicit
premise (`hmargin`, the same interface layering the strong development uses at
`CoveredMargin`), the output of `Weak.find_latest_confirmed_descendant` is
`SafeFrom` — an ancestor of every in-horizon honest node's fork-choice head
from the query slot onward. Both theorems depend only on
`propext, Classical.choice, Quot.sound`.

Supporting files, replacing every observer-honesty site on the one-shot path:
`WeakRulePredicateBridge` (weak ⇒ strong for all rule predicates),
`WeakEconomicReadback` (economic core over store-generic committee readback),
`WeakConfirmedSupporter` (honest supporter out of `is_one_confirmed` at a
non-honest store), `WeakAncestryEndpoint` (containment-free `is_ancestor`
replay), `WeakConfirmedDissemination` (dissemination routed from the honest
supporter — both receiver-side `block_relay` uses deleted),
`WeakSelectorInversion` (weak-selector inversion exposing strong predicates
plus the justification-witness certificate), `WeakOneShotSafety` (assembly;
also clones the two crossing-edge closers, whose `committees_agree`
dependency at the observer was genuine, contrary to the initial audit).

**`hmargin` is now discharged at a non-honest observer** (margin-discharge
wave, Stages G–J below); see that section for the full account.
`Execution.weak_safeFrom_find_latest_confirmed_descendant` and
`Execution.weak_confirmed_head` above remain as the *interface-layered*
statements — they still take `hmargin : SelectedCoveredMarginSupplyAt` (the
strong Prop) as an explicit premise, matching `CoveredMargin`'s own interface
shape, and stay useful wherever a caller already has a strong margin supply
in hand (e.g. from the existing `_of_pipeline_minimal` / `_of_stateRealization_
minimal` FFG-realization wrappers). The new, fully weak-native headline —
`Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged` — is
recorded in "Margin discharge (stages G–J)" below.

Historical note on the blocker this wave removed: `hmargin`'s Stage-8
obstruction was `WindowRecordedEpochMax` — epoch-freshness of the observer's
recorded LMD cells — which the strong development derives from vote delivery
*to* the observer (`vote_ubiquity`), a guarantee the inbox model removes and
broadcast certificates cannot replace (it asserts the *absence* of unseen
newer votes). Of the three candidate resolutions once listed here — (A) rule
delta 3 (epoch-fresh scorer, landed above), (B) an explicit
recorded-epoch-freshness assumption at the observer, (C) keep `hmargin` as an
interface premise — the wave took a variant of (A) sharper than originally
scoped: rather than deriving `WindowRecordedEpochMax` at the observer from
freshness and then re-running the strong (ground-truth-indexed) base-strip
argument, every ledger class on the weak path is read directly at the honest
*endpoint*, so `WindowRecordedEpochMax` at the observer is never needed at
all. See "Margin discharge (stages G–J)" for the design decision and its
consequences.

## The finalized-base corollary (proved)

The one-shot theorem above still takes its `SafeFrom` seed (`hbase`) as an
explicit premise. `FastConfirmation/Spec/Proof/WeakFinalizedInput.lean` closes
that gap for the finalized-checkpoint branch: it derives `hbase` — and the
seed's own knownness (`hlcr`) — from the accepted FFG semantics bundle
instead of asking the caller to supply either.

The honest origin of a non-anchor finalized field
(`Execution.FinalizedHonestVotingSourceOrigin` /
`Execution.finalizedHonestVotingSourceOrigin_of_causalStore`) replaces the
strong route's whole-store relay from an honest reader by the finalizing
certificate's own honest signer: two quorums of the certified finalizing link
intersect in an honest validator, whose genuine vote read its source off its
own store (`acceptedHonestAttestationDataSourceEqVSAtTarget`), and that vote
precedes the reading store's current slot because the including block does
(`includedAttestationSlot_lt_causalStoreCurrentSlot`). Honest-to-honest
`block_relay` then carries the signer's seed to every honest endpoint, and
`votingSource_epoch_le_remoteJustified_of_known` adopts the epoch there
(`Execution.weak_finalized_epoch_le_remoteJustified`) — the reading node
itself is never assumed honest, and no reading-store content besides its
finalized field and clock is relayed.

`Execution.weak_finalizedReset_justifiedDom_of_synchrony` and
`Execution.weak_finalizedReset_safeFrom_of_synchrony` are weak twins of
`finalizedReset_justifiedDom_of_nextSlotSynchrony` /
`finalizedReset_safeFrom_of_nextSlotSynchrony`
(`AcceptedFinalizedNextSlotSafety.lean`) built on that origin lemma: the
observer-honesty binder is dropped, and the single honesty site — the strong
next-slot adoption call — is replaced by `weak_finalized_epoch_le_
remoteJustified`. Because that lemma's relay gate is same-slot-capable
(`slot_at q ≤ slot_at m`, no `+ 1`), the `SafeFrom` conclusion holds from
`E.slot_start cfg (E.slot_at cfg q)` — the **query slot's own start** —
rather than one slot after a separately-quantified next-slot marker. This is
a property of the certificate route specifically; the strong next-slot
theorems are not themselves upgraded to same-slot by it.

`Execution.weak_safeFrom_find_latest_confirmed_descendant_from_finalized` and
its endpoint form `Execution.weak_confirmed_head_from_finalized` compose the
two pieces: `hlcr` and `hbase` (at `E.slot_start cfg (E.slot_at cfg q)`, the
exact shape `weak_safeFrom_find_latest_confirmed_descendant` expects) come
from `finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory` and
`weak_finalizedReset_safeFrom_of_synchrony` respectively, both applied at the
observer's own `(obs, q)`. The result is the same one-shot conclusion, seeded
directly at the observer's own finalized checkpoint instead of at a
caller-supplied `SafeFrom` input:

```lean
theorem weak_safeFrom_find_latest_confirmed_descendant_from_finalized
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (hmargin :
      Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root ≠
        fcr_store.store.finalized_checkpoint.root →
      E.SelectedCoveredMarginSupplyAt cfg ext
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store
          fcr_store.store.finalized_checkpoint.root)
        fcr_store.store.finalized_checkpoint.root obs q fcr_store) :
    E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext fcr_store
        fcr_store.store.finalized_checkpoint.root) q
```

**Premise surface.** `hW.base : SelectedMarginAssumptions` is the same
ratified floor the plain one-shot theorem uses; `B`, `hanchor`, `hboundary`,
`hphase`, `hboundaryPhase` are the ordinary accepted-FFG-semantics /
phase-source-coherence floor already used throughout the accepted pipeline
(`AcceptedActualFCRNextSlotSafetyFacade.lean`), not new premises specific to
the weak route. `ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions`
and `SelectedMarginAssumptions.toFFGAccountabilityAssumptions` project the
narrower trajectory and accountability interfaces the finalized-base
machinery consumes out of `hW.base` — they are derived, not additional
fields. In particular the FFG accountability statements
(`certified_justified_unique`, `certified_links_not_surround`, consumed via
`certified_finalized_prefix`) are **theorems** of `hW.base`
(`SelectedMarginAssumptions.toFFGAccountabilityAssumptions` +
`CheckpointCertificateAccountability.of_assumptions`), not economic/behavioral
premises added by this corollary.

After this corollary, the only extra-floor assumption about the observer's
own store is `hW.committees_agree` (a one-node extension of the committee
idealization to a non-honest observer) — plus the pre-existing Stage-8
`hmargin` premise above, unchanged by this corollary and carried for exactly
the same reason. Since this corollary already carries `B`/`hanchor`/
`hboundary` (and derives `hT` from `hW.base`), it takes the slim
`WeakObserverAssumptions` and builds the internal
`WeakObserverMarginAssumptions` itself via
`WeakObserverAssumptions.toMarginAssumptions`: `justified_root_known` is
discharged by
`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`
(packaged as `ObserverCoherence.of_acceptedTrajectory`) and is not a
premise.

Both `weak_safeFrom_find_latest_confirmed_descendant_from_finalized` and
`weak_confirmed_head_from_finalized` depend only on
`propext, Classical.choice, Quot.sound` (`scripts/Audit.lean`'s
`publicWitnesses` set, 17 declarations at the time this corollary landed, now
19 — see "Margin discharge (stages G–J)" below).

## Margin discharge (stages G–J)

The margin-discharge wave lands `hmargin`-free one-shot weak safety:
`Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged` and its
endpoint form `Execution.weak_confirmed_head_discharged`
(`FastConfirmation/Spec/Proof/WeakOneShotSafetyNative.lean`). Nothing on this
path assumes delivery of votes *to* the observer.

```lean
theorem weak_safeFrom_find_latest_confirmed_descendant_discharged
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (E.slot_start cfg (E.slot_at cfg q)))
    (hfilter : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ≠ lcr →
      Weak.SelectedStrictEdgeFilterSupplyAt cfg ext E
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) lcr obs q
        fcr_store) :
    E.SafeFrom cfg ext (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) q
```

### The endpoint-direct decision

The strong development's margin machinery classifies each honest window
member's ledger contribution (`Sclass`/`Aclass`/`Xclass`) at the *observer's*
own index `(obs, q)`, then transports the two honest classes to the
consuming honest endpoint `(w, m)`. That transport is exactly the honest→
non-honest relay the weak model forbids: converting an observer-indexed
`Sval`/`Aval` strip to the endpoint needs `hSt : SupportsDesc cfg ext obs q …
→ SupportsDesc cfg ext w m …`, which in turn needs the ground vote root to be
known in *both* stores — and an arbitrary `Sclass cfg ext obs q` member's
ground vote root need not be in a non-honest observer's block map at all.

The wave's one architectural decision routes around that wall instead of
patching it: **every ledger class on the weak margin path is read at the
honest endpoint `(w, m)`, never at the observer.** The observer contributes
only two *sums* — the weak fresh attestation score and the weak fresh
discount (`Weak.get_duty_fresh_attestation_score` /
`Weak.get_support_discount`, rule delta 3) — and each sum is placed directly
into `Sclass cfg ext w m` / `Aclass cfg ext w m` by freshness ⇒ newest-vote
(`Execution.recorded_lm_is_newest_in_store`, store-generic and honesty-free)
composed with honest→honest `block_relay` from the voting supporter's own
store (never *to* the observer) and `Execution.is_ancestor_replay_closed`
(`WeakEndpointClasses.lean`'s `freshSupporter_mem_endpoint_Sclass` /
`freshParentStuck_subset_endpoint_Aclass`). This is strictly less work than
the strong development would need at the observer: it deletes
`support_transport` / `ancestor_transport` / `classes_base_transport_honest`
/ `bval_strip_transport` from the weak path entirely, and every
`WindowRecordedEpochMax` premise at the observer along with them
(`WeakEndpointClasses.lean`, `WeakCrossingSets.lean`, `WeakSiblingScore.lean`,
`WeakSelectedMarginInputs.lean`).

### The non-subtractive crossing collapse

`Weak.compute_adversarial_weight` (rule delta 1) has no equivocation
subtraction, so the crossing-edge arm's *subtractive* conclusion — the
`− weight (crossingEquivPre …)` term the strong `crossingEdgeFuture_
endpoint_inequality_of_confirmed_window` carries — collapses to the same
non-subtractive shape as the intra-epoch/future-crossing arm. Consequently:

* `Weak.CrossingSelectedMarginInputs` (`WeakSelectedMarginInputs.lean`) is
  ONE structure for both crossing regimes, not two — `CrossingEdgeSelected
  MarginInputs` and `FutureCrossingSelectedMarginInputs` merge, and
  `Weak.SelectedEdgeMarginInputsAt` has three constructors, not four;
* `Weak.crossing_sibling_score_of_endpointLedger`
  (`WeakSiblingScore.lean`) serves both regimes with one non-subtractive
  bound, replacing the strong development's separate subtractive
  `crossingEdge_sibling_score_of_endpointLedger_minimal`;
* `Weak.freshByzSupporters_le_Bval` (`WeakCrossingSets.lean`) replaces
  `LastAlgebra.hR4b_of_confinement` with a 6-line subset argument (fresh byz
  supporters are non-honest span members — no equivocation score to split
  out);
* this is the **last use of `Synchrony.attester_slashing_relay` on the
  one-shot path** — the strong crossing arm's equivocation-visibility relay
  (`crossing_equivocation_score_split`, `crossingEquivPre`) never appears in
  the weak graph. Every remaining `Synchrony.block_relay`/`attestation_
  delivery` site reachable from the one-shot theorem is honest→honest.

### The remaining premise surface

After this wave, `weak_safeFrom_find_latest_confirmed_descendant_discharged`'s
premises are:

* **`hfilter` — the FFG-realization filter supply.** *(Historical note: at
  the time this corollary landed, this was expected to need a further
  `Execution.WeakRecentSourceSeedDissemination`-style relay premise. The
  `hfilter`-discharge wave's scout report found this expectation wrong: every
  observer-touching relay site the strong development uses to discharge the
  matching filter supply either closes with no new premise at a non-honest
  observer (confirmed-block dissemination, provenance, or a broadcast/
  witness certificate — all already available) or is closed by a
  monotonically stricter rule delta (delta 5′, gating the previous
  uncertified epoch-start escape behind the head broadcast certificate) that
  adds no assumption to the floor. `Weak.SelectedStrictEdgeFilterSupplyAt` is
  now fully discharged, with no `hfilter`-shaped premise surviving anywhere —
  see "The closed one-call step" below. `Execution.WeakRecentSourceSeedDissemination`
  was never landed and is not needed.)*
* **`hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext`** —
  endpoint-side only. It survives `vote_ubiquity`'s retirement because its
  *other* consumer, `endpointLedgerFields_from_execution_minimal`, runs
  entirely at the honest endpoint `(w, m)`, where honest-to-honest delivery
  is unchanged; only its observer-side instantiation
  (`windowRecordedEpochMax_at_query_minimal` at `(obs, q)`) disappears.
* **`committees_agree`** (inside `hW`) — the observer's own store computes
  committees consistently with the ground-truth assignment. This is the only
  genuinely free premise about the observer's own trajectory left:
  `ObserverCoherence.justified_root_known` is derivable
  (`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`) and,
  wherever the accepted-FFG package is in scope — i.e. at every top-level weak
  statement — it is derived rather than assumed, so the caller-facing bundle
  is `E.WeakObserverAssumptions` (floor + `committees_agree`; `obs` itself is
  unconstrained). The `hmargin`/`hfilter`-carrying one-shot floor forms
  (`weak_safeFrom_find_latest_confirmed_descendant`,
  `…_discharged`, and their endpoint forms), which carry no `B`, still take
  the internal `E.WeakObserverMarginAssumptions`.

### The finalized-base composition

`Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged_from_
finalized` and its endpoint form `weak_confirmed_head_discharged_from_
finalized` (`WeakOneShotSafetyNative.lean`) compose the discharged headline
with `WeakFinalizedInput.lean`'s finalized-base derivation of `hlcr`/`hbase` —
a cheap plumbing composition, identical to `weak_safeFrom_find_latest_
confirmed_descendant_from_finalized` above except that its final call is to
the discharged headline, so `hmargin` becomes `hfilter`.

`scripts/Audit.lean`'s `publicWitnesses` set now includes
`weak_safeFrom_find_latest_confirmed_descendant_discharged` and
`weak_confirmed_head_discharged` (19 declarations); both depend only on
`propext, Classical.choice, Quot.sound`.

## The closed one-call step

Stage S8 assembles the `hfilter`-discharge wave's own headline
(`Weak.StrictSelectorAdvanceAt.observerCall_selectedStrictEdgeFilterSupplyAt_
lazy`, `WeakObserverStrictCallFilterInputs.lean` — the S0–S7 stack's closed
strict-edge filter supplier, taking no `hinputs` bundle at all) with
`weak_safeFrom_find_latest_confirmed_descendant_discharged` above
(`WeakOneShotSafetyClosed.lean`). The result is the closed one-call weak
safety step, at an actual FCR call, with **no `hmargin` and no `hfilter`**:

```lean
theorem weak_safeFrom_observerCall_closed_lazy
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hji : JustificationInterface cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hphase0 : Phase0SourceCoherence cfg ext)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : AcceptedEpochCheckpointProjection B.anchor (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hCbase : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext obs n)
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1)))) :
    E.SafeFrom cfg ext (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result (n + 1)
```

The assembly is a case split on `E.weakGetLatestConfirmedTraceAt`'s exact
four-way candidate-history classification, uniform over which branch the
actual call took: the three "unchanged" branches close directly from
`hbase` (rewritten from the query slot's start to the call's own second
`n + 1` via `Execution.slot_start_eq_succ_of_advance_minimal`); the
`strictSelected` branch exposes exactly the `Weak.OrderedCandidateInputOrigin`
and `Weak.StrictSelectorAdvanceAt` facts the closed filter supplier consumes,
and its output is fed straight into `weak_safeFrom_find_latest_confirmed_
descendant_discharged`'s `hfilter` slot.

### The four one-shot closed witnesses were retired

Until `docs/weak-final-wave.md` W7 this file also carried four *one-shot*
closed statements — `weak_safeFrom_observerCall_closed`,
`weak_confirmed_head_closed` and their two `_from_finalized` forms — and they
were the four registered weak witnesses in `scripts/Audit.lean`. They took an
**eager** obligation route driven by an observer-quantified normative proviso
(`Weak.ObserverHistoricalA32CallAssumptions.observer_helper_provisos`), because
a one-shot statement's only safety input is `hbase` at its own second and
there is no route from that to `Weak.ObserverPriorCallWriteBackSafe`, the
trajectory fact the lazy route discharges its closures with; the observer's
non-honesty rules out borrowing the strong fold's honest-node output.

They are gone. They were subsumed by the full-rule fold (which closes *every*
second of the observer's trajectory, not one call), they had no consumers, and
they existed only as carriers of that proviso. Deleting them removed the eager
obligation route, the eager obligation families, the eager weak crossing
constructors and both observer proviso records — so no weak statement carries
a normative observer proviso any more. The `_from_finalized` compositions went
with them; they needed one extra scenario premise
(`hbfr : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
(E.weakFcrStep cfg ext obs n).store.finalized_checkpoint.root`) recording that
*this particular call's* candidate input reduced to the observer's own
finalized checkpoint, which the trajectory fold discharges branch-by-branch
instead.

### The complete premise surface, classified against the ratified floor

Every premise of `weak_safeFrom_observerCall_closed_lazy` — and, apart from
`hprior`/`hcall`/`hinput`/`hbase`, of the four trajectory headlines (the
audited unconditional pair and its conditional internal twin) — classified:

* **`hW : E.WeakObserverAssumptions cfg ext obs`** — `hW.base :
  SelectedMarginAssumptions` is the ratified floor: honest-to-honest
  Δ-delivery and the β bound (`hW.base.synchrony : PaperSafetySynchrony` —
  the **single** synchrony assumption of the model since
  `refactor: single synchrony assumption; the boundary delivery case is
  derived`: its delivery clause is horizon-scoped on the vote's slot and cast
  second but *not* on the mandated receipt second, so the old separate
  boundary record `HorizonVoteDeliveryLookahead` is now the derived lemma
  `PaperSafetySynchrony.toDeliveryLookahead`, and the old receipt-gated clause
  is the derived lemma `toHorizonScopedDelivery`;
  `Spec.attestation_delivery_pair_iff` proves the merged field is the same
  proposition as the old pair, so no assumption content was added to the
  model; the trajectory headlines, which carried both halves, come out exactly
  equal — one field lighter on the surface — while the weak one-shot witnesses,
  which carried only the gated half, now carry the boundary case too, that
  being what "one synchrony assumption" costs),
  estimation soundness and honest behavior/BLS (`hW.base.honest_behavior`),
  the static registry (`hW.base.static_validators`), the Byzantine bound
  (`hW.base.byzantine_bound`), `ExternalsCoherence` (static committees, ground
  truth), whole seconds, and genesis shape. The merge also adds
  `hW.genesis` for the committed anchor and `hW.validity` for indexed
  attestation validity on observer-run states. `hW.committees_agree` states
  that the observer's store computes committees consistently with the
  ground-truth assignment. There is no constraint on `obs` itself.
  `justified_root_known` is derived and no longer appears on the surface —
  `ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory` proves
  it from `B`/`hT`/`hanchor`/`hboundary`, which every statement on this list
  already carries, and
  `WeakObserverAssumptions.toMarginAssumptions` performs the promotion to the
  internal `WeakObserverMarginAssumptions` bundle inside the proofs.
* **`hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext`** —
  endpoint-side only (§"The endpoint-direct decision" above); part of the
  accepted synchronized-clocks/honest-behavior floor.
* **`B : ExactPrefixAcceptedFFGSemantics cfg ext E`, `hT`, `hanchor`,
  `hboundary`, `hDelay`, `hphase0`, `hpaper`, `P`, `V`, `hanchorExact`** —
  the accepted FFG semantic contracts already used throughout the accepted
  one-shot facade (`AcceptedActualFCRNextSlotSafetyFacade.lean`): genesis/
  anchor bookkeeping (`hanchor`, `hboundary`, `hanchorExact`, `P`), the
  accountability and finalization-delay bundle (`hT`, `hDelay`), and the
  Phase-0 source-coherence/link-validity/inclusion contracts (`hphase0`,
  `hpaper`, `V`) the accepted development already carries as floor, not
  premises new to the weak route. On the **trajectory headlines** three of
  these are no longer binders at all (`refactor: premise surface equals
  assumption set on the trajectory headlines`): `hT` is derived from
  `hW.base` by
  `ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions`, and
  `hphase0` / `hboundaryPhase : Phase0BoundarySourceCoherence cfg ext` (the
  latter for the finalized arm of the candidate-input derivation) are read off
  the call-contract supplement below.
* **`hji : JustificationInterface cfg ext E`** — the same executable
  justification-selection contract the accepted development's actual-call
  facade already assumes.
* **`hCbase`** — the completed-prefix call contract. The closed one-call step
  takes the accepted development's 6-field
  `E.AcceptedHistoricalA32CompletedPrefixCallAssumptions` (7 before the
  single-synchrony refactor deleted `delivery_lookahead`); the trajectory
  headlines take the 3-field
  `E.AcceptedHistoricalA32CompletedPrefixCallSupplement` (`phase0_source`,
  `phase0_boundary_source`, `balance_floor`) and rebuild
  the 6-field record internally, because its other three fields
  (`synchrony`, `static_validators`, `byzantine_bound`) are literally fields of
  `hW.base`. The supplement's former fourth field `delivery_lookahead` is
  gone: the single-synchrony refactor moved its content into
  `hW.base.synchrony`'s delivery clause, so it is supplied by a premise the
  headlines already carried — a premise weakening, not a new assumption. No observer-indexed extension of it exists any
  more: the historical A3.2 crossing payload is manufactured *lazily* at the
  consuming call from the fold's own output at strictly earlier seconds
  (`Weak.LazyCertAt` / `Weak.LazySupportAt`), which needs no proviso at all.
  Obligation X1 is therefore **discharged**, not assumed.
* **`hfit : EpochEndsFitUint64 cfg`** — a pure configuration-arithmetic fact
  (slots-per-epoch bookkeeping fits in `UInt64`), independent of honesty or
  synchrony.
* **`hcall : E.IsFCRCallAt cfg ext obs n`** — the actual-call clock predicate
  ("the store's slot advanced from `n` to `n + 1`"), honesty-free and
  store-level, shared verbatim with the accepted development
  (`FCRCallContracts.lean`). Not a premise of the trajectory headlines.
* **`hprior`, `hinput`, `hbase`** — the threaded trajectory fact and the
  call's own candidate input being known and `SafeFrom` from the start of the
  query slot. All three are *derived* inside the fold; none is a premise of
  the trajectory headlines.

**Not carried, anywhere in this premise list:** no delivery of votes, blocks,
or store contents *to* or *from* the observer (`obs` need not be a
`Synchrony`/`PaperSafetySynchrony` sender or receiver at all); no observer
honesty (and, since the obs-not-honest field was dropped, no *non*-honesty
either: `obs` is simply an arbitrary index);
no equivocation-visibility relay (`Synchrony.attester_slashing_relay` does
not occur on this path — the non-subtractive crossing collapse above retired
its last use); and no Paper Assumption 3.2 premise beyond the floor and the
accepted development's own unchanged `helper_provisos`.

### The audited witness list

`scripts/Audit.lean`'s `publicWitnesses` set (21 declarations) registers, on
the weak side:

* `Execution.weak_safeFrom_find_latest_confirmed_descendant` /
  `weak_confirmed_head` and their two `_from_finalized` forms — the
  `hmargin`-carrying one-shot floor forms;
* `Execution.weak_safeFrom_find_latest_confirmed_descendant_discharged` /
  `weak_confirmed_head_discharged` — the `hmargin`-free forms;
* `Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
  and `Execution.weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot`
  (`WeakObservedResetSeedSafety.lean`) — the **unconditional** full-rule fold
  and its endpoint form, with `hOR : Weak.ObservedResetSeedSafety` discharged
  from the floor. These two are the weak headlines.

The **conditional** pair
`Execution.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold` /
`…_head_of_weakFullRuleFold_nextSlot` (`WeakTrajectorySafety.lean`) is no
longer registered (`refactor: the unconditional fold pair are the weak
headline witnesses`): carrying `hOR` makes it a strictly weaker restatement of
the unconditional pair, which discharges `hOR` from premises the conditional
pair already has. It remains an internal theorem — the unconditional pair's
proof chain runs through it, and the one-call-at-a-time reading of `hOR` stays
available.

The unconditional pair's premise list is, in full: `B`, `hji`, `hanchor`,
`hboundary`, `hDelay`, `hpaper`, `P`, `V`, `hanchorExact`, `hW`, `hwalkDomain`,
`hCbase` (the 3-field supplement) and `hfit` — plus, on the endpoint form, the
endpoint binders `hw`/`hnm`/`hnext`/`hHm`. All registered witnesses depend only
on `propext, Classical.choice, Quot.sound`
(`lake env lean scripts/Audit.lean`).

## The full rule (trajectory safety)

The step above is still *one call*: its `hprior`/`hinput`/`hbase` premises are
exactly what an induction over `E.weakConfirmed`'s own history has to supply.
That induction has landed in
`FastConfirmation/Spec/Proof/WeakTrajectorySafety.lean`, with the two audited
weak headlines in `WeakObservedResetSeedSafety.lean` on top of it; the invariant, the four-branch step, the base
case and the discharge of the last obligation
(`Weak.ObservedResetSeedSafety`, safety of the epoch-start observed-reset seed
at a non-honest observer) are documented in
[`weak-full-rule.md`](weak-full-rule.md).
