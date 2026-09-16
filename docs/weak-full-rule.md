# Weak full rule: the trajectory invariant and its staged proof plan

Companion to [`weak-synchrony.md`](weak-synchrony.md). That note takes the weak
model from the network delta to the **closed one-shot** theorem: at one genuine
FCR call, given that the call's own candidate input is known and `SafeFrom`, the
weak selector's result is `SafeFrom`. This note takes it from one call to the
**whole trajectory**: for every in-horizon second `n`, the root the observer's
weak FCR holds at `n` is safe.

Stages 1–6 of that effort have landed, across
[`WeakTrajectorySafety.lean`](../FastConfirmation/Spec/Proof/WeakTrajectorySafety.lean),
[`WeakObservedRestartAdoption.lean`](../FastConfirmation/Spec/Proof/WeakObservedRestartAdoption.lean),
[`WeakObservedRestartDynamicSafety.lean`](../FastConfirmation/Spec/Proof/WeakObservedRestartDynamicSafety.lean)
and
[`WeakObservedResetSeedSafety.lean`](../FastConfirmation/Spec/Proof/WeakObservedResetSeedSafety.lean).
**The full-rule fold is unconditional**: the trajectory theorem and its
endpoint form now carry no residual obligation, only the ratified floor. The
one remaining stage is audit registration (stage 7), which is a human-review
gate rather than a proof. Everything below is either proved in those modules,
proved elsewhere and consumed there, or explicitly labelled open.

## The gap this closes

`WeakOneShotSafetyClosed.lean`'s own docstring records the gap verbatim:

> closing the "carried"/"observed-reset" branches unconditionally would need an
> induction over `E.weakConfirmed`'s own `SafeFrom` history that this wave does
> not build.

Concretely, `Execution.weak_safeFrom_observerCall_closed` takes two premises it
cannot produce:

```lean
(hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
  (E.weakFcrStep cfg ext obs n).store.block_roots)
(hbase : E.SafeFrom cfg ext
  (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
  (E.slot_start cfg (E.slot_at cfg (n + 1))))
```

and its self-contained composition `weak_safeFrom_observerCall_closed_from_
finalized` discharges them only under the **scenario predicate**

```lean
(hbfr : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved =
  (E.weakFcrStep cfg ext obs n).store.finalized_checkpoint.root)
```

— "this particular call reduced to a finalized reset", which most seconds do
not satisfy (most are "carried"). The trajectory induction is what makes the
scenario predicate unnecessary: at a carried call the previous second's own
invariant *is* `hbase`, and the finalized-reset arm's `hbase` is then needed
only when the reset genuinely fired, where `Weak.FinalizedResetCandidateInputAt.
input_eq` supplies `hbfr` for free.

## The invariant

```lean
def WeakConfirmedSafeFromFollowingSlot (obs : ValidatorIndex) (n : ℕ) : Prop :=
  E.SafeFrom cfg ext (E.weakConfirmed cfg ext obs n)
    (E.followingSlotStart cfg n)
```

In words: *the root the observer's weak FCR trajectory holds at second `n` is
an ancestor of every in-horizon honest node's fork-choice head from the first
second of the following slot onward.*

It is the exact weak twin of `Execution.ConfirmedSafeFromFollowingSlot`
(`AcceptedActualFCRNextSlotSafetyFold.lean`), with two differences, both on the
index rather than the statement: it reads `E.weakConfirmed` (the weak
bookkeeping trajectory, `WeakFCRCallContracts.lean`) instead of `E.confirmed`,
and it is asserted at an observer carrying **no** `obs ∈ E.honest` binder.
`E.followingSlotStart` and `E.SafeFrom` are reused verbatim — the weak model
changes neither the deadline convention nor the safety predicate.

### Why a single conjunct

The obvious design bundles three facts: safety, candidate knownness, and the
rule-delta-5 "certified banked justification" bookkeeping invariant. That would
duplicate two landed inductions. Both auxiliary facts are already proved for
*every* in-horizon second, by their own all-seconds weak inductions, and
neither depends on safety:

| auxiliary fact | producer | honesty at `obs` |
| --- | --- | --- |
| `E.weakConfirmed obs n ∈ (E.store obs n).block_roots` | `Weak.acceptedConfirmedSourceHistoryAt … .confirmed_known` (`WeakCandidateSourceHistory.lean`) | none |
| `Weak.CertifiedBankedJustification … (E.weakFcr obs n)` | `Weak.weakFcr_certifiedBankedJustification` (`WeakBankedJustification.lean`) | none |

So the fold **consumes** them as inputs. The safety induction is genuinely
one-conjunct, which is why the whole file is short.

The second row is the "restart" bookkeeping the full rule needs: rule delta 5
gates the epoch-start installation of
`current_epoch_observed_justified_checkpoint` on a head broadcast certificate
and banks the certified head's *own* unrealized justification, and
`Weak.CertifiedBankedJustification` is the resulting invariant — "the field
either holds a genesis root or carries a `Weak.BankedJustificationCertificate`".
It was already maintained across the whole trajectory before this stage, so the
certified-justification-witness requirement costs the full-rule induction
nothing.

## The base case ("restarts")

`Execution.weakConfirmedSafeFromFollowingSlot_zero`. The weak trajectory is
seeded by the same genesis initializer as the strong one
(`Execution.weakConfirmed_zero`: `E.weakConfirmed obs 0 =
(E.store obs 0).finalized_checkpoint.root`), so the seed is the trusted anchor
`B.anchor.root` under `hanchor`/`hT.genesis`, and
`Execution.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory` gives
`SafeFrom … 0`, relaxed to the deadline by `SafeFrom.mono`.

This is checkpoint-sync safe in exactly the sense
`Weak.acceptedConfirmedSourceHistoryAt_zero` already is: the anchor is read off
the store's own initial finalized checkpoint, not asserted to be a genesis
literal. A node that starts from a weak-subjectivity checkpoint rather than
genesis therefore needs no separate base case — the trusted-anchor boundary
alignment (`TrustedAnchorBoundaryAligned`) is the whole of the assumption, and
it is already the accepted development's floor.

Nothing about the base case is observer-specific:
`trustedAnchor_safeFrom_of_acceptedGlobalTrajectory` quantifies honesty only
over the *receiving* endpoint.

## The step: four branches, three candidate origins

At a call second the invariant's own deadline collapses onto the call —
`Execution.followingSlotStart_eq_succ_of_call` gives
`E.followingSlotStart n = n + 1`, and
`Execution.slot_start_eq_succ_of_advance_minimal` gives
`E.slot_start (E.slot_at (n + 1)) = n + 1`. So the induction hypothesis is
*literally* the `hbase` shape the closed theorem wants, at the carried origin.

The four-way operational branch classification
(`Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch`) is
`carriedUnchanged | finalizedResetUnchanged | observedResetUnchanged |
strictSelected`. The closed one-shot theorem already case-splits on it
internally and closes all four *given* `hinput`/`hbase`; what the step has to
do is supply those two over the **three candidate origins**, which
`Weak.CandidateHistoryCallBranch.origin` (new, trivial plumbing) projects out
of all four branches uniformly:

### Carried — `trace.afterObserved = query.confirmed_root`

* `hinput`: `Execution.weakFcrStep_confirmed_root` rewrites the query field to
  `E.weakConfirmed obs n`, then `(E.store_storeLE … (Nat.le_succ n)).1`
  transports the previous second's `confirmed_known` forward one second.
* `hbase`: the induction hypothesis, after `followingSlotStart_eq_succ_of_call`.

Discharged. **This is the branch the one-shot wave could not close**, and it is
free once the induction exists.

### Finalized reset — `trace.afterObserved = query.store.finalized_checkpoint.root`

* `hinput`:
  `Execution.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
  … .root_known`, at `(obs, n + 1)`; honesty-free.
* `hbase`: `Execution.weak_finalizedReset_safeFrom_of_synchrony`
  (`WeakFinalizedInput.lean`). This is the weak arm's real gift: because its
  relay gate is same-slot-capable, its conclusion already holds from
  `E.slot_start (E.slot_at q)` — the **query slot's own start** — so at
  `q := n + 1` it lands exactly on `hbase`'s index with no next-slot slack to
  absorb. It carries no observer-honesty binder.

Discharged. Note what this does to the one-shot wave's `hbfr` scenario
predicate: it is *not* needed at trajectory level. `hbfr` existed because
`weak_safeFrom_observerCall_closed_from_finalized` had to assume, without
evidence, that the actual call's input was the finalized checkpoint. Inside the
fold that assumption is replaced by the branch we are in:
`Weak.FinalizedResetCandidateInputAt.input_eq` *is* `hbfr`, produced by the
classifier rather than assumed. The scenario predicate disappears.

### Observed reset — `trace.afterObserved = query.current_epoch_observed_justified_checkpoint.root`

* `hinput`: `Weak.weakFcrStep_observed_known` — rule delta 5's `banked_known`,
  discharged for the whole weak trajectory, honesty-free.
* `hbase`: `Weak.ObservedResetSeedSafety`, consumed here as a named `Prop` and
  proved by `Weak.observedResetSeedSafety_of_acceptedDynamics` (stage 6).

Five of the six cells are discharged in `WeakTrajectorySafety.lean`. The sixth
was the entire residue of the full-rule effort; it is now proved in
`WeakObservedResetSeedSafety.lean` (stage 6).

## The obligation that used to be open

```lean
def ObservedResetSeedSafety (E : Execution Root) (obs : ValidatorIndex) : Prop :=
  ∀ n : ℕ, E.WithinHorizon cfg (n + 1) → E.IsFCRCallAt cfg ext obs n →
    ∀ trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n),
      Weak.ObservedResetCandidateInputAt cfg ext
          (E.weakFcrStep cfg ext obs n) trace →
        E.SafeFrom cfg ext trace.afterObserved (n + 1)
```

It is stated as a named `Prop` rather than left as a proof placeholder, in the
style `Spec/Model/WeakSynchrony.lean` already uses for
`Weak.CertificateHonestSupporter` / `Weak.CertificateDissemination` — the build
gate rejects proof placeholders outright (`lakefile.toml`'s `-E hasSorry`,
`scripts/check_build.sh`, and `scripts/validate.sh`'s exact-string scan), so a
named obligation is also the only shape in which a migration target can be
pinned in this repository at all.

**It is discharged.** `Weak.observedResetSeedSafety_of_acceptedDynamics`
([`FastConfirmation/Spec/Proof/WeakObservedResetSeedSafety.lean`](../FastConfirmation/Spec/Proof/WeakObservedResetSeedSafety.lean))
proves it from floor data only. The `def` stays where it is because
`WeakTrajectorySafety.lean` sits *below* the arm modules in the import order
and because the one-call-at-a-time (conditional) reading of the fold is still
worth having; the unconditional fold is the corollary in the same file as the
proof. See "Stages 5–6 as landed" below.

### Why it is the hard one

The strong twin is `Execution.ObservedResetCandidateInputAt.
safeFrom_of_acceptedDynamics` (`AcceptedObservedRestartDynamicSafety.lean`). Its
proof uses the querying node's honesty at exactly **two** sites, both
`PaperSafetySynchrony.block_relay` with that node as *sender*:

1. relaying the banked checkpoint root itself from the observer's store at the
   cache-installation second to every honest endpoint;
2. relaying the GU carrier tip, inside
   `ObservedResetCandidateInputAt.actualFCRGuardedObservedAdoption`.

Everything else in that proof — the epoch bound, accountable uniqueness, the
`head_ge_of_justified_ge_K` step, the honest-target strong induction — already
quantifies honesty over the *receiving* endpoint `w`, which the weak model
keeps.

Both sender-side relays already have weak, certificate-licensed replacements at
the level of **knownness**:

* `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` — the banked root
  is in every honest endpoint's store past the banking gate;
* `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer` /
  `Weak.gatedHead_known_at_all_honest_endpoints_at_observer` — so is its
  supplier, the certified boundary head;
* `Weak.headUnrealizedJustification_known_and_below` — the banked checkpoint
  sits on the certified head's own chain in the observer's store (this is the
  chain-intrinsic coverage rule delta 5 was redesigned to obtain);
* `Weak.ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource`
  — a full paper-Lemma-22 boundary-source witness for the banked candidate,
  with the strong record's `validator_honest`/`relay_gate` fields already
  replaced by a certificate-derived `seed_disseminated`.

What is missing is the step *on top of* knownness: head **domination** at a
foreign honest endpoint. `grep`ping the weak stack confirms there is no
weak-side lemma anywhere concluding `E.SafeFrom` or justified-domination of
`current_epoch_observed_justified_checkpoint.root`; the observed checkpoint
appears only as an `hbase` hypothesis. The strong route gets domination out of
`safeFrom_of_headStep_at` plus a split on
`c.epoch = J.epoch` (accountable uniqueness) versus `c.epoch < J.epoch` (an
honest formation target vote). Neither half needs the observer's honesty — the
*inputs* to them did.

(Stages 2–4 have since supplied those inputs and the `c.epoch = J.epoch` half;
the residue is the `c.epoch < J.epoch` half, stage 5. See "Stages 2–4 as
landed" below.)

The declared shape of the missing cross-carrier fact already exists as a `def`:
`Execution.ObservedRestartJustifiedSourceLockAt`
(`AcceptedResetAdoption.lean`), whose docstring notes that knownness,
`JustifiedIn`, and ordinary certificate accountability do not imply it. The
strong model makes it unnecessary; the weak model has to make it unnecessary
again, from certificates.

## Staged plan

Difficulty labels are relative to this repository's landed waves: **S** =
plumbing, hours; **M** = a focused file, a day; **L** = a multi-file wave like
Stages G–J; **XL** = a wave with a genuinely new argument, like
`WeakAncestryTransport.lean`.

| Stage | Deliverable | Difficulty | Status |
| --- | --- | --- | --- |
| 1a | `WeakConfirmedSafeFromFollowingSlot`, base case, idle step | **S** | landed |
| 1b | `weakGetLatestConfirmedTraceAt_input_known` (named extraction of an inline derivation the weak stack repeats at six sites) | **S** | landed |
| 1c | `Weak.CandidateHistoryCallBranch.origin`, input-safety dispatcher, call step, headline fold, endpoint form | **S** | landed |
| 2 | **Adoption**: weak twin of `ActualFCRGuardedObservedAdoption` — the banked checkpoint's epoch is `≤` every honest endpoint's justified epoch at the call second | **M** | landed |
| 3 | **Anchor arm**: the observed-reset seed reduces to `B.anchor` whenever the banked certificate degenerates; closes by `trustedAnchor_safeFrom_of_acceptedGlobalTrajectory` | **S** | landed |
| 4 | **Same-epoch arm**: `c.epoch = J.epoch` at the endpoint, closed by accountable uniqueness (`certified_justified_unique`) plus `head_ge_of_justified_ge_K` | **M** | landed |
| 5 | **Later-epoch arm**: `c.epoch < J.epoch`, the honest formation-target vote plus the `safeFrom_of_headStep_at` strong induction, with the sender-side relays replaced by the banked certificate's `seed_disseminated` | **L** | landed (turned out **M**) |
| 6 | Assemble stages 2–5 into `Weak.ObservedResetSeedSafety`; add the unconditional fold | **M** | landed (**S**) |
| 7 | Register the unconditional fold and its endpoint form in `scripts/Audit.lean`'s `publicWitnesses`; extend `docs/weak-synchrony.md`'s premise-surface classification | **S** | open (needs human review of stages 5–6 first) |

### Stages 2–4 as landed

Two new modules, both honesty-free at `obs`:

* [`FastConfirmation/Spec/Proof/WeakObservedRestartAdoption.lean`](../FastConfirmation/Spec/Proof/WeakObservedRestartAdoption.lean)
  — stage 2. `Weak.bankedCheckpoint_epoch_le_honestJustified` is the core:
  the certified supplier disseminates
  (`Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`), the banked
  value *is* that supplier's `GU` (the certificate's `banked_eq` plus
  `Execution.accepted_unrealized_justification_eq`), and the endpoint's own
  `AcceptedOldGURealized.oldGU` absorbs it. `Weak.GuardedObservedAdoption` /
  `Weak.ObservedResetCandidateInputAt.guardedObservedAdoption` are the
  call-indexed forms.
* [`FastConfirmation/Spec/Proof/WeakObservedRestartDynamicSafety.lean`](../FastConfirmation/Spec/Proof/WeakObservedRestartDynamicSafety.lean)
  — stages 3 and 4, plus `Weak.weakFcrStep_certifiedBankedJustification`, which
  supplies rule delta 5's invariant at the *query* store (one
  `certifiedBankedJustification_update` past the landed trajectory invariant),
  so neither arm assumes a certificate it cannot produce.
  Stage 3 is `Weak.genesisRoot_safeFrom_of_acceptedGlobalTrajectory` and
  `Weak.ObservedResetCandidateInputAt.safeFrom_of_anchorArm`; stage 4 is
  `Weak.sameEpochCertified_head_at_endpoint`,
  `Weak.ObservedResetCandidateInputAt.certifiedJustified` (the weak replacement
  for the strong proof's honest-node-only `hreal.certified`) and
  `Weak.ObservedResetCandidateInputAt.head_of_sameEpoch`.

#### The temporal carry, resolved

The note above ("the epoch-boundary arm is where the observer's inbox model
bites hardest") anticipated a new bridge from the installation second to the
call second. None was needed. Two existing facts cover it:

* the dissemination gate `E.slot_at h.second ≤ E.slot_at m` follows from
  `BankedJustificationCertificate.second_le` and `Execution.slot_at_mono` —
  the certificate's own index bound *is* the carry;
* the "carrier predates the boundary" step, which the strong proof gets from
  the cache installation's second, is instead intrinsic to the certificate:
  `has_head_broadcast_certificate` fixes the end slot at
  `get_current_slot store - 1`, so `Weak.has_broadcast_certificate_span_nonempty`
  plus the structure's `second_pos` fill give
  `Weak.BankedJustificationCertificate.supplier_slot_lt` (new, stage 2) — the
  supplier is strictly below the banking second's slot, hence strictly below
  the call's boundary slot after `slot_at_mono`.

So the installation second never has to be re-related to the call second by
anything stronger than monotonicity of the clock.

#### What stages 2–4 leave

The three landed arms compose into `Weak.ObservedResetSeedSafety`'s body
modulo exactly the stage-5 arm, with no index or temporal mismatch: split the
banking invariant (anchor arm ⇒ stage 3), run
`Execution.safeFrom_of_headStep_at`, derive `c.epoch ≤ J.epoch` at the endpoint
from stage 2 plus `Execution.store_justified_epoch_mono`, and split it with
`Nat.eq_or_lt_of_le` into stage 4 and stage 5. That prediction held exactly:
stage 6's body is that composition verbatim, with no index or temporal
adjustment and no extra hypothesis, once stage 5's arm is real.

Stage 5 was the only one that could have turned out **XL**: if the honest
formation target's vote could not be reached without transporting observer-store
ancestry into the voter's store, it would have needed a second containment-free
replay in the manner of `WeakAncestryTransport.lean`'s
`get_ancestor_aux_congr_closed`. It did not. See below.

### Stages 5–6 as landed

Stage 5 is in
[`FastConfirmation/Spec/Proof/WeakObservedRestartDynamicSafety.lean`](../FastConfirmation/Spec/Proof/WeakObservedRestartDynamicSafety.lean)
alongside stages 3 and 4 — the three arms of one split belong in one file — and
stage 6 is the new
[`FastConfirmation/Spec/Proof/WeakObservedResetSeedSafety.lean`](../FastConfirmation/Spec/Proof/WeakObservedResetSeedSafety.lean).

`Weak.ObservedResetCandidateInputAt.head_of_laterEpoch` is the stage-5 arm. It
takes the slot-indexed induction hypothesis of
`Execution.safeFrom_of_headStep_at` as an explicit premise, so the arm itself
is a plain endpoint statement and the induction is run once, in stage 6.

**No new argument was needed.** The strong proof's strictly-later branch is a
chain of endpoint-quantified facts —
`Execution.globalJustified_honestTarget`, the voter's own
`target_walk`/`get_ancestor_comp` composition,
`Execution.rootDescends_of_store_ancestor`,
`Execution.store_known_ancestor_of_rootDescends_for_storeReflection`, and
`head_ge_of_justified_ge_K` — every one of which already quantifies honesty
over the *receiving* endpoint (or over the formation voter it itself produces),
never over the querying node. Those transfer verbatim. Only three leaves of
the branch read the querying node's honesty, and each had a landed weak
replacement:

| strong honesty site | what it supplies | weak replacement |
| --- | --- | --- |
| `hsync.block_relay v hv …` at the banked root | `c.root` known at the formation voter's store | `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` (certificate dissemination; gate from `second_le` + `Execution.slot_at_mono`) |
| `hreal.root_known` | `c.root` known at the observer's own query store, hence `E.ExecutionRoot c.root` | `Weak.weakFcrStep_observed_known` (rule delta 5's `banked_known`) |
| `hreal.root_slot_le_boundary` | `c.root`'s block sits at or below its own epoch boundary | `Weak.ObservedResetCandidateInputAt.banked_blockEpoch_le`, i.e. `Weak.auCheckpoint_blockEpoch_le` at the query head, whose docstring already advertised itself as exactly this replacement |

and `hreal.certified` was already replaced in stage 4
(`Weak.ObservedResetCandidateInputAt.certifiedJustified`). Both stage-4 and
stage-5 uses now factor through the new
`Weak.ObservedResetCandidateInputAt.bankedAU`: the branch's own
`observed_eq_head_unrealized` conjunct plus
`Execution.accepted_unrealized_justification_eq` and `gu_AU` make the banked
value the query head's accepted `AU` checkpoint, honesty-free, and every
chain-intrinsic fact about it follows from that one record.

**The previous-epoch equation was only needed one way.** The strong proof's
`ObservedResetCandidateInputAt.observed_checkpoint_previous_epoch` proves
`c.epoch + 1 = e`, and its lower bound `c.epoch < e` is the half that reads the
cache installation's provenance (`acceptedInstallation`) — the honest-only
half. The later-epoch arm consumes only `e ≤ c.epoch + 1`, which is the
branch's own `observed_previous_epoch` conjunct composed with
`banked_blockEpoch_le`
(`Weak.ObservedResetCandidateInputAt.currentEpoch_le_banked_succ`). So the
honest-only half never appears, and `hspe : 1 < cfg.slots_per_epoch` — a
premise of the strong theorem, carried purely for that half — is not a premise
of the weak one.

Stage 6 is then the composition the previous stage had already checked
out-of-tree, with the stage-5 arm real: split
`Weak.weakFcrStep_certifiedBankedJustification`; the anchor arm closes by stage
3; otherwise apply `Execution.safeFrom_of_headStep_at`, derive
`c.epoch ≤ J.epoch` at the endpoint from stage 2's
`guardedObservedAdoption` plus `Execution.store_justified_epoch_mono`, and
split it with `Nat.eq_or_lt_of_le` into stage 4 and stage 5. The premise
surface of `Weak.observedResetSeedSafety_of_acceptedDynamics` is
`hA : SelectedMarginAssumptions`, `B`, `hT`, `hji : JustificationInterface`,
`hanchor`, `hboundary`, and the observer's own committee agreement `hcomm`
(literally `Execution.WeakObserverAssumptions.committees_agree`) — all six
already premises of the conditional fold. Hence

* `Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold`
* `Execution.weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot`

have exactly the conditional fold's premise list **minus** `hOR`, with nothing
added, and still no honesty binder at `obs`.

## Things the existing machinery made easier than expected

* **The certified-bank invariant is free.** `Weak.weakFcr_certifiedBankedJustification`
  already maintains `Weak.CertifiedBankedJustification` across the whole
  trajectory, with no honesty binder, so the "restart" bookkeeping needed no
  new conjunct in the invariant and no new base case.
* **Trajectory knownness is free.** `Weak.acceptedConfirmedSourceHistoryAt` is
  already a full all-seconds induction over `E.weakConfirmed` — it is the
  weak twin of `confirmed_known_of_acceptedGlobalTrajectory`, packaged as a
  record field rather than a standalone theorem. Only the trace-input
  projection was missing, and it is three rewrites.
* **The finalized arm lands on the nose.** The weak finalized-reset theorem's
  same-slot relay gate means its `SafeFrom` index is the query slot's start,
  which is exactly `hbase`'s index — no next-slot slack to absorb, unlike the
  strong fold, which has to route the same arm through
  `finalizedResetCandidateInput_safeFrom_of_nextSlotSynchrony` and a separate
  deadline-slot inequality.
* **The `hbfr` scenario predicate evaporates.** It was an artefact of proving
  one call in isolation, not a real assumption; the branch classifier supplies
  it.
* **Nothing in the weak stack actually consumes `obs ∉ E.honest`.** The weak
  lemmas are stated honesty-agnostically at `obs`, so they are strictly more
  general than the intended reading; `WeakObserverAssumptions.observer`
  is carried to pin the reading, and `Weak.ObserverContext` is currently only
  documentation.

## Things that are harder than expected

* **The observed-reset arm was a genuine hole, not a plumbing gap.** At the
  start of the effort there was no weak-side `SafeFrom`/justified-domination
  lemma for the banked checkpoint at all; the closest available facts stopped at
  dissemination, chain-intrinsic ancestry below the certified head, and GU-epoch
  orientation of the seed. Closing it took four waves (stages 2–5) and two new
  modules, but no new *kind* of argument: the domination step reduces to the
  accepted formation-vote machinery, which is endpoint-quantified throughout.
  The `Execution.ObservedRestartJustifiedSourceLockAt` shape flagged above as
  "the declared shape of the missing cross-carrier fact" never had to be
  produced — the split into an anchor arm, a same-epoch arm and a later-epoch
  arm avoids it entirely.
* **The epoch-boundary arm is where the observer's inbox model bites hardest.**
  The banked value is installed at an epoch boundary, possibly many seconds
  before the call that restarts from it; the certificate that licensed the
  banking is recorded at *that* second (`BankedJustificationCertificate.second`)
  and its dissemination conclusions are gated on
  `E.slot_at h.second ≤ E.slot_at m`. Any domination argument therefore has to
  carry the installation second forward, which the strong proof does not need
  to do because it re-relays from the querying node's store at query time.
  **Resolved in stages 2–5** at no cost: `second_le` plus
  `Execution.slot_at_mono` discharge the gate, and the certificate's own span
  (`Weak.BankedJustificationCertificate.supplier_slot_lt`) replaces the strong
  proof's installation-second age argument. See "The temporal carry, resolved"
  above.
* **`Weak.ObserverHistoricalA32CallAssumptions` stays floor-classified.** The
  fold inherits it unchanged from the closed one-shot theorem. It is the
  accepted development's own `helper_provisos` read at one more index, not a
  new class of assumption, but it is still a carried contract rather than a
  discharged one, and the full-rule statement does not improve on it.

## Audit status

None of the six weak full-rule modules contains a proof placeholder and the
full gate passes (`scripts/check_build.sh`, `lake env lean scripts/Audit.lean`,
`scripts/check_imports.py`). `#print axioms` on
`Weak.observedResetSeedSafety_of_acceptedDynamics`,
`Execution.weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold` and
`Execution.weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot` reports
`propext`, `Classical.choice`, `Quot.sound` and nothing else.

The declarations are still deliberately **not** added to `scripts/Audit.lean`'s
`publicWitnesses`. That set is the repository's list of headline results whose
premise surface has been *classified against the ratified floor* by a human,
and the classification of the unconditional fold's surface — in particular the
carried contract `Weak.ObserverHistoricalA32CallAssumptions` — is the
remaining work. `Execution.ObserverCoherence` is no longer part of that
surface: the fold takes `Execution.WeakObserverAssumptions` (floor + `obs ∉
E.honest` + committee readback) and derives `justified_root_known` internally
from `B`/`hT`/`hanchor`/`hboundary` via
`Execution.WeakObserverAssumptions.toMarginAssumptions`. Registration, together with
extending `docs/weak-synchrony.md`'s premise-surface table, is **stage 7**, to
be done after review of stages 5–6.
