# Weak full rule: the trajectory invariant and its staged proof plan

Companion to [`weak-synchrony.md`](weak-synchrony.md). That note takes the weak
model from the network delta to the **closed one-shot** theorem: at one genuine
FCR call, given that the call's own candidate input is known and `SafeFrom`, the
weak selector's result is `SafeFrom`. This note takes it from one call to the
**whole trajectory**: for every in-horizon second `n`, the root the observer's
weak FCR holds at `n` is safe.

Stage 1 of that effort has landed in
[`FastConfirmation/Spec/Proof/WeakTrajectorySafety.lean`](../FastConfirmation/Spec/Proof/WeakTrajectorySafety.lean).
Everything below is either proved there, proved elsewhere and consumed there,
or explicitly labelled open.

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
* `hbase`: **open.** Pinned as `Weak.ObservedResetSeedSafety`.

Five of the six cells are discharged in `WeakTrajectorySafety.lean`. The sixth
is the entire residue of the full-rule effort.

## The one open obligation

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
| 2 | **Adoption**: weak twin of `ActualFCRGuardedObservedAdoption` — the banked checkpoint's epoch is `≤` every honest endpoint's justified epoch at the call second | **M** | open |
| 3 | **Anchor arm**: the observed-reset seed reduces to `B.anchor` whenever the banked certificate degenerates; closes by `trustedAnchor_safeFrom_of_acceptedGlobalTrajectory` | **S** | open |
| 4 | **Same-epoch arm**: `c.epoch = J.epoch` at the endpoint, via `checkpointTakeoverEvidence_of_sameEpochCertificates` (already honesty-free) and `checkpointTakeover_head_of_globalTrajectory` (honesty on the endpoint only) | **M** | open |
| 5 | **Later-epoch arm**: `c.epoch < J.epoch`, the honest formation-target vote plus the `safeFrom_of_headStep_at` strong induction, with the sender-side relays replaced by the banked certificate's `seed_disseminated` | **L** | open |
| 6 | Assemble stages 2–5 into `Weak.ObservedResetSeedSafety`; delete the obligation from the fold's premise list | **M** | open |
| 7 | Register the unconditional fold and its endpoint form in `scripts/Audit.lean`'s `publicWitnesses`; extend `docs/weak-synchrony.md`'s premise-surface classification | **S** | open |

Stage 5 is the only one that could turn out **XL**: if the honest formation
target's vote cannot be reached without transporting observer-store ancestry
into the voter's store, it will need a second containment-free replay in the
manner of `WeakAncestryTransport.lean`'s `get_ancestor_aux_congr_closed`. The
existing `Weak.AcceptedLemma22EpochStartCandidateSourceAt` record is the
evidence that this is expected to be avoidable: it already carries a
dissemination field in place of the strong record's honesty-plus-relay-gate
pair, and it is already produced at exactly the observed-reset call site.

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
  general than the intended reading; `WeakObserverMarginAssumptions.observer`
  is carried to pin the reading, and `Weak.ObserverContext` is currently only
  documentation.

## Things that are harder than expected

* **The observed-reset arm is a genuine hole, not a plumbing gap.** There is no
  weak-side `SafeFrom`/justified-domination lemma for the banked checkpoint at
  all; the closest available facts stop at dissemination, chain-intrinsic
  ancestry below the certified head, and GU-epoch orientation of the seed.
* **The epoch-boundary arm is where the observer's inbox model bites hardest.**
  The banked value is installed at an epoch boundary, possibly many seconds
  before the call that restarts from it; the certificate that licensed the
  banking is recorded at *that* second (`BankedJustificationCertificate.second`)
  and its dissemination conclusions are gated on
  `E.slot_at h.second ≤ E.slot_at m`. Any domination argument therefore has to
  carry the installation second forward, which the strong proof does not need
  to do because it re-relays from the querying node's store at query time.
* **`Weak.ObserverHistoricalA32CallAssumptions` stays floor-classified.** The
  fold inherits it unchanged from the closed one-shot theorem. It is the
  accepted development's own `helper_provisos` read at one more index, not a
  new class of assumption, but it is still a carried contract rather than a
  discharged one, and the full-rule statement does not improve on it.

## Audit status

`WeakTrajectorySafety.lean` contains no proof placeholders and the full gate
passes (`scripts/check_build.sh`, `lake env lean scripts/Audit.lean`,
`scripts/check_imports.py`). Its declarations are deliberately **not** added to
`scripts/Audit.lean`'s `publicWitnesses` at this stage: the headline fold is a
genuine theorem, but it is conditional on `Weak.ObservedResetSeedSafety`, and
`publicWitnesses` is the repository's set of headline results whose premise
surface has been classified against the ratified floor. Registration is stage 7,
after stage 6 removes the obligation.
