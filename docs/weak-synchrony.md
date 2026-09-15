# Weak synchrony: model delta and proof-migration plan

Companion to `FastConfirmation/Spec/Model/WeakSynchrony.lean`. Source
discussion: the Ethlabs working note "Weakening the synchrony assumptions of
FCR" (September 2026).

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
- Weak model: the observer is `ObserverContext.obs ∉ E.honest` — an inbox. No
  law guarantees delivery to it, and nothing it holds propagates from it.
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

## Rule delta 3 — epoch-fresh scorer

`Weak.is_one_confirmed` and its empty-slot support discount now count only
**epoch-fresh** recorded LMD cells. `Weak.recorded_cutoff_epoch store` is the
epoch of the last completed slot (`compute_epoch_at_slot (get_current_slot
store − 1)`) — anchoring at `compute_epoch_at_slot current_slot` instead would
make the scorer identically zero at every epoch boundary, since
`LatestMessageProvenance` forces every recorded cell to have been set for a
slot `≤ current_slot − 1`. `Weak.is_epoch_fresh_message store lm` holds iff
`recorded_cutoff_epoch store ≤ get_latest_message_epoch lm`.
`Weak.get_epoch_fresh_attestation_score` and
`Weak.get_epoch_fresh_block_support_between_slots` add this conjunct to the
strong scorer's/discount's counted-cell filter (in the fixed order `(equiv &&
fresh) && ancestor`, so the weak-⇒-strong bridge lemmas drop conjuncts rather
than re-deriving them); `Weak.is_one_confirmed` and
`Weak.compute_empty_slot_support_discount` are restated over them.

**Why the discount must be gated too, not just the main scorer.** The
stale-tolerant base-strip argument
(`Execution.base_strip_of_confirmed_in_store_stale_minimal`,
`AcceptedStrictPrefixExtraQueryFeasibility.lean:191`) that Stage H needs reads
recorded parent-pointing cells through `PrefixGroundVoteAccountingReplay
.parent_replay`, which is stated over the *ground-truth* `AttSupporters`/
`ParentStuck` classes — exactly what this delta must let the weak store-side
scorer approximate. A stale parent-pointing honest cell with a sibling ground
vote lands in the `StoreXclass` (excess) bucket; `parent_replay` is false for
it unless the discount counts only fresh cells. Landing the freshness gate on
the main scorer alone would leave the discount able to count a stale cell the
replay premise does not backstop. (A safe fallback, if the discount's
`Finset` monotonicity proof ever regresses, is to zero the weak discount
outright — strictly stricter than gating — but gating is preferred since it
is only marginally more work: `Finset.sum_le_sum_of_subset_of_nonneg` composed
with the same-base-set predicate-strengthening step, `Finset.monotone_filter_right`.)

The sibling arm of the window partition needs no re-accounting: `Sclass`/
`Aclass`/`Xclass` are ground-truth-indexed and the partition identity does not
move, and `ByzantineBound.estimate_sound` already charges the whole window.
Only `Hsup ≤ s` and `Hsup + discount ≤ s + a` move, and freshness makes both
strictly easier. Landing this delta does not by itself remove any
`WindowRecordedEpochMax` premise from the base strip — freshness only pays off
once a weak-native (store-computed, not ground-truth) version of the base
strip exists (Stage H, out of scope for this wave); see "Deliberately open"
below.

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
| balance-source key from `unrealized_justified_checkpoint` (finding 8) | out of scope, documented below |

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

**Finding 8 — the balance source itself descends from an ungated read.**
`get_current_balance_source`/every weak certificate in this call keys off
`fcr_store.current_epoch_observed_justified_checkpoint`, which in turn derives
from `unrealized_justified_checkpoint` bookkeeping in `Confirmation.lean`
(around `:46-50`) that this delta does not touch and that is not itself
broadcast-certified. This is *deferred stored-state scope*, consistent with
the module docstring's standing exclusion of `get_latest_confirmed`'s
revert-to-finalized/epoch-start-restart maintenance and
`is_confirmed_chain_safe`. Recording this plainly so the delta is not
mistaken for closing that gap: the observer's balance source is only as
trustworthy as that upstream bookkeeping, which remains an open premise
surface, not a proved one.

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
slot back) is a distinct rule shape, deferred as **delta 5**, out of scope for
this wave.

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
(`FastConfirmation/Spec/Proof/WeakOneShotSafety.lean`): for an observer
`obs ∉ E.honest`, at any within-horizon second, under
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

Deliberately open (Stage 8): discharging `hmargin` at a non-honest observer.
Its blocker is `WindowRecordedEpochMax` — epoch-freshness of the observer's
recorded LMD cells — which the strong development derives from vote delivery
*to* the observer (`vote_ubiquity`), a guarantee the inbox model removes and
broadcast certificates cannot replace (it asserts the *absence* of unseen
newer votes). Candidate resolutions, in preference order: (A) rule delta 3 —
count only epoch-fresh support in `Weak.is_one_confirmed`, making freshness
derivable from `committee_assignment_unique`; (B) an explicit
recorded-epoch-freshness assumption at the observer (weaker than honesty but a
genuine delivery-to-observer premise); (C) keep `hmargin` as the interface
premise (the current state).

**Candidate A is taken** — rule deltas 3 and 4 above land the epoch-fresh
scorer/discount and the certificate-gated unrealized-justification
short-circuits. This does **not** by itself discharge Stage 8: landing the
delta only makes freshness of *counted* cells derivable; it does not yet
supply a *weak-native* (store-computed, not ground-truth-indexed) base-strip
argument that consumes that freshness fact to close `WindowRecordedEpochMax`
at the observer (Stage H), nor the hdom-supplier retirement (Stage I) or the
final `hmargin` discharge (Stage J) built on top of it. Those three stages
remain out of scope for this wave; `hmargin` is still carried as an explicit
premise of the one-shot theorem today.

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
    (hW : E.WeakObserverMarginAssumptions cfg ext obs)
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

After this corollary, the only extra-floor assumptions about the observer's
own store left in `hW.coherence : ObserverCoherence` are `committees_agree`
(a one-node extension of the committee idealization to a non-honest observer;
`justified_root_known` is derivable —
`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`, and now
also packaged as `ObserverCoherence.of_acceptedTrajectory`, which reduces the
record's construction to `committees_agree` alone given the accepted
bundle) — plus the pre-existing Stage-8 `hmargin` premise above, unchanged by
this corollary and carried for exactly the same reason.

Both `weak_safeFrom_find_latest_confirmed_descendant_from_finalized` and
`weak_confirmed_head_from_finalized` depend only on
`propext, Classical.choice, Quot.sound` (`scripts/Audit.lean`'s
`publicWitnesses` set, now 17 declarations).
