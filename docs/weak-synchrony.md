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
