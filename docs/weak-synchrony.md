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

Obligations 1 and 2 are stated as named `Prop`s in `WeakSynchrony.lean`
(no `sorry`s; the build enforces `-E hasSorry`). Proof sketches:

- **Obligation 1** (`CertificateHonestSupporter`): split the certificate
  support sum into honest and non-honest counted weight; the economic package
  (`ByzantineBound` + committee-estimation soundness, undiscounted — cf.
  `EconomicCore`'s `hne`-style facts without the equivocation term) bounds the
  non-honest part by the weak budget, so the strict inequality leaves an
  honest counted attester; `no_forgery` turns the counted latest message into
  that validator's genuine vote, `votes_assigned` pins its slot to the span.
- **Obligation 2** (`CertificateDissemination`): by Obligation 1 take the
  honest supporter `w` with vote at slot `s ≤ end_slot`; `votes_head` makes the
  vote the validator-spec attestation over `w`'s own store at a second of slot
  `s`, so the vote root and its ancestry — including `block_root`, by root
  injectivity (`WellFormedExecution`) transporting the observer-store ancestry
  fact — are in `w`'s store (store ancestor-closure is proved from the
  dynamics, cf. `Ancestry.lean`); `block_relay` from `w` then delivers
  `block_root` to every honest store from slot `s + 1 ≤ end_slot + 1`.
