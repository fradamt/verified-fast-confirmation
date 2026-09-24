# Weak synchrony rule

The weak execution uses the duty-fresh weak synchrony FCR and a Gloas
parent-payload discount that counts votes for the required parent status or
PENDING. The pinned source is the local `fcr-weak-synchrony` branch of
`consensus-specs-weak-pending`. Run the full check with
`scripts/validate.sh --consensus-repo /home/fradamt/lean/consensus-specs-weak-pending`.
The conformance trace is
`/home/fradamt/lean/orch/traces/w6-weak-altair-minimal.jsonl` (3,763 records).

## Claims and premise surface

The two full-rule safety headlines are
`weak_confirmed_root_safe_from_next_slot` and
`weak_confirmed_root_on_honest_heads_from_next_slot` in
`FastConfirmationProofs/Weak/Safety/WeakObservedResetSeedSafety.lean`. They
concern a weak observer's stored confirmed root at second n and each honest
head in a strictly later slot within the verification horizon. The observer
can be honest or non-honest. The theorem parameters are the accepted exact
prefix FFG semantics B, trusted anchor agreement hanchor, trusted boundary alignment hboundary, realized
finalization delay hDelay, paper A3.2 inclusion hpaper, checkpoint
projection P, exact link validity V, weak observer assumptions hW, the
completed-prefix supplement hCbase, and epoch-fit arithmetic hfit.
The endpoint theorem also binds the honest endpoint hw, `n ≤ m`, the
later-slot inequality, and the horizon bound. Anchor exactness and the
walk domain are derived within the proof; they are not headline binders.

If the observer is honest, `hW.base.synchrony` delivers honest votes and
relay messages to it. There is no direct receipt field for a non-honest
observer. The observer's committee readback checks
its local state; it does not deliver messages.
The only weak-path use of `JustificationInterface` was honest head-root
knownness. The proof now derives it from
`SelectedMarginDomain.justified_root_known`. The legacy interface remains for
other proof modules. The restricted-premise safety headline for a non-honest
observer is pending.

The trust audit registers 57 entries: 14 main-side, 42 weak-side, and
`review_claims`. The 42 weak-side
entries comprise eight weak safety, four replay, two negative containment,
17 complete-evidence helper, ten complete-evidence witness results, and the
non-honest observer premise-independence theorem.
The complete-evidence witness is a store-contract witness. There is no
accepted positive in-horizon execution that jointly supplies the full weak
safety bundle and a non-anchor weak output.

The six one-shot safety entries use a safe seed. The direct and discharged
forms supply `SafeFrom` for the input root. The two finalized-input forms
derive seed safety for the observer's finalized root from their FFG premises.
If the selector advances, the direct and finalized forms require selected
covered-margin supply; the discharged forms require strict-edge filter supply
to derive that margin. These conditional inputs include earlier honest-head
ancestry. They do not establish safety from an arbitrary seed.

## Open live statement

`WeakStoredRootMonotonicity` in
`FastConfirmationStatements/Weak/LiveMonotonicity.lean` is an open proposition,
not a public theorem. Its `WeakLiveMonotonicityPremises` record extends the
common live record with the configured threshold margin needed by the weak
attempt. It is intentionally absent from `scripts/Audit.lean`. The weak
adversarial budget does not subtract equivocation. An old supporter can
therefore disappear without a matching reduction in the threshold, so the
strong epoch-boundary persistence argument does not carry over. The current
record also does not establish an arbitrary observer-head ancestry condition;
no joint non-vacuity witness for the live premises is known. See the archived
weak notes and the W7 report for the proof attempt and arithmetic witness.

## Source and model boundary

The Python source audit checks twelve pinned upstream files and the exact
local weak Gloas overlay. The executable Lean model represents the weak
selector and vote freshness in `FastConfirmationModel/Weak/`; the weak
premises and claims live in `FastConfirmationStatements/Weak/`, proof steps
in `FastConfirmationProofs/Weak/`, and finite witnesses in
`FastConfirmationWitnesses/Weak/`. The model follows the Python code's
non-optimistic payload verification path. As with the strong model, the
accepted FFG semantics, network delivery, external verification, and
scheduled execution premises require a separate implementation refinement.
At slot zero, Lean natural subtraction in `Weak.recorded_cutoff_epoch` gives
zero for the previous slot. The Python unsigned `Slot` subtraction underflows
there. The duty-fresh comparison covers positive current slots.

Older design and proof notes are preserved under `docs/history/`.

## Restricted observer premises

`WeakObserverRestrictedPremises` is a compiled restricted surface. It does not
replace the headline premises above. Its independence theorem is
`Execution.weakObserverRestrictedPremises_observer_independent`, in
`FastConfirmationInternal/Weak/ObserverIndependence.lean`.

For `obs ∉ E.honest`, `E.withoutObserver obs` retains the honest set, votes,
committees, horizon and genesis, and sets only its schedule to the empty list.
All other schedules stay unchanged. `WeakRestrictedNetworkPremises` reuses
the main records on this view. Thus every relay source and receiver is in
`H = E.honest`. `HorizonVoteDeliveryLookahead` supplies the last
horizon vote case. Emptying the schedule also removes the observer from the
all-receiver no-forgery and all-node accepted-input quantifiers. Erasing only
the honest set would not do this. The Internal module proves equality of the
other nodes' stores and weak caches with the actual execution.

`WeakObserverRestrictedPremises` contains the restricted core and local inputs.
The independence theorem also requires `obs ∉ E.honest`. An honest observer
is covered by the existing weak headlines, with the usual delivery premises
and endpoint scope. Its stake stays in the honest set.

The actual observer has these `ObserverLocalInputs` fields:

- `validity`: the three indexed-attestation laws on its own keyed states.
- `committees_agree`: committee readback from its own store.
- `no_forgery`: a received signed vote must have an authentic, causal origin;
  it requires no receipt.
- `block_labels`: its input block labels agree with other input labels,
  including its own; this is content identity, with no receipt deadline.
- `genesis_blocks`: an input that uses a genesis root has the genesis content.
- `anchor_parent`: an input cannot reuse the unresolved anchor-parent label.
- `process_slots_validity`: preparation of its keyed validation state preserves
  the signature check.
- `votes_head`: this generic authenticity field checks an honest observer's
  signed head. It is vacuous when `obs ∉ E.honest`.

The oracle fixes all votes and all non-observer schedules. It transfers the
shared core, and takes the local fields for the new
observer run. It does not assert that arbitrary new inputs satisfy them.
`ObserverLocalInputs.wellFormed` reconstructs actual execution block-label
coherence from the restricted record and these local clauses.

One limit remains before the headlines can use this design. The
restricted accepted-root domain omits blocks accepted only by the observer.
The observer-local content package supplies separate equations for successful
transitions and checkpoint reads. It does not require receipt at another node.

## h6 local FFG extension (2026-09-24)

`ObserverLocalFFG` supplies the observer part of the FFG design. The eight
h5 input clauses now form `ObserverInputAuthenticity`. `ObserverLocalInputs`
extends that record with `ffg : Nonempty (ObserverLocalFFG cfg ext E obs)`.
The existing independence theorem still proves transfer after arbitrary
observer schedule replacement, with these listed local inputs supplied again.
The theorem does not require another node to receive an observer block.

`ObserverFFGContent` has a separate content domain. `domain_local` identifies
that domain with roots in the observer's own causal stores. Its inclusion
relation checks the actual carrier body and a target state prepared from the
observer's own keyed state. It does not require a separately scheduled
attestation or a validation store at an honest node. The shared record remains
indexed by `E.withoutObserver obs`.

The additional local assumptions are the following. Each applies to the
observer's own content or successful calls, with no receipt deadline:

- `state.checkpoint_epoch`: the content checkpoint uses the requested epoch.
- `state.formed_domain`, `formed_certificate`, `formed_on_chain`: a positive
  formed entry belongs to the local content domain and has an included
  certificate on its chain; this is the opaque FFG refinement contract.
- `state.gj_mem`, `gu_mem`, `gf_mem`, `guf_mem`: each local selector selects
  an available content certificate on that block's chain.
- `state.gj_anchor_or_before`, `gj_max`, `gu_max`, `au_epoch_le_block`: the
  content selectors obey their epoch bounds and maximum definitions.
- `state.gf_evidence`, `guf_evidence`: finalized content has a justified
  checkpoint and an included link to the next epoch.
- `state.gf_epoch_le_gj`, `guf_epoch_le_gu`, `gf_epoch_le_guf`: the four
  content selectors have the required epoch order.
- `domain_local`, `block_read`: content membership and identity match the
  observer's actual accepted inputs, including repeated roots.
- `included_evidence`: each included attestation is in that exact carrier
  body, validates on an observer-prepared target state, has an in-horizon
  slot before the carrier, and has the stated target epoch and chain paths.
- `selectors.genesis_gj`, `genesis_gf`, `genesis_gu`, `genesis_guf`,
  `genesis_unrealized_justification`: the trusted local initial state matches
  the content selectors; these retain the existing trusted-anchor contract.
- `selectors.transition_gj`, `transition_gf`, `transition_gu`,
  `transition_guf`: each successful local `on_block` post-state matches the
  content selectors, including the result of the opaque PJF function.
- `checkpoint_of_known`, `au_checkpoint_of_known`: checkpoint reads at local
  causal stores reflect the content checkpoint and AU relations.
- `finalization_delay`: a successful local block has anchor GF or GF at least
  two epochs before its block epoch; the abstract transition omits this rule.
- `checkpoint_projection`: local checkpoint projection is closed and
  compositional from the trusted anchor epoch onward.
- `exact_link_endpoints`: a contributing link on a **locally covered** carrier
  has the exact content endpoints. This clause has a domain guard. It does
  not require an arbitrary outside descendant to enter the observer's store.

The new proofs derive keyed-state validity from prepared-state validity,
committee confinement, an honest signer in H, the signer's actual restricted
vote and deadline, the five block-state reads at every local prefix, all four
store-global checkpoint origins, local justified-root knownness, carrier-body
timing, GUF one-epoch lag, and store-global GF two-epoch lag. They also prove
that a local body link and a shared scheduled link have the same root when
their target epochs agree. They prove GJ/GF/GU/GUF agreement on a root
already known locally and remotely, and C
agreement there from the anchor epoch onward. These agreement theorems assume
common knownness only when comparing the two stores; they impose no occurrence
requirement on other local roots. Store origins and justified-root knownness
are derived results, not fields of the new local input record.

The certificate producer remains a local content refinement assumption.
Signature authenticity proves who signed the data of an existing included
certificate. It does not establish that an opaque PJF result has such a
certificate. The observer FFG counterexample proves handler success for an
observer-only empty-body block, all eight original local authenticity clauses,
a GU value `(epoch 1, root 99)` whose root is unknown, absence of the block in
the restricted accepted domain, and nonexistence of the local FFG extension.
This is a counterexample to acceptance plus local authenticity alone. It is
not a countermodel of the complete restricted core: the full economic and
Phase0 package is not supplied for that run. No formal non-derivability result
from the complete core is claimed.

A body aggregate and a signer's individual vote can be different payloads.
`link_signed_origin` retains both objects, their data equality, and the
aggregate's body membership. It does not claim that the individual signed
payload itself appears in the body. Old consumers of `received_from_block`
and of the stronger exact-payload temporal witness need this explicit port.

The local FFG modules build independently of the old weak
headlines. `scripts/h6-observer-ffg-oracle.lean` checks arbitrary schedule
replacement and the axioms of its consumers. The h6 use ledger covers 22 direct
FFG/coherence entries and seven authenticity entries in h5's inventory. These
are supplied interfaces, not 29 migrated proof bodies. The old headlines and
the honest endpoint equal to the observer remain outside this local-FFG work.
