# Weak synchrony rule

The weak execution uses the duty-fresh weak synchrony FCR and a Gloas
parent-payload discount that counts votes for the required parent status or
PENDING. The pinned source is the local `fcr-weak-synchrony` branch of
`consensus-specs-weak-pending`. Run the full check with
`scripts/validate.sh --consensus-repo /home/fradamt/lean/consensus-specs-weak-pending`.
The conformance trace is
`/home/fradamt/lean/orch/traces/w6-weak-altair-minimal.jsonl` (3,763 records).

## Claims and premise surface

The two existing full-rule safety headlines are
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
other proof modules.

For `obs ∉ E.honest`, the additional headlines are
`nonhonest_weak_confirmed_root_safe_from_next_slot` and
`nonhonest_weak_confirmed_root_on_honest_heads_from_next_slot`, in
`FastConfirmationProofs/Weak/LocalFFG/ObserverHeadlines.lean`. They take only
`WeakObserverRestrictedPremises` and the non-honest condition, with the usual
honest endpoint, time, and horizon conditions. The actual-run interpretation,
anchor agreement, finalization delay, A3.2 inclusion, checkpoint closure, and
accepted-carrier exact-link law are derived. No actual-run A3.2 premise or new
local contract is added. The existing headline types remain unchanged.

The trust audit registers 60 entries: 14 main-side, 45 weak-side, and
`review_claims`. The 45 weak-side
entries comprise ten weak safety, four replay, two negative containment,
17 complete-evidence helper, ten complete-evidence witness results, and two
observer-independence theorems. The weak review list adds both non-honest
headlines and
`ActualRunFFG.actualRun_exactInterpretation_observer_independent`.
The latter builds the actual-run interpretation after any change to the
non-honest observer's schedule when its listed local input contracts hold
again. `weakObserverRestrictedPremises_observer_independent` remains proved.
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

`WeakObserverRestrictedPremises` is the premise surface of the new non-honest
headlines. The existing headlines retain their original premises. Its independence theorem is
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

- `validity`: the three indexed-attestation laws on its own keyed states;
  these connect the opaque signature check to genuine votes and committees.
- `committees_agree`: committee readback from its own store; this connects
  the local committee calculation to the fixed execution schedule.
- `no_forgery`: a received signed vote must have an authentic, causal origin;
  it requires no receipt.
- `block_labels`: its input block labels agree with other input labels,
  including its own; this is content identity, with no receipt deadline.
- `genesis_blocks`: an input that uses a genesis root has the genesis content;
  this preserves trusted input identity.
- `anchor_parent`: an input cannot reuse the unresolved anchor-parent label;
  this keeps the trusted ancestry walk at its initial boundary.
- `process_slots_validity`: preparation of its keyed validation state preserves
  the signature check.
- `votes_head`: this generic authenticity field checks an honest observer's
  signed head. It is vacuous when `obs ∉ E.honest`.

The oracle fixes all votes and all non-observer schedules. It transfers the
shared core, and takes the local fields for the new
observer run. It does not assert that arbitrary new inputs satisfy them.
`ObserverLocalInputs.wellFormed` reconstructs actual execution block-label
coherence from the restricted record and these local clauses.

The restricted accepted-root domain omits blocks accepted only by the observer.
The derived actual-run interpretation also covers these blocks.
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
observer's own keyed state. The local `received_from_block` clause records
an included body attestation as a from-block event in the observer's own
schedule. This is client input handling, with no deadline or remote receiver.
It does not require a validation store at an honest node. The shared record remains
indexed by `E.withoutObserver obs`.

The additional local assumptions are the following. Each applies to the
observer's own content or successful calls, with no receipt deadline:

- `state.checkpoint_epoch`: the content checkpoint uses the requested epoch;
  this is the epoch-indexed checkpoint definition.
- `state.formed_domain`, `formed_certificate`, `formed_on_chain`: a positive
  formed entry belongs to the local content domain and has an included
  certificate on its chain; this is the opaque FFG refinement contract.
- `state.gj_mem`, `gu_mem`, `gf_mem`, `guf_mem`: each local selector selects
  an available content certificate on that block's chain; this is the
  positive evidence required by the selector definitions.
- `state.gj_anchor_or_before`, `gj_max`, `gu_max`, `au_epoch_le_block`: the
  content selectors obey their epoch bounds and maximum definitions; these
  define the local FFG choices used by the opaque transition.
- `state.gf_evidence`, `guf_evidence`: finalized content has a justified
  checkpoint and an included link to the next epoch; this is the finalization
  certificate required by the FFG rule.
- `state.gf_epoch_le_gj`, `guf_epoch_le_gu`, `gf_epoch_le_guf`: the four
  content selectors have the required epoch order; these are the local FFG
  selector invariants of the opaque transition.
- `domain_local`, `block_read`: content membership and identity match the
  observer's actual accepted inputs, including repeated roots; this connects
  content reasoning to the exact input objects.
- `included_evidence`: each included attestation is in that exact carrier
  body, validates on an observer-prepared target state, has an in-horizon
  slot before the carrier, and has the stated target epoch and chain paths.
  Its `received_from_block` field requires the observer's local body-handling
  event. The executable block handler does not create this schedule event;
  the local contract states the client bookkeeping explicitly.
- `selectors.genesis_gj`, `genesis_gf`, `genesis_gu`, `genesis_guf`,
  `genesis_unrealized_justification`: the trusted local initial state matches
  the content selectors; these retain the existing trusted-anchor contract.
- `selectors.transition_gj`, `transition_gf`, `transition_gu`,
  `transition_guf`: each successful local `on_block` post-state matches the
  content selectors, including the result of the opaque PJF function; this
  is the local state-transition refinement.
- `checkpoint_of_known`, `au_checkpoint_of_known`: checkpoint reads at local
  causal stores reflect the content checkpoint and AU relations; this ties
  the abstract FFG entries to the local ancestry walk.
- `finalization_delay`: a successful local block has anchor GF or GF at least
  two epochs before its block epoch; the abstract transition omits this rule.
- `checkpoint_projection`: local checkpoint projection is closed and
  compositional from the trusted anchor epoch onward; the content reads must
  describe the same local ancestry walk.
- `exact_link_endpoints`: a contributing link on a **locally covered** carrier
  has the exact content endpoints; this connects the local certificate to
  the local checkpoint reads. This clause has a domain guard. It does
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
payload itself appears in the body. `includedRelation` supplies ordinary
inclusion evidence using the local body-handling event and local validation.
`au_certified` and `finalized_certified` project local content certificates to
the scheduled certificate API. The temporal formation witness now keeps the signed vote and the body
aggregate separate. It uses equal attestation data and body membership.

The local FFG modules provide the actual-run interpretation used by the new
non-honest headlines. `scripts/h6-observer-ffg-oracle.lean` checks arbitrary schedule
replacement and the axioms of its consumers. The h6 use ledger covers 22 direct
FFG/coherence entries and seven authenticity entries in h5's inventory. These
are supplied interfaces, not 29 migrated proof bodies. The old headlines
keep their types; their trusted fold now uses accepted-carrier exactness.

## Non-honest observer integration status

For `obs ∉ E.honest`, `WeakObserverRestrictedPremises` has only the shared core
and local inputs. The independence theorem preserves the non-honest condition
and transfers the core when only the observer schedule changes. The new run
must satisfy its own local contracts. Honest endpoints remain all of
`E.honest`.

The current proof recovers honest behavior, all honest-to-honest timed relay
fields, validation on honest causal stores, the static registry and economic
bound, and the operational prefix laws for the actual run. It also transfers
G4 paths when the receiver is honest. Local FFG proves observer head knownness
and AU checkpoint ancestry. These are compiled facts, with no observer
receipt deadline.

The local finalized-reset branch now has a direct proof.
`ObserverLocalFFG.finalized_epoch_le_honest_justified` extracts a genuine
honest signer from the local finalizing link. Body inclusion places its vote
before the carrier slot. The shared relay therefore supplies an honest
endpoint in the same or a later query slot. `finalized_on_honest_justified`
uses certificate accountability, and `finalized_safeFrom` derives safety from
the query slot's start. Neither theorem assumes the old global FFG bundle
for the actual run or a head-path contract at the observer.

`nonhonest_vote_ubiquity`, `nonhonest_vote_target_received`, and
`nonhonest_head_ancestor_known` supply the remaining honest-receiver delivery
operations from the restricted core. These are local proof suppliers.

The head-path blocker is closed. `ObserverLocalFFG.finalized_prefix_shared`
compares the local finalized certificate with a shared included certificate,
using their separate inclusion relations and common checkpoint reads.
`ObserverLocalFFG.honest_head_path` proves G4 at the actual observer.
`nonhonest_headPaths` supplies every receiver, and `nonhonest_selectedMargin`
constructs the complete old selected-margin record for the actual run.
`nonhonest_weakObserverPremises` then constructs the old observer record.
These are derived results; no observer receipt deadline was added.

`TrustedCarrierAttestationEvidence` and `TrustedCarrierAttestationRelation`
make the validation-store predicate explicit. The old carrier evidence maps
to and from their honest-store instance without changing its type.
`ObserverLocalFFG.trustedIncludedRelation` supplies the observer-causal-store
instance, with the accepted carrier, body membership and exact prepared-state
equation retained. `TrustedCausalCarrierFFGState` and `TrustedCausalPrefixFFGInterpretation`
now carry that predicate. The old honest-store record maps to the trusted
record and back without change. A trusted record also maps back without change
when its paper relation is the certificate relation. A separate paper relation
must be retained when certificates have been normalized. The old record identifiers and
all existing weak headline types stay unchanged. The formation witness uses
equal attestation data instead of exact signed-payload body membership.
`ExactIncludedLinkValidity` now checks carrier acceptance and endpoints only
inside its stated domain. The existing instance uses the full domain, while
`ObserverLocalFFG.guardedExactLinkValidity` uses the local content domain.
The local relation also lifts to the actual run's “honest causal store or
observer causal store” predicate.

The weak safety fold now accepts `TrustedCausalPrefixFFGInterpretation` for
any trusted validation-store predicate. The closed one-shot selector supply,
accepted global FFG projections, finalized reset, observed reset, and
historical A3.2 chain have trusted forms. The old fold keeps its exact theorem
type as an honest-store instance through `CausalPrefixFFGInterpretation.toTrusted`. The proof chain reads no
`validation_store_honest` field.

## Actual-run A3.2 and exact links

The actual-run interpretation combines the shared and observer-local formed
relations and selector reads. Certificate inclusion uses the exactness filter
from `ActualRunExactLinks.lean`. Each contributing shared or local certificate
survives with its signer set, and each retained mixed link has exact endpoints
at an accepted carrier. The fold uses `AcceptedExactLinkValidity`: it supplies
carrier acceptance from known roots or formed-entry evidence. It does not infer
acceptance of an arbitrary descendant from an accepted ancestor.

A3.2 uses `paperIncludedAttestations`, the raw union of shared and local body
relations. It has the same formed relation, AU, and selectors as the filtered
state. `shared_slashable_subset` proves that each shared slashing pair remains
in this raw view. Thus actual-run support implies shared support. Equality of
the two inclusion relations on shared blocks is unnecessary: the input
contracts do not require either relation to include every body attestation.
A larger slashing set only strengthens the support antecedent.

`exactState_paperA32` uses an honest view during epoch `e+1` to show that the
canonical base block belongs to the shared accepted domain. The shared A3.2
law then supplies its descendant and AU witness. Honest stores do not change
when the observer schedule is erased, shared formed evidence embeds in the
union, and shared checkpoint reads agree. `exactInterpretation_paperA32`
therefore follows from `core.paper_a32`. Filtering certificates does not remove
slashing evidence from the paper view.

`exactInterpretation_finalizationDelay` applies the local delay contract to
observer transitions and the core delay law to all other transitions. The
anchor and checkpoint closure laws come from the same interpretation. These
facts close the two non-honest headlines through the trusted fold. The
conditional forms in `ObserverConditionalHeadlines.lean` remain internal proof steps.

The guarantee uses one honest set for both behavior and delivery. For
`obs ∉ E.honest`, no timed delivery or relay premise names the observer; all
honest endpoints remain in `E.honest`. Schedule replacement fixes votes,
committees, genesis, horizon, the honest set, and all other schedules. It only
requires the listed observer-local input contracts again. Neither independence
theorem claims that an arbitrary replacement input satisfies those contracts.
There is still no full positive weak execution witness or weak live
monotonicity theorem.
