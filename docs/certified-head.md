# Certified ancestor selection

## Rule

The weak rule now selects the newest certified ancestor of the actual
fork-choice head. It walks the parent chain from newest to oldest. A candidate
must have a broadcast certificate over its block slot through `current_slot - 1`.
The certificate threshold and duty-based support rules do not change.

The selected carrier is used at these sites:

- The descendant selector ends its canonical scan at the carrier. It reads the
  carrier's own unrealized justification for the entry guards.
- The no-conflict short circuit requires the current target to equal that
  justification. The old global-equality guard remains as well.
- Epoch-start banking reads that justification and checks the certificate with
  the incoming balance source, before the banked value changes.
- The observed-restart guard checks the carrier selected with the query's
  balance source, requires its certificate, and compares its own justification
  with the banked checkpoint.

The actual head remains the source for fork-choice canonicity, current-target
and pulled-up-state calculations, and the current/previous slot-head fields.
The previous-slot justification witness keeps its separate certificate and
candidate-ancestry guard.

`get_certified_head` has a total fallback: if no certificate exists, it returns
the actual head. `has_head_broadcast_certificate` now checks the selected root,
so it is false in this fallback case on a valid store. The existing epoch-start
selector escape remains available; it does not consume a carrier justification.

The Python walk stops at unknown or non-decreasing parents. Lean uses slot-based
fuel and also checks knownness and ancestry. These guards agree on valid stores.
The Python-only rule that preserves the trusted genesis checkpoint until a
strictly newer epoch is available remains in place. It is a pre-existing
Python/Lean correspondence difference, not part of this change.

## Proof

`WeakCertifiedHead.lean` proves that successful search returns a known ancestor
with its own certificate. It proves selected-root knownness and head ancestry,
that a certified head is retained, and that an uncertified head with a certified
parent selects that parent.

The selector proofs establish that each strict result is an ancestor of the
selected carrier, and therefore also an ancestor of the actual head. Dissemination
lemmas now name the carrier. The banked invariant stores an exact certificate
for its supplier instead of equating the supplier with the actual head. The
accepted-FFG lemma for a block's own justification is generalized to any known
supplier. Epoch-start trace and source proofs use the explicit carrier certificate.

The public full-rule safety statement and its standing assumptions are unchanged.
No observer-delivery premise is added. The existing local-replay equality theorem
continues to apply to this deterministic rule. This does not establish a general
liveness bound or an end-to-end zk circuit correspondence theorem.

## Checks and remaining work

The official FCR reference-test source is ethereum/consensus-specs commit
`818bbed729b9e3a7c29d9ac9c91130862eac54d5` (#5627). The weak branch retains those
assertions, with two earlier helper-signature adaptations, and adds regressions.
Full Lean validation passes: 3642 build jobs; the trust audit checks 10005
declarations, 6247 theorems, 27 generated partials, and 21 public witnesses.
Only the allowed standard axioms are used.

New tests call FCR after the current-slot head arrives and check confirmation of
its parent. A second test repeats this ordering for two epochs, including their
boundaries. Results are recorded in the research validation report.

The backwards search is pure computation. Its worst-case cost includes a
certificate check for each visited ancestor. A zk implementation can share
support calculations, but must prove that its chosen carrier implements this
selection rule. No such cost optimization or circuit proof is claimed here.

Before merge, review the Python/Lean correspondence for the walk termination,
certificate span, incoming versus query balance sources, carrier-bound scan,
observed-restart certificate, and retained actual-head fields.
