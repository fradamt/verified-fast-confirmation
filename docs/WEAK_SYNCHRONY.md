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
`weakConfirmed_safeFromFollowingSlot_of_acceptedWeakFullRuleFold` and
`weakConfirmed_head_of_acceptedWeakFullRuleFold_nextSlot` in
`FastConfirmationProofs/Weak/Safety/WeakObservedResetSeedSafety.lean`. They
concern a weak observer's stored confirmed root at second n and each honest
head in a strictly later slot within the verification horizon. The observer
can be honest or non-honest. The theorem parameters are the accepted exact
prefix FFG semantics B, justification interface hji, trusted anchor
agreement hanchor, trusted boundary alignment hboundary, realized
finalization delay hDelay, paper A3.2 inclusion hpaper, checkpoint
projection P, exact link validity V, weak observer assumptions hW, the
completed-prefix supplement hCbase, and epoch-fit arithmetic hfit.
The endpoint theorem also binds the honest endpoint hw, `n ≤ m`, the
later-slot inequality, and the horizon bound. Anchor exactness and the
walk domain are derived within the proof; they are not headline binders.

The trust audit registers 56 public witnesses: the prior 55 (14 older
Spec/Paper and 41 weak-side) plus main's `review_claims`. The 41 weak-side
entries comprise eight weak safety, four replay, two negative containment,
17 complete-evidence helper, and ten complete-evidence witness results.
The complete-evidence witness is a store-contract witness. There is no
accepted positive in-horizon execution that jointly supplies the full weak
safety bundle and a non-anchor weak output.

## Open live statement

`WeakSpec_Monotonicity_live` in
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

Older design and proof notes are preserved under `docs/history/`.
