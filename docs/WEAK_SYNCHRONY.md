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
other proof modules. The observer restriction on the global synchrony
premises is pending.

The trust audit registers 56 entries: 14 main-side, 41 weak-side, and
`review_claims`. The 41 weak-side
entries comprise eight weak safety, four replay, two negative containment,
17 complete-evidence helper, and ten complete-evidence witness results.
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
