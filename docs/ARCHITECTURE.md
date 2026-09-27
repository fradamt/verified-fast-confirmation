# Architecture

Five Lean libraries separate definitions from proof terms. An arrow means that the library on
the right may import the one on the left: Model → Statements → Internal → Proofs →
Witnesses. `FastConfirmation.lean` imports all five.

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────────────────────────────────────┐
│ Library                    │ Contents                                                                                     │
├────────────────────────────┼──────────────────────────────────────────────────────────────────────────────────────────────┤
│ FastConfirmationModel      │ Python function translation in Spec/; scheduled runs, stake reads, external calls, and state │
│                            │ folds in Execution/.                                                                         │
│ FastConfirmationStatements │ Premise records in Premises/; propositions in Claims.lean and the safety-only Review.lean    │
│                            │ bundle.                                                                                      │
│ FastConfirmationInternal   │ Proof vocabulary and compatibility records. Subject folders hold FFG and synchrony facts;    │
│                            │ ProofVocabulary/ holds shared predicates.                                                    │
│ FastConfirmationProofs     │ Kernel checked proofs grouped by subject; ReviewTheorem.lean proves review_claims.           │
│ FastConfirmationWitnesses  │ Finite runs in NonVacuity/, negative results in Counterexamples/, and an inventory in        │
│                            │ Index.lean.                                                                                  │
└────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘
```

`FastConfirmationModel` and `FastConfirmationStatements` are the trusted review surface. They contain definitions and premise propositions. Model also proves `SuccessfulScheduledBlockImport.processedCount_lt` for its successor-prefix definition. The Lean kernel checks the proof bodies in Internal, Proofs, and Witnesses. The audit in `scripts/Audit.lean` checks public theorem dependencies and permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

`NextSlotSafetyPremises.anchor_state_checkpoints` covers a genesis anchor whose state
has the zero-root stub. It also covers a normalized anchor state whose current justified
and finalized checkpoints equal the anchor. At the FFG interpretation boundary,
`CheckpointReadsAs` reads a raw genesis stub as the genesis anchor because both
checkpoints have `GENESIS_EPOCH`. Executable handlers and wire attestations keep the raw
checkpoint. Checkpoint-sync anchors with older state checkpoints are outside this
condition. The raw source age and the filter's `+2` rule need an inclusion argument.
That argument is not formalized.
`CheckpointSyncFilterWitness.checkpoint_sync_filter_counterexample` has no attestation
inclusion for two epochs, so it is outside `EventualCheckpointInclusion`. It shows why
that premise matters; it is not an FCR safety failure.

`Phase0BoundarySourceCoherence` has five fields. `process_slots_one_boundary` equates
one boundary with eager PJF. `process_slots_same_target_epoch` equates target slots in
one epoch. `state_transition_process_slots` equates a crossing block transition with
slot processing. `process_slots_checkpoint_epoch` bounds the output checkpoint if every
intermediate slot-processed state satisfies `3 * effective_balance_increment < 2 *
get_total_active_balance`. This guard is exact because an empty vote set can pass the
two-thirds test at a total balance of at most one and a half increments.
`process_slots_two_boundaries` equates two or more boundaries from a start epoch of at
least `GENESIS_EPOCH + 2` with eager PJF, if the registry and the total active balance
are unchanged and the same guard holds at every intermediate state.
`ScheduledFCRCallPremises.balance_floor` requires two increments of anchor active
weight. With `registry_static_in_horizon`, this floor supplies the guard on in-horizon
reads. The concrete transition rejects blocks with slashings, voluntary exits, or
parent execution requests, and a Python run with an epoch-step registry change
(effective-balance update, activation, ejection, or pending deposit) is outside the
scope (`FixedFFGScope`).
`on_attestation_committee` confines successful delivered attestations in honest
in-horizon prefixes to their slot committee. Attester-slashing evidence can name
off-committee validators.

`ReviewClaims` contains only next-slot safety. Its conclusion gives observer-store
membership and executable ancestry.

## Review checks

```text
┌────────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│Check                       │What it enforces                                                                             │
├────────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│check_consensus_source.py   │The Python tag and the pinned source objects match the recorded hashes.                      │
│check_review_boundary.py    │Lean parser import closure of Statements contains only Model and Statements modules; every   │
│                            │Statements source is included.                                                               │
│StatementReachability.lean  │60 source declarations are claim-reachable from the claim type; no exception remains. No     │
│                            │other unreachable source declaration is allowed.                                             │
│ReviewSurfaceShape.lean     │Field names and types of 18 records and the claim body remain exact.                         │
│check_imports.py            │The five-library import direction holds.                                  │
│check_doc_names.py          │Backticked Lean names in current documents resolve to declarations or files.                 │
│Audit.lean                  │The 39 audited public theorems have only standard axiom dependencies. No forbidden           │
│                            │declaration is allowed.                                                                      │
│validate.sh                 │Fast checks above; full mode also builds every library and runs Lean checks.                 │
└────────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘
```

## FFG boundary and checks

`FastConfirmationStatements` holds the safety premise `ConcreteBridge.SafetyPremises`.
`FastConfirmationModel` contains the concrete FFG state, 34 Gloas functions, and
the bridge that runs them for `process_slots`, `state_transition`, and PJF. An
opaque block-validity oracle (class I) stands for the Python checks that the
projection does not model. `FastConfirmationProofs/FFG/Concrete/` computes the
FFG interpretation from the bridge and proves the internal records in
`FastConfirmationInternal`. The inclusion relation counts body votes that set
the timely-target flag; Python `process_attestation` does not check the target
root. A 59-case differential and a 48-block retained-projection comparison test
the concrete transition against pinned Python. The projection harness checks
each interpretation law on real pyspec runs. Full-bundle witnesses show
consistency, while the contract and differential checks test Python behavior.

The active inventory has 61 authored claim-reachable fields: 17 definitions (the A3.2 view and antecedent), 7 record fields whose own fields are listed, and 37 assumed leaves. The bridge proves the other internal external contracts and the static validator set (`ExternalsLaws.lean`), so they are not premise fields. The Lean reachability audit also checks two outside Prop boundaries. The leaf labels separate tested state laws, execution scope, network and behavior, and idealizations. Two relay fields have both network and idealization labels, and `SafetyPremises.genesis` has both scope and idealization labels.
The field list is checked against the claim-type reachability audit. CI runs the
Python contract, projection, realized-gap, and concrete differential checks in
a separate pinned-pyspec job.
