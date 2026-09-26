# Architecture

Six Lean libraries separate definitions from proof terms. An arrow means that the library on
the right may import the one on the left: Model → Statements → Internal → Proofs →
Witnesses. Paper is independent of the executable side. `FastConfirmation.lean` imports all
six.

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
│ FastConfirmationPaper      │ Independent paper definitions, claims, and proofs in Core/, LMDGhost/, and HFC/.             │
└────────────────────────────┴──────────────────────────────────────────────────────────────────────────────────────────────┘```

`FastConfirmationModel` and `FastConfirmationStatements` are the trusted review surface. They contain definitions and premise propositions. Model also proves `SuccessfulScheduledBlockImport.processedCount_lt` for its successor-prefix definition. The Lean kernel checks the proof bodies in Internal, Proofs, Witnesses, and Paper. The audit in `scripts/Audit.lean` checks public theorem dependencies and permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

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

`Phase0BoundarySourceCoherence` has four fields. `process_slots_one_boundary` equates
one boundary with eager PJF. `process_slots_same_target_epoch` equates target slots in
one epoch. `state_transition_process_slots` equates a crossing block transition with
slot processing. `process_slots_checkpoint_epoch` bounds the output checkpoint if every
intermediate slot-processed state satisfies `3 * effective_balance_increment < 2 *
get_total_active_balance`. This guard is exact because an empty vote set can pass the
two-thirds test at a total balance of at most one and a half increments.
`ScheduledFCRCallPremises.balance_floor` requires two increments of anchor active
weight. With `registry_static_in_horizon`, this floor supplies the guard on in-horizon
reads. The static-registry condition excludes included slashings, deposits, activations,
exits, and effective-balance changes that alter validator records in the horizon.
`on_attestation_committee` confines successful delivered attestations in honest
in-horizon prefixes to their slot committee. Attester-slashing evidence can name
off-committee validators.

`ReviewClaims` contains only next-slot safety. Its conclusion gives observer-store
membership and executable ancestry.

## Review checks

```text
┌────────────────────────────┬─────────────────────────────────────────────────────────────────────────────────────────────┐
│ Check                      │ What it enforces                                                                            │
├────────────────────────────┼─────────────────────────────────────────────────────────────────────────────────────────────┤
│ check_consensus_source.py  │ The Python tag and the pinned source objects match the recorded hashes.                     │
│ check_review_boundary.py   │ Lean parser import closure of Statements contains only Model and Statements modules; every  │
│                            │ Statements source is included.                                                              │
│ StatementReachability.lean │ 64 source declarations are claim-reachable. Synchrony is the one approved public exception.  │
│                            │ No other unreachable source declaration is allowed.                                         │
│ ReviewSurfaceShape.lean    │ The safety review field and selected premise record shapes remain exact.                    │
│ check_imports.py           │ The six-library import direction and Paper separation hold.                                 │
│ check_doc_names.py         │ Backticked Lean names in current documents resolve to declarations or files.                │
│ Audit.lean                 │ The 45 audited public theorems have only standard axiom dependencies.                       │
│                            │ No forbidden declaration is allowed.                                                        │
│ validate.sh                │ Fast checks above; full mode also builds every library and runs Lean checks.                │
└────────────────────────────┴─────────────────────────────────────────────────────────────────────────────────────────────┘```
