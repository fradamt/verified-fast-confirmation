# Source conventions

File and declaration names state their content. Model functions keep Python names, such as
`get_latest_confirmed`, so source comparison is direct. New proof names state the fact they
prove. Do not add a duplicate alias for a renamed declaration. Keep past work in Git. Keep
only useful historical evidence in `docs/history/`. The existing `Phase0SourceCoherence` and `Phase0BoundarySourceCoherence` names are historical: the laws also use Altair flags and Gloas epoch processing. `Execution.genesis_store` means the initial anchor store, including a normalized checkpoint-sync anchor. New declarations should name the full source domain. Premise records use FastConfirmation.Spec; execution-specific records use its `Execution` namespace.

Every library module starts with `module`, public imports, and a module docstring. Its first sentence states the function family, premise, invariant, or theorem in that file. A Model docstring cites the Python document and section. An import-only file needs no public section. Put declarations in an `@[expose] public section`, close nested scopes, and then close that section. Keep local proof helpers private where their dependencies permit it.

Add Python function definitions to Model/Spec by source section. Add run functions and external interfaces to Model/Execution. Put assumptions and claim propositions in Statements. Put intermediate records in Internal. Put proof lemmas in Proofs under the subject they establish. Put satisfying executions and counterexamples in Witnesses. Paper lemmas stay in Paper. Model and Statements stay free of authored theorems except definition obligations.

A change passes `scripts/validate.sh --fast` before commit. A library or import change also passes full `scripts/validate.sh`. The checks enforce source pinning, names, import closure, Statement reachability, exact review shape, full elaboration, and the trust audit. `scripts/check_imports.py` checks the library graph. `scripts/Audit.lean` remains a script with ordinary imports so that it can inspect proof bodies.
The current reachability check has 60 claim-reachable source declarations and
no approved exception. The trust audit checks 44 public
theorem witnesses. Update these counts when the check scripts change.
