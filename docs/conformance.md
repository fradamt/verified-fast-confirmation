# FCR conformance harness

The Lean runner checks the Comparison section of the conformance trace schema.
For each JSON Lines record, it rebuilds the `Store Nat` and
`FastConfirmationStore Nat`, builds `Config` from the recorded values, supplies
the recorded answers for the four executable external functions, runs
`on_fast_confirmation`, and compares the six FCR fields.

The runner also checks the runtime proof conditions required by `Config`:
positive slot and duration values, the threshold bound, a positive effective
balance increment, and divisibility of that increment by 100. A failed check
rejects the record with an error.

It does not check the `ExternalsCoherence` assumptions. The abstract FFG
semantics propositions are also not executable checks. The `id` field in a
state is informational; matching uses the five projected state fields defined
by the schema.

Run the interpreted runner with:

```sh
lake env lean --run scripts/conformance/lean/Conformance.lean <trace.jsonl>
```

The authoritative schema is
[`scripts/conformance/TRACE_SCHEMA.md`](../scripts/conformance/TRACE_SCHEMA.md).
The runner is interpreted on purpose. It is a plain Lean file and is not part
of a `lean_lib`; this avoids native linking of the Mathlib import closure.
