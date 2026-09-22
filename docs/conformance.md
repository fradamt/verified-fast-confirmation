# Gloas FCR conformance harness

The conformance target is `gloas-minimal`. The harness uses schema v2.
It rebuilds the projected `Store Nat`, the FCR store, and the configuration.
It compares the complete Gloas head node, including its payload status,
and the six fields after `on_fast_confirmation`.
New exports also record and compare `get_safe_execution_block_hash` after
FCR. Gloas uses the confirmed block's parent execution hash. The field is
optional in v2, so earlier v2 traces remain valid and skip this comparison.

Run the exporter and runner with an existing local pyspec environment:

```sh
scripts/conformance/run.sh /path/to/consensus-specs gloas minimal out/gloas-minimal.jsonl
```

The two-argument form selects Gloas and the minimal preset:

```sh
scripts/conformance/run.sh /path/to/consensus-specs out/gloas-minimal.jsonl
```

The script uses the checkout's `.venv/bin/python`. It performs no setup and
uses no network. It saves pytest diagnostics to `<out>.pytest.log` and Lean
diagnostics to `<out>.runner.log`. It reports the first three failures and
the runner's `SUMMARY` line. Pytest failure, empty export, malformed records,
and Lean comparison failure all produce a nonzero exit status.

Set `FCR_EXPORT_ONLY=1` to export and check the trace shape without starting
Lean. This permits source export while another lane uses the Lean compiler.
The script still returns the pytest status:

```sh
FCR_EXPORT_ONLY=1 scripts/conformance/run.sh /path/to/consensus-specs out/gloas-minimal.jsonl
```

To check an existing v2 trace, run:

```sh
python3 scripts/conformance/python/check_trace.py out/gloas-minimal.jsonl
lake env lean --run scripts/conformance/lean/Conformance.lean out/gloas-minimal.jsonl
```

Run only one Lean build or runner at a time on the shared machine.
The runner is a plain interpreted Lean file outside the `lean_lib`.

The trace records payload membership, both PTC vote maps, both block
arrival deadlines, the execution bid hashes, and each vote's slot and
payload flag. It supplies committee read lists to projected states from
all captured queries, including queries within Gloas `get_head`. State
comparison includes those lists and the full source state's opaque identity.
The runner stores the recorded state ID in `BeaconState.source_identity`.
Equal projected calls, including their identities, must give equal projected
answers. Distinct source states can have different external answers when
their other projected fields are equal.

The runner checks the executable configuration conditions. It does not
prove the `ExternalsCoherence` assumptions or replay the block, envelope,
and PTC handlers. The envelope's local data and execution validation are
preconditions of the source snapshot. A successful snapshot comparison is
not an end-to-end proof of those preconditions.

Altair, Bellatrix, Capella, and Deneb schema v1 traces are historical.
They describe phase0 fork-choice stores and are retired from the default
harness target. Both readers reject v1 with a clear phase0-store message.
Gloas FULL/available nodes do not establish equality with phase0 fork
choice. See [the design note](gloas-model-design.md).

The exact format is in
[the trace schema](../scripts/conformance/TRACE_SCHEMA.md).

The small `safe-execution-ok.jsonl` and `safe-execution-wrong.jsonl` examples
in `scripts/conformance/lean/examples` use distinct parent and block hashes.
They check the safe-hash comparison and its error path. These are synthetic
runner fixtures, not source-exported traces.

Direct helper fixtures cover strict PTC majorities, missing verified payloads,
payload tiebreaks, previous-slot zero weights, and early proposer equivocations:

```sh
python3 scripts/conformance/python/gloas_helper_observations.py --consensus-repo /path/to/consensus-specs --out out/gloas-helpers.json
lake env lean --run scripts/conformance/lean/GloasHelpers.lean out/gloas-helpers.json
```

The Python script executes unchanged functions from the pinned Git objects.
The Lean script rebuilds the same four-block store projection and compares
each recorded observation. These fixtures are separate from schema v2 FCR
traces. They do not establish an accepted execution.

## G3 STOP result (22 September 2026)

The fresh `gloas-minimal` export was stopped after the required G2-004 negative
result. It completed 68 of 184 source tests. A snapshot contains 1,492 complete
records, and the schema check passes. The trace is a partial artifact at
`out/g3-gloas-minimal-partial.jsonl`, with raw shards and metadata beside it.
Its SHA-256 is
`4f038598e8e3ca868b05939e1cf8fa3425c2ee04e400085fcd859bdeb7d5c603`.
There is no fresh full-suite Lean `SUMMARY`, and no new `4350/4350` claim.
The archived G2b `4350/4350` result is historical.

The ported runner passes both one-record positive fixtures. The separate
helper comparison reports:

```text
SUMMARY helpers=9 observations=162 mismatch=0
```

The model handler checks and both local Lean obstacle scripts also pass.
These small checks do not replace the full conformance run. The
[required negative result](gloas-negative-result.md) is a different exact-source
handler execution, with honest singleton votes and the new payload relay.
