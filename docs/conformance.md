# Gloas FCR conformance

The conformance target is `gloas-minimal` with schema v2. The Python source is fork `fradamt/consensus-specs`, tag `fcr-gloas-fix` (`13f391516`). Branch `fcr-gloas-discount-fix` contains the public fix on upstream master `63a81afa6`. The harness rebuilds the projected Lean store and compares the Gloas head, including payload status, the six FCR store fields, and the safe execution block hash when a trace contains it.

Use an existing local Python environment and a local source checkout:

```sh
scripts/conformance/run.sh /path/to/fradamt-consensus-specs gloas minimal out/gloas-minimal.jsonl
```

The runner uses the checkout's Python environment. It performs no setup. It writes Python and Lean logs next to the trace and returns a nonzero status for an empty export, schema error, test failure, or Lean mismatch. `FCR_EXPORT_ONLY=1` exports and checks the trace without invoking Lean. The Lean runner is a script outside the library.

Schema v2 records payload membership, PTC vote maps, block deadlines, bid hashes, message slots and payload flags, and committee reads. The projection keeps a source state identity for opaque external calls. The runner checks executable configuration conditions. It does not replay block, envelope, or PTC handlers, prove `BeaconExternalsPremises`, or implement execution engine validation. Each imported payload must already have passed source validation. A trace match is an observation comparison.

The [trace schema](../scripts/conformance/TRACE_SCHEMA.md) defines the format. The safe execution hash fixtures in `scripts/conformance/lean/examples/` check both a matching and a mismatching parent hash. The direct helper exporter in `scripts/conformance/python/gloas_helper_observations.py` covers strict PTC majorities, missing payloads, payload ties, previous-slot zero weight, and early proposer equivocations. Its Lean comparison is `scripts/conformance/lean/GloasHelpers.lean`.

Schema v1 phase0 traces remain historical and both readers reject them. Gloas FULL and available payload nodes do not establish equality with phase0 fork choice. See [modeling choices](MODELING_CHOICES.md). A recorded partial minimal export and an upstream-discount negative result are in [history](history/gloas-negative-result.md); they are not a full current conformance result.
