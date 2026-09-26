# Gloas FCR conformance

The conformance target is `gloas-minimal` with schema v2. The Python source is fork
`fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`). Branch
`fcr-gloas-discount-fix` adds the public fix to upstream master `63a81afa6`. The harness
rebuilds the projected Lean store. It compares the Gloas head and payload status. It also
compares the six FCR store fields. A trace can include the safe execution block hash for
comparison.

Use an existing local Python environment and a local source checkout:

```sh
scripts/conformance/run.sh /path/to/fradamt-consensus-specs gloas minimal out/gloas-minimal.jsonl
```

The runner uses the checkout's Python environment. It performs no setup. It writes Python and Lean logs next to the trace and returns a nonzero status for an empty export, schema error, test failure, or Lean mismatch. `FCR_EXPORT_ONLY=1` exports and checks the trace without invoking Lean. The Lean runner is a script outside the library.
Repository validation uses `scripts/validate.sh --fast` for source and
boundary checks. Full validation builds the libraries and audits 43 public
theorem witnesses. Neither check makes a trace match a refinement theorem.

Schema v2 records payload membership, Payload Timeliness Committee (PTC) vote maps, block deadlines, bid hashes, message slots and payload flags, and committee reads. The projection keeps a source state identity for opaque external calls. The runner checks executable configuration conditions. It does not replay block, envelope, or PTC handlers, prove `BeaconExternalsPremises`, or implement execution engine validation. Each imported payload must already have passed source validation. A trace match is an observation comparison.

The [trace schema](../scripts/conformance/TRACE_SCHEMA.md) defines the format. The safe execution hash fixtures in `scripts/conformance/lean/examples/` check both a matching and a mismatching parent hash. The direct helper exporter in `scripts/conformance/python/gloas_helper_observations.py` covers strict PTC majorities, missing payloads, payload ties, previous-slot zero weight, and early proposer equivocations. Its Lean comparison is `scripts/conformance/lean/GloasHelpers.lean`.

Schema v1 phase0 traces remain historical and both readers reject them. Gloas FULL and available payload nodes do not establish equality with phase0 fork choice. See [modeling choices](MODELING_CHOICES.md). A recorded partial minimal export and an upstream-discount negative result are in [history](history/gloas-negative-result.md); they are not a full current conformance result.

## Contract conformance

The [contract inventory](../scripts/conformance/contracts/inventory.toml) lists every
direct field in the premise structures. T means a generated-state property
of the pinned Python functions. E means an execution, network, or supplied
FFG interpretation assumption. I means a cryptographic or engine
idealization. The inventory has 165 active fields: T 19, E 135, and I 11. Thirteen selector, checkpoint, and anchor fields were moved from T to E because their old probes did not test the supplied execution interpretation. The inventory checker fails when a Lean field has no entry.

The deterministic tests use the Gloas minimal preset and Phase0 for the
Phase0 source laws. They cover slots and epoch boundaries, included votes,
low participation, a later anchor, and block transitions with attester and
proposer slashings. The test helpers disable BLS checks. The tests do not
establish BLS unforgeability, hash collision resistance, execution-engine
validity, KZG availability, network delivery, or a refinement theorem. A
Python exception is recorded as a failed total Boolean law. Known false laws
remain in the result JSON with a counterexample. New failures stop validation. regression.process_slots_checkpoint_epoch_without_balance_guard shows that one active increment can make an empty vote set pass the two-thirds test. regression.anchor_state_checkpoints_raw_checkpoint_sync shows that a later raw anchor with older state checkpoints fails the named anchor condition. Both are labelled expected failures. The tests record them as known findings.

Run the checker with an existing interpreter in the pinned checkout:

```sh
python3 scripts/conformance/contracts/check_inventory.py \
  --repo /path/to/consensus-specs-pending-discount \
  --output /tmp/contract-results.json
```

`scripts/validate.sh --consensus-repo /path/to/consensus-specs-pending-discount`
runs the same check. If the checkout interpreter is absent, it checks the inventory
and prints a test-skip message. CI checks the inventory through fast
validation. CI does not install the pyspec runtime.


### Accepted FFG projection

`scripts/conformance/contracts/projection/run.py` imports real blocks through
`on_tick` and `on_block`, and delivers their body attestations through
`on_attestation`. It sets `includedAttestations.Included` from those block
bodies. It forms a checkpoint only when the carrier chain has a two-thirds
source-to-target link from an already certified source, with exact target
ancestry and an earlier included target vote. It reads realized checkpoints
from imported block states, unrealized checkpoints from eager PJF, and epoch
checkpoints from the fork-choice chain. At genesis, `CheckpointReadsAs`
maps the raw zero-root stub to the anchor checkpoint. BLS is disabled through
the pyspec test-helper switch.

The default contract checker runs a fast genesis prefix and the review's
slot-16 prefix. `check_inventory.py --full` runs all eight cases: through
epoch 6, slot 16, delayed two-thirds inclusion, a skipped epoch, two forks, a
later raw anchor, and two runs with two-epoch finality. In both, epoch-2 votes
are included at slot 24 and epoch-3 votes at slot 32. The first run finalizes
epoch 1 through the link 1 -> 3 and epoch 2 through the link 2 -> 4. It is
labelled out of scope for `epoch_one_finalization_one_step`. The second run
never includes epoch-1 votes; it finalizes epoch 2 only through the link
2 -> 4 and passes the `k = 2` finalized evidence fields. The later anchor is labelled out of scope because it fails
`GenesisOrNormalizedAnchor`. The JSON output quotes each Lean field and gives
a status and a state witness for each case. Structural mappings are marked
construction; the exact Assumption 3.2 antecedent needs all honest views and
slashing state, so its result is marked as not established. Findings remain in
the JSON and do not make validation stop. The report for this lane is
/home/fradamt/lean/orch/reports/p1-projection-tests.md on the NUC.
