# Gloas FCR conformance

The conformance target is `gloas-minimal` with schema v2. The Python source is fork
`fradamt/consensus-specs` at tag `fcr-gloas-fix` (`13f391516`). The audited upstream base is `6b9bd532cca16555e2f3282d757622ebff29743e`.
The fork commit is `13f391516352f61b3ac5dcaae5be1884d104f86a`. The harness
rebuilds the projected Lean store. It compares the Gloas head and payload status. It also
compares the six FCR store fields. A trace can include the safe execution block hash for
comparison.

Use an existing local Python environment and a local source checkout:

```sh
scripts/conformance/run.sh /path/to/fradamt-consensus-specs gloas minimal out/gloas-minimal.jsonl
```

The runner uses the checkout's Python environment. It performs no setup. The checkout must be at the source pin `13f391516352f61b3ac5dcaae5be1884d104f86a`; each trace records that pin, and both trace readers reject another pin. It writes Python and Lean logs next to the trace and returns a nonzero status for an empty export, schema error, test failure, or Lean mismatch. `FCR_EXPORT_ONLY=1` exports and checks the trace without invoking Lean. The Lean runner is a script outside the library.
Repository validation uses `scripts/validate.sh --fast` for source and
boundary checks. With the pinned interpreter, both modes and CI also run
`scripts/conformance/check_smoke.sh`: the example traces, a wrong-pin trace,
and the Gloas helper comparison. Full validation builds the libraries and
audits 39 public theorem witnesses. Neither check makes a trace match a
refinement theorem.

Schema v2 records payload membership, Payload Timeliness Committee (PTC) vote maps, block deadlines, bid hashes, message slots and payload flags, and committee reads. The projection keeps a source state identity for opaque external calls. The runner checks executable configuration conditions. It does not replay block, envelope, or PTC handlers, prove `BeaconExternalsPremises`, or implement execution engine validation. Each imported payload must already have passed source validation. A trace match is an observation comparison.

The [trace schema](../scripts/conformance/TRACE_SCHEMA.md) defines the format. The safe execution hash fixtures in `scripts/conformance/lean/examples/` check both a matching and a mismatching parent hash. The direct helper exporter in `scripts/conformance/python/gloas_helper_observations.py` covers strict PTC majorities, missing payloads, payload ties, previous-slot zero weight, and early proposer equivocations. Its Lean comparison is `scripts/conformance/lean/GloasHelpers.lean`.

Schema v1 phase0 traces remain historical and both readers reject them. Gloas FULL and available payload nodes do not establish equality with phase0 fork choice. See [modeling choices](MODELING_CHOICES.md). A recorded partial minimal export and an upstream-discount negative result are in [history](history/gloas-negative-result.md); they are not a full current conformance result.

## Contract conformance

The [contract inventory](../scripts/conformance/contracts/inventory.toml) lists every
direct field in the premise structures. T means a generated reachable-state property of the pinned Python functions. E-scope labels execution limits. E-network/behavior labels delivery, scheduling, and honest or adversarial behavior. E-interpretation labels supplied interpretation obligations; no current leaf has it. The definition class labels a field fixed by a definition: the seven fields of the A3.2 view, which the bridge fixes (its modeling choices are the fixed committee schedule, AU from the four carried selectors, and the genesis-epoch read as the anchor), and the ten parts of the A3.2 antecedent. The record class labels a field whose type is a listed premise record. A3.2 itself is E-network/behavior. I labels cryptographic, engine, or fixed-committee idealizations. Some mixed relay fields carry both E-network/behavior and I. The inventory covers 59 authored claim-reachable structure fields (35 assumed leaves, 17 definitions, and 7 record fields) and two outside Prop boundaries: EpochEndsFitUint64 and BeaconFunctionInterface.AnchorCommitsToState. The checker verifies their source declarations. Thirteen selector, checkpoint, and anchor fields were moved from T to E
because their old probes did not test the supplied execution interpretation. The
inventory checker fails when a Lean field has no entry.

The deterministic tests use the Gloas minimal preset and Phase0 for the
Phase0 source laws. They cover slots and epoch boundaries, included votes,
low participation, a later anchor, and block transitions with attester and
proposer slashings. The test helpers disable BLS checks. The tests do not
establish BLS unforgeability, hash collision resistance, execution-engine
validity, KZG availability, network delivery, or a refinement theorem. A
Python exception is recorded as a failed total Boolean law. Known false laws
remain in the result JSON with a counterexample. New failures stop validation. regression.process_slots_checkpoint_epoch_without_balance_guard shows that one active increment can make an empty vote set pass the two-thirds test. regression.process_slots_two_boundaries_from_epoch_one shows why the two-boundary law starts in epoch 2. regression.pjf_checkpoint_epoch_out_of_domain and regression.state_transition_checkpoint_epoch_out_of_domain show that the PJF and `state_transition` checkpoint-epoch laws need their antecedent. regression.anchor_state_checkpoints_raw_checkpoint_sync shows that a later raw anchor with older state checkpoints fails the named anchor condition. All five are labelled expected failures. The tests record them as known findings. Because BLS is disabled, the attestation-validity probe checks only the structure of the indexed attestation.

Run the checker with an existing interpreter in the pinned checkout:

```sh
python3 scripts/conformance/contracts/check_inventory.py \
  --repo /path/to/fradamt-consensus-specs \
  --output /tmp/contract-results.json
```

`scripts/validate.sh --consensus-repo /path/to/fradamt-consensus-specs`
runs the same check. The contract runner fails if the checkout interpreter is absent. Fast validation
can check the inventory alone when no interpreter is installed. CI installs the pinned fork in a separate job and runs the contract suite, full projection, realized-gap regression, and concrete differential.


### Accepted FFG projection

`scripts/conformance/contracts/projection/run.py` imports real blocks through
`on_tick` and `on_block`, and delivers their body attestations through
`on_attestation`. It selects included body attestations whose target matches the checkpoint.
Python `process_attestation` does not check the target root. It forms a checkpoint only when the carrier chain has a two-thirds
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
labelled out of scope for `epoch_one_finalization_scope` (the internal law `epoch_one_finalization_one_step` in the JSON). The second run
never includes epoch-1 votes; it finalizes epoch 2 only through the link
2 -> 4 and passes the `k = 2` finalized evidence fields. The later anchor is labelled out of scope because it fails
`GenesisOrNormalizedAnchor`.

Three checks test the concrete canonical evidence. `RealizableBySlotRun` runs
`process_slots` on a copy of the state of each accepted block to the start of
each of the next three epochs. The justified checkpoint must have formed
evidence at the block. In four runs some of these checkpoints are not carried
by any selector of the block. `HonestEarlierTargetVoteOnCarrierChain` tests the
aggregate convention: for each signer of an included aggregate, the split that
keeps only the bit of that signer indexes exactly that signer, keeps the data,
and passes the structural indexed check. `IncludedCheckpointEvidence.causal`
requires, for each formed non-anchor checkpoint, a signer whose split vote has
an earlier slot and that target and is included on the chain. Every validator
of these fixtures is honest. The JSON output quotes each Lean field and gives
a status and a state witness for each case. Structural mappings are marked
construction; the exact Assumption 3.2 antecedent needs all honest views and
slashing state, so its result is marked as not established. Unexcluded FAIL results make validation fail. Expected scope failures remain OUT_OF_SCOPE. `EventualCheckpointInclusion.included` is NOT_ESTABLISHED in each full run: the sampled consequence does not test the A3.2 implication. AU in the sample is the four carried selectors of the blocks on the chain, as in the bridge view, and the consequent accepts C(b, e) or a later carried checkpoint that extends it. The law EventualCheckpointInclusion.included.sampled_consequent fails if the consequent fails in a view where a single-view sample of the antecedent holds: b is on the head chain at each block import of epoch e + 1, and the included votes there give a two-thirds link from vs(b, e) to C(b, e). `test_realized_gap.py` adds a run in which one justification pass justifies epochs 4 and 5 together. No carried selector holds the epoch-4 checkpoint (law regression.a32_exact_carried_superseded, expected FAIL), and the consequent holds with the epoch-5 checkpoint (law EventualCheckpointInclusion.included.superseded).

### Whole-bundle sample

`scripts/conformance/contracts/check_real_bundle.py` imports 48 normally participating blocks from a 100-validator Gloas genesis with 32, 33, 34, and 35 ETH effective balances. On this one accepted run it evaluates 78 finite fields, and the uniform genesis adds two (80 in total): 53 FFG projection checks, 18 registry, committee, economic, anchor, and configuration checks, five state-law samples on accepted keyed states, one retained-projection comparison, and one negative control. Ten of the 78 are public premise fields; 66 are laws of the derived internal records, including the external contracts and the static validator set that the bridge proves. Each run reads the committees of each epoch from its own Python states. The comparison sends each of the 48 accepted blocks, the retained fields of its parent state, and the committees that its attestations read to the Lean `state_transition` with an accepting oracle. The Lean result, including its registry, must equal the retained fields of the Python post-state, and the Python registry must not change. The comparison uses the Lean evaluator of the concrete differential. No block of this run has a full parent payload or an operation outside the fixed scope. The negative control lowers the balance of one validator below the hysteresis threshold before an epoch-crossing block. Python then lowers its effective balance, so the registry changes and the run is outside the scope; the same comparator must detect this change. `ByzantineWeightPremises.estimate_sound` fails on 208 of 1176 checked spans: 104 of 216 within-epoch spans (first at slots 0 to 1: 846e9 Gwei against an estimate of 837.5e9 Gwei) and 104 of 960 cross-boundary spans. A second genesis with 128 validators of 32 ETH (16 validators in each slot committee) checks only `estimate_sound`, in two fields. No within-epoch span fails (0 of 216), so a real pyspec registry meets part (i) of the committee-sampling idealization. 106 of 960 cross-boundary spans fail (first at slots 1 to 14: 4096e9 Gwei against 4052.16e9 Gwei), because the pro-rated estimate is the expected overlap of a reshuffle and the real reshuffle is one sample; this is part (ii). The checker lists these failures as expected. The other checked fields pass, except `EventualCheckpointInclusion.included`, which is NOT_ESTABLISHED. This run has one view and no Byzantine validators; it cannot test network relay, all honest views, BLS, KZG, engine validity, or a nonvacuous span fault bound. CI runs this sample and fails if an unlabelled field fails.

## Scope of the checks

The safety theorem computes its FFG interpretation from the concrete bridge. The projection harness checks sampled fields of that interpretation on real pyspec runs. It does not establish A3.2 as an implication. The concrete
FFG state and 34 Gloas functions in `FastConfirmationModel` passed 59 differential
cases and the 48-block retained-projection comparison. The block-validity oracle
stays opaque (class I). Full-bundle witnesses show
that the premises are consistent. Python faithfulness comes from the contract
suite, projection harness, and concrete differential. The witnesses' PJF returns
early in epochs 0 and 1 as Python does.

The active field inventory is checked with the type-based Statements reachability
audit. `IncludedAttestationEvidence.attesters_in_committee` is class I because
it uses one fixed committee map across forks. For e = 1, A3.2 requires a carrier of
epoch 2 or later for C(b, 1); the regression in
`scripts/conformance/contracts/test_realized_gap.py` records a confirmed block
lost when that evidence is seeded too early. Finality has a two-epoch lag, the
boundary source law covers two or more epoch crossings, and the `F = 1` scope
excludes a two-step finalization of epoch 1. The real anchor witness is genesis.
Checkpoint sync with older raw state checkpoints remains outside the result.
