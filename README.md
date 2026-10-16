# Verified Fast Confirmation

[![CI](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/fradamt/verified-fast-confirmation/actions/workflows/ci.yml)

A Lean 4 proof that Ethereum's Fast Confirmation Rule (FCR) is safe. The FCR lets a node
identify a block that will stay canonical much earlier than FFG finality. The theorem
states: if an honest node stores a block root as confirmed at a slot boundary, then from
the next slot to the end of a finite horizon, every honest node has that root in its
block store and on its fork-choice head.

The model is an executable Lean transcription of the FCR and the fork-choice functions of
the Python consensus specifications, through the Gloas fork. Python tests check the model
against the specification. The Lean kernel checks the proof, and the trust audit allows
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The FCR is described in the paper
[A Fast Confirmation Rule for the Ethereum Consensus Protocol](https://arxiv.org/abs/2405.00549v4).
Paper citations in this repository use arXiv v4.

## The theorem

The claim is `ReviewClaims` in `FastConfirmationStatements/Review.lean`, and
`review_claims` in `FastConfirmationProofs/ReviewTheorem.lean` proves it. Its one field is:

```lean
def ConfirmedRootSafeFromNextSlot : Prop :=
  ∀ (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root),
    B.SafetyPremises E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at B.setup.cfg n + 1 ≤ E.slot_at B.setup.cfg m →
          E.WithinHorizon B.setup.cfg m →
            E.confirmed B.setup.cfg B.interface v n ∈
                (E.store B.setup.cfg B.interface w m).block_roots ∧
              is_ancestor (E.store B.setup.cfg B.interface w m)
                (get_head B.setup.cfg (E.store B.setup.cfg B.interface w m))
                (get_node_for_root (E.confirmed B.setup.cfg B.interface v n)) = true
```

The confirmed root of honest node *v* at second *n* is in the store of every honest node
*w*, and is an ancestor of the head of *w*, at every in-horizon second *m* from the next
slot on. Head ancestry is the substantive part. Store membership follows mostly from the
block-relay premise `DeadlineBlockRelay`.

The result is about the root that a node stores after its scheduled slot-boundary call. It
does not cover a query at an arbitrary time within a slot.

## What the theorem assumes

The premise `ConcreteBridge.SafetyPremises` has 14 fields. In plain words:

- **Synchrony from the start of the run.** Honest votes, blocks, payload envelopes, and
  slashing evidence reach every honest node, and the node processes them, by the next slot
  boundary (`NextSlotSynchronyPremises`).
- **Honest behavior.** Honest committee members vote for their head by the deadline, sign
  no slashable pair, and are not forged (`HonestBehavior`).
- **A stake bound on every slot span.** The non-honest weight is below the threshold on
  every span of slots, including one slot. A global fault share is not sufficient
  (`ByzantineWeightPremises`). The committee-weight estimate of the specification is taken
  as exact.
- **Eventual checkpoint inclusion.** Paper Assumption 3.2, stated over the blocks and
  votes of the run (`EventualCheckpointInclusion`).
- **A fixed scope.** The run starts at genesis, the horizon is finite, the validator
  registry and the committee assignment are fixed, and no block state finalizes epoch 1.
- **Opaque components with stated contracts.** Signatures, hash roots, proposer
  selection, the other block-validity checks, data availability, and execution
  validation.

The proof derives the FFG interpretation, the anchor conditions, the checkpoint source
laws, and eight of the 17 external contracts from the concrete model. They are not
assumptions. [Assumptions and scope](docs/ASSUMPTIONS.md) gives each field, its class, and
the Python checks of the premise.

## What the theorem does not cover

- **Queries within a slot.** Two counterexamples show that an extra FCR query in the
  middle of a second can return a root that is not an ancestor of the head of another
  honest node at that moment. Next-slot safety of such a query is open.
- **Validator registry changes.** A Python run is in scope only if no epoch step in the
  horizon changes a validator record (activation, exit, effective balance, or slashed
  flag). On mainnet this can limit the horizon to about one epoch.
- **Epoch-1 finality through a 1 -> 3 link.** Python finalizes epoch 1 in this way when
  epoch-2 justification needs votes included in epoch 3.
- **The statistics of committee sampling.** The premise takes the committee-weight
  estimate as exact.
- **Upstream changes after the pinned source.** See [Source](#source).

Some protocol paths have no full-bundle witness: competing forks, a positive proposer
boost, a positive empty-slot discount, PTC events, and non-anchor finality. See
[witnesses](docs/WITNESSES.md).

## Source

The model follows the fork `fradamt/consensus-specs` at tag `fcr-gloas-fix`
(`13f391516`), on top of upstream commit `6b9bd532`. The fork repairs the Gloas empty-slot
discount: it counts parent votes with a matching payload status or PENDING status. Upstream
later merged a different repair (ethereum/consensus-specs PR 5672) that does not count
PENDING parent votes, and an optional restart-resilient confirmed root (PR 5673). The model
includes neither. The [source map](docs/SPEC_MAP.md) maps each Python function to the model
and records the differences.

## Verify

Install Python 3 and Elan. Use the pinned Lean toolchain from `lean-toolchain`. Make a full
clone of the Python fork. The source check reads an earlier Git object, so a shallow clone
does not work. Set up its interpreter and generate the Gloas pyspec before validation:

```sh
git clone https://github.com/fradamt/consensus-specs.git /path/to/fradamt-consensus-specs
git -C /path/to/fradamt-consensus-specs checkout fcr-gloas-fix
python3 -m venv /path/to/fradamt-consensus-specs/.venv
/path/to/fradamt-consensus-specs/.venv/bin/python -m pip install -e '/path/to/fradamt-consensus-specs[test]'
(cd /path/to/fradamt-consensus-specs && .venv/bin/python -m pysetup.generate_specs --all-forks)
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
scripts/validate.sh --consensus-repo /path/to/fradamt-consensus-specs
```

`scripts/validate.sh --fast` checks the source pin, document names, library boundaries,
and hygiene. With the pinned Python interpreter, it also runs the contract and conformance
checks. Full validation also
builds the libraries, replays every project module through the kernel, and audits the
axioms of the public theorems. The [review guide](docs/REVIEW_GUIDE.md#source-and-checks)
lists all checks.

## Repository layout

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────┐
│ Library                    │ Content                                                  │
├────────────────────────────┼──────────────────────────────────────────────────────────┤
│ FastConfirmationModel      │ Executable transcription of the Python specification,    │
│                            │ scheduled runs, and external interfaces                  │
│ FastConfirmationStatements │ Premise records and the public claim                     │
│ FastConfirmationInternal   │ Internal proof vocabulary                                │
│ FastConfirmationProofs     │ Proofs, grouped by subject                               │
│ FastConfirmationWitnesses  │ Finite runs that satisfy the premise, and counterexamples│
└────────────────────────────┴──────────────────────────────────────────────────────────┘
```

Model and Statements are the review surface: they contain definitions and premises, and no
authored proofs except one definition obligation.

## Where to read

- [Review guide](docs/REVIEW_GUIDE.md): the reading order for a review, and the checks.
- [Assumptions and scope](docs/ASSUMPTIONS.md): every premise field, the scope limits, and
  the Python checks of the premise.
- [Modeling choices](docs/MODELING_CHOICES.md): how the model differs from Python, and why.
- [Source map](docs/SPEC_MAP.md): each Python function and its Lean counterpart.
- [Witnesses](docs/WITNESSES.md): the finite runs and what they exercise.
- [Architecture](docs/ARCHITECTURE.md) and [conventions](docs/CONVENTIONS.md): the
  library layout and the source rules.
- [Conformance](docs/conformance.md): the trace comparison with Python.

## Citation

To cite this repository, use the "Cite this repository" button on GitHub. It reads
[CITATION.cff](CITATION.cff).

The repository uses the MIT [license](LICENSE).
