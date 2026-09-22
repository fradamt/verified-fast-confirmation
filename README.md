# Verified Fast Confirmation

Lean 4 formalizations of Ethereum's Fast Confirmation Rule.

This repository contains two separate developments:

| Development | Source | Role and import |
| --- | --- | --- |
| [`FastConfirmation/Spec/`](FastConfirmation/Spec/) | Ethereum consensus specification, pinned at public commit [`30aa65f`](https://github.com/ethereum/consensus-specs/blob/30aa65fc21cf7f7c7dd1f7d6b686d0250462d04f/specs/phase0/fast-confirmation.md) | Primary executable model and accepted safety proof; `import FastConfirmation.Spec` |
| [`FastConfirmation/Paper/`](FastConfirmation/Paper/) | [Fast Confirmation Rule paper](https://arxiv.org/abs/2405.00549), Sections 3.1 and 4 | Independent companion model and proofs; `import FastConfirmation.Paper` |

The accepted consensus-spec theorem is proved entirely within
`FastConfirmation/Spec/`. It does not import the paper-model modules, and
there is currently no formal refinement theorem connecting the two models.
The paper's arguments guide the spec proof, but every fact used by the
accepted theorem is represented and proved—or stated as an explicit
assumption—inside the spec development.

## Consensus-spec formalization

This is the primary result of the repository.

In declaration names, `Accepted` means that the scheduled protocol events were
accepted by their handlers; it is not a review-status label.

The executable functions in
[`FastConfirmation/Spec/Model/`](FastConfirmation/Spec/Model/) follow
`consensus-specs/specs/phase0/fast-confirmation.md` and the Phase 0 fork-choice
and beacon-chain helpers it calls. They preserve the Python names and
control-flow structure to support line-by-line review.

The surrounding execution, synchrony, FFG-semantics, and assumption records
are verification infrastructure rather than Python transcriptions. Together
they model scheduled node executions, honest behavior, message delivery,
fork-choice state, and the semantic facts connecting accepted block
transitions to Casper FFG.

Useful entry points:

- [Model facade](FastConfirmation/Spec/Model.lean)
- [Public proved-theorem facade](FastConfirmation/Spec/ProvenTheorems.lean)
- [Accepted assumptions, statement, and proof implementation](FastConfirmation/Spec/Proof/AcceptedActualFCRNextSlotSafetyFacade.lean)
- [Concrete non-vacuity witness](FastConfirmation/Spec/Proof/AcceptedActualFCRJointNonVacuityFinal.lean)

### Primary theorem

`acceptedSpec_safety_next_slot` proves:

> If an honest node stores a block root as confirmed, then from the following
> slot onward that root is an ancestor of every in-horizon honest node's
> fork-choice head.

The theorem concerns stored FCR outputs at completed execution boundaries.
Its assumption bundle includes the execution trajectory, honest behavior,
synchronous relay deadlines, the one-slot vote delivery lookahead, a static
validator set over the finite horizon, the Byzantine-weight bound, the balance
floor, the Phase0 source-coherence contracts, accepted FFG semantics,
trusted-anchor coherence, checkpoint projection, the paper's Assumption 3.2,
and call-scoped helper provisos. Reset safety and the head-ancestry conclusion
are derived, not assumed.

The same facade proves
`findLatestConfirmedDescendant_safeFrom_of_actualCall` for the literal helper
result at an actual scheduled boundary call, including an unchanged return.

The result is the GST-0 specialization: its relay laws hold throughout the
checked execution. It does not claim cross-node safety for optional queries at
arbitrary in-slot action prefixes. The exported finite counterexamples exhibit
that failure under the proved structural, synchrony, and economic packages.
They deliberately do not assume the accepted FFG semantics, so they are not
countermodels to a strengthening under the complete accepted assumption bundle.

### Spec model layout

```text
FastConfirmation/Spec/Model/
  Config.lean                protocol configuration and mainnet values
  Types.lean                 beacon types, helpers, and abstract Externals
  ForkChoice.lean            Store and fork-choice functions
  FCRStore.lean              FastConfirmationStore and state helpers
  LMDHelpers.lean            LMD-GHOST support and safety helpers
  FFGHelpers.lean            current-target and justification predictors
  Confirmation.lean          the Fast Confirmation Rule
  Handlers.lean              fork-choice event handlers
  Validator.lean             honest attestation construction
  Execution.lean             scheduled multi-node executions
  AcceptedExecution.lean     exact accepted-prefix semantics
  Assumptions.lean           honest, network, external, and economic contracts
  FFGCertificates.lean       included FFG certificate objects
  FFGStateSemantics.lean     accepted Casper-FFG semantic interface
  ExactCheckpointLinks.lean  exact epoch-checkpoint projection laws
```

## Paper companion

The paper companion is an independent abstract formalization of
[arXiv:2405.00549](https://arxiv.org/abs/2405.00549):

- [`Core/`](FastConfirmation/Paper/Core/) defines time, blocks, validators, votes,
  views, filters, and fork choice.
- [`LMDGhost/`](FastConfirmation/Paper/LMDGhost/) formalizes the Section 3.1
  LMD-GHOST safety and monotonicity results.
- [`HFC/`](FastConfirmation/Paper/HFC/) formalizes the Section 4 LMD-GHOST-HFC rule
  and its Algorithm-1 safety and monotonicity results.

Its complete facade is [`FastConfirmation/Paper.lean`](FastConfirmation/Paper.lean).

Public paper-facing entry points:

- [Section 3.1 statements](FastConfirmation/Paper/LMDGhost/TheoremStatements.lean)
- [Section 3.1 proved facade](FastConfirmation/Paper/LMDGhost/ProvenTheorems.lean)
- [Section 4 statements](FastConfirmation/Paper/HFC/TheoremStatements.lean)
- [Section 4 proved facade](FastConfirmation/Paper/HFC/ProvenTheorems.lean)

The headline paper theorems are `Theorem1_Safety_proved`,
`Theorem1_Monotonicity_proved`, `HFC_Safety_Alg1_proved`, and
`HFC_Monotonicity_Alg1_proved`.

## Documentation

Consensus-spec development:

- [Spec-model design](docs/spec-model-design.md)
- [Spec-to-Lean function mapping](docs/spec-annotation.md)

Paper companion:

- [Paper-to-Lean model mapping](docs/model-annotation.md)
- [Paper-model design](docs/paper-model-design.md)
- [Algorithm-1 proof interface](docs/algorithm1-gate-discharge.md)
- [FFG vote and AU model](docs/ffg-delivery-abstraction.md)
- [Source and predicate notes](docs/source-notes.md)

Repository review:

- [Architecture, trust, and source review guide](docs/REVIEW_GUIDE.md)

## Build

The project uses Lean `v4.30.0-rc2` with the matching mathlib release.

```sh
lake exe cache get
lake build
```

`lake build` elaborates every model, proof, witness, and counterexample. The
project contains no `sorry`, `admit`, or project-defined axioms.

## Verification

The deterministic validation suite also checks the public consensus-source
objects, facade reachability and independence, project declaration trust, and
the axiom dependencies of the public Spec and Paper theorems:

```sh
scripts/validate.sh --fast  # source provenance and repository hygiene
scripts/validate.sh         # plus import graph, build, and Lean-native trust audit
```

By default the source audit looks for `consensus-specs` beside this checkout,
then one directory higher. Pass `--consensus-repo PATH` if the checkout
containing the pinned public commit lives elsewhere. GitHub CI runs these
checks without a model API or repository write permission.
