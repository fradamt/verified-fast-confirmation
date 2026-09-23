# Paper-model design

This document describes the companion formalization of Sections 3.1 and 4 of
the [Fast Confirmation Rule paper](https://arxiv.org/abs/2405.00549). It covers
`FastConfirmation/Paper/Core/`, `FastConfirmation/Paper/LMDGhost/`, and
`FastConfirmation/Paper/HFC/`.

This is not the consensus-spec model. The primary verification target lives in
`FastConfirmation/Spec/`, follows the executable consensus specification, and
does not import the paper-model modules. The two developments currently have no
formal refinement theorem between them.

## Scope

The paper model formalizes:

- the Section 3.1 LMD-GHOST confirmation rule, safety theorem, monotonicity
  theorem, and reusable future-head-agreement engine; and
- the Section 4 LMD-GHOST-HFC rule, including the paper-shaped Algorithm 1 and
  its safety and monotonicity theorems.

It does not formalize the Section 5 variable-balance generalization or the
paper's best-case liveness result. The production consensus-spec predicate is
modeled separately under `FastConfirmation/Spec/`.

## Architecture

```text
FastConfirmation/
  Spec.lean        consensus-spec facade
  Spec/            independent consensus-spec development
  Paper.lean       complete paper-companion facade
  Paper/
    Core/          time, blocks, validators, votes, views, filters, fork choice
    LMDGhost/      paper Section 3.1 model, statements, and proofs
    HFC/           paper Section 4 checkpoint/FFG model, statements, and proofs
```

`Core` is parameterized by the message payload and block filter. `LMDGhost`
instantiates the shared machinery for the unfiltered Section 3.1 rule. `HFC`
adds checkpoint and FFG-vote structure, instantiates the filter seam, and reuses
the filter-generic LMD-GHOST proof engine.

Each layer separates model definitions, theorem statements, proof scripts, and
proved public facades.

## Main modeling choices

- Time, slots, and epochs are natural numbers. The proofs use the slot lattice
  and GST ordering, not a continuous-time metric.
- Validators are `Fin n`, so committees and validator sets are finite.
- Balances are exact rational numbers.
- A Section 3.1 anchor is an abstract balance assignment. The HFC layer supplies
  checkpoint/justification structure behind that abstraction.
- Blocks form a parent-pointer tree. HFC blocks may additionally carry finite
  FFG-vote payloads used to compute on-chain AU information.
- Views contain blocks and messages. Network synchrony and honest voting are
  explicit theorem premises rather than an executable network simulator.
- Fork choice is parameterized by an eligibility filter and a deterministic
  tie-break. Strict safety margins ensure the proved path does not depend on the
  tie-break.
- The LMD-GHOST confirmation predicate is the paper's clean Definition 8. The
  production spec's support discount, equivocation adjustment, and other
  executable refinements belong to the separate consensus-spec model.

## Section 3.1 result

The public proved constants are:

- `Theorem1_Safety_proved`
- `Theorem1_Monotonicity_proved`
- `HeadFutureAgreement_proved`

The assumptions distinguish:

- honest behavior: honest committee members vote for their fork-choice heads
  and do not equivocate;
- network behavior: monotone views, post-GST delivery, and block availability;
- economic structure: committee honest-weight bounds, static balances,
  proposer-boost well-formedness, epoch committee coverage, and the paper's
  adversary bound for monotonicity.

`HeadFutureAgreement_proved` is filter-generic and anchor-generic. This is the
interface reused by the HFC proof.

## Section 4 result

The headline proved constants are:

- `HFC_Safety_Alg1_proved`
- `HFC_Monotonicity_Alg1_proved`

Algorithm 1 uses AU-based selectors computed from FFG votes contained in a
block's ancestry. `OnChainAnchorInterface` states the remaining connection
between those on-chain vote payloads, honest inclusion, block availability, and
the view-level justification facts used by the proof. The model also assumes a
single-slot committee-size bound for the previous-epoch branch.

For monotonicity, `SafeConfirmedAlg1Inputs` packages FFG closure for every safe
confirmed block. This is stronger and more direct than the paper's conditional
eventual-closure Assumption 6; the distinction is part of the theorem surface,
not hidden in the proof.

The gate-based `HFC_Safety` and `HFC_Monotonicity` constants are internal proof
interfaces. The `_Alg1` theorems are the public paper-facing results.

## Reading map

- [`FastConfirmation/Paper/LMDGhost/TheoremStatements.lean`](../FastConfirmation/Paper/LMDGhost/TheoremStatements.lean)
  and [`ReviewTheorem.lean`](../FastConfirmation/Paper/LMDGhost/ReviewTheorem.lean)
  expose the Section 3.1 statements and proofs.
- [`FastConfirmation/Paper/HFC/TheoremStatements.lean`](../FastConfirmation/Paper/HFC/TheoremStatements.lean)
  and [`ReviewTheorem.lean`](../FastConfirmation/Paper/HFC/ReviewTheorem.lean)
  expose the Section 4 statements and proofs.
- [`model-annotation.md`](model-annotation.md) maps paper definitions,
  assumptions, and theorems to Lean declarations.
- [`algorithm1-gate-discharge.md`](algorithm1-gate-discharge.md) explains the
  Algorithm-1 proof interface.
- [`ffg-delivery-abstraction.md`](ffg-delivery-abstraction.md) documents the
  block-contained FFG-vote and AU visibility model.
- [`source-notes.md`](source-notes.md) distinguishes the paper's adversary
  bounds and predicate variants from the production-spec formula.
