# Removed paper-side library

The last commit that contains `FastConfirmationPaper/` and
`FastConfirmationPaper.lean` is `e549055` (tag `v0.1.0`). The library was
deleted after this commit. Use that commit to read or build its source.

## What it held

The library was an independent Lean model of the fast confirmation paper. Its
`Core/` files defined natural-number slots, blocks, validators, messages,
views, and a synchrony record. `LMDGhost/` defined committee-union weights,
support fractions, a confirmation predicate, and LMD-GHOST proof terms.
`HFC/` added checkpoints, block-carried FFG votes, realized and unrealized
justification, a gate, a filter, and a confirmation rule. Its rational weights
and slot views were separate from the executable Gloas model.

The trust audit named seven public paper-side theorems:

```text
┌────────────────────────────────────────┬────────────────────────────────────────────────────┐
│ Subject                                │ Audited theorem                                    │
├────────────────────────────────────────┼────────────────────────────────────────────────────┤
│ LMD-GHOST head agreement               │ head_agreement_after_confirmation                  │
│ LMD-GHOST confirmed-block safety       │ confirmed_block_safety                             │
│ LMD-GHOST confirmed-block monotonicity │ confirmed_block_monotonicity                       │
│ HFC gate safety                        │ gate_confirmed_block_safety                        │
│ HFC gate monotonicity                  │ gate_confirmed_block_monotonicity                  │
│ HFC rule safety                        │ rule_confirmed_block_safety                        │
│ HFC rule monotonicity                  │ rule_confirmed_block_monotonicity                  │
└────────────────────────────────────────┴────────────────────────────────────────────────────┘
```

The LMD-GHOST claims were in `LMDGhost/Claims.lean` and their facade was in
`LMDGhost/ReviewTheorem.lean`. The HFC claims and facade were in the matching
`HFC/` files. The HFC safety claim used `FFG_AccountableSafety` and a per-call
`Alg1SelectorSafetyInterface`. Its monotonicity claim used
`SafeConfirmedAlg1Inputs`, which required each block safe in an honest view
to be rule-confirmed at that time. The library had no finite non-vacuity
witness. It had no refinement theorem to the executable library.

The former `docs/PAPER_MAP.md` mapped the base timing and view definitions to
`Core/`, the LMD-GHOST support and confirmation definitions to `LMDGhost/`,
and the FFG checkpoint, source, gate, filter, and rule definitions to `HFC/`.
It also compared executable delivery deadlines with the paper's positive
message delay. The executable model uses an attestation deadline, ready-message
handler service, and an evidence discount. Those features were not proved to
refine the paper model. The old map mixed numbering from an earlier paper
draft and an unpublished explainer. Current paper citations use
[arXiv:2405.00549v4](https://arxiv.org/abs/2405.00549v4).

## Why it was removed

The executable specification is the reference for the retained Lean claim
`ReviewClaims`. That claim has no dependency on the paper library. The paper
library had no refinement theorem that connected its abstract objects or
claims to the executable specification.

An independent audit found these defects at `e549055`:

- **B1:** Three audited HFC theorems were vacuous. The finalized-realization
  premise required the finalized epoch to be less than the current epoch at
  time zero. For a nonempty honest set, this requires a natural number below
  zero. The affected theorems were both gate theorems and HFC rule
  monotonicity.
- **M1:** The paper-side GJ(b) selector read votes from the same epoch as b.
  The paper's GJ(b) reads earlier epochs only.
- **M2:** The paper-side synchrony record required next-slot delivery even for
  a message first seen at the end of a slot. This was stronger than the
  paper's message-delay model.
- **M3:** The HFC rule safety interface constrained future honest heads through
  its P-link condition. This supplied part of the desired safety conclusion
  as an input.
- **M4:** The library did not pin a paper version. Its statements and map used
  numbering from different versions. The former `docs/PAPER_MAP.md` was not a
  reliable guide to v4.

The source remains available in Git history at `e549055`. The current trust
audit covers 40 public executable theorems in five libraries.
