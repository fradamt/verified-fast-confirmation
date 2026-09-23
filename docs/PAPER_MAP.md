# Paper correspondence map

This map condenses the definitions, assumptions, and theorems of [arXiv:2405.00549](https://arxiv.org/abs/2405.00549), Sections 3.1 and 4. It describes the independent `FastConfirmationPaper` library. Names without a file in the table are under the Core, LMDGhost, or HFC subject named in the first column; check the linked source files below for the exact declaration.

```text
┌────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────────┐
│ Paper item                                 │ Lean declaration or folder                                                    │ Meaning and limit                                                             │
├────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────┤
│ Base time, blocks, validators, views       │ FastConfirmationPaper/Core/                                                   │ Natural-number slots, parent tree, finite validators, messages and views.     │
│ Definition 5: committee-union weight       │ committeeUnion; W                                               │ Exact rational weight over the slot union.                                    │
│ Definition 6: supporting weight and        │ S; Q                                             │ LMD support over committee-union weight.                                      │
│ fraction                                   │                                                                               │                                                                               │
│ Definition 7: honest safety indicator      │ J; H; Phon                                                         │ Honest support fraction.                                                      │
│ Definition 8: one-confirmation and         │ isOneConfirmed; isLMDGHOSTSafe                                                │ Clean paper threshold, without executable discounts.                          │
│ ancestor lift                              │                                                                               │                                                                               │
│ Algorithm 4: confirmed block               │ highestConfirmedSinceEpoch; isConfirmed                                       │ LMD confirmation selector and predicate.                                      │
│ Assumption 1: static balances              │ StaticBalances                                                                │ Balance and committee coverage law.                                           │
│ Assumption 2: honest committee majority    │ CommitteeHonestMajority                                                       │ Committee and boost fault bound.                                              │
│ Section 3.1 head agreement, Lemma 6 style  │ HeadAgreementAfterConfirmation; head_agreement_after_confirmation             │ Future honest heads agree above a confirmed block.                            │
│ Theorem 1 safety                           │ ConfirmedBlockSafety; confirmed_block_safety                                  │ Confirmed block stays on future honest heads.                                 │
│ Theorem 1 monotonicity                     │ ConfirmedBlockMonotonicity; confirmed_block_monotonicity                      │ Confirmed predicate persists.                                                 │
│ Section 4 checkpoint and FFG vote          │ Checkpoint; FFGVote; Justified; Finalized                                     │ On-chain vote model and checkpoint relations.                                 │
│ Assumption 3: FFG message receipt          │ Assumption3; OnChainAnchorInterface                                           │ Honest vote receipt in views; no block-inclusion claim from Assumption3.      │
│ Section 4 source selectors                 │ greatestJustified; greatestFinalized; votingSource                            │ GU, GF, and source choices.                                                   │
│ Algorithm 1 FFG gate                       │ WillNoConflictingChkpBeJustified                                              │ Predicted target support.                                                     │
│ Algorithm 1 confirmation                   │ isConfirmedNoCaching; isHFCConfirmed                                          │ Rule predicate and selected result.                                           │
│ Algorithm 1 safety                         │ RuleConfirmedBlockSafety; rule_confirmed_block_safety                         │ Section 4 safety theorem.                                                     │
│ Algorithm 1 monotonicity                   │ SafeConfirmedAlg1Inputs; RuleConfirmedBlockMonotonicity;                      │ Later rule confirmation is assumed for every honest-view-safe block; stronger │
│                                            │ rule_confirmed_block_monotonicity                                             │ than Assumption 6.                                                            │
└────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────┘
```

Read `FastConfirmationPaper/LMDGhost/Claims.lean` with `FastConfirmationPaper/LMDGhost/ReviewTheorem.lean` for Theorem 1. Read `FastConfirmationPaper/HFC/Claims.lean` with `FastConfirmationPaper/HFC/ReviewTheorem.lean` for Algorithm 1. `SafeConfirmedAlg1Inputs` gives future rule confirmation as an input, so its theorem has a stronger premise than paper Assumption 6. The source and paper models have no formal refinement theorem.
