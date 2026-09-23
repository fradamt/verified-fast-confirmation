# Algorithm 1 Gate Discharge

The public §4 Algorithm-1 facades are proved over
`isConfirmedAlg1`, whose selector ranges over the paper-shaped per-block
`isConfirmedNoCaching` predicate. The semantic gate
`WillNoConflictingChkpBeJustified` is not a public Algorithm-1 premise.

## Public Surface

- `HFC_Safety_Alg1` and `HFC_Monotonicity_Alg1` are the headline Algorithm-1 statements.
- `HFC_Safety_Alg1_proved` and `HFC_Monotonicity_Alg1_proved` discharge those statements in
  `FastConfirmationPaper/HFC/ReviewTheorem.lean`.
- `Alg1SelectorSafetyInterface` keys the safety theorem's auxiliary facts to the actual
  selector witness slot `s'` where the selected block satisfies `isConfirmedNoCaching`.
- `Alg1SafetyInterface` and `SafeConfirmedAlg1Inputs` expose the remaining Gasper/AU obligations:
  well-formed block-contained AU payloads through `OnChainAnchorInterface`, block gossip
  availability, AU realization/visibility, greatest-finalized realization, filter selector
  agreement (`FilterSelectorAgreementAt`), committee partition, and P-link common source. The
  justified voting source needed by the current-epoch certificate is derived from the AU interface,
  not carried as a separate public premise.

## Model Route

The rule keeps the paper branch structure and conjunct set. Algorithm 1 uses the AU-based
`ruleVotingSource`/`ruleGJBlock` selectors, computed from block-contained votes on `chain(b)` via
the default `blockContainedFFGVotes` adapter.

`ffgFilterAt` likewise uses the paper-facing AU selectors: `ruleRealizedGJ` is the max over
`ruleVotingSource(b,t)` for known non-future blocks, `ruleRealizedGF` is the corresponding on-chain
finalized selector, and leaf recency is checked with `ruleVotingSource`.

- Current-epoch branch: `isConfirmedNoCaching` provides the local `willChkpBeJustified` check and
  LMD-GHOST safety. The proof derives the required certificate and uses
  `OnChainAnchorInterface` to make the AU source and GU anchor visible in honest views.
- Previous-epoch branch: the witness `b'` and the lower-bound recency check are read directly from
  `isConfirmedNoCaching`. The source upper bound and `vs(b',t).block ≼ b` ancestor conjunct are not
  part of the rule. The needed realization bound is proved using `SlotCommitteeMinority`; the
  AU witness source `ruleVotingSource(b',t)` is handled through the b'-keyed
  `OnChainAnchorInterface`.

## AU Bridge

The proof uses no direct view-delivery shortcut. Algorithm-1 statements use
`OnChainAnchorInterface`, backed by the block-contained vote model:

- `Block.mkWithVotes` / `ContainedFFGVote`
- `blockContainedFFGVotes τ`
- `chainIncludedFFGVotes`
- `OnChainJustifiedAtTransition`, `AU`, `GU`, `onChainGJBlock`, `onChainVotingSource`, and `GF`

`SafeConfirmedAlg1Inputs` is intentionally stronger than paper Assumption 6's conditional eventual
FFG-closure statement: it packages the closure as a per-safe-block `isConfirmedNoCaching` plus
AU/visibility-interface obligation for the monotonicity proof.

See `docs/ffg-delivery-abstraction.md` for the detailed AU model and simplifications.
