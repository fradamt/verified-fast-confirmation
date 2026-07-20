import FastConfirmation.Paper.HFC.Model.Checkpoint
import FastConfirmation.Paper.HFC.Model.FFGVote
import FastConfirmation.Paper.HFC.Model.Justification
import FastConfirmation.Paper.HFC.Model.FFGFilter
import FastConfirmation.Paper.HFC.Model.Rule
import FastConfirmation.Paper.HFC.Model.FFGRule
import FastConfirmation.Paper.HFC.Model.HonestFFG

/-!
# HFC / Model

Model-only facade for the §4 HFC / FFG-Casper layer: checkpoints
(`Checkpoint`), the FFG vote payload (`FFGVote`), the justification notions
read off a view (`View.ffgVotes`, `linkWeight`, `Justified`, `Finalized`,
`greatestJustified`, `greatestFinalized`, `greatestRealizedJustified`, `gjblock`,
`votingSource`, `gjFFG`), the AU rule/filter selectors (`ruleGJBlock`,
`ruleVotingSource`, `ruleRealizedGJ`, `ruleRealizedGF`), and the
§4 justification filter (`ffgFilter` / `ffgFilterAt`, the `FIL_hfc` predicate),
the honest FFG non-equivocation discipline (`HonestFFGNoEquivocation`, the
§4 mirror of `HonestBehavior.noEquivocation`), and the Algorithm-1 confirmation-rule shape
(`linkWeightUpTo`, `willChkpBeJustified`, `isConfirmedNoCaching`; `FFGRule`). The AU-based
Def-1/Def-2 selectors are `onChainGJBlock` and `onChainVotingSource`; `ffgFilterAt` consumes the
rule-realized AU selectors, while the older `gjblock` and `votingSource` names remain
proof-facing view-realized selectors.

These are additive over `FastConfirmation.Paper.Core` and
`FastConfirmation.Paper.LMDGhost.Model`; nothing here edits §3.1.
-/
