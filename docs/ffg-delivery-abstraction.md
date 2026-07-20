# FFG on-chain vote model and AU visibility bridge

The §4 model has two connected surfaces:

- `Block.mkWithVotes` / `ContainedFFGVote` in `FastConfirmation/Paper/Core/Model/Blocks.lean`: a block may include any finite number of simplified, chain-targeted FFG vote records, each with signer, vote slot, source epoch, and target epoch. The source/target blocks are interpreted as checkpoints on the including block's chain; the reified `Message` is marked `countsForLMD := false`, so it carries an FFG source→target link without becoming a synthetic LMD fork-choice vote. Known votes for other forks are outside this compact AU adapter and do not count toward `AU(b)`. The vote slot is preserved so a block can include votes from its current or previous epoch. The model does not implement execution-spec participation flags; on-chain readers ignore a validator for an epoch if the chain contains an equivocation for that validator/epoch.
- `BlockFFGVotes`, `chainIncludedFFGVotes`, `OnChainJustifiedAtTransition`, `AU`, `GU`, `onChainGJBlock`, `onChainVotingSource`, and `GF` in `FastConfirmation/Paper/HFC/Model/Justification.lean`: the chain-carried FFG vote set is computed from ancestry. On-chain justification is a source-to-target-link predicate over votes included in the chain, and a later chain tip inherits a certificate formed by an epoch-`N` block in its ancestry. `onChainGJBlock` and `onChainVotingSource` are the AU-based Def-1/Def-2 selectors.

`FastConfirmation/Paper/HFC/Model/Rule.lean` provides `blockContainedFFGVotes`, the default adapter from Core block payloads to the HFC `BlockFFGVotes` API. The public Algorithm-1 bundles use this adapter directly, so modeled AU facts are computed from actual block payloads, not from an arbitrary vote-content oracle.

## AU Interface

`OnChainAnchorInterface` is the active bridge used by the Algorithm-1 theorem statements. It has five parts:

- `OnChainAnchorWellFormed`: the block-contained AU payloads on the selected/rule-witness chain are well-formed current/previous-epoch source-to-target links before they are read as view messages.
- `HonestProposerIncludesKnownVotes`: for each epoch represented on a chain tip, some block on that chain is seen by an honest proposer at its proposal slot and includes all known previous/current-epoch FFG votes that target that chain's checkpoints, with known per-validator/per-epoch equivocators filtered.
- `OnChainAnchorBlockAvailable`: the block carrying the AU payload is in honest views at the relevant boundary. `OnChainAnchorBlockAvailable.of_blockRelay` discharges this from `Synchrony.blockRelay` once some honest view has the block during a post-GST slot; every honest view has it by the next slot boundary.
- `ViewReadsChainFFGVotes`: if a block tip is in a view, the well-formed FFG payloads carried by that tip's ancestry are readable as view messages.
- `OnChainAnchorRealization`: a locally justified chain anchor used by the rule must be realized as `OnChainJustified` from the block-contained votes on that chain.

From these, `OnChainAnchorVisibility.of_block_available`, `OnChainAnchorInterface.onChainJustified_visible`, and the `ruleGJBlock` / `ruleVotingSource` visibility lemmas derive the useful view-level consequence: an AU fact on `chain(b)` is visible as an honest-view `Justified` fact from the relevant slot boundary onward.

`gjblock`, `votingSource`, and `greatestRealizedJustified` are proof-facing view-realized selectors/helpers. Algorithm 1 uses `ruleGJBlock` and `ruleVotingSource`, and `ffgFilterAt` uses `ruleRealizedGJ` / `ruleRealizedGF`; `FilterSelectorAgreementAt` is the explicit bridge that lets the proofs transport view-realized facts to the AU filter.

`OnChainAnchorInterfacesForRule` narrows this bridge to the blocks Algorithm 1 can consume: the selected block and any previous-slot witness block in the previous-epoch branch. This avoids a global availability premise for arbitrary forks.

This is the model-level form of the paper assumption that an honest proposer eventually places the available certificate on the canonical chain and block gossip makes the carrying block visible. The block availability part is a theorem from synchrony, AU/view justification use the same source-to-target link shape, and the view-level `Justified` bridge is derived by an explicit inductive visibility theorem. The model deliberately omits block-size caps and execution participation flags.
