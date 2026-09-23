module
public import FastConfirmationPaper.HFC.Model.FFGVote
public import FastConfirmationPaper.LMDGhost.Model

@[expose] public section

/-!
# HFC / Model / Justification

The derived FFG notions §4's anchor and filter need come in two layers
(arXiv:2405.00549 §2.2.1; explainer pp.1-2):

* a paper-facing, chain-contained AU/GU/GF layer computed from FFG votes included
  in block ancestry, and
* an older proof-facing, view-realized layer computed from FFG votes visible in
  an honest view.

The AU layer is the literal `AU(b)`/`GU(b)` surface. The view layer is the
gossip/visibility consequence consumed by the existing never-filter proofs; it
is intentionally named below as view-realized, not paper-literal AU. Neither
layer builds the full Casper slashing/link-graph machinery (that is out of the
minimal §4 slice; FFG accountable safety is stated in `TheoremStatements`, not
built here).

Objects (paper names):

* `View.ffgVotes` — the FFG votes in a view.
* `linkWeight A V Cs Ct` — total balance of signers whose FFG vote is `Cs → Ct`
  (the link analogue of `latestSupportWeight`).
* `OnChainJustified` / `AU` / `GU` / `GF` — paper-facing block-contained
  justification/finalization over votes included in `chain(b)`.
* `onChainGJBlock` / `onChainVotingSource` — AU-based Def-1/Def-2 selectors.
* `Justified` — view-level inductive visibility consequence: genesis-epoch
  checkpoint (base), or a ≥ 2/3 weighted supermajority link from an
  already-justified source.
* `Finalized` — justified with a justified immediate next-epoch successor.
* `mentionedCheckpoints` — the finite candidate set the `greatest*` selectors
  range over (every source/target appearing in `V`'s FFG votes, plus the
  genesis checkpoint).
* `greatestJustified` / `greatestFinalized` — view-level max-by-epoch over the
  justified/finalized mentioned checkpoints; default genesis checkpoint if none.
* `greatestJustifiedOfChain` — view-realized analogue of `GU(b)`, the greatest
  justified checkpoint in the chain of `b` visible in a view.
* `greatestRealizedJustified` — proof-facing view-realized, epoch-cut helper corresponding to the
  collapse of Def-3 when AU/view selector agreement is available.
* `gjblock` — view-realized analogue of Def-1 `gjblock(b)`.
* `votingSource` — view-realized analogue of Def-2 `vs(b,t)` used by the existing
  rule/filter proofs; use `onChainVotingSource` for the AU-based selector.
* `gjFFG` — the §3.1 abstract `gj` parameter realized by FFG: under Assumption 1
  (static balances) it is a constant `Stakes`, so the §3.1 weight engine is
  reused verbatim (see the design note below).

`noncomputable` is forced by `Finset.image` / `totalWeight` / `argmax`.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- The genesis checkpoint `(genesis, 0)`; the default greatest-justified /
    greatest-finalized value and the base of the `Justified` induction. -/
def genesisCheckpoint : Checkpoint n := ⟨Block.genesis, 0⟩

/-- Local copy of the epoch-boundary block selector used by the on-chain AU model. It matches
    `Rule.boundaryBlock` but lives here to avoid an import cycle: `Rule.lean` imports this file. -/
def onChainBoundaryBlock (bound : Slot) : Block n → Block n
  | Block.genesis => Block.genesis
  | Block.mk bid p s => if s ≤ bound then Block.mk bid p s else onChainBoundaryBlock bound p
  | Block.mkWithVotes bid p s votes =>
      if s ≤ bound then Block.mkWithVotes bid p s votes else onChainBoundaryBlock bound p

/-- Local checkpoint helper for on-chain AU/GU/GF. It matches `checkpointOf`: the epoch-`e` onset
    block of `chain(b)`, tagged with `e`. -/
def onChainCheckpointOf (τ : Timing) (b : Block n) (e : Epoch) : Checkpoint n :=
  ⟨onChainBoundaryBlock (τ.fslot e) b, e⟩

/-- The FFG votes carried in a view (read off the `extra` payloads). Declared in
    the `FastConfirmation.View` namespace so `V.ffgVotes` dot-notation resolves. -/
def _root_.FastConfirmation.View.ffgVotes (V : View n (FFGVote n)) : Finset (FFGVote n) :=
  V.msgs.image Message.extra

/-- HFC-level block contents: the FFG vote records included by each block.

This keeps `Core.Block` as the shared parent-pointer type while making the §4 on-chain FFG-vote
payload explicit. A block may include any finite number of FFG votes; the model deliberately does
**not** implement the execution-spec "one recorded vote per validator/epoch" participation-flag
machinery. Instead, the on-chain selectors below ignore a validator's votes for an epoch when the
chain contains an equivocation for that validator/epoch. -/
abbrev BlockFFGVotes (n : ℕ) := Block n → Finset (Message n (FFGVote n))


/-- Chain-scoped well-formed block-contained FFG votes. Public HFC theorem bundles use this
    chain-scoped surface rather than requiring every syntactically constructible block in the model
    to have well-formed payloads. -/
def BlockFFGVotes.WellFormedOnChain (τ : Timing) (blockVotes : BlockFFGVotes n)
    (tip : Block n) : Prop :=
  ∀ ⦃b : Block n⦄, b ≼ tip → ∀ ⦃m : Message n (FFGVote n)⦄, m ∈ blockVotes b →
    (τ.epochOf m.ghost.slot = τ.epochOf b.slot ∨
      τ.epochOf m.ghost.slot + 1 = τ.epochOf b.slot) ∧
    m.extra.target.epoch = τ.epochOf m.ghost.slot ∧
    m.extra.source.epoch ≤ m.extra.target.epoch ∧
    m.extra.source = onChainCheckpointOf τ b m.extra.source.epoch ∧
    m.extra.target = onChainCheckpointOf τ b m.extra.target.epoch

/-- The FFG vote records carried by `b`'s ancestry, including `b` itself. This is the model's
    computable `chain(b)` vote set. -/
def chainIncludedFFGVotes (blockVotes : BlockFFGVotes n) : Block n → Finset (Message n (FFGVote n))
  | Block.genesis => blockVotes Block.genesis
  | Block.mk bid parent slot =>
      blockVotes (Block.mk bid parent slot) ∪ chainIncludedFFGVotes blockVotes parent
  | Block.mkWithVotes bid parent slot votes =>
      blockVotes (Block.mkWithVotes bid parent slot votes) ∪ chainIncludedFFGVotes blockVotes parent

/-- A validator equivocates on-chain for epoch `e` if `chain(b)` contains two distinct FFG payloads
    for that validator with target epoch `e`. The simplified AU model drops that validator's votes
    for `e` from on-chain weight calculations. -/
def OnChainFFGEquivocator (votes : Finset (Message n (FFGVote n))) (i : Validator n)
    (e : Epoch) : Prop :=
  ∃ m₁ ∈ votes, ∃ m₂ ∈ votes,
    m₁.ghost.validator = i ∧ m₂.ghost.validator = i ∧
      m₁.extra.target.epoch = e ∧ m₂.extra.target.epoch = e ∧ m₁.extra ≠ m₂.extra

open Classical in
/-- The non-equivocating on-chain FFG vote records for target epoch `e` in `chain(b)`. -/
noncomputable def onChainFFGVotesForEpoch (blockVotes : BlockFFGVotes n) (b : Block n)
    (e : Epoch) : Finset (Message n (FFGVote n)) :=
  let votes := chainIncludedFFGVotes blockVotes b
  votes.filter (fun m =>
    m.extra.target.epoch = e ∧
      ¬ OnChainFFGEquivocator votes m.ghost.validator e)

open Classical in
/-- Source→target on-chain link weight in `chain(b)`, again ignoring validators that equivocate for
    the target epoch. This is the block-contained analogue of `linkWeight`. -/
noncomputable def onChainLinkWeight (A : Anchor n) (blockVotes : BlockFFGVotes n)
    (b : Block n) (src tgt : Checkpoint n) : Weight :=
  totalWeight A (Finset.univ.filter (fun i =>
    ∃ m ∈ onChainFFGVotesForEpoch blockVotes b tgt.epoch,
      m.ghost.validator = i ∧ m.extra.source = src ∧ m.extra.target = tgt))

open Classical in
/-- Checkpoints mentioned by FFG votes included in `chain(b)`, plus genesis. -/
noncomputable def onChainMentionedCheckpoints (blockVotes : BlockFFGVotes n)
    (b : Block n) : Finset (Checkpoint n) :=
  let votes := chainIncludedFFGVotes blockVotes b
  insert genesisCheckpoint
    (votes.image (fun m => m.extra.source) ∪ votes.image (fun m => m.extra.target))

/-! The following predicates are the paper-literal AU/GU/GF surface for the simplified on-chain
model. They are intentionally parallel to the older view/gossip `Justified` selectors above, which
remain for compatibility with existing proofs. -/

/-- `C ∈ AU(b)`: `C` is justified by source→target FFG links included on `chain(b)`. A non-genesis
    checkpoint is justified at an epoch transition when an epoch-`N` witness block `B` on `chain(b)`
    carries, in its ancestry, a ≥2/3 static-validator-set source→target link from an already
    on-chain-justified source `Cs` to the chain checkpoint `Ct = C(b,Ct.epoch)`. The witness block
    matters: a later chain tip inherits the AU fact formed when the epoch-`N` block appeared.

    Included votes are constrained separately by `BlockFFGVotes.WellFormed`. On-chain link weights
    ignore per-validator/per-target-epoch equivocators, matching the simplified equivocation
    handling used throughout the AU surface. -/
inductive OnChainJustified (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n) :
    Block n → Checkpoint n → Prop
  | base {b : Block n} : OnChainJustified A τ blockVotes b genesisCheckpoint
  | link {b : Block n} {N : Epoch} {B : Block n} {Cs Ct : Checkpoint n}
      (hchainBlock : B ≼ b)
      (hblockEpoch : τ.epochOf B.slot = N)
      (hsource : OnChainJustified A τ blockVotes B Cs)
      (htargetEpoch : Ct.epoch = N ∨ Ct.epoch + 1 = N)
      (hchainTarget : Ct = onChainCheckpointOf τ b Ct.epoch)
      (hsup : 3 * onChainLinkWeight A blockVotes B Cs Ct ≥ 2 * totalWeight A Finset.univ) :
      OnChainJustified A τ blockVotes b Ct


/-- `C` is finalized on-chain in `chain(b)`: it and an immediate next-epoch descendant checkpoint
    are both in `AU(b)`. -/
def OnChainFinalized (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) (C : Checkpoint n) : Prop :=
  OnChainJustified A τ blockVotes b C ∧
    ∃ C' : Checkpoint n,
      C'.epoch = C.epoch + 1 ∧ C.block ≼ C'.block ∧
        OnChainJustified A τ blockVotes b C'

open Classical in
/-- `AU(b)`: the finite set of on-chain justified checkpoints mentioned by votes in `chain(b)`. -/
noncomputable def AU (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) : Finset (Checkpoint n) :=
  (onChainMentionedCheckpoints blockVotes b).filter
    (fun C => OnChainJustified A τ blockVotes b C)

open Classical in
/-- `GU(b)`: the greatest on-chain justified checkpoint in `AU(b)`, by epoch. -/
noncomputable def GU (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) : Checkpoint n :=
  match ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainJustified A τ blockVotes b C ∧ C.block ≼ b)).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- AU-based `gjblock(b)` (Def 1): the greatest on-chain justified checkpoint in `AU(b)` whose
    block is on `chain(b)` and whose epoch is strictly below `epoch(b)`. This is the paper-facing
    companion to the proof-facing, view-realized `gjblock`. -/
noncomputable def onChainGJBlock (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) : Checkpoint n :=
  match ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainJustified A τ blockVotes b C ∧
        C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- AU-based voting source `vs(b,t)` (Def 2): `onChainGJBlock(b)` when
    `epoch(b) = epoch(t)`, otherwise `GU(b)`. This is chain-local and view-independent, unlike the
    proof-facing `votingSource`, which is the corresponding view-realized selector used by the
    existing never-filter proofs. As with `votingSource`, the `epoch(b) > epoch(t)` input is
    totalized by the `else` branch; that input is unreachable for blocks read from a causal view. -/
noncomputable def onChainVotingSource (A : Anchor n) (τ : Timing)
    (blockVotes : BlockFFGVotes n) (b : Block n) (t : Time) : Checkpoint n :=
  if τ.epochOf b.slot = τ.epochOf (τ.slotOf t) then onChainGJBlock A τ blockVotes b
  else GU A τ blockVotes b

open Classical in
/-- `GF(b)`: the greatest on-chain finalized checkpoint in `chain(b)`, by epoch. -/
noncomputable def GF (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) : Checkpoint n :=
  match ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainFinalized A τ blockVotes b C)).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- Source→target link weight at anchor `A`: total balance of signers whose FFG
    vote in `V` is exactly `src → tgt` (the link analogue of
    `latestSupportWeight`; arXiv §2.2.1 supermajority links). -/
noncomputable def linkWeight (A : Anchor n) (V : View n (FFGVote n))
    (src tgt : Checkpoint n) : Weight :=
  totalWeight A (Finset.univ.filter (fun i =>
    ∃ m ∈ V.msgs, m.ghost.validator = i ∧ m.extra.source = src ∧ m.extra.target = tgt))

/-- `C` is justified in `V` at anchor `A` (arXiv §2.2.1, inductive): a
    genesis-epoch checkpoint, or the target of a ≥ 2/3 weighted supermajority link
    from an already-justified source. A pure weight predicate (no `β`). -/
inductive Justified (A : Anchor n) (V : View n (FFGVote n)) : Checkpoint n → Prop
  | base : Justified A V genesisCheckpoint
  | link {Cs Ct : Checkpoint n} (hs : Justified A V Cs)
      (hsup : 3 * linkWeight A V Cs Ct ≥ 2 * totalWeight A Finset.univ) :
      Justified A V Ct

/-- `C` is finalized in `V` at anchor `A` (arXiv §2.2.1): justified, with its
    immediate next-epoch successor (a descendant checkpoint one epoch later) also
    justified. -/
def Finalized (A : Anchor n) (V : View n (FFGVote n)) (C : Checkpoint n) : Prop :=
  Justified A V C ∧
    ∃ C' : Checkpoint n,
      C'.epoch = C.epoch + 1 ∧ C.block ≼ C'.block ∧ Justified A V C'

/-- The candidate checkpoints the `greatest*` selectors range over: every source
    and target appearing in `V`'s FFG votes, together with the genesis checkpoint.
    `GJ`/`GF` are realized only against checkpoints actually mentioned in the view. -/
noncomputable def mentionedCheckpoints (V : View n (FFGVote n)) : Finset (Checkpoint n) :=
  insert genesisCheckpoint
    (V.ffgVotes.image FFGVote.source ∪ V.ffgVotes.image FFGVote.target)

open Classical in
/-- The greatest justified checkpoint in `V` at anchor `A`: max-by-epoch over the
    justified mentioned checkpoints; default genesis checkpoint if none. **Lean-internal
    helper** — the global, view-wide, any-epoch max-by-epoch justified checkpoint. It has
    NO direct paper counterpart (the paper's `GU(b) = gujblock(b)` is *chain-relative* — see
    `greatestJustifiedOfChain` — and the public Def-3 `GJ(V,t)` is `ruleRealizedGJ`);
    this is used only to epoch-dominate the realized/chain selectors, not as a protocol object. -/
noncomputable def greatestJustified (A : Anchor n) (V : View n (FFGVote n)) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter (fun C => Justified A V C)).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- The greatest finalized checkpoint in `V` at anchor `A` (`GF`): max-by-epoch
    over the finalized mentioned checkpoints; default genesis checkpoint if none. -/
noncomputable def greatestFinalized (A : Anchor n) (V : View n (FFGVote n)) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter (fun C => Finalized A V C)).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- The view-realized greatest justified checkpoint in the chain of `b`: max-by-epoch over
    checkpoints that are justified in the view and whose block is an ancestor of `b`; default
    genesis checkpoint if none. This is the proof-facing analogue of paper `GU(b)`, not the
    AU-based `GU` above. It can be strictly older than the view-global `greatestJustified` whenever
    that global checkpoint sits off `chain(b)`, which is how the view-realized voting source ages
    when `chain(b)` stops being re-justified. -/
noncomputable def greatestJustifiedOfChain (A : Anchor n) (V : View n (FFGVote n))
    (b : Block n) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b)).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- Proof-facing, view-realized epoch-cut greatest justified checkpoint. It corresponds to the
    collapse of **Def 3** `GJ(𝒱,t)` when the AU voting-source selectors visible in a view agree with
    the view-realized helper selectors (arXiv:2405.00549 §2.2.1). The
    paper reads `GJ(𝒱,t) = max{vs(b,t) : slot(b) ≤ slot(t)}`. Since every view-realized voting
    source `vs(b,t)` is *realized* — its epoch is strictly below the current epoch
    `epochOf(slotOf t)` — this `max` collapses (upper bound, each
    `vs.epoch < epoch(t)`; lower
    bound, the max justified checkpoint `C*` of epoch `< epoch(t)` is itself
    `vs(C*.block, t)`, the view-realized chain selector at `C*.block`)
    to the **max-by-epoch over the justified mentioned checkpoints of epoch strictly
    below the current epoch**. Default genesis checkpoint if none.

    This is genuinely distinct from `greatestJustified` (the global, non-realized, view-level max)
    and from `greatestJustifiedOfChain` (the view-realized chain selector used in the `else`
    branch): `greatestRealizedJustified` is global but *epoch-cut*,
    excluding the still-unrealized current-epoch justifications. -/
noncomputable def greatestRealizedJustified (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.epoch < τ.epochOf (τ.slotOf t))).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- View-realized `gjblock(b)` analogue: the greatest checkpoint justified in the view, in the
    chain of `b`, whose epoch is strictly below `epoch(b)`. Max-by-epoch over view-justified
    mentioned checkpoints `C` with `C.block ≼ b` and `C.epoch < epoch(b)`; default genesis. This is
    the proof-facing same-epoch branch of `votingSource`. The AU-based paper-facing selector is
    `onChainGJBlock`. -/
noncomputable def gjblock (A : Anchor n) (τ : Timing) (V : View n (FFGVote n)) (b : Block n) :
    Checkpoint n :=
  match ((mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax
      (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

/-- View-realized voting source used by the existing rule/filter proofs: `gjblock A τ V b` when
    `epoch(b) = epoch(t)`, otherwise `greatestJustifiedOfChain A V b`. Both branches are
    chain-relative inside the view, but this is **not** the paper-literal AU function: it routes
    through view-level `Justified A V`. Use `onChainVotingSource` for the AU-based,
    view-independent Def-2 selector over `AU(b)`.

    `τ`, `b`, `t` are all used: the epoch split is
    `epochOf b.slot = epochOf(slotOf t)`, `gjblock` reads `b`'s own epoch cut, and `b` selects the
    chain in both branches.

    **Totalization caveat (disclosed):** Def 2 is *undefined* when `epoch(b) > e` (tex l.303-307);
    this `else` branch returns `gujblock(b)` for the whole `epoch(b) ≠ epoch(t)` case, so it
    **totalizes** that undefined input. Benign — it is unreachable: a block read from a view at `t`
    has `slot(b) ≤ slotOf t` (`noFutureMessages`) ⇒ `epoch(b) ≤ epoch(t)`, and the proof lemmas only
    apply this helper to such in-view blocks. For the AU-level Def-2 function, see
    `onChainVotingSource`; here the totalization only fixes a proof-helper value for inputs that
    never occur. -/
noncomputable def votingSource (A : Anchor n) (τ : Timing) (V : View n (FFGVote n))
    (b : Block n) (t : Time) : Checkpoint n :=
  if τ.epochOf b.slot = τ.epochOf (τ.slotOf t) then gjblock A τ V b
  else greatestJustifiedOfChain A V b

/-- **The FFG prefix property** (`GF ⪯ GJ` in a single view), as a named faithful
    premise. In FFG-Casper the greatest *finalized* checkpoint's block is an ancestor of
    every justified checkpoint of weakly-greater epoch (the finalized chain is a prefix
    of the justified chain — arXiv §2.2.1). In the minimal §4 slice `Justified`/`Finalized`
    are pure *weight* predicates with no built-in chain linkage between distinct justified
    checkpoints, so this prefix relation is **not** derivable from the model alone — its
    corresponding Casper slashing / 2/3-link-intersection argument is represented by
    `FFG_AccountableSafety`. This is the named structural premise that **D1**
    (`greatestFinalized_block_ancestor_greatestJustified`) instantiates. -/
def FinalizedPrefixOfJustified (A : Anchor n) (V : View n (FFGVote n)) : Prop :=
  ∀ ⦃Cf Cj : Checkpoint n⦄, Finalized A V Cf → Justified A V Cj →
    Cf.epoch ≤ Cj.epoch → Cf.block ≼ Cj.block

/-- **The `gj` realization** (Def 3 / explainer footnote 2). The §3.1 abstract
    parameter `gj : ViewFamily → Validator → Time → Anchor` realized by FFG. The
    §3.1 engine consumes `gj`/`C` **only** as a `Stakes` balance source; under
    Assumption 1 (static validator set / balances, modulo slashing — explainer
    Assumption 1) the FFG anchor's *balances* are the static deployment balances
    `bal₀` regardless of which checkpoint is GJ. So the faithful minimal
    realization is a constant `Stakes`, and the §3.1 `AnchorsCoincide` /
    `StaticBalances` premises are then discharged exactly as §3.1 does. The
    checkpoint *structure* is read by `ffgFilter` (through `ruleRealizedGJ` / `ruleRealizedGF`), not
    by this balance anchor. -/
noncomputable def gjFFG (bal₀ : Stakes n) :
    ViewFamily n (FFGVote n) → Validator n → Time → Anchor n :=
  fun _ _ _ => bal₀

end FastConfirmation.HFC

end
