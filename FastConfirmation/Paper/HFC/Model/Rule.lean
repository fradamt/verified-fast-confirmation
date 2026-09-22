module
public import FastConfirmation.Paper.HFC.Model.Justification

@[expose] public section

/-!
# HFC / Model / Rule

The §4 **checkpoint of a block** helpers that the §3.1 `isConfirmed` (Algorithm 4)
does not provide: the epoch-boundary block of a chain (`boundaryBlock`) and the FFG
checkpoint `C(b, e)` (`checkpointOf`) — the epoch-`e` boundary block of `chain(b)`,
tagged with `e`. These feed the honest FFG-voting discipline (`HonestFFGNoEquivocation`)
and the cross-epoch never-filter argument
(`FastConfirmation/Paper/HFC/Proof/CrossEpoch.lean`).
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- The boundary block of a chain at an arbitrary slot bound `bound`: the highest-slot ancestor of
    `b` whose slot is `≤ bound` (structural recursion down the parent chain). `checkpointOf` below
    fixes the paper checkpoint convention by calling this helper with `bound := fslot e`. -/
def boundaryBlock (bound : Slot) : Block n → Block n
  | Block.genesis => Block.genesis
  | Block.mk bid p s => if s ≤ bound then Block.mk bid p s else boundaryBlock bound p
  | Block.mkWithVotes bid p s votes =>
      if s ≤ bound then Block.mkWithVotes bid p s votes else boundaryBlock bound p

/-- `C(b, e)`: the checkpoint of `b` at epoch `e` (arXiv:2405.00549 §2.2.1, Def of `chkp`) —
    the epoch-`e` **onset** (start) boundary block of `chain(b)`, tagged with `e`: the highest-slot
    ancestor of `b` with slot `≤ fslot e` (the first slot of epoch `e`). Verbatim: checkpoints are
    "blocks positioned at the onset of an epoch" (paper §2.2.1). For a same-epoch head
    (`epoch(b)=e`, `b.slot ≥ fslot e`) this is a *settled ancestor* of `b`, NOT `b` itself — so two
    honest validators
    whose heads both descend from a canonical block `b` compute the **same** `C(b,e)` (prefix
    agreement `b ⪯ head` suffices, no head convergence). This is the load-bearing reason the §4.1
    certificate lemma (`lem:sufficient-condition-for-justification`) sums GHOST votes for *varying*
    `b'' ⪰ b` onto the single target `C(b,e)`: each FFG target `chkp(b'',e) = chkp(b,e)` is that
    shared onset ancestor. Using `lslot e` would instead select the epoch-end boundary, equal to the
    head for same-epoch heads, and would require head equality; `fslot e` selects the paper's onset
    boundary. -/
def checkpointOf (τ : Timing) (b : Block n) (e : Epoch) : Checkpoint n :=
  ⟨boundaryBlock (τ.fslot e) b, e⟩

/-- Default AU contents from the Core block payloads. Each simplified
    `ContainedFFGVote` is interpreted as an FFG-only source→target link on the
    including block's chain, while preserving the signer and slot at which that
    vote was cast. The reified message is marked `countsForLMD := false`, so
    block-contained AU payloads can support FFG justification without becoming
    synthetic LMD fork-choice votes. This is the preferred model surface for §4:
    `chainIncludedFFGVotes (blockContainedFFGVotes τ) b` is computable from `b`'s
    ancestry alone. -/
noncomputable def blockContainedFFGVotes (τ : Timing) : BlockFFGVotes n :=
  fun b =>
    b.containedFFGVotes.image (fun r =>
      let target := checkpointOf τ b r.targetEpoch
      { ghost :=
          { validator := r.validator
            slot := r.slot
            block := target.block }
        countsForLMD := false
        extra :=
          { source := checkpointOf τ b r.sourceEpoch
            target := target } })

/-- The paper-facing Def-1 source selector used by Algorithm 1, computed from the default
    block-contained AU payload adapter on `chain(b)`. -/
noncomputable def ruleGJBlock (A : Anchor n) (τ : Timing) (b : Block n) : Checkpoint n :=
  onChainGJBlock A τ (blockContainedFFGVotes (n := n) τ) b

/-- The paper-facing Def-2 voting source used by Algorithm 1, computed from the default
    block-contained AU payload adapter on `chain(b)`. Unlike the proof helper `votingSource`, this
    is view-independent. -/
noncomputable def ruleVotingSource (A : Anchor n) (τ : Timing) (b : Block n)
    (t : Time) : Checkpoint n :=
  onChainVotingSource A τ (blockContainedFFGVotes (n := n) τ) b t

open Classical in
/-- The paper-facing realized greatest-justified checkpoint `GJ(V,t)` (Def 3), computed literally
    as the max-by-epoch of the AU voting sources `vs(b,t)` for blocks known in `V` whose slot is no
    later than `slot(t)`. The genesis checkpoint is inserted as the total default. -/
noncomputable def ruleRealizedGJ (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) : Checkpoint n :=
  match (insert genesisCheckpoint
      ((V.blocks.filter (fun b => b.slot ≤ τ.slotOf t)).image
        (fun b => ruleVotingSource A τ b t))).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

open Classical in
/-- The paper-facing realized greatest-finalized checkpoint `GF(V,t)`, computed as the
    max-by-epoch of the on-chain finalized selector `GF(b)` for blocks known in `V` whose slot is no
    later than `slot(t)`. The genesis checkpoint is inserted as the total default. -/
noncomputable def ruleRealizedGF (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) : Checkpoint n :=
  match (insert genesisCheckpoint
      ((V.blocks.filter (fun b => b.slot ≤ τ.slotOf t)).image
        (fun b => GF A τ (blockContainedFFGVotes (n := n) τ) b))).toList.argmax (·.epoch) with
  | some C => C
  | none => genesisCheckpoint

/-- Chain-scoped well-formedness of the concrete `Block.mkWithVotes` AU payload adapter. This is
    part of the active AU interface: malformed block-contained FFG records are not allowed to be
    read as view messages for the Algorithm-1 bridge. -/
def OnChainAnchorWellFormed (_A : Anchor n) (τ : Timing) (b : Block n) : Prop :=
  BlockFFGVotes.WellFormedOnChain (n := n) τ (blockContainedFFGVotes (n := n) τ) b

/-- The raw on-chain FFG vote set `AU(b)` read from the votes contained in `b`'s
    ancestry. -/
noncomputable def onChainFFGVotes (τ : Timing) (b : Block n) :
    Finset (Message n (FFGVote n)) :=
  chainIncludedFFGVotes (blockContainedFFGVotes τ) b

/-- AU-style chain fact: checkpoint `C` is on `chain(b)` and is justified from the FFG votes
    carried by `chain(b)`. -/
def OnChainAnchorFromVotes (A : Anchor n) (τ : Timing) (contents : BlockFFGVotes n)
    (b : Block n) (C : Checkpoint n) : Prop :=
  C.block ≼ b ∧ OnChainJustified A τ contents b C

/-- A view contains an FFG equivocation for validator `i` at target epoch `e` when it contains two
    distinct FFG payloads by `i` targeting `e`. The simplified proposer-inclusion model drops all
    known votes by such a validator for that target epoch. -/
def ViewFFGEquivocator (V : View n (FFGVote n)) (i : Validator n) (e : Epoch) : Prop :=
  ∃ m₁ ∈ V.msgs, ∃ m₂ ∈ V.msgs,
    m₁.ghost.validator = i ∧ m₂.ghost.validator = i ∧
      m₁.extra.target.epoch = e ∧ m₂.extra.target.epoch = e ∧ m₁.extra ≠ m₂.extra

/-- The known FFG vote is a vote for checkpoints on `b`'s chain. `ContainedFFGVote` stores the
    compact chain-relative form, so known-vote inclusion only ranges over messages whose source and
    target already match the including block's chain checkpoints. Votes for other forks may still
    be carried by a real block, but they are outside this simplified AU payload adapter and do not
    count toward `AU(b)`. -/
def FFGVoteTargetsBlockChain (τ : Timing) (b : Block n) (m : Message n (FFGVote n)) : Prop :=
  m.extra.target.epoch = τ.epochOf m.ghost.slot ∧
    m.extra.source.epoch ≤ m.extra.target.epoch ∧
    m.extra.source = checkpointOf τ b m.extra.source.epoch ∧
    m.extra.target = checkpointOf τ b m.extra.target.epoch

/-- A vote is eligible to be included in `b` under the simplified no-cap block model iff it was
    cast in `b`'s current epoch or immediately previous epoch and targets checkpoints on `b`'s
    chain. -/
def FFGVoteEligibleForBlock (τ : Timing) (b : Block n) (m : Message n (FFGVote n)) : Prop :=
  (τ.epochOf m.ghost.slot = τ.epochOf b.slot ∨
      τ.epochOf m.ghost.slot + 1 = τ.epochOf b.slot) ∧
    FFGVoteTargetsBlockChain τ b m

/-- Equality notion for including a known FFG vote in a block payload. The block payload adapter
    synthesizes an FFG-only carrier message for the source→target link on the including chain, so
    inclusion compares the signer, vote slot, and FFG source/target rather than requiring exact
    `Message` equality with the proposer's view message or its LMD head. -/
def SameFFGVoteForInclusion (m included : Message n (FFGVote n)) : Prop :=
  included.ghost.validator = m.ghost.validator ∧
    included.ghost.slot = m.ghost.slot ∧
    included.extra.source = m.extra.source ∧
    included.extra.target = m.extra.target

/-- The paper's "honest proposer includes all known FFG votes" assumption, localized to a concrete
    block proposal. Since this model has no block-cap limit and no execution participation flags,
    an including block contains every previous/current-epoch FFG vote known to the proposer, except
    that if the proposer knows an equivocation by a validator for an epoch then no vote by that
    validator/epoch is required or allowed by this simplified interface. -/
def BlockIncludesKnownFFGVotes (τ : Timing) (𝒱 : ViewFamily n (FFGVote n))
    (proposer : Validator n) (t : Time) (b : Block n) : Prop :=
  (∀ ⦃m : Message n (FFGVote n)⦄, m ∈ (𝒱 proposer t).msgs →
    FFGVoteEligibleForBlock τ b m →
    ¬ ViewFFGEquivocator (𝒱 proposer t) m.ghost.validator m.extra.target.epoch →
      ∃ included ∈ blockContainedFFGVotes τ b, SameFFGVoteForInclusion m included) ∧
  (∀ ⦃m : Message n (FFGVote n)⦄, m ∈ blockContainedFFGVotes τ b →
    ¬ ViewFFGEquivocator (𝒱 proposer t) m.ghost.validator m.extra.target.epoch)

/-- Epoch `N` is represented by some block on `chain(tip)`. -/
def ChainHasEpoch (τ : Timing) (tip : Block n) (N : Epoch) : Prop :=
  ∃ B : Block n, B ≼ tip ∧ τ.epochOf B.slot = N

/-- Every epoch represented on `chain(tip)` has a block on that chain, seen by an honest proposer at
    its proposal slot, whose payload includes all known previous/current-epoch FFG votes that target
    that chain's checkpoints, with known equivocators filtered. This is the theorem-statement
    version of the paper's no-cap honest-proposer inclusion assumption; it deliberately abstracts
    proposer schedules and block-size limits. -/
def HonestProposerIncludesKnownVotes (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (tip : Block n) : Prop :=
  ∀ ⦃N : Epoch⦄, ChainHasEpoch τ tip N →
    ∃ proposer : Validator n, ∃ B : Block n,
      proposer ∈ fm.honest ∧ B ≼ tip ∧ B ∈ (𝒱 proposer (τ.st B.slot)).blocks ∧
        τ.epochOf B.slot = N ∧ BlockIncludesKnownFFGVotes τ 𝒱 proposer (τ.st B.slot) B

/-- Local honest-view justification is realized by the block-contained AU vote surface on
    `chain(b)`. This captures the direction used by Algorithm 1's GU-anchor precondition: a locally
    observed chain anchor is not treated as a free gossip fact; it must correspond to
    `OnChainJustified` computed from the votes carried by `b`'s ancestry. -/
def OnChainAnchorRealization (A : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  HonestProposerIncludesKnownVotes fm τ 𝒱 b →
    ∀ ⦃Cc : Checkpoint n⦄, Cc.block ≼ b →
    (∃ v : Validator n, v ∈ fm.honest ∧ Justified A (𝒱 v t) Cc) →
      OnChainJustified A τ (blockContainedFFGVotes τ) b Cc

/-- The block carrying the AU payload is available to honest views at the interface time. The
    intended discharge is `Synchrony.blockRelay`: once any honest view sees the block, block gossip
    makes the block, and hence its contained FFG votes, available to every honest view by the chosen
    boundary. -/
def OnChainAnchorBlockAvailable (fm : FaultModel n) (𝒱 : ViewFamily n (FFGVote n))
    (b : Block n) (t : Time) : Prop :=
  (∃ v : Validator n, v ∈ fm.honest ∧ b ∈ (𝒱 v t).blocks) ∧
    ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, t ≤ t' →
      b ∈ (𝒱 w t').blocks

/-- Block availability discharged from synchrony: once an honest view has `b`, `blockRelay` puts
    `b` in every honest view at the next post-GST slot boundary, and view monotonicity keeps it
    there afterward. -/
theorem OnChainAnchorBlockAvailable.of_blockRelay {fm : FaultModel n} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} (hSync : Synchrony n (FFGVote n) τ fm 𝒱)
    {v : Validator n} (hv : v ∈ fm.honest) {t : Time} {b : Block n} {s' : Slot}
    (hb : b ∈ (𝒱 v t).blocks) (htslot : τ.slotOf t ≤ s') (hgst : τ.AfterGST (τ.st s')) :
    OnChainAnchorBlockAvailable fm 𝒱 b (τ.st (s' + 1)) := by
  constructor
  · exact ⟨v, hv, hSync.blockRelay hv hv hb htslot hgst⟩
  · intro w hw t' ht'
    exact (hSync.monotone w (τ.st (s' + 1)) t' ht').2
      (hSync.blockRelay hv hw hb htslot hgst)

/-- HFC view consistency for well-formed block-contained FFG payloads: when a block tip is in a
    view, the FFG vote records carried by any well-formed ancestor payload on that tip's chain are
    readable as view messages. This is not a network-delay assumption; it is the local
    interpretation that valid block payloads are available with the block. -/
def ViewReadsChainFFGVotes (τ : Timing) (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  ∀ ⦃v : Validator n⦄ ⦃t : Time⦄ ⦃tip b : Block n⦄ ⦃m : Message n (FFGVote n)⦄,
    tip ∈ (𝒱 v t).blocks →
      b ≼ tip →
      BlockFFGVotes.WellFormedOnChain (n := n) τ (blockContainedFFGVotes (n := n) τ) b →
      m ∈ chainIncludedFFGVotes (blockContainedFFGVotes (n := n) τ) b →
        m ∈ (𝒱 v t).msgs

/-- AU facts on `chain(b)` are visible as honest-view `Justified` facts from the relevant slot
    boundary onward, provided the block carrying those AU votes is available in honest views.

    `OnChainAnchorBlockAvailable.of_blockRelay` discharges the block-availability part from
    `Synchrony.blockRelay`, and `ViewReadsChainFFGVotes` records the local payload-readability
    invariant that makes block-contained source→target links count as view messages. -/
def OnChainAnchorVisibility (A : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  HonestProposerIncludesKnownVotes fm τ 𝒱 b →
    OnChainAnchorWellFormed A τ b →
    OnChainAnchorBlockAvailable fm 𝒱 b (τ.st (τ.slotOf t)) →
    ∀ ⦃Cc : Checkpoint n⦄, Cc.block ≼ b →
    OnChainJustified A τ (blockContainedFFGVotes τ) b Cc →
      ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' →
        Justified A (𝒱 w t') Cc

/-- The active AU/Gasper bridge used by the Algorithm-1 theorem statements: block payloads are
    chain-well-formed, honest-proposer-complete for the epochs on the chain, available to honest
    views at the interface boundary, readable as view FFG messages, and local GU anchors are
    realized as AU facts. The block-availability conjunct is directly dischargeable from
    `Synchrony.blockRelay`; AU-to-view `Justified` visibility is derived from well-formedness, block
    availability, and `ViewReadsChainFFGVotes`. -/
def OnChainAnchorInterface (A : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  OnChainAnchorWellFormed A τ b ∧
    HonestProposerIncludesKnownVotes fm τ 𝒱 b ∧
    OnChainAnchorBlockAvailable fm 𝒱 b (τ.st (τ.slotOf t)) ∧
      ViewReadsChainFFGVotes τ 𝒱 ∧
        OnChainAnchorRealization A fm τ 𝒱 b t

/-- AU interfaces for the blocks that Algorithm 1 can actually consume at time `t`: the confirmed
    block itself and any previous-slot witness block `b'` that the previous-epoch branch ranges
    over. This avoids assuming AU availability for arbitrary blocks/forks that are not rule
    witnesses. -/
def OnChainAnchorInterfacesForRule (A : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  OnChainAnchorInterface A fm τ 𝒱 b t ∧
    ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃b' : Block n⦄,
      b' ∈ (𝒱 v (τ.st (τ.slotOf t - 1))).blocks →
      b ≼ b' → τ.epochOf b'.slot < τ.epochOf (τ.slotOf t) →
        OnChainAnchorInterface A fm τ 𝒱 b' t

end FastConfirmation.HFC

end
