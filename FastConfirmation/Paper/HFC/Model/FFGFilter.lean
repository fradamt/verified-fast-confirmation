module
public import FastConfirmation.Paper.HFC.Model.Rule

@[expose] public section

/-!
# HFC / Model / FFGFilter

The §4 justification filter `FIL_hfc` (`LMD-GHOST-HFC = LMD-GHOST ∘ FIL_hfc`),
realized as the Core `BlockFilter` seam at `P := FFGVote n`. Plain LMD-GHOST uses
`trivialFilter`; §4 swaps in `ffgFilter`, leaving the §3.1 weight machinery
filter-agnostic.

**Paper form (arXiv:2405.00549 §4), confirmed against the arXiv HTML
`𝒱 ∖ { b ∈ blocks(𝒱) : ¬( b ⪯ GJ(𝒱,t) ∨ [ b ⪰ block(GJ) ∧ … ] ) }`:**

`FIL_hfc(𝒱, t)` **keeps** block `b` iff
* `b ⪯ GJ(𝒱,t)` — `b` is an ancestor of the greatest-justified checkpoint's
  block; **or**
* `b ⪰ block(GJ(𝒱,t))` (descends from the GJ block) **and** there is a leaf
  `b' ⪰ b` that descends from the greatest-finalized checkpoint's block, is no
  later than the current epoch, has no children in the view, and whose voting
  source is either `GJ(𝒱,t)` itself or no older than `epoch(t) − 2`.

It **removes** any block that conflicts with `GJ(𝒱,t)` (neither ancestor nor
descendant of the GJ block) or descends from it but whose subtree has no leaf with
a recent-enough voting source. This is "the FFG-Casper protocol filtering out
blocks not descending from / conflicting with the justified checkpoint" (§4 intro:
§4 "amounts to adding conditions that ensure that once a block is confirmed, the
FFG-Casper protocol will never remove this block").

The voting-source recency `epoch(vs(b',t)) ≥ epoch(t) − 2` matches the explainer's
`vs(phead, now) ≥ epoch(now) − 2` (Algorithm 2, Case 1; explainer p.8). The leaf
condition `children(b',𝒱) = ∅` reuses the Core `eligibleChildren … trivialFilter`
(children of `b'` in the view, unfiltered).

The anchor `A` is needed to evaluate `ruleRealizedGJ` / `ruleRealizedGF`
/ `ruleVotingSource`; in §4 it is the GJ-anchor `C` threaded into the engine.
-/

namespace FastConfirmation.HFC

open FastConfirmation
open scoped Block

variable {n : ℕ}

/-- `FIL_hfc` keep-predicate (arXiv §4): block `b` is FFG-eligible in `(V,t)` at
    anchor `A`. See the module doc for the paper mapping.

    **`GJ` is the *paper* realized greatest-justified checkpoint of Def 3**
    (`ruleRealizedGJ A τ V t`): max-by-epoch over AU voting sources `vs(b,t)` for known blocks
    with `slot(b) ≤ slot(t)`. The leaf source also uses the AU Def-2 selector
    `ruleVotingSource`, not the view-realized proof helper. -/
def ffgFilterAt (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) (b : Block n) : Prop :=
  let gjC := ruleRealizedGJ A τ V t
  let gfC := ruleRealizedGF A τ V t
  b ≼ gjC.block ∨
    ( gjC.block ≼ b ∧
      ∃ b' ∈ V.blocks, b ≼ b' ∧ gfC.block ≼ b' ∧
        τ.epochOf b'.slot ≤ τ.epochOf (τ.slotOf t) ∧
        eligibleChildren τ trivialFilter V t b' = ∅ ∧
        ( ruleVotingSource A τ b' t = gjC ∨
          (ruleVotingSource A τ b' t).epoch + 2 ≥ τ.epochOf (τ.slotOf t) ) )

/-- The `FIL_hfc` filter as the Core `BlockFilter` seam (the slot of `ffgFilterAt`,
    where `trivialFilter` sits). The anchor it reads is the §4 GJ-anchor `C`; the
    §4 statements partially apply it at that `C`. -/
def ffgFilter (A : Anchor n) (τ : Timing) : BlockFilter n (FFGVote n) :=
  ffgFilterAt A τ

end FastConfirmation.HFC

end
