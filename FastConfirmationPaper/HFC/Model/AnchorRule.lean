module
public import FastConfirmationPaper.HFC.Model.ConfirmationRule
public import FastConfirmationPaper.LMDGhost.Model.ConfirmationRule

@[expose] public section

/-!
# HFC / Model / FFGRule

**Algorithm 1 (the LMD-GHOST-HFC confirmation rule), modeled explicitly** (arXiv:2405.00549,
`alg:ffg`, l.2328-2378). This replaces the earlier *semantic* abstraction of confirmation
(`isConfirmed ∧ WillNoConflictingChkpBeJustified`) with the paper-shaped *local, computable* rule.
The source selector consumed by this file is the AU-based `ruleVotingSource`, computed from
block-contained votes on `chain(b)`.

* `ruleGJBlock` — AU-based `gjblock(b)` (Def 1, l.289-294): the greatest checkpoint justified by
  votes contained in `chain(b)`, of epoch strictly below `epoch(b)`.
* `linkWeightUpTo` — the `ffgvalsettoslot[to=s]` weight (l.2527): the balance of committee
  members of slots `[firstslot(epoch tgt), s]` whose FFG vote in the view is `src → tgt`.
* `willChkpBeJustified` — the local FFG-weight reservation (l.2334-2343).
* `isConfirmedNoCaching` — the current-epoch and previous-epoch branches (l.2344-2361).
* `Alg1.highestConfirmedSinceEpoch` / `Alg1.isConfirmed` — the top-level Algorithm-1 wrapper:
  choose the highest block satisfying `isConfirmedNoCaching` since an epoch, then confirm its
  ancestors.

These feed `FastConfirmation/Paper/HFC/Proof/`, where the never-filter is driven directly by `willChkpBeJustified` (via the
§4.1 certificate `checkpoint_justified_of_willChkp` /
`checkpoint_justified_of_confirmedNoCaching_prev`
and `greatestRealizedJustified_on_chain_from_confirmation`), **eliminating** the semantic gate
`WillNoConflictingChkpBeJustified` rather than deriving it. Balances are constant (`bal₀`), so the
per-anchor weight `weight_{C(b,e)}` is `totalWeight bal₀` (Assumption 1). `we` is the max-slashable
parameter `ffgEquivWeight` (Assumption 5.2).
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

open Classical in
/-- The `ffgvalsettoslot[source=src, target=tgt, to=upTo]` weight (arXiv:2405.00549 l.2527): the
    balance of validators in the committee of slots `[firstslot(epoch tgt), upTo]` whose FFG vote in
    `V` is exactly `src → tgt` and was cast in that slot range. The message-slot bound is
    load-bearing: votes from the current/future part of the epoch must not be counted as already
    observed support and then counted again through the honest-future term of
    `willChkpBeJustified`. -/
noncomputable def linkWeightUpTo (A : Anchor n) (cm : Committees n) (τ : Timing)
    (V : View n (FFGVote n)) (src tgt : Checkpoint n) (upTo : Slot) : Weight :=
  totalWeight A ((committeeUnion cm (τ.fslot tgt.epoch) upTo).filter (fun i =>
    ∃ m ∈ V.msgs, m.ghost.validator = i ∧
      τ.fslot tgt.epoch ≤ m.ghost.slot ∧ m.ghost.slot ≤ upTo ∧
      m.extra.source = src ∧ m.extra.target = tgt))

/-- **`willChkpBeJustified_v(b, e, t)`** (arXiv:2405.00549 Algorithm 1, l.2334-2343): the local
    FFG-weight reservation that the checkpoint `C(b,e)` *will* be justified. The FFG votes for the
    link `vs(b,t) → C(b,e)` received so far (committee up to `slot(t)-1`) plus the honest `(1-β)`
    fraction of the remaining epoch-`e` committee `[slot(t), lastslot(e)]` reach `2/3·W` net of the
    slashable bound `min(W_e, β·W)`. (Weights are at the constant `bal₀`; `we = W_e` the
    max-slashable, Assumption 5.2.) -/
def willChkpBeJustified (bal₀ : Stakes n) (cm : Committees n) (fm : FaultModel n) (we : Weight)
    (τ : Timing) (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n) (b : Block n) (e : Epoch)
    (t : Time) : Prop :=
  linkWeightUpTo bal₀ cm τ (𝒱 v t) (ruleVotingSource bal₀ τ b t) (checkpointOf τ b e)
      (τ.slotOf t - 1)
    + (1 - fm.β) * totalWeight bal₀ (committeeUnion cm (τ.slotOf t) (τ.lslot e))
    ≥ (2 / 3) * totalWeight bal₀ Finset.univ
      + min we (fm.β * totalWeight bal₀ Finset.univ)

/-- **`isConfirmedNoCaching(b, t)`** (arXiv:2405.00549 v3, Algorithm `alg:ffg`, tex l.2344-2361):
    the per-block, per-slot FFG confirmation predicate, with the two paper branches and no extra
    conjuncts. Its `vs` calls use `ruleVotingSource`, the AU-based Def-2 selector over
    block-contained votes in `chain(b)`.

    * **Current epoch** (`epoch(b) = epoch(t)`): `willChkpBeJustified(b, epoch(t), t)`, the
      GU-anchor precondition `epoch(gjblock(b)) = epoch(t)-1`, and
      `isLMDGHOSTSafe(b, gjblock(b), t)`. In the Lean static-balance model the safety predicate is
      parameterized by `bal₀`; the source checkpoint is represented by the AU `ruleGJBlock`.
      (tex l.2348-2352)
    * **Previous epoch** (else): it is the epoch's first slot (`slot(t) = fslot(epoch(t))`),
      `willChkpBeJustified(b, epoch(t)-1, t)`, and there is a witness `b' ⪰ b` in the view at
      `st(slot(t)-1)` of epoch `< epoch(t)` whose voting source is **recent**
      (`epoch(vs(b',t)) ≥ epoch(t)-2`, the paper's lower-bound recency, tex l.2360), with
      `isLMDGHOSTSafe(b, vs(b',t), t)`. (tex l.2353-2361)

    Balances are constant, so `isLMDGHOSTSafe(b, C, t)` is evaluated at `bal₀` (the anchor `C`'s
    balances); per the paper (`isLMDGHOSTSafe`, tex l.945) `C` is a **pure balance anchor** with no
    `C ≼ b` precondition — exactly as encoded here (the anchor argument is implicit, the call is the
    same `isLMDGHOSTSafe … bal₀ (𝒱 v t) b t` in both branches). The paper notes (tex l.2592) the
    safety-condition balance source "is not necessarily extracted from the greatest justified
    checkpoint"; the AU/GU block-vote surface supplies the needed on-chain realization in the
    theorem-statement bundles.

    **Paper fidelity.** The branch structure and conjunct set match `alg:ffg`, with `vs` realized by
    the AU selector over `chain(b)`. The previous-epoch branch carries only the paper's lower-bound
    recency `≥ epoch(t)-2`: there is NO upper bound `epoch(vs) ≤ epoch(t)-1`
    and NO `vs(b',t).block ≼ b` ancestor conjunct (earlier versions added both — now
    **eliminated**). Previous-epoch safety is re-proved without re-adding them
    (`lem:base-case-prev-epoch-for-safety-of-confirmation-ffg`, tex l.3475–3531): for a realized
    `GJ` of epoch `≤ epoch(t)-1`, **Case A** (`GJ.epoch = epoch(t)-1`) uses the
    `Synchrony.messageRelay`
    common-future-view no-conflicting argument over the observed-only certificate
    `checkpointOf(b, epoch(t)-1)`, and **Case B** (`GJ.epoch < epoch(t)-1`) delivers the witness
    source `vs(b',t) = ruleVotingSource(b',t)` keyed at the witness `b'` via AU-style
    block-contained vote availability, concluding only *compatibility* `block(GJ) ~ b`; the
    realization bound
    `epoch(vs(b',t)) ≤ epoch(t)-1` is **proven** from `SlotCommitteeMinority`
    (`justified_epoch_le_of_firstSlot`), not assumed — see `Certificate.lean` /
    `NeverFilteredAlg1.lean`. -/
noncomputable def isConfirmedNoCaching (bal₀ : Stakes n) (fm : FaultModel n) (cm : Committees n)
    (pb : Weight) (we : Weight) (τ : Timing) (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n)
    (b : Block n) (t : Time) : Prop :=
  if τ.epochOf b.slot = τ.epochOf (τ.slotOf t) then
    willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf (τ.slotOf t)) t ∧
      (ruleGJBlock bal₀ τ b).epoch = τ.epochOf (τ.slotOf t) - 1 ∧
      isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v t) b t
  else
    τ.slotOf t = τ.fslot (τ.epochOf (τ.slotOf t)) ∧
      willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf (τ.slotOf t) - 1) t ∧
      ∃ b' : Block n, b' ∈ (𝒱 v (τ.st (τ.slotOf t - 1))).blocks ∧ b ≼ b' ∧
        τ.epochOf b'.slot < τ.epochOf (τ.slotOf t) ∧
        (ruleVotingSource bal₀ τ b' t).epoch ≥ τ.epochOf (τ.slotOf t) - 2 ∧
        isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v t) b t

namespace Alg1

open Classical in
/-- Algorithm-1 wrapper selector: the highest-slot block, in `v`'s views since the second slot of
    epoch `e`, whose local Algorithm-1 predicate `isConfirmedNoCaching` holds. This mirrors
    LMD-GHOST's Algorithm-4 `highestConfirmedSinceEpoch`, but ranges over HFC's FFG-aware rule. -/
noncomputable def highestConfirmedSinceEpoch (bal₀ : Stakes n) (fm : FaultModel n)
    (cm : Committees n) (pb : Weight) (we : Weight) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n) (e : Epoch) (t : Time) : Block n :=
  let cand : Finset (Block n) :=
    (Finset.Icc (τ.fslot e + 1) (τ.slotOf t)).biUnion (fun s' =>
      (𝒱 v (τ.st s')).blocks.filter (fun b' =>
        isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b' (τ.st s')))
  match cand.toList.argmax (·.slot) with
  | some b => b
  | none => Block.genesis

/-- Top-level HFC Algorithm-1 confirmation predicate: `b` is confirmed when it is an ancestor of
    the highest `isConfirmedNoCaching` block for the previous epoch. This is the public wrapper
    theorem statements should use instead of either raw `isConfirmedNoCaching` or LMD-GHOST's
    imported `isConfirmed`. -/
noncomputable def isConfirmed (bal₀ : Stakes n) (fm : FaultModel n) (cm : Committees n)
    (pb : Weight) (we : Weight) (τ : Timing) (𝒱 : ViewFamily n (FFGVote n))
    (v : Validator n) (b : Block n) (t : Time) : Prop :=
  b ≼ highestConfirmedSinceEpoch bal₀ fm cm pb we τ 𝒱 v
    (τ.epochOf (τ.slotOf t) - 1) t

end Alg1

/-- Alias for the HFC Algorithm-1 selector, avoiding collision with LMD-GHOST's same paper name. -/
noncomputable def highestConfirmedSinceEpochAlg1 (bal₀ : Stakes n) (fm : FaultModel n)
    (cm : Committees n) (pb : Weight) (we : Weight) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n) (e : Epoch) (t : Time) : Block n :=
  Alg1.highestConfirmedSinceEpoch (n := n) bal₀ fm cm pb we τ 𝒱 v e t

/-- Alias for the HFC Algorithm-1 confirmation wrapper. -/
noncomputable def isConfirmedAlg1 (bal₀ : Stakes n) (fm : FaultModel n) (cm : Committees n)
    (pb : Weight) (we : Weight) (τ : Timing) (𝒱 : ViewFamily n (FFGVote n))
    (v : Validator n) (b : Block n) (t : Time) : Prop :=
  Alg1.isConfirmed (n := n) bal₀ fm cm pb we τ 𝒱 v b t

end FastConfirmation.HFC

end
