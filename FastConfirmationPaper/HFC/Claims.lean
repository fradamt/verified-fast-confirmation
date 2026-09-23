module
public import FastConfirmationPaper.LMDGhost.Claims
public import FastConfirmationPaper.HFC.Model

@[expose] public section

/-!
# HFC / TheoremStatements

The public, proof-free §4 surface — the claims checked against arXiv:2405.00549 §4
and the explainer (Kalinin/Saltini/Zanolini). Every result structurally mirrors a
§3.1 statement at `P := FFGVote n`, `flt := ffgFilter C τ`, reusing the
filter-generic engine `HeadAgreementAfterConfirmation`
(`FastConfirmation/Paper/LMDGhost/TheoremStatements.lean`). The proved module
facade is `FastConfirmation.Paper.HFC.ProvenTheorems`.

Results:

* **`RuleConfirmedBlockSafety` / `RuleConfirmedBlockMonotonicity`** — the primary §4 theorems. Same
  conclusion as the Theorem-1 analogues, but the confirmation hypothesis is the
  HFC Algorithm-1 wrapper `isConfirmedAlg1`, whose selector ranges over the paper-shaped local rule
  `isConfirmedNoCaching` (both the current-epoch and previous-epoch branches; `vs` is represented
  by the AU-based `ruleVotingSource` / `ruleGJBlock` selectors over block-contained votes), with
  the semantic gate
  `WillNoConflictingChkpBeJustified` **eliminated** in favor of the rule's own checks
  plus the explicit `Alg1SelectorSafetyInterface`, `Alg1SafetyInterface`, and
  `SafeConfirmedAlg1Inputs` bundles, which expose the AU, `P-link`, committee-partition,
  realization, and selector-slot premises used by the proofs.
  See `docs/algorithm1-gate-discharge.md`.
* `GateConfirmedBlockSafety` / `GateConfirmedBlockMonotonicity` — the gate-based §4 confirmation-rule theorems (the
  analogue of Theorem 1), at `flt := ffgFilter`, stated over the combined predicate
  `isHFCConfirmed` (LMD-safe + the *semantic* gate). The `_Alg1` pair states the
  Algorithm-1 result directly.
* `WillNoConflictingChkpBeJustified` — the *semantic* FFG confirmation gate (explainer
  Algorithm 1, line 15-16): no checkpoint conflicting with `C(b)` will ever be
  justified in any honest view. Used only by the gate-based pair.
* `ConfirmedNotFFGFiltered` — the genuinely new §4 obligation, *stated*:
  FFG-confirmed ⇒ `NeverFiltered` at `ffgFilter`, by the inductive cross-epoch argument.
* `Assumption3` — the §4 FFG-behavior assumption (explainer p.2 / arXiv Assumption 5.3):
  honest FFG votes are not blocked from inclusion for an entire epoch.
* `FFG_AccountableSafety` — the underlying FFG-Casper guarantee (arXiv §2.2.1),
  represented as an explicit premise: no two conflicting checkpoints are both finalized.
  The weight-only model omits the slashing evidence needed to derive this guarantee.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **Assumption 3** (the new §4 FFG-behavior assumption; explainer p.2).

    **Numbering caveat:** this is the *explainer's* "Assumption 3". In arXiv:2405.00549 the
    same FFG-inclusion property is **Assumption 5.3**; the arXiv "Assumption 3" is a different,
    unrelated statement (no validator gets slashed). The Lean name follows the explainer, not
    the arXiv numbering — read `Assumption3` as arXiv Assumption 5.3.

    (3.1) `β < 1/3` — already carried by `FaultModel.hβ`, so not restated here.

    (3.2) "Byzantine validators cannot block honest FFG votes from inclusion in
    canonical blocks for an entire epoch." Modeled, in the spirit of `honestVoteUbiq`
    for GHOST votes, as: an honest committee member's FFG vote (riding in `extra`) cast
    in a slot `≤ s'` is, by the next boundary `st(s'+1)`, present in *every* honest view —
    once **slot `s'` itself** is past `gst` (the same faithful Δ-delivery gate as
    `honestVoteUbiq`; gating on `st(s'+1) ≥ gst` would be unsound). So honest FFG votes
    are never blocked from inclusion.

    **Scope:** this is not a premise of the public §4 theorems. The
    `willChkpBeJustified` certificate route (`Certificate.lean`) discharges justification from a
    validator's *local* observed link weight, which needs no FFG-inclusion assumption; this
    assumption is used by the alternative theorem `checkpoint_justified_of_canonical`
    (`Formation.lean`). -/
def Assumption3 (τ : Timing) (fm : FaultModel n) (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  ∀ ⦃w : Validator n⦄, w ∈ fm.honest →
    ∀ ⦃m : Message n (FFGVote n)⦄ ⦃s' : Slot⦄,
      HonestCast fm 𝒱 τ m → m.ghost.slot ≤ s' → τ.AfterGST (τ.st s') →
        m ∈ (𝒱 w (τ.st (s' + 1))).msgs

/-- Agreement between the paper-facing AU filter selectors and the view-realized proof selectors at
    one view/time. This is the explicit bridge discharged by the block-contained-vote/gossip
    interface: once the AU votes carried on known chains are visible in the view, the paper
    `GJ(V,t) = max{vs(b,t)}` / `GF(V,t)` selectors coincide with the corresponding view-realized
    proof selectors, and AU `vs(b,t)` coincides with the view-realized chain source for known
    non-future blocks. -/
def FilterSelectorAgreementAt (C : Anchor n) (τ : Timing) (V : View n (FFGVote n))
    (t : Time) : Prop :=
  ruleRealizedGJ C τ V t = greatestRealizedJustified C τ V t ∧
  ruleRealizedGF C τ V t = greatestFinalized C V ∧
  ∀ ⦃b : Block n⦄, b ∈ V.blocks → b.slot ≤ τ.slotOf t →
    ruleVotingSource C τ b t = votingSource C τ V b t

/-- **The §4 honest-view GU-anchor inputs at `b`** — a decomposed interface following the
    paper's argument (Algorithm 1 lines 21–22: the confirmation re-roots each epoch at the *previous*
    epoch's greatest *unrealized* justified checkpoint `GU_conf`). In every honest view at every
    `t' ≥ st(slot(t))` it carries the faithful facts the never-filter argument *derives* the
    `block(GJ)` placement from (rather than assuming the ancestry outright):

    * **GU recency + root** — a justified checkpoint `GUc` of epoch exactly `epoch(b) − 1`
      whose block is an ancestor of `b` (`GUc.block ≼ b`). This is the GU anchor the confirmed
      `b` descends from (Alg 1 l.21–22), read in `w`'s view at `t'` (justification recurs, so the
      confirmation-time GU stays justified — `Justified_mono_time`). It gives the **lower bound**
      `epoch(b) − 1 ≤ epoch(GJ)` (via `greatestRealizedJustified_max`), and the never-filter
      combines it with `FFG_AccountableSafety`'s justified-uniqueness-per-epoch in the case
      `epoch(GJ) < epoch(b)` to force `GJ = GUc`, hence `block(GJ) = GUc.block ≼ b`. **No honest
      head agreement above `b` is needed**: this avoids the `HonestEpochLinkDelivered` route,
      which would justify a fresh checkpoint above `b` and require a canonical leaf.
    * **No GU-root slot bound is required.** In the lower-or-equal-epoch case
      `epoch(b) ≤ epoch(GJ_real) ≤ epochOf s` the gate
      (J2/D3, `greatestRealizedJustified_on_chain`) supplies only the *compatibility*
      `block(GJ_real) ~ B`, and the never-filter **case-splits on its direction** instead of pinning
      one with a slot bound: the `B ≼ block(GJ_real)` branch keeps every ancestor `B' ≼ B ≼
      block(GJ_real)` *directly* by the first `ffgFilter` disjunct (`B' ≼ block(GJ_real)` —
      no recency, no gate beyond the compatibility), and the `block(GJ_real) ≼ B` branch is the
      D1/D2 comparability-split logic. So both directions keep the block without selecting one
      direction by a slot comparison. (The descendant case `epoch(GJ_real) >
      epochOf s` uses no slot bound via the cross-epoch ladder; the `epoch(GJ_real) <
      epoch(b)` sub-band uses the GU-recency/uniqueness route, also slot-bound-free.)
    * **finalized realization** — `epoch(GF) < epochOf(slotOf t')`, i.e. the greatest *finalized*
      checkpoint is *realized* (its epoch is strictly below the running epoch). In the protocol the
      greatest finalized always lags the current epoch; in the weight-only model this realization is
      not derivable (the same gap as the realized-`GJ` `epochOf ≥ 1` side-condition), so it is
      carried as a faithful realization invariant. It lets the realized **D1**
      (`greatestFinalized_block_ancestor_greatestRealizedJustified`) place
      `block(GF) ≼ block(GJ_real)` (`greatestRealizedJustified_max` dominates the realized `GF` in
      epoch, then `FinalizedPrefixOfJustified`), so the D2 leaf's finalized-descent condition reads
      against the realized `GJ` block.
    * **selector agreement** — the paper-facing AU filter selectors
      `ruleRealizedGJ`/`ruleRealizedGF`/`ruleVotingSource` agree with the view-realized proof
      selectors at honest views. This is the explicit block-contained-vote visibility bridge, not a
      silent definitional identification.

    Unlike `FFGAnchorsBelowConfirmed`, this never asserts the ancestry `block(GJ) ≼ b` directly —
    the gate + the GU-recency/uniqueness argument do that work. The carried facts are the honest
    §4 GU-rootedness invariants of the confirmation rule (Algorithm 1). Their
    derivation from confirmation and fork-choice dynamics is represented by
    this explicit interface premise.

    **Slot bound:** the GU-root slot bound `block(GJ_real).slot ≤ b.slot` is unnecessary because
    the comparability case-split in the never-filter covers both directions,
    matching the paper: the gate's compatibility is enough, and the proof need not select the
    `block(GJ_real) ≼ b` direction. -/
def GreatestJustifiedAnchorInputs (C : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' →
    (∃ GUc : Checkpoint n, Justified C (𝒱 w t') GUc ∧
        GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b) ∧
      (greatestFinalized C (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
      FilterSelectorAgreementAt C τ (𝒱 w t') t'

/-- The **FFG confirmation gate** (explainer Algorithm 1, line 15-16,
    `willNoConflictingChkpBeJustified`): no checkpoint conflicting with the block's
    latest checkpoint will ever be justified in any honest view from `st(slot(t))`
    on. Modeled at the §4 anchor `C`: for every honest validator `w` and every time
    `t' ≥ st(slot(t))`, every checkpoint `Cc` justified in `w`'s view at `t'` whose
    epoch is at least `epoch(b)` has its block compatible (`~`) with `b` — i.e. no
    *conflicting* checkpoint becomes justified. -/
def WillNoConflictingChkpBeJustified (C : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' →
    ∀ ⦃Cc : Checkpoint n⦄, Justified C (𝒱 w t') Cc →
      τ.epochOf b.slot ≤ Cc.epoch → (b ~ Cc.block)

/-- **The confirmation rule's GU-anchor precondition** (arXiv:2405.00549 Algorithm 1, l.21–22 /
    `ln:ffg:gjblock-from-previous-epoch`, l.2349). For `b` to be confirmed, the greatest justified
    checkpoint on `chain(b)` is at epoch exactly `epoch(b)−1`, justified in an honest view at `t`.
    A *local* check the rule performs — part of what "confirmed" means — not an environmental
    assumption. -/
def GreatestJustifiedAnchorPrecondition (C : Anchor n) (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n (FFGVote n)) (b : Block n) (t : Time) : Prop :=
  ∃ GUc : Checkpoint n, GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b ∧
    ∃ v, v ∈ fm.honest ∧ Justified C (𝒱 v t) GUc

/-- **Safe-block FFG-soundness inputs** (the §4-monotonicity companion to
    `GreatestJustifiedAnchorInputs`, in decomposed form). Every block `X` that is
    `isLMDGHOSTSafe` in an honest view at
    `t'` satisfies the §4 confirmation-soundness conditions: the conflict-exclusion gate
    `WillNoConflictingChkpBeJustified … X t'` (no checkpoint conflicting with `C(X)` ever
    becomes justified in an honest view) **and** the GU-anchor inputs
    `GreatestJustifiedAnchorInputs … X t'` (the J1 GU recency+root and the realized-GJ/GF
    well-formedness/realization facts — *not* the ancestry, which the gate derives via J2/D3,
    and *no* GU-root slot bound, because the comparability case-split covers both directions).

    This is what makes monotonicity's *later* highest-confirmed block `B''` never-filtered: the
    §4 never-filter argument (`confirmedNotFFGFiltered_proved`) is applied at `b := X` for each
    safe candidate `X`, so it must be fed the gate + GU-anchor inputs for `X`. They are exactly
    the §4 confirmation gate / fork-choice-rootedness conditions, recorded as holding for *any*
    honest-view-safe block (a faithful behavioral invariant parameterized by explicit
    AU-style block vote contents; see `docs/ffg-delivery-abstraction.md`). Like
    `GreatestJustifiedAnchorInputs`, this interface records the required fork-choice and FFG
    dynamics as an explicit premise of `GateConfirmedBlockMonotonicity`.

    The D2 leaf voting-source recency disjunct follows structurally in the never-filter from the on-chain
    placement `block(GJ_real) ≼ B'` (D2) plus accountable-safety justified-uniqueness and the
    realization lemmas, with **no recency/liveness assumption**. -/
def SafeGreatestJustifiedAnchorInputs (τ : Timing) (fm : FaultModel n) (cm : Committees n)
    (pb : Weight) (C : Anchor n) (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄ ⦃X : Block n⦄,
    isLMDGHOSTSafe τ fm cm pb C (𝒱 w t') X t' →
      WillNoConflictingChkpBeJustified C fm τ 𝒱 X t' ∧
        OnChainAnchorWellFormed C τ X ∧
        GreatestJustifiedAnchorInputs C fm τ 𝒱 X t'

/-- **The HFC (§4) confirmation predicate** — the paper's HFC confirmation rule as a single
    object (Definition 4): `b` is HFC-confirmed by honest `v` at `t` when it is
    LMD-GHOST-confirmed (Algorithm 4, `isConfirmed`) **and** the FFG gate holds (no checkpoint
    conflicting with `b` will ever be justified in an honest view). `GateConfirmedBlockSafety` /
    `GateConfirmedBlockMonotonicity` are stated on this combined predicate, mirroring Definition 4.

    The gate is the **semantic** invariant `WillNoConflictingChkpBeJustified` (no checkpoint
    conflicting with `C(b)` is ever justified in any honest view), *not* the validator's local
    weight reservation at Algorithm 1 line 16 (the FFG-target `≥ 2/3` check an honest validator
    computes from its own view); the bridge from that local weight reservation to this semantic
    honest-view invariant is FFG accountable safety, represented by the explicit
    `FFG_AccountableSafety` premise of `GateConfirmedBlockSafety`. We
    take the gate semantically so the never-filter argument consumes the honest-view invariant
    directly. -/
def isHFCConfirmed (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (gj : ViewFamily n (FFGVote n) → Validator n → Time → Anchor n) (C : Anchor n)
    (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n) (b : Block n) (t : Time) : Prop :=
  isConfirmed τ fm cm pb gj 𝒱 v b t ∧
    WillNoConflictingChkpBeJustified C fm τ 𝒱 b t

/-- **FFG accountable safety** (arXiv §2.2.1) — three consequences of
    the Casper `β < 1/3` + slashing argument used by §4. The paper cites these as
    fundamental properties ensured by Gasper rather than reproving them in §4. The clauses below are
    accountable-safety consequences in that family (clause 1 = the commented
    `prop:gasper-basic:finalization`; clause 2 = active
    `prop:gasper-basic:only-one-justified-per-epoch`, l.2536; clause 3 = the finalized-prefix
    consequence, a strengthening of the active `prop:gasper-basic:just-succ-finalization`, l.2538,
    that
    Casper's 2/3-link-intersection delivers). The three consequences §4 leans on:

    * **(finalized non-conflicting)** no two conflicting checkpoints are both finalized in an
      honest view of the active view family;
    * **(justified unique per epoch)** at most one block is justified at any single epoch in such an
      honest view: two justified checkpoints of the same epoch share the same block;
    * **(finalized prefix of justified)** in such an honest view, the greatest *finalized*
      checkpoint's block is an ancestor of every justified checkpoint of weakly-greater epoch — the
      finalized chain is a prefix of the justified chain.

    All three follow from the *same* underlying argument — a checkpoint becomes justified /
    finalized only via a `≥ ⅔` supermajority link, and (by `β < 1/3` honest non-equivocation)
    two distinct `≥ ⅔` link targets at one epoch would force an honest validator to sign two
    conflicting epoch-`e` votes, a slashable double-vote (`2/3 + 2/3 - β > 1`); the
    finalized-prefix property is the 2/3-link-intersection chaining of that same argument
    across epochs (a finalized checkpoint's two-thirds support pins every weakly-later
    justified checkpoint onto its chain). The premise is intentionally scoped to honest views in
    the active view family; it is not an impossible claim about every syntactically constructible
    `View`. The model's weight-only `Justified` / `Finalized`
    predicates cannot see the per-validator no-double-vote / slashing discipline (FFG votes
    are opaque `extra` payloads, and the honest FFG discipline (`HonestFFGNoEquivocation`)
    constrains only honest validators' *own* casts — it says nothing about adversarial votes, and a
    validator spanning several epoch-`e` slots may legitimately re-target as its head moves), so
    none of the three clauses is derivable from the weight-only model. They require the Casper
    slashing-evidence and 2/3-link-intersection argument, so `FFG_AccountableSafety` is an explicit
    premise of `ConfirmedNotFFGFiltered`, `GateConfirmedBlockSafety`, and `GateConfirmedBlockMonotonicity`. The
    justified-uniqueness clause is what the never-filter consumes via
    `greatestRealizedJustified_on_chain` (the GU-recency case) to pin `block(GJ_real)` to the
    previous-epoch GU anchor without honest head agreement; the finalized-prefix clause discharges
    **D1** (`greatestFinalized_block_ancestor_greatestRealizedJustified`), incorporating the
    `FinalizedPrefixOfJustified` per-view property — it is the same cited
    accountable-safety bundle, so no new top-level assumption is introduced. -/
def FFG_AccountableSafety (A : Anchor n) (fm : FaultModel n)
    (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  (∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
    Finalized A (𝒱 w t) C₁ → Finalized A (𝒱 w t) C₂ → (C₁.block ~ C₂.block)) ∧
  (∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
    Justified A (𝒱 w t) C₁ → Justified A (𝒱 w t) C₂ → C₁.epoch = C₂.epoch →
      C₁.block = C₂.block) ∧
  (∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄,
    FinalizedPrefixOfJustified A (𝒱 w t))

/-- **The §4 obligation:** FFG-confirmed ⇒ `NeverFiltered` at `ffgFilter`.
    The proof uses `CommitteeHonestMajority`, the finalized-prefix
    clause of `FFG_AccountableSafety` (D1), and — per safe descendant `B` at its safe time
    `st s` — the gate `WillNoConflictingChkpBeJustified … B (st s)`, the epoch cover, and the
    GU-anchor inputs `GreatestJustifiedAnchorInputs … B (st s)`. **The conclusion is the
    joint-induction functional form `NeverFilteredFromHead`** (the head-safety engine's
    `hNFilOfHead` antecedent), so the never-filter at cutoff slot `k` may consume §3.1 head safety
    for `B` at all *earlier* honest views (slot boundaries `j < k`) — supplied by the engine's
    own strong induction, never circular.

    **R3 — the realized-GJ placement is split on the realized `GJ`'s epoch vs `epochOf(slot s)`:**
    * **`epoch(GJ_real) > epochOf s`** (the bulk): the realized `GJ` *descends from* `B`,
      `B ≼ block(GJ_real)`, derived by the §4 RECENCY descendant lemma of the cross-epoch ladder
      (`realizedGJ_descends_of_canonicalEpoch`, `CrossEpoch.lean`). Its justifying link's honest
      voter
      (extracted by `β < 1/3` from the global Byzantine bound `hByz`, with `HonestNoForgery` +
      `HonestFFGNoEquivocation` pinning its target to its head's checkpoint) voted at a slot whose
      epoch is `epoch(GJ_real) > epochOf s`, hence *no earlier than* `B`'s safe time `st s` and
      *strictly before* `k` (realization) — so the engine's head-safety antecedent `hHead` applies
      at exactly that slot. Then `B' ≼ B ≼ block(GJ_real)` keeps `B'` by the *first* `ffgFilter`
      disjunct. **No gate, no slot bound, no recency** in this case.
    * **`epoch(GJ_real) ≤ epochOf s`** (the lower-or-equal-epoch case, **slot-bound-free**): the
      gate (J2/D3, `greatestRealizedJustified_on_chain`, in its comparability form) yields only the
      *compatibility* `block(GJ_real) ~ B`, and the never-filter **case-splits on its direction**:
      - `B ≼ block(GJ_real)`: every ancestor `B' ≼ B ≼ block(GJ_real)` is kept *directly* by the
        first `ffgFilter` disjunct — no gate beyond compatibility, no recency, **no slot bound**;
      - `block(GJ_real) ≼ B`: the existing D1/D2 comparability-split logic;
      plus, when `epoch(GJ_real) < epoch(B)`, the gate already returns the `block(GJ_real) ≼ B`
      direction via the GU-recency/uniqueness route. **No GU-root slot bound is needed**:
      compatibility is enough, and the proof need not select
      a direction. The per-safe-block gate / cover / anchor are supplied at the
      safe time `st s` so the gate's `t'`-bound `st(slotOf(st s)) ≤ t'` matches the functional
      quantifier — this is what lets the gate fire. The per-view
    `FinalizedPrefixOfJustified` property is supplied by `FFG_AccountableSafety.2.2` (the single cited
    accountable-safety bundle); chained with the greatest-finalized realization
    (`GreatestJustifiedAnchorInputs`), the realized **D1**
    (`greatestFinalized_block_ancestor_greatestRealizedJustified`) places
    `block(GF) ≼ block(GJ_real)`.
    The **D2 leaf existential** (a leaf with no eligible children, no later than the current
    epoch) is derived structurally by `view_leaf_witness`, a finite-block-tree leaf walk
    from any in-view block of slot `≤ slotOf t'`; no block-production assumption is used. The D2 leaf's **voting-source recency**
    disjunct is proven first for the view-realized proof source and then transported to the
    paper-facing AU `ruleVotingSource` by `FilterSelectorAgreementAt`; it follows structurally in the
    never-filter — the same-epoch case identifies `gjblock(b'') = gjC` (the realized GJ) by
    realized-max + uniqueness — from the placement `block(GJ_real) ≼ b''` + accountable-safety
    justified-uniqueness +
    realization (`votingSource_disjunct`), with **no recency/liveness assumption**, not per-leaf.
    `HonestFFGNoEquivocation` and the global Byzantine bound `hByz` are **consumed by the R3
    descendant case** (the honest-voter extraction + target-pinning of the realized `GJ`).

    **GST guard `AfterGST(st(s-1))`** (one slot before the safe slot `s`, not `st s`): the
    never-filter's base delivery (`chain_in_view`) puts the safe block's prefix into every
    honest view by `st s`, which under the faithful `honestVoteUbiq` (delivery gated on the
    *circulating* slot being post-`gst`) needs slot `s-1` post-`gst`. `GateConfirmedBlockSafety` /
    `GateConfirmedBlockMonotonicity` discharge it from `sg` for free: Algorithm 4's candidate range starts
    at the *second* slot of the epoch (`fslot e + 1 ≤ s`), so `fslot e ≤ s-1`, and `sg` gives
    `AfterGST(st(fslot e))`. -/
def ConfirmedNotFFGFiltered (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (boost : ProposerBoost n (FFGVote n))
    (C : Anchor n) (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n) (b : Block n) : Prop :=
  FFG_AccountableSafety C fm 𝒱 →
  HonestFFGNoEquivocation τ fm cm C boost pb 𝒱 →
  GlobalByzantineBound C fm →
  ∀ ⦃s : Slot⦄ ⦃B : Block n⦄, 1 ≤ s → τ.AfterGST (τ.st (s - 1)) → b ≼ B →
    isLMDGHOSTSafe τ fm cm pb C (𝒱 v (τ.st s)) B (τ.st s) →
    WillNoConflictingChkpBeJustified C fm τ 𝒱 B (τ.st s) →
    GreatestJustifiedAnchorInputs C fm τ 𝒱 B (τ.st s) →
    NeverFilteredFromHead τ fm (gjFFG C) boost pb (ffgFilter C τ) 𝒱 B (τ.st s)

/-- **§4 HFC Confirmation-Rule SAFETY** (the analogue of Theorem 1's safety half,
    arXiv §4.1/§4.3): an honest validator FFG-confirming `b` at `t` ⇒ from some time
    on, `b` is on every honest validator's **LMD-GHOST-HFC** head. Same shape as
    `ConfirmedBlockSafety`, with `flt := ffgFilter C τ`, `gj := gjFFG bal₀`, `C := bal₀`,
    and the extra `FFG_AccountableSafety` and the per-block FFG gate
    (carried in `isHFCConfirmed`). The D2 leaf existential is derived structurally, so no
    `EpochLeafWitness` premise is needed.

    `RuleConfirmedBlockSafety` removes the semantic gate
    `WillNoConflictingChkpBeJustified` by driving safety from `isConfirmedNoCaching`
    together with the explicit `Alg1SafetyInterface`; this definition records the
    corresponding gate-based form. -/
def GateConfirmedBlockSafety (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)},
    let gj := gjFFG bal₀
    let C  := bal₀
    Synchrony n (FFGVote n) τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb (ffgFilter C τ) 𝒱 →
    ViewsValid cm 𝒱 →
    (∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) →
    WellFormedBoost τ boost →
    0 ≤ pb →
    StaticBalances gj 𝒱 →
    FFG_AccountableSafety C fm 𝒱 →
    HonestFFGNoEquivocation τ fm cm C boost pb 𝒱 →
    GlobalByzantineBound C fm →
    SafeGreatestJustifiedAnchorInputs τ fm cm pb C 𝒱 →
    ∀ {v : Validator n} {b : Block n} {t : Time},
      v ∈ fm.honest → sg τ b t → isHFCConfirmed τ fm cm pb gj C 𝒱 v b t →
        ∃ t0 : Time, ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → t0 ≤ t' →
          b ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb (ffgFilter C τ) (𝒱 w t') t'

/-- **§4 HFC Confirmation-Rule MONOTONICITY** (the analogue of Theorem 1's
    monotonicity half, arXiv §4.2): once HFC-confirmed, always HFC-confirmed. Same shape as
    `ConfirmedBlockMonotonicity`, at `flt := ffgFilter C τ`, `gj := gjFFG bal₀`, `C := bal₀`, plus the
    FFG gate persisting (immediate: the gate `WillNoConflictingChkpBeJustified` is a future-closed
    `∀`-over-future-times invariant, so it carries to every `t' ≥ t` for free).

    **On the β-bound (faithful to Assumption 6.2).** The paper proves §4 HFC monotonicity
    (Theorem 2 / `lem:ffg-motonocity`, l.3849) under **Assumption 6.2**, `β < min(1/6, 1/3 − d)`
    (`d` = safety decay), where the `1/6` is forced by `honFFGratio(β) = (2/3 + β)/(1 − β) ≤ 1` (the
    **FFG-closure** constant — the honest FFG ratio that must vote to keep re-justifying the
    canonical
    checkpoint) and `1/3 − d` is the safety-decay bound (Assumption 5.1).

    The statement carries **`β < min(1/6, (1 − pb)/4)`**: the `1/6` is exactly Assumption 6.2's
    FFG-closure bound (matched verbatim); the `(1 − pb)/4` (Assumption 4, the LMD-GHOST monotonicity
    bound `¼(1 − p/E)`) stands in for the paper's `1/3 − d` — i.e. this Lean abstracts the safety
    decay `d` and instead requires the LMD-GHOST monotonicity bound the §3 canonical-epoch crux
    needs
    (`canonical_epoch_imp_safe_flt`, the `½(1+pb)+β < 1−β` step). Thus the **visible β-bound
    includes the `1/6` FFG-closure constant**; the proof extracts `(1−pb)/4` from the `min` for the LMD crux, and the
    FFG-closure strength is additionally supplied by `FFG_AccountableSafety` +
    `SafeGreatestJustifiedAnchorInputs` (the cited Gasper accountable-safety properties, which the
    paper also assumes — §2.2.1 l.2522). (Verified verbatim against arXiv:2405.00549v3;
    see `docs/source-notes.md`.)

    `RuleConfirmedBlockMonotonicity` removes the semantic gate by driving each
    `highestConfirmedSinceEpoch` block canonical from `isConfirmedNoCaching`
    via `SafeConfirmedAlg1Inputs`; this definition records the corresponding gate-based form. -/
def GateConfirmedBlockMonotonicity (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)},
    let gj := gjFFG bal₀
    let C  := bal₀
    Synchrony n (FFGVote n) τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb (ffgFilter C τ) 𝒱 →
    ViewsValid cm 𝒱 →
    (∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) →
    WellFormedBoost τ boost →
    0 ≤ pb →
    StaticBalances gj 𝒱 →
    fm.β < min (1 / 6) ((1 - pb) / 4) →
    FFG_AccountableSafety C fm 𝒱 →
    HonestFFGNoEquivocation τ fm cm C boost pb 𝒱 →
    GlobalByzantineBound C fm →
    SafeGreatestJustifiedAnchorInputs τ fm cm pb C 𝒱 →
    ∀ {v : Validator n} {b : Block n} {t t' : Time},
      v ∈ fm.honest → sg τ b t → t ≤ t' →
      CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1) →
      isHFCConfirmed τ fm cm pb gj C 𝒱 v b t → isHFCConfirmed τ fm cm pb gj C 𝒱 v b t'

/-- **The explicit per-confirmation interface for the Algorithm-1 safety theorem.** The facts
    the gate-free never-filter consumes for a single confirmation of `b` at `st s`, each a
    paper-cited Gasper/protocol property (none is the semantic gate).

    1. **block-contained AU votes** — the modeled on-chain vote surface is the chain-targeted
       payload carried by `Block.mkWithVotes`, interpreted by `blockContainedFFGVotes τ`, with each
       block carrying any finite number of FFG votes from its current or previous epoch. The
       chain-carried vote set is `chainIncludedFFGVotes (blockContainedFFGVotes τ) X`, and on-chain
       justification is represented by `OnChainJustifiedAtTransition`; validator equivocations for
       an epoch are ignored by `onChainFFGVotesForEpoch`.
    2. greatest-finalized **realization** plus selector agreement — the carried Gasper realization
       invariant (`greatestFinalized` epoch strictly below the running epoch) and
       `FilterSelectorAgreementAt`, which connects the AU filter selectors to the view-realized
       proof helpers.
    3. committee **partition** — Ethereum's per-epoch committee disjoint-union `⊔` (the paper's
       `⊔`),
       splitting the epoch committee at `slotOf(st s)`.
    4. **`P-link`** common source — all honest epoch-`epoch(b)` voters for `b` share the AU FFG
       source `vs(b, st s)` (Gasper `ldm-vote-for-b-is-ffg-vote-for-cb`, l.2544).

    The source-justification fact needed by the current-epoch certificate is derived from conjunct 1
    (`OnChainAnchorInterfacesForRule`): `ruleVotingSource(b, st s)` is AU-justified on `chain(b)`
    and visible to honest views by block availability/readability.

    Conjuncts 3–4 are consumed only by the **current-epoch** certificate; the previous-epoch
    branch uses the rule-targeted AU interface at the witness `b'` plus `SlotCommitteeMinority`
    (the realization bound is *proven*, not assumed — `justified_epoch_le_of_firstSlot`) and the
    rule's own witness recency (`isConfirmedNoCaching`). -/
def Alg1SafetyInterface (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (boost : ProposerBoost n (FFGVote n)) (bal₀ : Stakes n)
    (𝒱 : ViewFamily n (FFGVote n)) (_v : Validator n) (b : Block n) (s : Slot) : Prop :=
  OnChainAnchorInterfacesForRule bal₀ fm τ 𝒱 b (τ.st s) ∧
  (∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
    (greatestFinalized bal₀ (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
    FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') ∧
  Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf (τ.st s) - 1))
           (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf b.slot))) ∧
  (∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃sl : Slot⦄, τ.slotOf (τ.st s) ≤ sl →
    τ.epochOf sl = τ.epochOf b.slot → i ∈ cm.member sl →
    ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st sl)) boost pb
      (ffgFilter bal₀ τ) (𝒱 i (τ.st sl)) (τ.st sl)) (τ.st sl)
      = ruleVotingSource bal₀ τ b (τ.st s))

/-- The safety theorem's interface for the block selected by `highestConfirmedSinceEpochAlg1`.
    The selector ranges over slot-boundary views; this interface is therefore keyed by the actual
    witness slot `s'` at which the selected block satisfied `isConfirmedNoCaching`, not by the
    caller's later slot. -/
def Alg1SelectorSafetyInterface (τ : Timing) (fm : FaultModel n) (cm : Committees n)
    (pb we : Weight) (boost : ProposerBoost n (FFGVote n)) (bal₀ : Stakes n)
    (𝒱 : ViewFamily n (FFGVote n)) (v : Validator n) (b : Block n)
    (e : Epoch) (t : Time) : Prop :=
  ∀ ⦃s' : Slot⦄,
    s' ∈ Finset.Icc (τ.fslot e + 1) (τ.slotOf t) →
    b ∈ (𝒱 v (τ.st s')).blocks →
    isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v b (τ.st s') →
      τ.AfterGST (τ.st (s' - 1)) ∧
        Alg1SafetyInterface τ fm cm pb boost bal₀ 𝒱 v b s'

/-- **§4 HFC Confirmation-Rule SAFETY about the paper's ALGORITHM 1** (the gate eliminated). The
    public analogue of `GateConfirmedBlockSafety` whose confirmation hypothesis is the top-level HFC wrapper
    `isConfirmedAlg1`: its selector chooses the highest block satisfying the paper's local,
    computable rule `isConfirmedNoCaching`, and the public predicate confirms that block's
    ancestors. The semantic gate `WillNoConflictingChkpBeJustified` is gone; in its place are the
    selector witness's own local rule proof plus the explicit `Alg1SelectorSafetyInterface`.
    Its nested `Alg1SafetyInterface` is tied to explicit block-contained FFG vote payloads
    (`blockContainedFFGVotes τ`) through `OnChainAnchorInterfacesForRule`: AU interfaces for the
    selected block and the previous-slot witness blocks that Algorithm 1 can actually consume.

    Unlike `GateConfirmedBlockSafety`, the precondition is the rule's slot-boundary form (`1 ≤ s`, `b.slot ≤ s`,
    `AfterGST(st (s-1))`) rather than the semantic guard `sg` + `isHFCConfirmed`; `sg`'s GST/range
    content is discharged for free at the slot boundary (Algorithm 4's candidate range starts at the
    epoch's second slot — see `ConfirmedNotFFGFiltered`'s GST-guard note). -/
def RuleConfirmedBlockSafety (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)},
    let gj := gjFFG bal₀
    let C  := bal₀
    Synchrony n (FFGVote n) τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb (ffgFilter C τ) 𝒱 →
    ViewsValid cm 𝒱 →
    (∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) →
    0 ≤ pb →
    FFG_AccountableSafety C fm 𝒱 →
    HonestFFGNoEquivocation τ fm cm C boost pb 𝒱 →
    GlobalByzantineBound C fm →
    SlotCommitteeMinority fm cm C →
    ∀ {v : Validator n} {b : Block n} {s : Slot} {we : Weight},
      let B := highestConfirmedSinceEpochAlg1 C fm cm pb we τ 𝒱 v
        (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s)
      v ∈ fm.honest → 1 ≤ s → τ.AfterGST (τ.st (s - 1)) → b.WellFormed → b.slot ≤ s → 0 ≤ we →
      isConfirmedAlg1 C fm cm pb we τ 𝒱 v b (τ.st s) →
      Alg1SelectorSafetyInterface τ fm cm pb we boost C 𝒱 v B
        (τ.epochOf (τ.slotOf (τ.st s)) - 1) (τ.st s) →
        ∃ t0 : Time, ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → t0 ≤ t' →
          b ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb (ffgFilter C τ) (𝒱 w t') t'

/-- **The Algorithm-1 monotonicity input bundle** — for every honest `v` and safe block `X` at
    `st s`
    (`isLMDGHOSTSafe`), `X` is confirmed via the rule (`isConfirmedNoCaching`, either branch)
    together
    with the explicit `Alg1SafetyInterface` (block-contained AU vote contents, finalized
    realization, `P-link` common source, committee partition — exactly
    `Alg1SafetyInterface`'s conjuncts, here ranged over every honest-view-safe block). The
    Algorithm-1 analogue of
    `SafeGreatestJustifiedAnchorInputs` (which bundles the assumed gate per safe block); the
    current-epoch-only interface conjuncts are ignored by the previous-epoch fold; the AU side is
    represented by actual chain-targeted `Block.mkWithVotes` payloads through
    `blockContainedFFGVotes τ` and rule-targeted `OnChainAnchorInterfacesForRule`, with
    `SlotCommitteeMinority` threaded into `RuleConfirmedBlockMonotonicity`.

    Disclosure: this is stronger and more direct than paper Assumption 6's conditional-eventual
    FFG-closure premise. The Lean bundle packages that closure as a per-safe-block obligation:
    every honest-view-safe `X` must already satisfy rule confirmation together with
    the AU/visibility interfaces needed by the monotonicity fold. -/
def SafeConfirmedAlg1Inputs (τ : Timing) (fm : FaultModel n) (cm : Committees n) (pb : Weight)
    (we : Weight) (boost : ProposerBoost n (FFGVote n)) (bal₀ : Stakes n)
    (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃s : Slot⦄ ⦃X : Block n⦄,
    isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) X (τ.st s) →
      isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v X (τ.st s) ∧
      OnChainAnchorInterfacesForRule bal₀ fm τ 𝒱 X (τ.st s) ∧
      (∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' →
        (greatestFinalized bal₀ (𝒱 w t')).epoch < τ.epochOf (τ.slotOf t') ∧
        FilterSelectorAgreementAt bal₀ τ (𝒱 w t') t') ∧
      Disjoint (committeeUnion cm (τ.fslot (τ.epochOf X.slot)) (τ.slotOf (τ.st s) - 1))
               (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf X.slot))) ∧
      (∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃sl : Slot⦄, τ.slotOf (τ.st s) ≤ sl →
        τ.epochOf sl = τ.epochOf X.slot → i ∈ cm.member sl →
        ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st sl)) boost pb
          (ffgFilter bal₀ τ) (𝒱 i (τ.st sl)) (τ.st sl)) (τ.st sl)
          = ruleVotingSource bal₀ τ X (τ.st s))

/-- **§4 HFC Confirmation-Rule MONOTONICITY about the paper's ALGORITHM 1** (without the semantic gate).
    The public analogue of `GateConfirmedBlockMonotonicity` is stated over the HFC wrapper
    `isConfirmedAlg1`, not LMD-GHOST's imported `isConfirmed`: once `b` is Algorithm-1-confirmed
    at `t`, it stays Algorithm-1-confirmed at every `t' ≥ t`. The FFG soundness that keeps each
    Algorithm-1 `highestConfirmedSinceEpoch` block canonical is supplied by the rule + the
    explicit `SafeConfirmedAlg1Inputs` block-vote bundle, not the assumed
    `WillNoConflictingChkpBeJustified`. The
    β-bound is Assumption 6.2's FFG-closure `1/6` ⊓ the LMD-GHOST monotonicity bound `(1-pb)/4`
    (matched to `GateConfirmedBlockMonotonicity`). -/
def RuleConfirmedBlockMonotonicity (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)},
    let gj := gjFFG bal₀
    let C  := bal₀
    Synchrony n (FFGVote n) τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb (ffgFilter C τ) 𝒱 →
    ViewsValid cm 𝒱 →
    (∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) →
    0 ≤ pb →
    fm.β < min (1 / 6) ((1 - pb) / 4) →
    FFG_AccountableSafety C fm 𝒱 →
    HonestFFGNoEquivocation τ fm cm C boost pb 𝒱 →
    GlobalByzantineBound C fm →
    SlotCommitteeMinority fm cm C →
    0 ≤ we →
    SafeConfirmedAlg1Inputs τ fm cm pb we boost C 𝒱 →
    ∀ {v : Validator n} {b : Block n} {t t' : Time},
      v ∈ fm.honest → sg τ b t → t ≤ t' →
      CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1) →
      isConfirmedAlg1 C fm cm pb we τ 𝒱 v b t →
        isConfirmedAlg1 C fm cm pb we τ 𝒱 v b t'

end FastConfirmation.HFC

end
