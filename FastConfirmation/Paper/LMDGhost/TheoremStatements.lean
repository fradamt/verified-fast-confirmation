module
public import FastConfirmation.Paper.Core.Model
public import FastConfirmation.Paper.LMDGhost.Model

@[expose] public section

/-!
# LMDGhost / TheoremStatements

The public, proof-free §3.1 surface — the claims checked against arXiv:2405.00549 §3.

The hypotheses of each theorem fall into three deliberately-separated categories:

* **Honest behavior** (`HonestBehavior`) — *definitional* honest protocol (vote your
  fork-choice head, in-committee, no equivocation). Not an environmental assumption.
* **Network model** (`Synchrony`) — monotone views, post-GST vote delivery, block gossip.
* **Economic assumptions** — `CommitteeHonestMajority` (Assumption 2), `StaticBalances`
  (Assumption 1), `WellFormedBoost` (the proposer boost attaches to the current slot),
  and, for monotonicity, the tighter `β < (1 - pb)/4` (Assumption 4) plus the full-epoch
  committee-coverage corollary `CommitteeCoversEpoch`.

Results:

* `Theorem1_Safety` / `Theorem1_Monotonicity` — Algorithm 4 under `sg` is a Confirmation
  Rule for plain LMD-GHOST (Definition 4, `trivialFilter`).
* `HeadFutureAgreement` — the **reusable engine** (≈ Lemma 6): filter-generic and
  arbitrary-anchor, so the §4 HFC layer reuses it at `flt := ffgFilter`.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- Every ancestor of `b` stays eligible (unfiltered) in every honest view from
    `st(slot(t))` onward. Trivial for `trivialFilter`. -/
def NeverFiltered (τ : Timing) (fm : FaultModel n) (flt : BlockFilter n P)
    (𝒱 : ViewFamily n P) (b : Block n) (t : Time) : Prop :=
  ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' →
    ∀ ⦃b' : Block n⦄, b' ≼ b → flt (𝒱 w t') t' b'

/-- **`NeverFiltered` in the joint-induction *functional* form** — the head-safety engine's
    `hNFilOfHead` antecedent, named. Filter-eligibility of every `b' ≼ b` at the cutoff slot
    `k` is granted *given head safety for `b` at all earlier honest views at slot boundaries
    `j < k`*. This is what lets the §4 never-filter argument consume head safety at the
    justifying voters' (strictly earlier) slots **inside the same well-founded recursion** —
    `NeverFiltered(k)` is a function of head-safety`(< k)`, never `head-safety(k)`, so no
    circularity. A static `NeverFiltered` is, in particular, of this shape (the head-safety
    antecedent is simply ignored — `neverFiltered_to_hNFilOfHead`); the §4 proof builds the
    genuinely functional form, deriving the realized-`GJ` descendant placement from the
    supplied head safety at the voters' earlier slots. -/
def NeverFilteredFromHead (τ : Timing) (fm : FaultModel n)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) (boost : ProposerBoost n P)
    (pb : Weight) (flt : BlockFilter n P)
    (𝒱 : ViewFamily n P) (b : Block n) (t : Time) : Prop :=
  ∀ ⦃k : Slot⦄, τ.slotOf t ≤ k →
    (∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < k → ∀ ⦃i' : Validator n⦄, i' ∈ fm.honest →
      b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j)) →
    ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.slotOf t' = k →
      τ.st (τ.slotOf t) ≤ t' → ∀ ⦃b' : Block n⦄, b' ≼ b → flt (𝒱 w t') t' b'

/-- **Reusable engine (≈ Lemma 6).** Filter-generic, arbitrary-anchor head safety and
    future agreement: a block safe in some honest view at `t` is, from `st(slot(t))` on,
    on every honest validator's filtered LMD-GHOST head. The §4 HFC layer reuses this at
    `flt := ffgFilter`.

    Hypotheses beyond the network/economic core are **faithful well-formedness / honesty
    premises** mapping to the paper:

    * `HonestNoForgery` — honest votes are unforgeable (signature unforgeability for
      honest signers); lets honest-attributed votes transfer across honest views.
    * `ViewsValid` — every vote is from a committee member of its slot for a not-greater-slot
      well-formed block (`FIL_¬valid`); reconciles fork-choice support with committee weight.
    * `AnchorsCoincide` — the §3.1 specialization of Lemma 6 hyp (4): every honest
      voter's `gj`-anchor coincides with `C`.
    * `b.WellFormed`, `b.slot ≤ slot(t)`, `1 ≤ slot(t)` — the confirmed block is a
      well-formed block of a past, post-genesis slot.
    * `AfterGST(st(slot(t) - 1))` — `gst` precedes the slot **before** the safe slot
      `slot(t)` (not `st(slot(t))`): the base supporters voted by slot `slot(t)-1`, and the
      faithful `honestVoteUbiq` (delivery gated on the *circulating* slot being post-`gst`)
      delivers their votes to every honest view by `st(slot(t))` only once slot `slot(t)-1`
      is post-`gst`. `Theorem1_Safety`/`_Monotonicity` supply this from `sg` for free
      (Algorithm 4 evaluates from the *second* slot of the epoch, giving the one-slot margin).

    The recurrence-robust honest LMD-GHOST safety indicator `P = H/J` (Def 7) is the
    maintained quantity (`P_nondecreasing` + `P_base_of_Q` + `Hmargin_of_P` internally);
    `CommitteeHonestMajority` (Assumption 2) is the **only** honest-fraction hypothesis;
    no per-slot honest-growth premise is used, because such a premise is neither a paper
    assumption nor implied by the others. -/
def HeadFutureAgreement (τ : Timing) (flt : BlockFilter n P) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {gj : ViewFamily n P → Validator n → Time → Anchor n} {boost : ProposerBoost n P}
    {𝒱 : ViewFamily n P} (C : Anchor n),
    Synchrony n P τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb flt 𝒱 →
    ViewsValid cm 𝒱 →
    CommitteeHonestMajority fm cm C →
    0 ≤ pb →
    AnchorsCoincide gj 𝒱 fm τ C →
    ∀ {v : Validator n} {b : Block n} {t : Time},
      v ∈ fm.honest → b.WellFormed → b.slot ≤ τ.slotOf t →
      1 ≤ τ.slotOf t → τ.AfterGST (τ.st (τ.slotOf t - 1)) →
      isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t →
      NeverFiltered τ fm flt 𝒱 b t →
      ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → τ.st (τ.slotOf t) ≤ t' →
        b ≼ forkChoiceHead τ C boost pb flt (𝒱 w t') t'

/-- **Theorem 1, Safety half** (Definition 4) for plain LMD-GHOST: a confirmed block
    is, from some time on, on every honest validator's LMD-GHOST head. -/
def Theorem1_Safety (τ : Timing)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight} {boost : ProposerBoost n P}
    {𝒱 : ViewFamily n P},
    Synchrony n P τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb trivialFilter 𝒱 →
    ViewsValid cm 𝒱 →
    (∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) →
    WellFormedBoost τ boost →
    0 ≤ pb →
    StaticBalances gj 𝒱 →
    ∀ {v : Validator n} {b : Block n} {t : Time},
      v ∈ fm.honest → sg τ b t → isConfirmed τ fm cm pb gj 𝒱 v b t →
        ∃ t0 : Time, ∀ ⦃w : Validator n⦄ ⦃t' : Time⦄, w ∈ fm.honest → t0 ≤ t' →
          b ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb trivialFilter (𝒱 w t') t'

/-- **Theorem 1, Monotonicity half** (Definition 4): once confirmed, always confirmed.
    Needs the tighter **Assumption 4**, `β < ¼(1 - pb)` (paper `assum:beta-lmd-monotonicity`,
    `β < ¼(1 - p/E)`). The denominator `4` is necessary: the proof uses
    `1 - 2β > ½(1 + pb)`, equivalently `β < (1 - pb)/4`; a denominator of `2`
    would even admit `β > 1/3`.

    One further premise beyond Safety's bundle, faithful:

    * `CommitteeCoversEpoch` (Assumption-1 corollary): over a full epoch the committee
      union is the whole validator set, so `W_{b'}^{slot(t')-1} = totalWeight univ` and
      `Wp / W_{b'} = pb`. This pins the later-epoch safety threshold to `½(1 + pb) + β`,
      which Assumption 4 then dominates (paper Lemma 8). -/
def Theorem1_Monotonicity (τ : Timing)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) : Prop :=
  ∀ {fm : FaultModel n} {cm : Committees n} {pb : Weight} {boost : ProposerBoost n P}
    {𝒱 : ViewFamily n P},
    Synchrony n P τ fm 𝒱 →
    HonestNoForgery fm τ 𝒱 →
    HonestBehavior τ fm cm gj boost pb trivialFilter 𝒱 →
    ViewsValid cm 𝒱 →
    (∀ ⦃w : Validator n⦄ ⦃t : Time⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) →
    WellFormedBoost τ boost →
    0 ≤ pb →
    StaticBalances gj 𝒱 →
    fm.β < (1 - pb) / 4 →
    ∀ {v : Validator n} {b : Block n} {t t' : Time},
      v ∈ fm.honest → sg τ b t → t ≤ t' →
      CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1) →
      isConfirmed τ fm cm pb gj 𝒱 v b t → isConfirmed τ fm cm pb gj 𝒱 v b t'

end FastConfirmation.LMDGhost

end
