import FastConfirmation.Paper.Core.Model.Filter

/-!
# Core / Model / ForkChoice

The LMD-GHOST head function, parameterized by an eligibility `BlockFilter` and a
time-dependent `ProposerBoost`. Implemented as a fuel-bounded GHOST traversal:
from genesis, repeatedly move to the heaviest filter-eligible child of slot
`≤ slot(t)`, where a child's weight is the anchor-weight of validators whose
latest vote supports its subtree, plus the proposer boost if the boosted block
lies in that subtree. Ties are broken by `List.argmax`'s (deterministic) order;
Definition 8's strict inequality ensures the safe path never relies on it.

This layer is `noncomputable` (it rests on the LMD `latestVote`), which is fine:
the model states the rule without implementing an execution engine.
-/

namespace FastConfirmation

variable {n : ℕ} {P : Type}

/-- Proposer boost: the (optional) current-slot block that receives the boost. -/
structure ProposerBoost (n : ℕ) (P : Type) where
  proposalAt : View n P → Time → Option (Block n)

/-- Anchor-weight of validators whose effective vote (slot `≤ upTo`) in `V` supports `c`. -/
noncomputable def latestSupportWeight (A : Anchor n) (V : View n P) (upTo : Slot) (c : Block n) :
    Weight :=
  totalWeight A (Finset.univ.filter (fun i => V.supportsLMD c i upTo = true))

/-- Proposer-boost contribution to child `c`: the boost weight if the boosted
    block lies in `c`'s subtree, else `0`. -/
noncomputable def boostWeight (A : Anchor n) (boost : ProposerBoost n P) (pb : Weight)
    (V : View n P) (t : Time) (c : Block n) : Weight :=
  match boost.proposalAt V t with
  | some bp => if c.isAncestorOf bp = true then pb * totalWeight A Finset.univ else 0
  | none => 0

/-- GHOST weight of candidate child `c` (votes counted up to slot `upTo`). -/
noncomputable def childWeight (A : Anchor n) (boost : ProposerBoost n P) (pb : Weight)
    (V : View n P) (t : Time) (upTo : Slot) (c : Block n) : Weight :=
  latestSupportWeight A V upTo c + boostWeight A boost pb V t c

open Classical in
/-- Filter-eligible children of `b` in `V`: child of `b`, well-formed (`FIL_¬valid`,
    slot strictly above parent), slot `≤ slot(t)` (`FIL_cur` on blocks), and `flt`-eligible.
    The arbitrary `Prop`-valued conjuncts are made decidable classically (noncomputable layer). -/
noncomputable def eligibleChildren (τ : Timing) (flt : BlockFilter n P)
    (V : View n P) (t : Time) (b : Block n) : Finset (Block n) :=
  V.blocks.filter
    (fun b' => b'.parent? = some b ∧ b'.WellFormed ∧ b'.slot ≤ τ.slotOf t ∧ flt V t b')

/-- One GHOST step: the heaviest eligible child, or `none` if there is none.
    Votes are counted up to `slot(t) - 1` (`FIL_cur`). -/
noncomputable def ghostStep (τ : Timing) (A : Anchor n) (boost : ProposerBoost n P)
    (pb : Weight) (flt : BlockFilter n P) (V : View n P) (t : Time) (b : Block n) :
    Option (Block n) :=
  (eligibleChildren τ flt V t b).toList.argmax (childWeight A boost pb V t (τ.slotOf t - 1))

/-- Fuel-bounded GHOST traversal. -/
noncomputable def ghostAux (τ : Timing) (A : Anchor n) (boost : ProposerBoost n P)
    (pb : Weight) (flt : BlockFilter n P) (V : View n P) (t : Time) :
    ℕ → Block n → Block n
  | 0, b => b
  | fuel + 1, b =>
    match ghostStep τ A boost pb flt V t b with
    | some best => ghostAux τ A boost pb flt V t fuel best
    | none => b

/-- The LMD-GHOST head in view `V` at time `t`. Slots strictly increase along
    children, so `slot(t) + 1` fuel suffices to exhaust any eligible path. -/
noncomputable def forkChoiceHead (τ : Timing) (A : Anchor n) (boost : ProposerBoost n P)
    (pb : Weight) (flt : BlockFilter n P) (V : View n P) (t : Time) : Block n :=
  ghostAux τ A boost pb flt V t (τ.slotOf t + 1) Block.genesis

/-- The proposer boost may attach only to the **current proposal received in a timely manner**
    (arXiv:2405.00549, proposer-boost description l.527): the boosted block, when present, is a
    **well-formed block in the view** (`bp ∈ V.blocks ∧ bp.WellFormed` — a real, received proposal)
    proposed in the **current slot** (`bp.slot = slotOf t`). So the boost adds at most `W_p` to one
    current-slot branch — the margin Def 8 budgets. (The `bp ∈ V.blocks`/`WellFormed` conjuncts make
    the boost faithful to the paper's timely-current-proposal; the safety proof bounds the boost
    structurally via `boostWeight_le_Wp` and does not consume them, so the result also holds for
    arbitrary boost placement — they tighten the *model* to match the paper, not the proof.) -/
def WellFormedBoost (τ : Timing) (boost : ProposerBoost n P) : Prop :=
  ∀ (V : View n P) (t : Time) (bp : Block n),
    boost.proposalAt V t = some bp → bp.slot = τ.slotOf t ∧ bp ∈ V.blocks ∧ bp.WellFormed

end FastConfirmation
