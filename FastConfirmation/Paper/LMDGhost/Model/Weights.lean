module
public import Mathlib.Order.Interval.Finset.Nat
public import FastConfirmation.Paper.Core.Model.View

@[expose] public section

/-!
# LMDGhost / Model / Weights

The Definition 5–7 weights, all **anchored** at an arbitrary balance source `A`
(the paper's checkpoint `C`; the engine stays anchor-generic so §4/HFC reuses it
verbatim) and parameterized by the per-slot committees. `W`/`S` are taken over the committee
*union* over the slot range `[psPlus1 b, s]` (matching the paper's `W̄`), so each
validator is counted once. `Q = S / W`, and `safetyThreshold` is the Definition 8
right-hand side, factored into a named def so the refined (Def 10 / PR #4747) predicate is a
**model-level** localized swap.

**Caveat:** the localization is at the *definition* layer only, **not** the
proof layer. The proofs unfold `safetyThreshold` and depend on its exact Def-8 shape —
e.g.
`Q_imp_H_majority` (`Proof/Quorum.lean`) rewrites `(½(1+Wp/W)+β)·W = (W+Wp)/2 + β·W` and cancels the
`+β` against the adversary bound `S_adv ≤ βW`, and `P_base_of_Q` carries the `1/(2(1−β))` factor. So
adding the Def-10 `ρ/π/ϵ` or PR-#4747 `support_discount`/`adversarial_weight` terms would change the
target margin and require re-deriving those lemmas; it is **not** a proof-free swap. (Out of scope
here; see `docs/source-notes.md` and `docs/paper-model-design.md`.)
-/

namespace FastConfirmation.LMDGhost

variable {n : ℕ} {P : Type}

/-- Union of committees over slots `[lo, hi]`. -/
def committeeUnion (cm : Committees n) (lo hi : Slot) : Finset (Validator n) :=
  (Finset.Icc lo hi).biUnion cm.member

/-- `W_b`: committee-union weight over `[psPlus1 b, s]`, at anchor `A`. -/
def W (A : Anchor n) (cm : Committees n) (b : Block n) (s : Slot) : Weight :=
  totalWeight A (committeeUnion cm b.psPlus1 s)

/-- `S_b`: anchor-weight of committee-union validators whose effective vote (up to
    slot `s`) supports `b`. -/
noncomputable def S (A : Anchor n) (cm : Committees n) (V : View n P) (b : Block n) (s : Slot) :
    Weight :=
  totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i => V.supportsLMD b i s = true))

/-- `Q_b = S_b / W_b`. -/
noncomputable def Q (A : Anchor n) (cm : Committees n) (V : View n P) (b : Block n) (s : Slot) :
    Weight :=
  S A cm V b s / W A cm b s

/-- `J_b`: honest part of `W_b` (honest committee-union weight). -/
def J (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (b : Block n) (s : Slot) : Weight :=
  totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i => i ∈ fm.honest))

/-- `H_b`: honest part of `S_b` (honest supporters of `b`). -/
noncomputable def H (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b : Block n) (s : Slot) : Weight :=
  totalWeight A ((committeeUnion cm b.psPlus1 s).filter
    (fun i => i ∈ fm.honest ∧ V.supportsLMD b i s = true))

/-- `P_b = H_b / J_b`, the honest LMD-GHOST safety indicator (Def 7).
    Named `Phon` to avoid clashing with the payload type variable `P`. -/
noncomputable def Phon (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (V : View n P)
    (b : Block n) (s : Slot) : Weight :=
  H A cm fm V b s / J A cm fm b s

/-- `W_p^C = pb · W_t^C`, proposer boost as a fraction of total validator-set weight. -/
def Wp (A : Anchor n) (pb : Weight) : Weight := pb * totalWeight A Finset.univ

/-- Definition 8 single-block threshold: `½(1 + W_p/W_b) + β`. -/
def safetyThreshold (A : Anchor n) (cm : Committees n) (fm : FaultModel n) (pb : Weight)
    (b : Block n) (s : Slot) : Weight :=
  (1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β

end FastConfirmation.LMDGhost

end
