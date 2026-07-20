import FastConfirmation.Paper.LMDGhost.Proof.ProvenTheorems

/-!
# LMDGhost / ProvenTheorems

Proved facade for the §3.1 LMD-GHOST confirmation-rule theorems. The proof-free
statements live in `LMDGhost.TheoremStatements`; the theorem constants below expose
only that each public statement has a proof, delegating the scripts to
`LMDGhost.Proof.ProvenTheorems` (and thence to `Proof/`).
-/

namespace FastConfirmation.LMDGhost

variable {n : ℕ} {P : Type}

/-- **Reusable engine (Lemma 6).** Filter-generic, arbitrary-anchor head safety and
    future agreement. -/
theorem HeadFutureAgreement_proved (τ : Timing) (flt : BlockFilter n P) :
    HeadFutureAgreement τ flt :=
  proof_HeadFutureAgreement τ flt

/-- **Theorem 1, Safety half** (Definition 4, Lemmas 7–8) for plain LMD-GHOST: a confirmed
    block is, from some time on, on every honest validator's LMD-GHOST head. -/
theorem Theorem1_Safety_proved (τ : Timing)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) :
    Theorem1_Safety τ gj :=
  proof_Theorem1_Safety (τ := τ) (gj := gj)

/-- **Theorem 1, Monotonicity half** (Definition 4, Lemma 9) for plain LMD-GHOST: once
    confirmed, always confirmed. The cross-epoch step (Lemma 8) consumes Assumption 4
    (`β < (1 - pb)/4`) and the full-epoch coverage premise `CommitteeCoversEpoch`. -/
theorem Theorem1_Monotonicity_proved (τ : Timing)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) :
    Theorem1_Monotonicity τ gj :=
  proof_Theorem1_Monotonicity (τ := τ) (gj := gj)

end FastConfirmation.LMDGhost
