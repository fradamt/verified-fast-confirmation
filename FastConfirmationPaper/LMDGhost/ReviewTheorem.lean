module
public import FastConfirmationPaper.LMDGhost.Proof.FutureHeadAgreement
public import FastConfirmationPaper.LMDGhost.Proof.RuleSafety
public import FastConfirmationPaper.LMDGhost.Claims

@[expose] public section

/-!
# LMDGhost / ReviewTheorem

The internal proven facade: theorem constants discharging each public statement of
`LMDGhost.TheoremStatements`, delegating to the proof scripts under `Proof/`. The
public `LMDGhost.ProvenTheorems` re-exposes only that each statement has a proof.

* `proof_HeadFutureAgreement` — the reusable engine (Lemma 6), directly from
  `head_safety_engine`. **Proved.**
* `proof_Theorem1_Safety` — the Algorithm-4 Safety half (Lemmas 7–8), via `Rule.lean`,
  instantiated at `trivialFilter`. **Proved.**
* `proof_Theorem1_Monotonicity` — the Algorithm-4 Monotonicity half (Lemma 9), via
  `Rule.lean`. The cross-epoch step is `canonical_epoch_imp_safe` (Lemma 8, consuming
  Assumption 4 `β < (1−pb)/4` and `CommitteeCoversEpoch`), and the two-case assembly
  re-establishes a safe candidate `≽ b` of slot `≥ b.slot` inside the next epoch's range.
  **Proved.** (`sg` is load-bearing — it supplies both the GST bound and the epoch-recency
  bound `epochOf(slot t) ≤ epochOf b.slot + 1` the cross-epoch step needs.)
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- **The reusable engine (Lemma 6) is proved.** `HeadAgreementAfterConfirmation` for any filter
    `flt` follows directly from the arbitrary-time `head_safety_engine`: the public
    statement's premises are exactly the engine's hypotheses (with `AnchorsCoincide`
    the §3.1 form of hyp (4)). -/
theorem proof_HeadFutureAgreement (τ : Timing) (flt : BlockFilter n P) :
    HeadAgreementAfterConfirmation τ flt := by
  intro fm cm pb gj boost 𝒱 C hSync hNF hHB hVV hcm hpb hAnchor
    v b t hv hbwf hbslot h1 hgst0 hsafe hNFil w t' hw ht'
  exact head_safety_engine hSync hNF hHB hVV hcm hpb hAnchor hv hbwf hbslot
    h1 hgst0 hsafe (neverFiltered_to_hNFilOfHead hNFil) hw ht'

-- `proof_Theorem1_Safety` (Lemmas 7–8) and `proof_Theorem1_Monotonicity` (Lemma 9) are
-- proved in `Proof.Rule` (imported above), in this same namespace, so they are directly
-- available to the public `ProvenTheorems` facade.

end FastConfirmation.LMDGhost

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
    future agreement.
Paper source: Lemma 6, Section 3.1 of arXiv:2405.00549. -/
theorem head_agreement_after_confirmation (τ : Timing) (flt : BlockFilter n P) :
    HeadAgreementAfterConfirmation τ flt :=
  proof_HeadFutureAgreement τ flt

/-- **Theorem 1, Safety half** (Definition 4, Lemmas 7–8) for plain LMD-GHOST: a confirmed
    block is, from some time on, on every honest validator's LMD-GHOST head.
Paper source: Theorem 1, safety part, Section 3.1 of arXiv:2405.00549. -/
theorem confirmed_block_safety (τ : Timing)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) :
    ConfirmedBlockSafety τ gj :=
  proof_Theorem1_Safety (τ := τ) (gj := gj)

/-- **Theorem 1, Monotonicity half** (Definition 4, Lemma 9) for plain LMD-GHOST: once
    confirmed, always confirmed. The cross-epoch step (Lemma 8) consumes Assumption 4
    (`β < (1 - pb)/4`) and the full-epoch coverage premise `CommitteeCoversEpoch`.
Paper source: Theorem 1, monotonicity part, Section 3.1 of arXiv:2405.00549. -/
theorem confirmed_block_monotonicity (τ : Timing)
    (gj : ViewFamily n P → Validator n → Time → Anchor n) :
    ConfirmedBlockMonotonicity τ gj :=
  proof_Theorem1_Monotonicity (τ := τ) (gj := gj)

end FastConfirmation.LMDGhost

end
