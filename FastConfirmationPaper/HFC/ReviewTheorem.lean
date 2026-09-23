module
public import FastConfirmationPaper.HFC.Proof.Monotonicity
public import FastConfirmationPaper.HFC.Proof.Algorithm1Monotonicity

@[expose] public section

/-!
# HFC / ProvenTheorems

Proved facade for the §4 HFC confirmation-rule theorems — the original gate-based pair
(`GateConfirmedBlockSafety` / `GateConfirmedBlockMonotonicity`) and the gate-free Algorithm-1 pair
(`RuleConfirmedBlockSafety` / `RuleConfirmedBlockMonotonicity`). The proof-free statements live in
`FastConfirmation.Paper.HFC.TheoremStatements`; the theorem constants below expose only that each public statement has a
proof, delegating scripts to `FastConfirmation/Paper/HFC/Proof/` (`Compose.lean`, `Monotonicity.lean`,
`NeverFiltered.lean` for the gate-based pair; `NeverFilteredAlg1.lean` and
`MonotonicityAlg1.lean` for the Algorithm-1 pair).

Mirrors `FastConfirmation.Paper.LMDGhost.ProvenTheorems` (the §3.1 module facade): the public statement constant is discharged
by the internal proof. For the gate-based safety the public `isHFCConfirmed` premise
(`isConfirmed ∧ WillNoConflictingChkpBeJustified`) is threaded through: its first component feeds
`hfc_safety_of_notFiltered`'s `isConfirmed` premise, and its `ConfirmedNotFFGFiltered` premise is
supplied by `confirmedNotFFGFiltered_proved` (the never-filter, proved from the gate).

The Algorithm-1 facades carry no semantic gate: `rule_confirmed_block_safety` and
`rule_confirmed_block_monotonicity` use the `isConfirmedAlg1` wrapper and drive selected
`highestConfirmedSinceEpochAlg1` blocks canonical via the unified `isConfirmedNoCaching`
dispatcher.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

set_option linter.style.setOption false
-- Facade aliases over the Algorithm-1 wrapper force reduction of large public statement types.
set_option maxHeartbeats 3000000

variable {n : ℕ}

/-- **§4 HFC Confirmation-Rule SAFETY proved** (arXiv:2405.00549 §4.1/§4.3): an honest
    validator HFC-confirming `b` at `t` ⇒ from some time on, `b` is on every honest
    validator's LMD-GHOST-HFC head. Discharges the public `GateConfirmedBlockSafety` statement by
    composing the filter-generic §3.1 engine (`hfc_safety_of_notFiltered`) with the §4
    never-filter (`confirmedNotFFGFiltered_proved`), threading the gate out of
    `isHFCConfirmed`. -/
theorem gate_confirmed_block_safety (τ : Timing) (bal₀ : Stakes n) : GateConfirmedBlockSafety τ bal₀ := by
  intro fm cm pb boost 𝒱 gj C hSync hNF hHB hVV hcm hWFB hpb hsb hAS hnoequiv hByz hSGJ
    v b t hv hsg hHFCconf
  obtain ⟨hconf, _hgate⟩ := hHFCconf
  exact hfc_safety_of_notFiltered bal₀ hSync hNF hHB hVV hcm hpb hv hsg hAS hnoequiv hByz
    hSGJ hconf (confirmedNotFFGFiltered_proved bal₀ hSync hNF hHB hVV hcm hpb hv)

/-- **§4 HFC Confirmation-Rule MONOTONICITY proved** (arXiv:2405.00549 §4.2): once
    HFC-confirmed, always HFC-confirmed. Discharges the public `GateConfirmedBlockMonotonicity`
    statement via `hfc_monotonicity_proved`. -/
theorem gate_confirmed_block_monotonicity (τ : Timing) (bal₀ : Stakes n) : GateConfirmedBlockMonotonicity τ bal₀ :=
  hfc_monotonicity_proved bal₀

/-- **§4 HFC SAFETY about the paper's ALGORITHM 1, proved** (the semantic gate eliminated).
    Discharges the public `RuleConfirmedBlockSafety` statement over `isConfirmedAlg1`: the wrapper extracts
    the selected highest `isConfirmedNoCaching` block and its actual selector witness slot, runs the
    current/previous-epoch Algorithm-1 safety fold there, and transfers canonicity back to the
    requested ancestor. `Alg1SelectorSafetyInterface` supplies the witness-slot GST guard plus the
    explicit AU, `P-link`, committee-partition, and realization premises. -/
theorem rule_confirmed_block_safety (τ : Timing) (bal₀ : Stakes n) : RuleConfirmedBlockSafety τ bal₀ := by
  exact hfc_safety_alg1_public τ bal₀

/-- **§4 HFC MONOTONICITY about the paper's ALGORITHM 1, proved** (the semantic gate eliminated).
    Discharges the public `RuleConfirmedBlockMonotonicity` statement via `hfc_monotonicity_alg1`, whose two
    `highestConfirmedSinceEpochAlg1` never-filter sites are driven by the rule
    `isConfirmedNoCaching` (both branches, through the unified canonicity dispatcher) fed by the
    `SafeConfirmedAlg1Inputs` bundle, rather than the assumed `WillNoConflictingChkpBeJustified`. -/
theorem rule_confirmed_block_monotonicity (τ : Timing) (bal₀ : Stakes n) :
    RuleConfirmedBlockMonotonicity τ bal₀ := by
  intro fm cm pb we boost 𝒱 gj C hSync hNF hHB hVV hcm hpb hβ4 hAS hnoequiv hByz hSCM hwe0 hBundle
    v b t t' hv hsg hle hcover hconf
  exact hfc_monotonicity_alg1 bal₀ hSync hNF hHB hVV hcm hpb hβ4 hAS hnoequiv hByz hSCM hwe0 hBundle
    hv hsg hle hcover hconf

end FastConfirmation.HFC

end
