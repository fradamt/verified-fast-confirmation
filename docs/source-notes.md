# FCR β-bounds and refined-predicate terms

This note summarizes the distinct adversary bounds and confirmation-predicate
variants used by the paper and consensus specification.

## Primary sources

- [Fast Confirmation Rule](https://arxiv.org/abs/2405.00549), version 3.
- [`consensus-specs/specs/phase0/fast-confirmation.md`](https://github.com/ethereum/consensus-specs/blob/6b9bd532cca16555e2f3282d757622ebff29743e/specs/phase0/fast-confirmation.md)
  at public commit `6b9bd532cca16555e2f3282d757622ebff29743e`.
- [consensus-specs PR #4747](https://github.com/ethereum/consensus-specs/pull/4747).

## There are SEVERAL β-bounds, for different rules / properties — not one

| Rule / property | Bound | Source |
|---|---|---|
| §3 LMD-GHOST **safety** | general `β < 1/3` adversary (Assumption 2: `A_b ≤ β·W_b`) | paper §3 |
| §3 LMD-GHOST **monotonicity** | `β < ¼(1 − p/E)` ≈ 0.247 (**Assumption 4**) | paper §3.2 |
| §4 LMD-GHOST-HFC **safety** | `β < 1/3 − d` (**Assumption 5.1**; `d` = safety decay, §2.2.2) | paper §4.1 |
| §4 LMD-GHOST-HFC **monotonicity** | `β < min(1/6, 1/3 − d)` (**Assumption 6.2**) | paper §4.2 |
| §5 variable-balance variant | `β < min(1/6, 1/3 − d)` with `honFFGratioVar` (Assumption 7) | paper §5 |
| Production spec (PR #4747) | `CONFIRMATION_BYZANTINE_THRESHOLD = 25%` (configurable; ≈ the LMD `¼(1−p/E)`) | consensus-specs #4747 |
| fastconfirm.it (marketing) | "less than 25% adversarial stake" (headline; no β notation) | fastconfirm.it |

**`0.25` and `1/6` are both real and NOT in conflict — different constants:**
- `0.25 ≈ ¼(1−p/E)` is the **LMD-GHOST** monotonicity bound (Assumption 4) — and what the deployed
  rule + fastconfirm.it target (`CONFIRMATION_BYZANTINE_THRESHOLD = 25%`).
- `1/6` is the **FFG-closure** constant (Assumption 6.2), forced by `honFFGratio(β) ≤ 1`, needed in
  the paper to *prove* the canonical checkpoint keeps getting re-justified (so HFC confirmation
  stays monotone across epoch boundaries).

## Assumption 6 and honFFGratio

> **Assumption 6.** 1. [if `b` canonical and FFG support for `C(b,e)` ≥ `(2/3) W_t^{b'}` ...] then
> there is a checkpoint `C ⪰ b`, `epoch(C)=e+1`, … with `|F_{vs→C}|^C / J_t^C > honFFGratio(β)`,
> where **`honFFGratio(β) = 1/(1−β)·(2/3 + β)`**. 2. **`β < min(1/6, 1/3 − d)`.**
> "[the β bound] is implied by the constraint that `honFFGratio(β) ≤ 1`, but, given its
> significance, we make it explicit above."

`honFFGratio(β) ≤ 1 ⟺ (2/3+β) ≤ (1−β) ⟺ β ≤ 1/6`. `honFFGratio` is the effective-balance-weighted
fraction of *honest* validators that must FFG-vote for `C` to guarantee its justification (a ≥ 2/3
link) against a β-adversary. Lemmas 20/21 prove §4 monotonicity (Theorem 2) from it; Lemma 20 uses
Property 2 (`p/E < 5/18`). Decisive corroboration: **Appendix A is titled "A Confirmation Rule for
LMD-GHOST-HFC that does not rely on Assumption 6."**

## The refined confirmation predicate

**Clean Definition 8 (what the Lean formalizes):**
> `isLMDGHOSTSafe_v(b,C,t) := ∀ b'⪯b, Q_{b'} > ½(1 + W_p^C/W_{b'}) + β  ∨  b'=b_gen`, with
> `W_p^C := (p/E)·W_t^C` (proposer boost). The Lean's `isLMDGHOSTSafe` / `safetyThreshold` is exactly this.

**Production spec (PR #4747, integer-Gwei form):** `is_one_confirmed` = `support > safety_threshold`,
`safety_threshold = (maximum_support + proposer_score + 2·adversarial_weight − support_discount) / 2`:
- `proposer_score` — **proposer boost** (added).
- `support_discount` — **empty/missing-slot** discount: parent's support gathered in empty slots
  (`parent.slot+1 .. block.slot−1`, detected via `parent.slot+1 != block.slot`) minus
  `adversarial_weight`, floored at 0. `maximum_support` is estimated over `[parent.slot+1, current−1]`
  with a 5-per-mille `COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR`.
- `adversarial_weight` — **slashable/equivocation**: `committee_weight × 25% − equivocation_score`
  (already-equivocated, slashable weight discounted); `support` also excludes `slashed` /
  `equivocating_indices`. The clean `+β` is realized as `+2·adversarial_weight` (halved → `+adversarial_weight`).
- FFG side: `will_no_conflicting_checkpoint_be_justified`: `3·honest_ffg_support > total`;
  `will_current_target_be_justified`: `3·honest_ffg_support ≥ 2·total`.

**Paper §5 "Full" Definition 10 (validator-balance changes):**
> `Q_{b'} > (1+ρ)/(2(1−π))·(1 + W_p^C(1+ϵ+ρ)/W_{b'}) + ϵ·W_t^C/W_{b'} + β`,
with `ρ, π, ϵ` for entering/exiting/rewards-penalties; the FFG side `willChkpBeJustified` adds the
slashable `min(W_e, β·W)` term (`W_e` = max slashed Byzantine balance, Assumption 5.2), and FFG
votes are counted as `F ∖ D^{b'}` (excluding the slashable-evidence set `D`).

The `(2/3+β)/(1−β)` factor is `honFFGratio` on the FFG-justification side,
not a scaling of the LMD predicate's `β`. The refinements are proposer boost,
the empty-slot discount, the slashable/equivocation adjustment, and (§5) the
ρ/π/ϵ balance terms.

## What the Lean does, and what is packaged more strongly

`GateConfirmedBlockMonotonicity` requires the visible bound `β < min(1/6, (1−pb)/4)`: the `1/6` side is the
paper's FFG-closure constant from Assumption 6.2, and `(1−pb)/4` is the LMD-GHOST monotonicity
bound used by the canonical-epoch crux. The additional FFG strength is supplied by
`FFG_AccountableSafety`, `HonestFFGNoEquivocation`, `GlobalByzantineBound`, and
`SafeGreatestJustifiedAnchorInputs`. The voting-source recency obligation is proved
structurally in the never-filter argument.

For the Algorithm-1 monotonicity facade, `SafeConfirmedAlg1Inputs` packages the Assumption-6-style
closure more directly than the paper: every honest-view-safe block is required to satisfy
`isConfirmedNoCaching` plus the AU/visibility interfaces needed by the monotonicity fold. That is a
stronger per-safe-block premise than Assumption 6's conditional eventual FFG-closure statement.

Additional context: [fastconfirm.it](https://fastconfirm.it/) and Ethereum
Research discussions 15454 and 22167.
