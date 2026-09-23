module
public import FastConfirmationProofs.Discount.WindowStartMargin
public import FastConfirmationProofs.Execution.Delivery.Registry
public import FastConfirmationProofs.FFG.SelectedSource.EndpointMargin
public import FastConfirmationInternal.Discount.ByzantineBudget

@[expose] public section

/-!
# Spec / Proof / Arms

This module contains `estimate_same_epoch`, `slotcount_split`, `estimate_additive` and related declarations.
-/

namespace FastConfirmation.Spec

/-! ## Part A — ingredient lemmas (R13, R9′) from the Model defs

Both are true facts about `compute_proposer_score` /
`estimate_committee_weight_between_slots`; the machine-checked arms do **not**
consume them; they close the earlier cross-multiplied form. -/


/-- **R9′ (same-epoch estimate linearity).** On a nonempty span `[a,b]` lying in
one epoch (`is_full_validator_set_covered` false, `epoch a = epoch b`),
`estimate = (TAB / SLOTS_PER_EPOCH)·(b − a + 1)` — the same-epoch branch of
`estimate_committee_weight_between_slots`. The covered/epoch guards are explicit
hypotheses (they are true of the spec's confirmation spans but not free in
general — a span can cover a full epoch, or straddle a boundary). -/
theorem estimate_same_epoch (cfg : Config) (tab : Gwei) (a b : Slot)
    (hab : a ≤ b)
    (hcov : is_full_validator_set_covered cfg a b = false)
    (hep : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg b) :
    estimate_committee_weight_between_slots cfg tab a b
      = tab / cfg.slots_per_epoch * (b - a + 1) := by
  simp only [estimate_committee_weight_between_slots, hep]
  split_ifs with hgt hcovered
  · exact absurd hgt (Nat.not_lt.mpr hab)
  · rw [hcov] at hcovered; exact absurd hcovered (by decide)
  · rfl

/-- Pure-ℕ slot-count split (`omega` on genuine `ℕ`; abbrev-typed `Slot` goals
trip `omega`, hence the extraction). -/
private theorem slotcount_split (a b c : ℕ) (hab : a ≤ b) (hbc : b + 1 ≤ c) :
    b - a + 1 + (c - (b + 1) + 1) = c - a + 1 := by omega

/-- **R9′ (same-epoch additivity).** With both `[a,b]` and `[b+1,c]` in one epoch,
the estimate is additive: `estimate a c = estimate a b + estimate (b+1) c`. Pure
consequence of the linearity (`estimate_same_epoch`) on the three spans — the
`(c − a + 1) = (b − a + 1) + (c − b)` slot count splits, `b+1 ≤ c`, `a ≤ b`. -/
theorem estimate_additive (cfg : Config) (tab : Gwei) (a b c : Slot)
    (hab : a ≤ b) (hbc : b + 1 ≤ c)
    (hcovAC : is_full_validator_set_covered cfg a c = false)
    (hcovAB : is_full_validator_set_covered cfg a b = false)
    (hcovBC : is_full_validator_set_covered cfg (b + 1) c = false)
    (hepAC : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg c)
    (hepAB : compute_epoch_at_slot cfg a = compute_epoch_at_slot cfg b)
    (hepBC : compute_epoch_at_slot cfg (b + 1) = compute_epoch_at_slot cfg c) :
    estimate_committee_weight_between_slots cfg tab a c
      = estimate_committee_weight_between_slots cfg tab a b
        + estimate_committee_weight_between_slots cfg tab (b + 1) c := by
  rw [estimate_same_epoch cfg tab a c (le_trans hab (le_trans (Nat.le_succ b) hbc)) hcovAC hepAC,
      estimate_same_epoch cfg tab a b hab hcovAB hepAB,
      estimate_same_epoch cfg tab (b + 1) c hbc hcovBC hepBC,
      ← Nat.mul_add, slotcount_split a b c hab hbc]









variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)





end FastConfirmation.Spec

end
