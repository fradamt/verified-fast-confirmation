module
public import FastConfirmation.Spec.Proof.EdgeDynamics
public import FastConfirmation.Spec.Proof.StepDischarge
public import FastConfirmation.Spec.Proof.Discount

@[expose] public section

/-!
# Spec / Proof / Confinement

This module contains `le_guarded_sub_add`, `le_compute_adversarial_weight_add_equiv`, `qV_le_get_adversarial_add_eqV` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Part 1 — the adversarial-weight bridges (`hAhi`/`hAlo`) -/


/-- Pure-ℕ lower bound: the guarded difference plus the subtrahend dominates `M`. -/
private theorem le_guarded_sub_add {M eq : ℕ} : M ≤ (if M > eq then M - eq else 0) + eq := by
  split_ifs <;> omega


/-- **`maxAdv ≤ compute_adversarial_weight + equiv`** (`hAlo` core). The budget net of the
equivocation score, plus that score back, recovers the full `maxAdv`. Pure `split_ifs`. -/
theorem le_compute_adversarial_weight_add_equiv {store : Store Root} {bs : BeaconState Root}
    (a e : Slot) :
    estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) a e / 100
        * cfg.confirmation_byzantine_threshold ≤
      compute_adversarial_weight cfg ext store bs a e
        + get_equivocation_score cfg ext store bs a e := by
  simp only [compute_adversarial_weight]
  exact le_guarded_sub_add


/-- **`hAlo` at the real spec quantity.** `qV·C ≤ get_adversarial_weight + eqV` with
`qV := estimate(advSpan)//100`, `eqV := get_equivocation_score(advSpan)`. Exactly
`arms_of_confirmed`'s `hAlo`. -/
theorem qV_le_get_adversarial_add_eqV {store : Store Root} {bs : BeaconState Root} {b : Root} :
    estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (if get_block_epoch cfg store b >
              get_block_epoch cfg store (store.blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
          else (store.blocks b).slot)
          (get_current_slot cfg store - 1) / 100
        * cfg.confirmation_byzantine_threshold ≤
      get_adversarial_weight cfg ext store bs b
        + get_equivocation_score cfg ext store bs
          (if get_block_epoch cfg store b >
              get_block_epoch cfg store (store.blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
          else (store.blocks b).slot)
          (get_current_slot cfg store - 1) := by
  rw [get_adversarial_weight_eq]
  exact le_compute_adversarial_weight_add_equiv cfg ext _ _

/-! ## Part 2 — the discount bridge (`hd`), via `Discount.support_discount_le_parent_stuck` -/

namespace Execution

variable (E : Execution Root)


/-! ## Part 3 — the honest sibling confinement (`hHon`), at the base cutoff `es`

At the base cutoff `es = get_current_slot(store w m) − 1`, an honest recorded supporter of a
sibling `c'` of the `b`-side child `c` lands in `Xclass … es`. The recorded newest-by-`es`
message *is* the newest-by-`es` ground vote (`StepDischarge.recorded_lm_is_newest_at`), so the
recorded block `lm.root` is the sole newest vote block; `Forks.siblings_incompatible` (with
`c ⪯ b`) then rules out both class-membership branches:

* `¬SupportsDesc`: `lm.root ⪰ b` would make `lm.root` a common descendant of `c` (`c ⪯ b ⪯ lm.root`)
  and `c'` (`c' ⪯ lm.root`) — impossible for distinct `h`-children.
* `¬AncestorOrVoteless`: `b ⪰ lm.root` would give `c' ⪯ lm.root ⪯ b`, so `b` is a common
  descendant of `c` and `c'` — again impossible; and the voteless branch dies on the recorded vote.

The blanket walk domain `hwalkK` is the Layer-0 `AnchorFacade.store_walkKnownK` shape; `hdom` is
`Bridge.RecordedEpochMax` (the ubiquity domination); `hbc`/`hlo`/`hpc`/`hpc'`/`hne` are the fork
geometry. `hlmknown` (recorded message roots are known blocks) is the per-store knownness fact the
attestation-application block gate provides. -/





end Execution

end FastConfirmation.Spec

end
