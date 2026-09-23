module
public import FastConfirmationProofs.Execution.Trajectory.ExecutionClock

@[expose] public section

/-!
# Spec / Proof / Quorum (part 1: the threshold arithmetic)

Layer 2 of the safety proof — the spec-side Lemmas 3∘4 core. This module
holds the pure-arithmetic half: unfolding `is_one_confirmed` /
`compute_safety_threshold` into the branch-free inequality

`2·support + support_discount ≥ maximum_support + proposer_score +
2·adversarial_weight + 1`

(the spec's commented formula with the underflow guard resolved, floor
division absorbed), and the adversarial-budget algebra
(`compute_adversarial_weight`'s equivocation discount is sound for any
actual Byzantine weight within the pre-discount budget). The accounting
half — identifying `support`'s summands with ground-truth weights and
bounding the Byzantine part via `ByzantineBound` — lands with Layer 1.
-/

namespace FastConfirmation.Spec

/-- Pure form of the threshold inequality: `s > ⌊(X − d)/2⌋` (guarded) gives
`2s + d ≥ X + 1` in both guard branches. -/
private theorem threshold_arith {s d X : ℕ}
    (h : s > if d < X then (X - d) / 2 else 0) : 2 * s + d ≥ X + 1 := by
  split_ifs at h <;> omega


variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- `is_one_confirmed`, resolved to a branch-free inequality: twice the
support plus the discount strictly exceeds the maximum-support + boost +
twice-adversarial budget. Both branches of the spec's underflow guard land
here (in the degenerate guard-false branch the discount alone already
covers the budget and `support ≥ 1`). -/
theorem is_one_confirmed_ineq {store : Store Root} {bs : BeaconState Root}
    {b : Root} (h : is_one_confirmed cfg ext store bs b = true) :
    2 * get_attestation_score cfg store (get_node_for_root b) bs
        + get_support_discount cfg ext store bs b
      ≥ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b).parent_root).slot + 1)
          (get_current_slot cfg store - 1)
        + compute_proposer_score cfg bs
        + 2 * get_adversarial_weight cfg ext store bs b + 1 := by
  have h' : get_attestation_score cfg store (get_node_for_root b) bs >
      compute_safety_threshold cfg ext store b bs := by
    simpa [is_one_confirmed] using h
  have heq : compute_safety_threshold cfg ext store b bs =
      if get_support_discount cfg ext store bs b <
          estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b).parent_root).slot + 1)
            (get_current_slot cfg store - 1)
          + compute_proposer_score cfg bs
          + 2 * get_adversarial_weight cfg ext store bs b then
        (estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b).parent_root).slot + 1)
            (get_current_slot cfg store - 1)
          + compute_proposer_score cfg bs
          + 2 * get_adversarial_weight cfg ext store bs b
          - get_support_discount cfg ext store bs b) / 2
      else 0 := rfl
  rw [heq] at h'
  exact threshold_arith h'


/-- `get_adversarial_weight` unfolded to its span (both branches use the end
slot `current_slot - 1`; the start is the block's slot or, across an epoch
boundary, the epoch's first slot). -/
theorem get_adversarial_weight_eq {store : Store Root} {bs : BeaconState Root}
    {b : Root} :
    get_adversarial_weight cfg ext store bs b =
      compute_adversarial_weight cfg ext store bs
        (if get_block_epoch cfg store b >
            get_block_epoch cfg store (store.blocks b).parent_root then
          compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
        else (store.blocks b).slot)
        (get_current_slot cfg store - 1) := by
  simp only [get_adversarial_weight]
  split_ifs <;> rfl

end FastConfirmation.Spec

end
