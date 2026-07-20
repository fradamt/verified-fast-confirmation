import FastConfirmation.Spec.Proof.Trajectory

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

/-- Pure form of the equivocation-discount soundness. -/
private theorem net_arith {w M q : ℕ} (h : w ≤ M) :
    w - q ≤ if M > q then M - q else 0 := by
  split_ifs <;> omega

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

/-- The equivocation discount is sound: if the actual (per-balance-source)
Byzantine committee weight of the span is within the pre-discount budget
`maximum_weight / 100 * CBT`, then the Byzantine weight net of the
equivocation score is within `compute_adversarial_weight` (both guard
branches; ℕ truncation works in our favor in the degenerate branch). -/
theorem byzantine_net_le_compute_adversarial_weight
    {store : Store Root} {bs : BeaconState Root} {a b : Slot}
    {byz_weight : Gwei}
    (hbudget : byz_weight ≤
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg bs) a b / 100 *
        cfg.confirmation_byzantine_threshold) :
    byz_weight - get_equivocation_score cfg ext store bs a b ≤
      compute_adversarial_weight cfg ext store bs a b := by
  have heq : compute_adversarial_weight cfg ext store bs a b =
      if estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs) a b / 100 *
            cfg.confirmation_byzantine_threshold >
          get_equivocation_score cfg ext store bs a b then
        estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs) a b / 100 *
            cfg.confirmation_byzantine_threshold
          - get_equivocation_score cfg ext store bs a b
      else 0 := rfl
  rw [heq]
  exact net_arith hbudget

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
