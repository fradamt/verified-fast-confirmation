module
public import FastConfirmationProofs.Execution.Delivery.Registry
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import FastConfirmationInternal.Discount.CommitteeWeight

@[expose] public section

/-!
# Spec / Proof / Fraction

Proves honest committee span-weight identities using the `Jspec` accessor in Internal.

This module contains `span_committee_mono`, `weight_split_honest` and related lemmas.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the ground-truth fraction quantities -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The span committee grows with the upper slot (paper `committeeUnion_mono`). -/
theorem span_committee_mono (a : Slot) {b b' : Slot} (h : b ≤ b') :
    E.span_committee a b ⊆ E.span_committee a b' := by
  simp only [Execution.span_committee]
  apply Finset.biUnion_subset_biUnion_of_subset_left
  exact Finset.Icc_subset_Icc_right h

omit [LinearOrder Root] [Inhabited Root] in
/-- Ground-truth weight of a set splits into its honest and non-honest parts. -/
theorem weight_split_honest (s : Finset ValidatorIndex) :
    E.weight s = E.weight (s.filter (fun i => i ∈ E.honest))
      + E.weight (s.filter (fun i => i ∉ E.honest)) := by
  simp only [Execution.weight]
  exact (Finset.sum_filter_add_sum_filter_not s (fun i => i ∈ E.honest) E.weight_of).symm


/-! ## Section 2 — growth decompositions -/

omit [LinearOrder Root] [Inhabited Root] in
/-- `J` decomposes as the value at `b` plus the honest weight of the committee
growth set (paper `J_eq_add_growth`, `Monotone.lean`). Exact equality — no
support hypotheses. -/
theorem Jspec_eq_add_growth (a : Slot) {b b' : Slot} (h : b ≤ b') :
    E.Jspec a b' = E.Jspec a b
      + E.weight ((E.span_committee a b' \ E.span_committee a b).filter
          (fun i => i ∈ E.honest)) := by
  simp only [Execution.Jspec, Execution.weight]
  have hset : (E.span_committee a b' \ E.span_committee a b).filter (fun i => i ∈ E.honest)
      = (E.span_committee a b').filter (fun i => i ∈ E.honest)
          \ (E.span_committee a b).filter (fun i => i ∈ E.honest) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [add_comm, hset]
  exact (Finset.sum_sdiff (Finset.filter_subset_filter _ (E.span_committee_mono a h))).symm


/-! ## Section 3 — the pure-ℕ fraction step and assembled monotonicity -/



end Execution

end FastConfirmation.Spec

end
