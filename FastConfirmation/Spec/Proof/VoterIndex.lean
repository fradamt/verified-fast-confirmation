import FastConfirmation.Spec.Proof.Clock

/-!
# Spec / Proof / Voter Index

Clock monotonicity bounds for voting-second indices. Strict growth of
`Execution.slot_at` reflects strict growth of its second argument; consequently,
a vote in a later slot than `slot_at (n + 1)` must occur at or after `n + 1`.

The proofs use only `ℕ` order and addition. In particular, slot arithmetic is
discharged with explicit `Nat` lemmas rather than arithmetic automation over the
`Slot` abbreviation.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

namespace Execution

variable (E : Execution Root) (cfg : Config)

/-- If the clock slot strictly increases, then its second index strictly
increases. -/
theorem index_lt_of_slot_at_lt {n1 n2 : ℕ}
    (h : E.slot_at cfg n1 < E.slot_at cfg n2) : n1 < n2 := by
  apply Nat.lt_of_not_ge
  intro hn2n1
  exact (Nat.not_le_of_lt h) (E.slot_at_mono cfg hn2n1)

/-- At a genuine slot advance `n → n+1`, a voter in slot `s'+1` at or after
`slot_at (n+1) = es+1` has a second index at least `n+1`.  The equality-slot
case is the important boundary case: if `ni < n+1`, then `ni ≤ n`, so clock
monotonicity would put `slot_at ni` at or before `slot_at n`, contradicting the
strict slot advance. -/
theorem voter_index_bound {ni n : ℕ} {s' es : Slot}
    (hni : E.slot_at cfg ni = s' + 1)
    (hn : E.slot_at cfg (n + 1) = es + 1)
    (hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1))
    (hes : es ≤ s') : n + 1 ≤ ni := by
  apply Nat.le_of_not_gt
  intro hni_lt
  have hni_le_n : ni ≤ n := Nat.le_of_lt_succ hni_lt
  have hslot_lt : E.slot_at cfg ni < E.slot_at cfg (n + 1) :=
    lt_of_le_of_lt (E.slot_at_mono cfg hni_le_n) hadvance
  rw [hni, hn] at hslot_lt
  exact (Nat.not_lt_of_ge (Nat.add_le_add_right hes 1)) hslot_lt

end Execution

end FastConfirmation.Spec
