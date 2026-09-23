module
public import FastConfirmation.Spec.Proof.ObservedDom
public import FastConfirmation.Spec.Proof.L4Fold

@[expose] public section

/-!
# Spec / Proof / MicroSteps

This module contains `walkClosure_of_min`, `update_fcv_observed_boundary`, `fcrStep_observed_boundary` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section 1 — `walk_closure` from the anchor-minimum guard

`WalkClosure store sl` (`∀ r ∈ block_roots, sl < (blocks r).slot →
(blocks r).parent_root ∈ block_roots`) classifies *every* block above `sl`. Under
`ParentInRootsOr P store` each block's parent is already known **or** the anchor's
dangling `P`; parent-`P` blocks are guarded by the flat
minimal-slot fact `parent = P → slot ≤ sl`. -/

/-- **`WalkClosure` from `ParentInRootsOr` + the anchor-min guard.** For a block `r`
above `sl`, `ParentInRootsOr` gives its parent known (done) or `= P`; in the `= P`
case the guard forces `slot ≤ sl`, contradicting `sl < slot`. So the full closure
reduces to constraining only the parent-`P` blocks — the anchor's own edge. -/
theorem walkClosure_of_min {store : Store Root} {P : Root} {sl : Slot}
    (hQ : ParentInRootsOr P store)
    (hguard : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root = P → (store.blocks r).slot ≤ sl) :
    WalkClosure store sl := by
  intro r hr hlt
  rcases hQ r hr with hin | hP
  · exact hin
  · exact absurd hlt (Nat.not_lt.mpr (hguard r hr hP))

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 2 — confirming-store descent from the loop inversions

`L4Fold.find_latest_confirmed_descendant_spec` shows the confirmed result is the input
`lcr` or passed `is_one_confirmed`. This strengthening additionally exposes the
loop-structural certificate: a non-`lcr` result is a **member of
`get_ancestor_roots store head base`** for the loop base — the
ascending chain from `base` toward the head — so it descends from a reset anchor *at
the confirming store*. The lift to an arbitrary endpoint `(w, m)` is represented by the
`DynamicsChainStruct` endpoint premise. -/


/-! ## Section 3 — the source of `prev_greatest_justifiedIn`

`ObservedDom`'s sole corner (`is_start_slot_at_epoch = true`, no slot advance) has the
`fcrStep`-observed checkpoint set by `update_fast_confirmation_variables`' rotation.
`update_fcv_observed_boundary` computes that rotation **on** the epoch boundary: the
observed checkpoint becomes the store's `unrealized_justified_checkpoint` (when the
next slot is also an epoch start — only possible for `slots_per_epoch = 1`) or the
carried `previous_epoch_greatest_unrealized_checkpoint`. Both are greatest-unrealized
/ unrealized-justified checkpoints supplied by the boundary-source premise. -/

/-- **`update_fast_confirmation_variables`' observed rotation, on an epoch boundary.**
When the store's current slot is an epoch start, the rotation writes
`current_epoch_observed_justified_checkpoint` from the (possibly just-updated)
`previous_epoch_greatest_unrealized_checkpoint`: the store's
`unrealized_justified_checkpoint` if the *next* slot is also an epoch start (the
last-slot-of-epoch branch fired, `slots_per_epoch = 1`), else the carried
`previous_epoch_greatest_unrealized_checkpoint`. The `else` branch of the outer `if`
is `update_fcv_observed_else` (`ObservedDom`); this is its `then` branch. -/
theorem update_fcv_observed_boundary (fcr_store : FastConfirmationStore Root)
    (hstart : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) = true) :
    (update_fast_confirmation_variables cfg fcr_store).current_epoch_observed_justified_checkpoint
      = (if is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store + 1) then
          fcr_store.store.unrealized_justified_checkpoint
        else fcr_store.previous_epoch_greatest_unrealized_checkpoint) := by
  simp only [update_fast_confirmation_variables]
  rw [if_pos hstart]
  split_ifs <;> rfl

namespace Execution

variable (E : Execution Root)



/-- **`fcrStep`'s observed checkpoint on an epoch boundary.** Re-seating
`update_fcv_observed_boundary` on `store v (n+1)`: on the boundary the `fcrStep`-observed
checkpoint is the store's `unrealized_justified_checkpoint` (`slots_per_epoch = 1`
degenerate branch) or the carried `(fcr v n).previous_epoch_greatest_unrealized_checkpoint`.
This exposes the rotation `fcrStep` applies even at a non-advance second
(the `fcr` recursion itself discards it), exposing the actual checkpoint source. -/
theorem fcrStep_observed_boundary (v : ValidatorIndex) (n : ℕ)
    (hstart : is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1)))
      = true) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
      = (if is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
          (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
        else (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint) := by
  rw [Execution.fcrStep]
  exact update_fcv_observed_boundary cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) } hstart


end Execution

end FastConfirmation.Spec

end
