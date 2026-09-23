module
public import FastConfirmationProofs.FFG.State.ObservedCheckpointAncestry
public import FastConfirmationProofs.FFG.SourceHistory.SafeFromInvariant

@[expose] public section

/-!
# Spec / Proof / MicroSteps: structural reductions

This module supplies two reductions used by `ResidualMechanicalII` and
`ObservedDom`:

* **`walk_closure` from an anchor-minimum guard.** `ResidualMechanicalII.WalkClosure`
  asks every known block above the target slot to have a *known* parent. Its
  "parent is known **or** the anchor's dangling pointer `P`" half is Layer-0:
  `Execution.store_parentInRootsOr` re-exposes the `ParentInRootsOr P` component of
  `WFTrajectory.WFPlus` at the trajectory level (the same induction as
  `store_parentSlotLt`, extracting `.2.2.1`). `walkClosure_of_min` then derives
  `WalkClosure` from `ParentInRootsOr P` plus the flat
  **anchor/minimal-slot guard** `∀ r, parent = P → slot ≤ sl` (only the anchor's own
  dangling edge, not every block). So `walk_closure` shrinks to `anchor_slot_guard`.

* **The confirming-store descent used by `dynamics_struct`.** The loops in
  inversions (`L4Fold.find_latest_confirmed_descendant_spec` /
  `get_latest_confirmed_spec`) already expose that the confirmed block is a reset
  anchor or passed `is_one_confirmed`; strengthened here to `..._mem`, they also
  expose that a non-anchor result is a **member of `get_ancestor_roots store head r₀`**
  — i.e. it descends from the reset anchor `r₀` *at the confirming store*. This is the
  loop-structural half of `hcase`. Lifting it to the arbitrary endpoint `(w, m)` of
  `DynamicsChainStruct` uses an explicit cross-store transport premise.

A third reduction — the on-boundary source for `prev_greatest_justifiedIn`
(`update_fcv_observed_boundary`, `fcrStep_observed_boundary`,
`prev_greatest_justifiedIn_of_boundarySource`) — stood here too. It unfolded
`update_fast_confirmation_variables`' epoch-boundary rotation of
`current_epoch_observed_justified_checkpoint` for the observed-anchor filter bundle, and is
deleted with the legacy `SpecAssumptions` observed-anchor cone's orphan sweep (P-6; see the
section note below and `docs/p6-justified-descends-derivation.md` §8). The off-boundary
`fcrStep_observed_else` is unaffected.
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
`fcrStoreAtCall`-observed checkpoint set by `update_fast_confirmation_variables`' rotation.
`update_fcv_observed_boundary` computes that rotation **on** the epoch boundary: the
observed checkpoint becomes the store's `unrealized_justified_checkpoint` (when the
next slot is also an epoch start — only possible for `slots_per_epoch = 1`) or the
carried `previous_epoch_greatest_unrealized_checkpoint`. Both are greatest-unrealized
/ unrealized-justified checkpoints supplied by the boundary-source premise. -/

/-! ### Deleted: the epoch-boundary observed-rotation micro-steps

`update_fcv_observed_boundary`, `fcrStep_observed_boundary` and
`prev_greatest_justifiedIn_of_boundarySource` stood here. They unfolded the on-boundary
rotation of `current_epoch_observed_justified_checkpoint` for the observed-anchor filter
bundle's `observed_known` / `prev_greatest_justifiedIn` fields. The off-boundary
`fcrStep_observed_else` and the rest of the module are unaffected.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

namespace Execution

variable (E : Execution Root)



end Execution

end FastConfirmation.Spec

end
