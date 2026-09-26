module
public import FastConfirmationProofs.Execution.Trajectory.ChainWalkClosure
public import FastConfirmationProofs.FFG.SourceHistory.SafeFromInvariant

@[expose] public section

/-!
# Spec / Proof / MicroSteps

Proves anchor walk closure from a minimum-slot guard.
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

end FastConfirmation.Spec

end
