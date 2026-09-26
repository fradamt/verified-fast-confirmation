module
public import FastConfirmationStatements.Premises.Synchrony

@[expose] public section

/-! Known ancestor walks and the internal honest-head admissibility conclusion. -/

namespace FastConfirmation.Spec
variable {Root : Type*}

/-- The parent-walk from `r` down to `slot` stays inside the store's known
blocks — the domain on which python's `get_ancestor` recursion is defined.
Uses the store's own `parent_slot_lt` discipline implicitly: derivations are
finite by construction. -/
inductive WalkKnown (store : Store Root) (slot : Slot) : Root → Prop
  | stop {r : Root} (hr : r ∈ store.block_roots)
      (hle : (store.blocks r).slot ≤ slot) : WalkKnown store slot r
  | step {r : Root} (hr : r ∈ store.block_roots)
      (hgt : slot < (store.blocks r).slot)
      (hp : WalkKnown store slot (store.blocks r).parent_root) :
      WalkKnown store slot r

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- Only the roots on this vote head's target-epoch ancestor walk must avoid
the receiver's permanent finalized-checkpoint exclusion. This is the exact
path consumed by attestation validation. -/
inductive VotePathAdmissible (E : Execution Root)
    (v : ValidatorIndex) (n : ℕ) (w : ValidatorIndex)
    (boundary : ℕ) (slot : Slot) : Root → Prop
  | stop {r : Root} (hr : r ∈ (E.store cfg ext v n).block_roots)
      (hnot : ¬ PermanentBlockExclusion cfg ext E v n r w boundary)
      (hle : ((E.store cfg ext v n).blocks r).slot ≤ slot) :
      VotePathAdmissible E v n w boundary slot r
  | step {r : Root} (hr : r ∈ (E.store cfg ext v n).block_roots)
      (hnot : ¬ PermanentBlockExclusion cfg ext E v n r w boundary)
      (hgt : slot < ((E.store cfg ext v n).blocks r).slot)
      (hp : VotePathAdmissible E v n w boundary slot
        ((E.store cfg ext v n).blocks r).parent_root) :
      VotePathAdmissible E v n w boundary slot r

/-- Internal G4 conclusion for each actual honest head, before its next tick.
The accepted FFG and economic premises derive this property. -/
def HonestHeadPathAdmissibility (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n, E.WithinHorizon cfg n → ∀ w slot,
    E.WithinHorizon cfg (E.slot_start cfg (E.slot_at cfg n + 1)) →
    WalkKnown (E.store cfg ext v n) slot (get_head cfg (E.store cfg ext v n)).root →
    VotePathAdmissible cfg ext E v n w
      (E.slot_start cfg (E.slot_at cfg n + 1) - 1) slot
      (get_head cfg (E.store cfg ext v n)).root

end FastConfirmation.Spec
end
