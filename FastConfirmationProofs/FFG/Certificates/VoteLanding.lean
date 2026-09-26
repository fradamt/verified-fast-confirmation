module
public import FastConfirmationProofs.Execution.Trajectory.InductionHypothesis
public import FastConfirmationProofs.Discount.ByzantineSiblingWeight

@[expose] public section

/-!
# Spec / Proof / VoteLanding

Proves that honest committee votes land in the expected FFG certificate window.

This module contains `honest_committee_vote` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-! ## Section 1 — `hdil`: the boost dilution from the saturated `Jspec` lower bound -/



namespace Execution

variable (E : Execution Root)


/-! ## Section 2 — the sibling confinement wiring (`hHon` / `hByz`)

`EdgeDynamics.EdgeInputResidual.hHon`/`hByz` confine every recorded supporter of a
filtered sibling `c'` of the `b`-side child `c` to the base classes at the cutoff
`es` (honest ⟹ `Xclass es`; byz ⟹ `BbadSet es ∪ SpentSet es σ`). Both are the
*proven* lemmas `Confinement.honest_sibling_confinement` and
`ByzVpre.byz_sibling_confinement` — this is the shared structural step left as
an explicit input by the lower-level reductions (`ByzVpre` is a leaf, and honest confinement is a convenience
lemma). Here the two Layer-0-mechanical domain premises — `ParentSlotLt`
(`store_parentSlotLt`) and the blanket walk domain (`store_walkKnownK`) — are
discharged from `SpecAssumptions`, and the sibling's `hc'`/`hpc'`/`hlo` are derived
from the fork-choice child membership (`mem_get_node_children_resolved` +
`filtered_subset_block_roots` + `ParentSlotLt`). The provenance (`hprov`), recorded
knownness (`hlmknown`), domination (`hdom`), and the `b`-side fork-edge geometry
(`hh`/`hpc`/`hbc`/`hlo_h`) stay as the enumerated per-endpoint residuals. -/



/-! ## Section 3 — the honest committee vote existence (`votes_head` consequence)

The `Sclass`-membership bridge and the `ρ = 0` partition both start from an honest
committee member's own ground vote. `honest_committee_vote` is `HonestBehavior.votes_head`
packaged: an honest validator assigned to slot `s` (with `s` at or after the anchor
slot) casts, at some second `n` with `slot_at n = s`, exactly the validator-spec
attestation computed from its own store — the `(n, honest_attestation …)` witness the
`SupportsDesc` predicate and `Delivery.vote_ubiquity` consume. -/

/-- **Honest committee members vote at their assigned slot** (`VoteLanding`). Direct
consequence of `HonestBehavior.votes_head`: an honest validator `v` assigned to slot
`s` (`s ≥ slot_at 0`) has a recorded vote at `s` equal to its own honest attestation
computed at the voting second `n` (`slot_at n = s`). This is the ground-vote witness
the pre-`T1` fresh-committee entry (`hSmono`) and the saturation crux (`hsat`) build on
via `Delivery.vote_ubiquity` + the `SupportsDesc` bridge. -/
theorem honest_committee_vote (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {s : Slot}
    (hcomm : v ∈ E.committee s) (hsH : E.SlotWithinHorizon cfg s)
    (hs0 : E.slot_at cfg 0 ≤ s) :
    ∃ (n : ℕ) (index : CommitteeIndex), E.slot_at cfg n = s ∧
      E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v) :=
  by
    obtain ⟨n, index, _hnH, hslot, hvote⟩ := hhb.votes_head v hv s hcomm hsH hs0
    exact ⟨n, index, hslot, hvote⟩

/-! ## Section 4 — the `ρ = 0` same-epoch partition (`hρ0`)

`IHMechanize.hdeltas_of_monotone`'s `hρ0` asks that the honest committee of slot
`σ'+1` is covered by the base-supporter recurrence (`Unrec σ' \ Unrec (σ'+1)`) plus
the honest window growth (`span lo (σ'+1) \ span lo σ'`) — the `ξ = α = 0` witness of
the migrant existential. In the **strict same-epoch** regime (every slot of the window
`[lo, σ']` sits in `epoch(σ'+1)`), a slot-`σ'+1` honest committee member cannot also be
assigned anywhere in `[lo, σ']`: `committee_assignment_unique` would force that slot to
be `σ'+1` itself. So the honest committee of `σ'+1` is **entirely fresh** — contained in
the window-growth set — and `hρ0` holds with the `Unrec`-difference contribution merely
non-negative. This is the tentative (current-epoch) loop's `ρ = 0`; the crossing
(previous-epoch) regime has earlier-epoch recurrers and uses the explicit
`ξ`/`α > 0` migration inputs. -/


/-! ## Section 5 — the IHMechanize-facing compositions

The two clean compositions delivering the `EdgeInputResidual` fields directly from
the reduced cruxes: `hmaj` from support saturation + the `Jspec` lower bound, and
`hdeltas` from the two migration monotonicities with `hρ0` discharged in the
same-epoch regime. -/



end Execution

end FastConfirmation.Spec

end
