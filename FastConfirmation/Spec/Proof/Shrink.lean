import FastConfirmation.Spec.Proof.LastCruxes
import FastConfirmation.Spec.Proof.Cruxes

/-!
# Spec / Proof / Shrink: the minimal input bundle

`INVstarTrack.Spec_Safety_of_ground` reduces `Spec_Safety` to
`SameSlotFinalizedRootKnown` and `EngineGroundResiduals`. The genesis case of the first
component follows from within-node `StoreLE`, leaving
`SameSlotFinalizedRootKnownNonGenesis`. Thus the facade below depends on exactly:

* `SameSlotFinalizedRootKnownNonGenesis`, the non-genesis, below-anchor, same-slot
  reset-root knownness condition. `LastCruxes.mem_of_is_ancestor_above_anchor`
  handles roots above the anchor, while the `block_relay` theorem requires a
  strictly later slot for the remaining cross-node case.
* `EngineGroundResiduals`, consisting of the structural descent field
  `dynamics_struct` and the per-edge supply `fork_edges_ground`. Each supplied
  `ForkEdgeGroundInputs` contains the maintained `INVstar` certificate, honest
  confinement transports, and the ground-truth `Bval` sibling bounds.

The ground-truth `Bval` route does not require the recorded base-enemy transport
`hBb`: `Bval` is store-independent and bounded directly by `span_fraction` at
the endpoint. The store-dynamics lemmas `Cruxes.hPS_crux`, `hcov_crux`,
`hsat_crux`, and `hrec_crux` provide the named inputs used inside the engine.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The final-shrink headlines -/

/-- **`Spec_Safety` from the minimal input bundle.**

The public FCR safety guarantee follows from a proof that every execution's `SpecAssumptions`
supplies (i) `SameSlotFinalizedRootKnownNonGenesis` (the same-slot reset corner
with its genesis sub-case removed via within-node `StoreLE`) and (ii) the `hBb`-free engine bundle
`EngineGroundResiduals` (`dynamics_struct` + `fork_edges_ground`, the head-safety engine's base
mechanization on the store-independent ground-truth-`Bval` track).

This strengthens `INVstarTrack.Spec_Safety_of_ground` by discharging the genesis reset case,
so the same-slot assumption is confined to non-genesis reset anchors. -/
theorem Spec_Safety_shrunk
    (hSameSlot : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.SameSlotFinalizedRootKnownNonGenesis cfg ext)
    (hEng : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.EngineGroundResiduals cfg ext) :
    Spec_Safety cfg ext :=
  Spec_Safety_of_ground cfg ext
    (fun E hSA => E.sameSlotFinalizedRootKnown_of_nonGenesis cfg ext (hSameSlot E hSA)) hEng

/-- **`Spec_Monotonicity` from the minimal input bundle.** Chain consistency of an honest
node's confirmed roots follows
from the same minimal bundle (`SameSlotFinalizedRootKnownNonGenesis` + `EngineGroundResiduals`) plus the
single-store confirmed-root knownness residual `hck` (`confirmed v k ∈ (store v k).block_roots`,
lifted across time by within-node `StoreLE` — no cross-node relay). Composes `Spec_Safety_shrunk`
with `StrongPrefixSafety.spec_monotonicity_of_safety`, on exactly the same two input fields plus
`hck`. -/
theorem Spec_Monotonicity_shrunk
    (hSameSlot : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.SameSlotFinalizedRootKnownNonGenesis cfg ext)
    (hEng : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.EngineGroundResiduals cfg ext)
    (hck : ∀ E : Execution Root, SpecAssumptions cfg ext E → ∀ v ∈ E.honest, ∀ k : ℕ,
      E.WithinHorizon cfg k →
      E.confirmed cfg ext v k ∈ (E.store cfg ext v k).block_roots) :
    Spec_Monotonicity cfg ext :=
  spec_monotonicity_of_safety cfg ext (Spec_Safety_shrunk cfg ext hSameSlot hEng)
    (hkc_of_confirmed_known cfg ext hck)

end FastConfirmation.Spec
