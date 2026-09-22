module
public import FastConfirmation.Spec.Proof.ShellCompose

@[expose] public section

/-!
# Spec / Proof / Definitive: composition of the safety residuals

This module composes the FCR safety reduction chain:
`Spec_Safety_of_strongPrefix_inputs` (`Spec_Safety` → the 3-field
`StrongPrefixSafetyInputs`), `ShellCompose.Spec_Safety_of_engineResiduals`
(`Spec_Safety` → the transparent engine bundle `EngineSafetyResiduals`, with the
per-edge `ForkEdgeEngineInputs` fields the named engine residuals), the
class algebra (`LastAlgebra.vpreIdentities_of` behind `hbase`), and the closed
side conditions (`Identities.hjc_le_closed`, whose `PjfCheckpointEpoch` is now
discharged from `ExternalsCoherence.pjf_checkpoint_epoch`). It yields:

> `Spec_Safety` follows from two explicit hypothesis bundles: the **same-slot availability
> family** (`SameSlotFinalizedRootKnown`, the cleanly-isolated cross-node reset
> corner) and the **engine store-dynamics residuals** (`EngineOpenResiduals`, the
> head-safety induction's explicit base premises at every slot regime).

Both bundles reduce to `EngineSafetyResiduals`.

## Why there is no reduction to same-slot availability alone (and no next-slot outright form)

The economic core `fork_edges_engine` (`ForkEdgeEngineSupply`) is **not** eliminated —
its base mechanization (`hsat` full saturation, the block-relay `FreshEngineInputs`
behind `hdeltaIn`, the coverage floor `hcov`, and the recorded↔ground bridges behind
`VpreIdentities`) is represented by premises at **every** slot regime. The structural chain's
`hcase` (the cross-store L4 descent `b ⪰ jc(w,m)`) is a same-slot-sensitive fork-choice
fact the shell's own strong induction must supply. So:

* `EngineOpenResiduals` carries explicit store-dynamics premises that are **not**
  same-slot availability — it is uniform across slot regimes.
* `SameSlotFinalizedRootKnown` is only the **cleanly-isolated** same-slot availability field (the E5-reset
  corner); the same-slot corners of same-slot availability *also* live inside `dynamics_struct`'s
  `hb` and `fork_edges_engine`'s `hdeltaIn`/`hBb` same-slot legs (`ShellCompose`
  header), so this split does not remove those engine inputs.
* Consequently this reduction does not yield an outright next-slot-weakened `Spec_Safety`: the shell's
  strong induction visits same-slot base stores, and the engine base has premises at every
  slot. The later-slot regime only discharges the *reset-anchor knownness* corners
  (`FinalWiring.finalized_root_relay_known`, `hb_of_confirming`), not the engine.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — same-slot and engine input bundles

The same-slot availability family is `Execution.SameSlotFinalizedRootKnown`
(the cleanly-isolated cross-node reset corner). This module pairs it with the engine
store-dynamics residuals below. -/

/-- **The engine store-dynamics residuals** — the head-safety engine's explicit base
mechanization, uniform across slot regimes. The structural confirmed chain
(`dynamics_struct`, whose `hcase` is the cross-store L4 descent) and the transparent
per-edge engine supply (`fork_edges_engine` = `ForkEdgeEngineSupply`, whose
`ForkEdgeEngineInputs` fields are `hsat`, the block-relay `FreshEngineInputs` behind
`hdeltaIn`, `hcov`, `hnondeg`, the `VpreIdentities` behind `hbase`, and the sibling
confinements `hHon`/`hByz`). These premises are **not** same-slot availability
(though their same-slot legs additionally carry same-slot availability corners — see the module
header). Verbatim the non-`finalized_dom_sameslot` fields of
`ShellCompose.EngineSafetyResiduals`. -/
structure EngineOpenResiduals (E : Execution Root) : Prop where
  /-- `[E-struct]` — the structural confirmed chain, including the cross-store L4 descent `hcase`. -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- `[E-edges]` — the transparent per-edge engine supply per confirmed block. -/
  fork_edges_engine : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeEngineSupply cfg ext b (n + 1)

/-- **The split rebuilds `EngineSafetyResiduals`.** The two input bundles reassemble
`ShellCompose.EngineSafetyResiduals` verbatim: the same-slot availability field is `SameSlotFinalizedRootKnown`,
the two engine fields are `EngineOpenResiduals`. -/
theorem engineSafetyResiduals_of_split
    (hSameSlot : E.SameSlotFinalizedRootKnown cfg ext) (hEng : E.EngineOpenResiduals cfg ext) :
    E.EngineSafetyResiduals cfg ext :=
  { finalized_dom_sameslot := hSameSlot
    dynamics_struct := hEng.dynamics_struct
    fork_edges_engine := hEng.fork_edges_engine }

end Execution

/-! ## Section 2 — the conditional safety result -/

/-- **`Spec_Safety` from the same-slot and engine input bundles.** FCR safety
follows from a proof that every execution's `SpecAssumptions` supplies
(i) the cleanly-isolated same-slot availability family (`SameSlotFinalizedRootKnown`), and (ii) the
engine store-dynamics residuals (`EngineOpenResiduals` — the head-safety induction's explicit
base mechanization, uniform across slot regimes). Composes `engineSafetyResiduals_of_split`
with `ShellCompose.Spec_Safety_of_engineResiduals`.

This headline uses only Lean's standard axioms `propext`, `Classical.choice`, and
`Quot.sound`, with no project axiom: the whole reduction from the public `Spec_Safety` down to these two
bundles is machine-checked. The two bundles state the same-slot input (i) and the engine
base premises (ii). This theorem does not reduce the proof to same-slot availability
alone, and hence no outright next-slot-weakened `Spec_Safety` (module header). -/
theorem Spec_Safety_of_sameSlot_and_engine
    (hSameSlot : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.SameSlotFinalizedRootKnown cfg ext)
    (hEng : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.EngineOpenResiduals cfg ext) :
    Spec_Safety cfg ext :=
  Spec_Safety_of_engineResiduals cfg ext
    (fun E hSA => E.engineSafetyResiduals_of_split cfg ext (hSameSlot E hSA) (hEng E hSA))

/-- **`Spec_Monotonicity` from the two input bundles and confirmed-root knownness.**
Chain consistency of an honest node's confirmed roots follows from the same two
input bundles plus the single-store confirmed-root knownness premise `hck` (via
`hkc_of_confirmed_known`, within-node `StoreLE`). Composes `Spec_Safety_of_sameSlot_and_engine` with
`spec_monotonicity_of_safety`. -/
theorem Spec_Monotonicity_of_sameSlot_and_engine
    (hSameSlot : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.SameSlotFinalizedRootKnown cfg ext)
    (hEng : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.EngineOpenResiduals cfg ext)
    (hck : ∀ E : Execution Root, SpecAssumptions cfg ext E → ∀ v ∈ E.honest, ∀ k : ℕ,
      E.WithinHorizon cfg k →
      E.confirmed cfg ext v k ∈ (E.store cfg ext v k).block_roots) :
    Spec_Monotonicity cfg ext :=
  spec_monotonicity_of_safety cfg ext (Spec_Safety_of_sameSlot_and_engine cfg ext hSameSlot hEng)
    (hkc_of_confirmed_known cfg ext hck)

end FastConfirmation.Spec

end
