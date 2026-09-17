import FastConfirmation.Spec.Proof.ShellCompose

/-!
# Spec / Proof / Definitive: composition of the safety residuals

This module splits the transparent engine bundle `ShellCompose.EngineSafetyResiduals` into two
explicit hypothesis bundles: the **same-slot availability family**
(`StrongPrefixSafety.SameSlotFinalizedRootKnown`, the cleanly-isolated cross-node reset corner)
and the **engine store-dynamics residuals** (`EngineOpenResiduals`, the head-safety induction's
explicit base premises at every slot regime). `engineSafetyResiduals_of_split` rebuilds
`EngineSafetyResiduals` from the two.

The two conditional headlines that used to close this split into `Spec_Safety` /
`Spec_Monotonicity` are deleted with the legacy `SpecAssumptions` observed-anchor cone (P-6);
see the Section 2 note below.

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

/-! ## Section 2 — deleted: the conditional safety and monotonicity results

`Spec_Safety_of_sameSlot_and_engine` and `Spec_Monotonicity_of_sameSlot_and_engine` stood here.
They composed `engineSafetyResiduals_of_split` with
`ShellCompose.Spec_Safety_of_engineResiduals`, carrying the unproduced ahead-regime head-tracking premise `htracks`. Both are unconsumed roots of the legacy
`SpecAssumptions` observed-anchor cone and are deleted with it (P-6). The two input bundles —
`EngineOpenResiduals` and the split `engineSafetyResiduals_of_split` — are unaffected. See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
