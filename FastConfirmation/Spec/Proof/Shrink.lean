import FastConfirmation.Spec.Proof.LastCruxes
import FastConfirmation.Spec.Proof.Cruxes

/-!
# Spec / Proof / Shrink: the minimal input bundle (retired)

This module held the two final-shrink headlines `Spec_Safety_shrunk` /
`Spec_Monotonicity_shrunk`, which reduced `Spec_Safety` / `Spec_Monotonicity` to
`SameSlotFinalizedRootKnownNonGenesis` + `EngineGroundResiduals`.

Both belonged to the legacy `SpecAssumptions` observed-anchor cone and are deleted (P-6): they
carried `AheadFacade`'s ahead-regime head-tracking premise, which nothing in the
development ever produced and which no audited witness reached. The module now carries only
the note below. See `docs/p6-justified-descends-derivation.md` §8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Deleted: the final-shrink headlines

`Spec_Safety_shrunk` and `Spec_Monotonicity_shrunk` stood here — `Spec_Safety` /
`Spec_Monotonicity` from `SameSlotFinalizedRootKnownNonGenesis` + `EngineGroundResiduals`,
composing `INVstarTrack.Spec_Safety_of_ground` with the genesis reduction of the same-slot
corner. Both carried the unproduced ahead-regime
head-tracking premise `htracks`, both were unconsumed roots (or fed one) of the legacy
`SpecAssumptions` observed-anchor cone, and both are deleted with it (P-6).

Nothing produced that premise, and the audited route does not need it:
`AcceptedObservedRestartDynamicSafety` proves `obs.epoch ≤ jc(w, n+1).epoch` at every honest
`w`, so the observed anchor never enters the ahead regime. See
`docs/p6-justified-descends-derivation.md` §8 and `docs/plumbing-spec-citations.md` P-6. -/

end FastConfirmation.Spec
