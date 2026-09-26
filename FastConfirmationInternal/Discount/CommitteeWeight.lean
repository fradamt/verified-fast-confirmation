module
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-! Defines the honest committee weight `Jspec` over a slot span. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- `J_b`: honest committee-union weight over the slot span `[a, b]` (paper `J`,
`Weights.lean`). -/
def Jspec (a b : Slot) : Gwei :=
  E.weight ((E.span_committee a b).filter (fun i => i ∈ E.honest))

end Execution

end FastConfirmation.Spec

end
