module
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-! Defines the honest committee weight `Jspec` over a slot span. Paper `J` uses [arXiv:2405.00549v4](https://arxiv.org/abs/2405.00549v4). -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- `J_b`: honest committee-union weight over the slot span `[a, b]` (paper `J`). -/
def Jspec (a b : Slot) : Gwei :=
  E.weight ((E.span_committee a b).filter (fun i => i ∈ E.honest))

end Execution

end FastConfirmation.Spec

end
