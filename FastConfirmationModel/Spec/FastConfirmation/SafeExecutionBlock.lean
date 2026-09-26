module
public import FastConfirmationModel.Spec.ForkChoice
public import FastConfirmationModel.Spec.FastConfirmation.Store

@[expose] public section

/-! Defines the Gloas safe execution block hash selector from the confirmed block's parent payload. Python: `specs/gloas/fast-confirmation.md`, `get_safe_execution_block_hash`. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- `get_safe_execution_block_hash`
(`specs/gloas/fast-confirmation.md:113-116` at fork commit `13f391516`). Only the parent payload of the
confirmed beacon block is safe. -/
def get_safe_execution_block_hash (fcr_store : FastConfirmationStore Root) : Root :=
  (fcr_store.store.blocks fcr_store.confirmed_root).parent_block_hash

end FastConfirmation.Spec

end
