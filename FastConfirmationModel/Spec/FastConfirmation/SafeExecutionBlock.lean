module
public import FastConfirmationModel.Spec.ForkChoice
public import FastConfirmationModel.Spec.FastConfirmation.Store

@[expose] public section

/-! SafeExecutionBlock declarations from FastConfirmation.Spec.Model.FCRStore. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
/-- `get_safe_execution_block_hash`
(`specs/gloas/fast-confirmation.md:38`). Only the parent payload of the
confirmed beacon block is safe. -/
def get_safe_execution_block_hash (fcr_store : FastConfirmationStore Root) : Root :=
  (fcr_store.store.blocks fcr_store.confirmed_root).parent_block_hash

end FastConfirmation.Spec

end
