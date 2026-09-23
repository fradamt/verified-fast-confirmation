module
public import FastConfirmation.Spec.Model.Config

@[expose] public section

/-!
# Config model facts

Proofs about Model/Config. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
theorem mainnet_epochEndsFitUint64 : EpochEndsFitUint64 mainnet_config := by
  refine ⟨2 ^ 59, ?_⟩
  norm_num [EpochEndsFitUint64, UINT64_MAX, mainnet_config]

end FastConfirmation.Spec

end
