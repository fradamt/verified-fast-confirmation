module
public import FastConfirmationStatements.Traces

@[expose] public section

/-! The phased latest-confirmed evaluator used by internal proof calculations. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- The phased evaluator reconstructed from the three named guards. -/
def getLatestTraceResult
    (query : FastConfirmationStore Root) : Root :=
  let candidate := getLatestAfterObserved cfg ext query
  if get_block_epoch cfg query.store candidate + 1 ≥
      get_current_store_epoch cfg query.store then
    find_latest_confirmed_descendant cfg ext query candidate
  else
    candidate

/-- The named phased evaluator is definitionally the pinned executable
`get_latest_confirmed`. -/
theorem getLatestTraceResult_eq_getLatestConfirmed
    (query : FastConfirmationStore Root) :
    getLatestTraceResult cfg ext query = get_latest_confirmed cfg ext query := by
  rfl

end FastConfirmation.Spec

end
