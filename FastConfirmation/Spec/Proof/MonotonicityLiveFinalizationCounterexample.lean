module
public import FastConfirmation.Spec.Proof.AcceptedActualFCRJointNonVacuityFinal

@[expose] public section

/-!
# First-boundary finalization counterexample

The accepted finalization delay has an anchor exception. At the first epoch
boundary, the finalized checkpoint can still be the anchor at the start of
the previous epoch. Thus the strict inequality proposed as L3 in the live
monotonicity plan is false. This witness uses an actual accepted execution
and an actual boundary FCR call.
-/

namespace FastConfirmation.Spec
namespace MonotonicityLiveFinalizationCounterexample

open AcceptedActualFCRJointNonVacuityBase
open AcceptedActualFCRJointNonVacuityFinal

-- Reduction of the finite execution needs a deeper recursion limit.

end MonotonicityLiveFinalizationCounterexample
end FastConfirmation.Spec

end
