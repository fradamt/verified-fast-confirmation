module
public import FastConfirmation.Spec.Proof.AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample

@[expose] public section

/-!
# A one-slot head ancestry obstruction

The live economic bounds are total-stake bounds. They do not force one slot's
honest committee weight to exceed the proposer boost. This executable store
has a delivered honest vote for a slot-two block, but a newly boosted sibling
is the head at slot three. The configuration retains the accepted 25 percent
confirmation threshold and meets both live arithmetic margins with zero
non-honest stake.
-/

namespace FastConfirmation.Spec
namespace MonotonicityLiveHeadCounterexample

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

open AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample





























end MonotonicityLiveHeadCounterexample
end FastConfirmation.Spec

end
