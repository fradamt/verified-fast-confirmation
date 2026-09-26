module
public import FastConfirmationModel

@[expose] public section

/-! Trajectory safety predicates shared by internal proofs. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- **The trajectory predicate.** From second `n` on, the safe block `b` is an
ancestor of every honest node's fork-choice head. This is `EngineInv` with the
cutoff-slot cap removed (`∀ k` folded in), retaining the pinned executable
spec's current-moment claim. -/
def SafeFrom (b : Root) (n : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root b) = true

end Execution
end FastConfirmation.Spec

end
