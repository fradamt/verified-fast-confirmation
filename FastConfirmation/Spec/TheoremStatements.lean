module
public import FastConfirmation.Spec.Internal.Legacy.Vocabulary
public import FastConfirmation.Spec.Proof.WeakFCRCallContracts

@[expose] public section

/-! Open weak live monotonicity statement. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Weak-rule counterpart of `Spec_Monotonicity_live`, with the same live
block, vote, and timely-checkpoint assumptions. The `acceptedWeak` parameter
is instantiated downstream with the accepted FFG and weak observer premises
used by the weak safety witnesses. The conclusion concerns the weak observer's
stored output, and is the executable weak-synchrony version of the
monotonicity half of paper Theorem 1. -/
def WeakSpec_Monotonicity_live
    (acceptedWeak : Execution Root → ValidatorIndex → Prop) : Prop :=
  ∀ E : Execution Root, ∀ v : ValidatorIndex, acceptedWeak E v →
    ∀ n m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      MonotonicityLiveAssumptions cfg ext E v n m →
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.weakConfirmed cfg ext v m))
        (get_node_for_root (E.weakConfirmed cfg ext v n)) = true

end FastConfirmation.Spec

end
