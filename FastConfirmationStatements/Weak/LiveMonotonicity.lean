module
public import FastConfirmationStatements.Premises.LiveMonotonicity
public import FastConfirmationModel.Weak.Execution
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-! Open weak live monotonicity statement. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The open weak claim uses the two common live fields and the configured
threshold margin. The weak adversarial budget does not subtract equivocation,
so the strong epoch-boundary argument does not carry over; see W7. -/
structure WeakLiveMonotonicityPremises (E : Execution Root)
    (v : ValidatorIndex) (n m : ℕ) : Prop extends
    LiveMonotonicityPremises cfg ext E v n m where
  configured_threshold_margin :
    2 * E.weight ((Finset.range E.registry.length).filter fun i =>
      i ∉ E.honest ∧
        is_active_validator (E.registry.getD i default)
          (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true) +
      2 * (E.total_active cfg / 100 * cfg.confirmation_byzantine_threshold) +
      compute_proposer_score cfg E.anchor_state < E.total_active cfg

/-- Weak-rule counterpart of `ConfirmedRootMonotonicity`, with the common live block and timely-checkpoint fields plus the
configured threshold margin. This statement is open: the weak adversarial
budget does not subtract equivocation, so the strong epoch-boundary argument
does not carry over; see W7. The `acceptedWeak` parameter
is instantiated downstream with the accepted FFG and weak observer premises
used by the weak safety witnesses. The conclusion concerns the weak observer's
stored output, and is the executable weak-synchrony version of the
monotonicity half of paper Theorem 1. -/
def WeakSpec_Monotonicity_live
    (acceptedWeak : Execution Root → ValidatorIndex → Prop) : Prop :=
  ∀ E : Execution Root, ∀ v : ValidatorIndex, acceptedWeak E v →
    ∀ n m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      WeakLiveMonotonicityPremises cfg ext E v n m →
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.weakConfirmed cfg ext v m))
        (get_node_for_root (E.weakConfirmed cfg ext v n)) = true

end FastConfirmation.Spec

end
