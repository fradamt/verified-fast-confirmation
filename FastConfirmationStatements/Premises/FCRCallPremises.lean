module
public import FastConfirmationModel
public import FastConfirmationStatements.Traces
public import FastConfirmationStatements.Premises.LiveMonotonicity
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions

@[expose] public section

/-!
# Premises/FCRCallPremises

Completed call premises state the remaining conditions on scheduled FCR calls.
-/

section

/-! ## Selected call support -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- From the call slot on, each honest vote of epoch `e` targets a root
that descends from `result` in the execution's parent graph. This is the
support needed by paper Lemma 42 for a previous-epoch selected result. It
allows honest voters to use different epoch-boundary checkpoints. -/
def HonestVotesTargetDescendFrom (E : Execution Root)
    (result : Root) (e : Epoch) (q : ℕ) : Prop :=
  E.WithinHorizon cfg q ∧
    ∀ w ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = e → E.slot_at cfg q ≤ s →
      ∀ k a, E.vote w s = some (k, a) →
        a.data.target.epoch = e ∧ E.RootDescends a.data.target.root result


end FastConfirmation.Spec

end

section

/-! ## Completed call premises -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable {E : Execution Root}
/-- Primitive bundle left after replaying the completed scheduled prefix.

The first five fields are direct protocol/model contracts.  `balance_floor`
excludes the executable helper's artificial empty-active-set minimum-balance
branch. `delivery_lookahead` is the paper-synchrony boundary closure for
honest votes created inside the prefix. Prediction support is derived by
joint induction over calls and endpoint slots.

Everything else needed by the accepted target gate--causal replay, current
slot, latest-message provenance, non-equivocation, committee accounting,
pulled-up registry and total balance, target geometry, anchor horizon, and
current-epoch-end horizon--is derived in this module or upstream. -/
structure ScheduledFCRCallPremises : Prop where
  synchrony : NextSlotSynchronyPremises cfg ext E
  static_validators : StaticValidatorSet cfg E
  byzantine_bound : ByzantineWeightPremises cfg E
  phase0_source : Phase0SourceCoherence cfg ext
  phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext
  balance_floor : cfg.effective_balance_increment ≤
    E.weight (E.currentTargetAnchorActive cfg)
  delivery_lookahead : HorizonVoteDeliveryLookahead cfg E

end Execution
end FastConfirmation.Spec

end

end
