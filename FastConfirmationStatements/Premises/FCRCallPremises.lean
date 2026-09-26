module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.LiveMonotonicity
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions

@[expose] public section

/-!
Defines delivery, stake, source, and horizon conditions for scheduled FCR calls.
Prediction support follows from the safety proof's call and endpoint induction.
-/

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
