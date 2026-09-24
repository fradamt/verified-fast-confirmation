module
public import FastConfirmationStatements.Premises.SelectedMargin
public import FastConfirmationStatements.Premises.FCRCallPremises

@[expose] public section

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)

/-- The part of `E.CompletedFCRCallPremises` that is
**not** already contained in `SelectedMarginAssumptions`: the two phase-0
source-coherence contracts and the anchor-active balance floor.

The full 6-field call contract additionally carries `synchrony`,
`static_validators` and `byzantine_bound`, which are literally three fields of
`SelectedMarginAssumptions` — a record every weak trajectory headline already
carries inside `hW.base`.  Taking those three a second time would only
double-count the premise *surface*, so the headlines take this 3-field
supplement and rebuild the full contract internally with
`toCompletedPrefixCallAssumptions` below.

The fourth field restores the vote receipt at the last horizon boundary.
It is the `delivery_lookahead` field of the completed-call package. -/
structure WeakCompletedFCRCallSupplement : Prop where
  phase0_source : Phase0SourceCoherence cfg ext
  phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext
  balance_floor : cfg.effective_balance_increment ≤
    E.weight (E.currentTargetAnchorActive cfg)
  delivery_lookahead : HorizonVoteDeliveryLookahead cfg E

end Execution
end FastConfirmation.Spec

end
