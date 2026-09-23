module
public import FastConfirmation.Spec.Model
public import FastConfirmation.Spec.Statements.Traces
public import FastConfirmation.Spec.Statements.Premises.Live
public import FastConfirmation.Spec.Statements.Premises.FFG
public import FastConfirmation.Spec.Statements.Premises.Execution

@[expose] public section

/-!
# Premises/Trajectory

Completed call and selected helper premises. Reads the Spec Model and earlier Statements modules. Read Claims next.
-/

section

/-! ## From SelectedTraceFilterPipeline -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
/-- Normative support provisos for prediction helpers actually used by one
selector call.  Epoch-start short-circuit paths carry no no-conflict proviso,
because that helper need not be evaluated there. -/
structure SelectedHelperProvisosAt (E : Execution Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  current_target : ∀ a c : Root,
    CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  no_conflict : ∀ a c : Root,
    PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  /-- The final tentative stage can return a previous-epoch result even when
  that result is not a retained previous-loop edge.  In a non-start slot the
  wrapper's final guard still used the same no-conflict helper, so its
  normative support proviso must be indexed by the selected result as well as
  by previous-loop edges. -/
  selected_previous_result_no_conflict : ∀ result : Root,
    find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot = result →
    result ≠ latestConfirmedRoot →
    get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q

namespace Execution
variable (E : Execution Root)
end Execution
end FastConfirmation.Spec

end

section

/-! ## From AcceptedHistoricalA32CallSupplier -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root}
/-- Primitive bundle left after replaying the completed scheduled prefix.

The first five fields are direct protocol/model contracts.  `balance_floor`
excludes the executable helper's artificial empty-active-set minimum-balance
branch. `delivery_lookahead` is the paper-synchrony boundary closure for
honest votes created inside the prefix. `helper_provisos` is the literal
normative proviso from the FCR specification, required only when the outer
evaluator's descendant-selector guard is true.

Everything else needed by the accepted target gate--causal replay, current
slot, latest-message provenance, non-equivocation, committee accounting,
pulled-up registry and total balance, target geometry, anchor horizon, and
current-epoch-end horizon--is derived in this module or upstream. -/
structure AcceptedHistoricalA32CompletedPrefixCallAssumptions : Prop where
  synchrony : PaperSafetySynchrony cfg ext E
  static_validators : StaticValidatorSet cfg E
  byzantine_bound : ByzantineBound cfg E
  phase0_source : Phase0SourceCoherence cfg ext
  phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext
  balance_floor : cfg.effective_balance_increment ≤
    E.weight (E.currentTargetAnchorActive cfg)
  delivery_lookahead : HorizonVoteDeliveryLookahead cfg E
  helper_provisos : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.IsFCRCallAt cfg ext v n → E.WithinHorizon cfg (n + 1) →
      getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved →
        SelectedHelperProvisosAt cfg ext E v (n + 1)
          (E.fcrStep cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved

end Execution
end FastConfirmation.Spec

end

end
