module
public import FastConfirmationModel
public import FastConfirmationStatements.Traces
public import FastConfirmationStatements.Premises.LiveMonotonicity
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions

@[expose] public section

/-!
# Premises/FCRCallPremises

Completed call and selected helper premises. States conditions on completed FCR calls and selected helper results.
-/

section

/-! ## Selected call support -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
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

/-- Support provisos for prediction helpers actually used by one
selector call. `current_target` covers the tentative edges that cross to a
later epoch. `selected_previous_result_no_conflict` covers the final
no-conflict guard in a non-start slot with descendant support. The proof
does not need a proviso for retained previous-loop edges. -/
structure FCRPredictionSupportAt (E : Execution Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  current_target : ∀ a c : Root,
    CurrentTargetSelectedEdge cfg ext fcrStore latestConfirmedRoot a c →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  /-- The final tentative stage can return a previous-epoch result. In a
  non-start slot the wrapper's final guard uses the no-conflict helper, so
  every later honest target must descend from the selected result. The
  target need not equal the caller's current target. -/
  selected_previous_result_no_conflict : ∀ result : Root,
    find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot = result →
    result ≠ latestConfirmedRoot →
    get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store →
    is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true →
    HonestVotesTargetDescendFrom cfg E result
      (get_current_store_epoch cfg fcrStore.store) q

end FastConfirmation.Spec

end

section

/-! ## Completed call premises -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root}
/-- Primitive bundle left after replaying the completed scheduled prefix.

The first five fields are direct protocol/model contracts.  `balance_floor`
excludes the executable helper's artificial empty-active-set minimum-balance
branch. `delivery_lookahead` is the paper-synchrony boundary closure for
honest votes created inside the prefix. `helper_provisos` states exact
current-target support and previous-result descendant support. It applies
only when the outer evaluator's descendant-selector guard is true.

Everything else needed by the accepted target gate--causal replay, current
slot, latest-message provenance, non-equivocation, committee accounting,
pulled-up registry and total balance, target geometry, anchor horizon, and
current-epoch-end horizon--is derived in this module or upstream. -/
structure CompletedFCRCallPremises : Prop where
  synchrony : NextSlotSynchronyPremises cfg ext E
  static_validators : StaticValidatorSet cfg E
  byzantine_bound : ByzantineWeightPremises cfg E
  phase0_source : Phase0SourceCoherence cfg ext
  phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext
  balance_floor : cfg.effective_balance_increment ≤
    E.weight (E.currentTargetAnchorActive cfg)
  delivery_lookahead : HorizonVoteDeliveryLookahead cfg E
  helper_provisos : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.IsScheduledFCRCallAt cfg ext v n → E.WithinHorizon cfg (n + 1) →
      getLatestSelectorGuard cfg (E.fcrStoreAtCall cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved →
        FCRPredictionSupportAt cfg ext E v (n + 1)
          (E.fcrStoreAtCall cfg ext v n)
          (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved

end Execution
end FastConfirmation.Spec

end

end
