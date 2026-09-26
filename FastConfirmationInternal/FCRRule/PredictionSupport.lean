module
public import FastConfirmationStatements.Premises.FCRCallPremises

/-!
Prediction-support proof vocabulary records exact and descendant vote targets.
The joint safety and history induction derives these facts. They are not
fields of the safety premise.
-/

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- Derived support for prediction helpers used by one
selector call. `current_edge_vote_support` covers the tentative edges that cross to a
later epoch. `previous_result_vote_support` covers the final
no-conflict guard in a non-start slot with descendant support. The safety premise does not contain this record. Generic proof adapters and
concrete run facts retain it without changing their declaration names. -/
structure SelectedPredictionVoteSupport (E : Execution Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  current_edge_vote_support : ∀ a c : Root,
    CurrentTargetSelectedEdge cfg ext fcrStore latestConfirmedRoot a c →
    HonestVotesSupportTarget cfg E
      (get_current_target cfg fcrStore.store) q
  /-- The final tentative stage can return a previous-epoch result. In a
  non-start slot the wrapper's final guard uses the no-conflict helper, so
  every later honest target must descend from the selected result. The
  target need not equal the caller's current target. -/
  previous_result_vote_support : ∀ result : Root,
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
