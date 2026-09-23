module
public import FastConfirmation.Spec.Proof.FCRCallContracts

public import FastConfirmation.Spec.Statements.Traces
@[expose] public section

/-!
# Exact evaluator provenance for `get_latest_confirmed`

The three roots read by `get_latest_confirmed` may coincide.  A result-only
disjunction therefore cannot identify which guard actually fired.  This file
mirrors the ordered lets of the executable definition and retains the branch
proof at each phase:

1. carry the cached root or revert to finalized;
2. retain that candidate or restart from the observed checkpoint;
3. invoke the descendant selector or return the candidate unchanged.

The trace is defined for an arbitrary `FastConfirmationStore`.  It contains
no knownness, certificate, payload, ancestry, canonicity, or safety result.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The three exact executable guards -/


/-! ## Branch-indexed phase traces -/

namespace GetLatestFinalizedPhase

theorem branch_cases
    {query : FastConfirmationStore Root} {candidate : Root}
    (h : GetLatestFinalizedPhase cfg ext query candidate) :
    (candidate = query.confirmed_root ∧
        ¬ getLatestFinalizedRevertGuard cfg ext query) ∨
      (candidate = query.store.finalized_checkpoint.root ∧
        getLatestFinalizedRevertGuard cfg ext query) := by
  cases h with
  | carried hfalse => exact Or.inl ⟨rfl, hfalse⟩
  | reverted htrue => exact Or.inr ⟨rfl, htrue⟩

end GetLatestFinalizedPhase

namespace GetLatestObservedPhase

theorem branch_cases
    {query : FastConfirmationStore Root} {before after : Root}
    (h : GetLatestObservedPhase cfg query before after) :
    (after = before ∧
        getLatestObservedRestartGuard cfg query before = false) ∨
      (after = query.current_epoch_observed_justified_checkpoint.root ∧
        getLatestObservedRestartGuard cfg query before = true) := by
  cases h with
  | unchanged hfalse => exact Or.inl ⟨rfl, hfalse⟩
  | restarted htrue => exact Or.inr ⟨rfl, htrue⟩

end GetLatestObservedPhase

namespace GetLatestSelectorPhase

theorem branch_cases
    {query : FastConfirmationStore Root} {input result : Root}
    (h : GetLatestSelectorPhase cfg ext query input result) :
    (result = input ∧ ¬ getLatestSelectorGuard cfg query input) ∨
      (result = find_latest_confirmed_descendant cfg ext query input ∧
        getLatestSelectorGuard cfg query input) := by
  cases h with
  | unchanged hfalse => exact Or.inl ⟨rfl, hfalse⟩
  | selected htrue => exact Or.inr ⟨rfl, htrue⟩

end GetLatestSelectorPhase

/-! ## Canonical evaluator trace and projections -/

namespace GetLatestConfirmedTrace

/-- The post-finalized candidate is classified by the actual first guard,
not by comparing its root with the two possible values. -/
theorem afterFinalized_cases
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query) :
    (trace.afterFinalized = query.confirmed_root ∧
        ¬ getLatestFinalizedRevertGuard cfg ext query) ∨
      (trace.afterFinalized = query.store.finalized_checkpoint.root ∧
        getLatestFinalizedRevertGuard cfg ext query) :=
  trace.finalized.branch_cases

/-- The post-observed candidate is classified by the actual second guard. -/
theorem afterObserved_cases
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query) :
    (trace.afterObserved = trace.afterFinalized ∧
        getLatestObservedRestartGuard cfg query trace.afterFinalized = false) ∨
      (trace.afterObserved =
          query.current_epoch_observed_justified_checkpoint.root ∧
        getLatestObservedRestartGuard cfg query trace.afterFinalized = true) :=
  trace.observed.branch_cases

/-- Exact final branch: either the selector ran on the retained candidate or
the evaluator returned that candidate unchanged. -/
theorem selector_cases
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query) :
    (trace.result = trace.afterObserved ∧
        ¬ getLatestSelectorGuard cfg query trace.afterObserved) ∨
      (trace.result = find_latest_confirmed_descendant cfg ext query
          trace.afterObserved ∧
        getLatestSelectorGuard cfg query trace.afterObserved) :=
  trace.selector.branch_cases

/-- The exact result equation when the final selector guard is active.

Unlike the carried-only projection used by the first historical wrapper, this
form is deliberately indexed by `trace.afterObserved`; it therefore applies
unchanged to finalized and observed reset inputs.
-/
theorem selected_facts
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved) :
    trace.result = find_latest_confirmed_descendant cfg ext query
      trace.afterObserved := by
  rcases trace.selector_cases with ⟨_hresult, hfalse⟩ |
      ⟨hresult, _htrue⟩
  · exact False.elim (hfalse hselector)
  · exact hresult


/-- An active observed restart exposes all four conjuncts of the exact guard,
including the previous-epoch equation and the stale comparison against the
candidate *after* finalized processing. -/
theorem observedRestart_facts
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hactive : getLatestObservedRestartGuard cfg query
      trace.afterFinalized = true) :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∧
      get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store ∧
      query.current_epoch_observed_justified_checkpoint =
        query.store.unrealized_justifications
          (get_head cfg query.store).root ∧
      get_block_slot query.store trace.afterFinalized <
        get_block_slot query.store
          query.current_epoch_observed_justified_checkpoint.root := by
  simp only [getLatestObservedRestartGuard, Bool.and_eq_true,
    decide_eq_true_eq] at hactive
  exact ⟨hactive.1.1.1, hactive.1.1.2, hactive.1.2, hactive.2⟩

end GetLatestConfirmedTrace

/-! ## Actual-call specialization -/

namespace Execution

variable (E : Execution Root)


end Execution


end FastConfirmation.Spec

end
