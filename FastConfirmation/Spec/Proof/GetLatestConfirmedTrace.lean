module
public import FastConfirmation.Spec.Proof.FCRCallContracts

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

/-- The first guard, before any finalized reset has occurred. -/
def getLatestFinalizedRevertGuard
    (query : FastConfirmationStore Root) : Prop :=
  get_block_epoch cfg query.store query.confirmed_root + 1 <
      get_current_store_epoch cfg query.store ∨
    ¬ is_ancestor query.store
      (get_node_for_root (get_head cfg query.store).root)
      (get_node_for_root query.confirmed_root) ∨
    (is_start_slot_at_epoch cfg (get_current_slot cfg query.store) ∧
      ¬ is_confirmed_chain_safe cfg ext query query.confirmed_root)

/-- Candidate after the finalized-revert phase. -/
def getLatestAfterFinalized
    (query : FastConfirmationStore Root) : Root :=
  if get_block_epoch cfg query.store query.confirmed_root + 1 <
        get_current_store_epoch cfg query.store ∨
      ¬ is_ancestor query.store
        (get_node_for_root (get_head cfg query.store).root)
        (get_node_for_root query.confirmed_root) ∨
      (is_start_slot_at_epoch cfg (get_current_slot cfg query.store) ∧
        ¬ is_confirmed_chain_safe cfg ext query query.confirmed_root) then
    query.store.finalized_checkpoint.root
  else
    query.confirmed_root

/-- The second Boolean guard, parameterized by the candidate produced by the
first phase.  In particular, its stale comparison is not made against the
original cached root when the finalized guard fired. -/
def getLatestObservedRestartGuard
    (query : FastConfirmationStore Root) (candidate : Root) : Bool :=
  is_start_slot_at_epoch cfg (get_current_slot cfg query.store) &&
    decide (get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg query.store) &&
    decide (query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (get_head cfg query.store).root) &&
    decide (get_block_slot query.store candidate <
      get_block_slot query.store
        query.current_epoch_observed_justified_checkpoint.root)

/-- Candidate after the observed-restart phase. -/
def getLatestAfterObserved
    (query : FastConfirmationStore Root) : Root :=
  let afterFinalized := getLatestAfterFinalized cfg ext query
  if getLatestObservedRestartGuard cfg query afterFinalized then
    query.current_epoch_observed_justified_checkpoint.root
  else
    afterFinalized

/-- The final recency guard deciding whether the descendant selector runs. -/
def getLatestSelectorGuard
    (query : FastConfirmationStore Root) (candidate : Root) : Prop :=
  get_block_epoch cfg query.store candidate + 1 ≥
    get_current_store_epoch cfg query.store

/-- The phased evaluator reconstructed from the three named guards. -/
def getLatestTraceResult
    (query : FastConfirmationStore Root) : Root :=
  let candidate := getLatestAfterObserved cfg ext query
  if get_block_epoch cfg query.store candidate + 1 ≥
      get_current_store_epoch cfg query.store then
    find_latest_confirmed_descendant cfg ext query candidate
  else
    candidate

/-- The named phased evaluator is definitionally the pinned executable
`get_latest_confirmed`. -/
theorem getLatestTraceResult_eq_getLatestConfirmed
    (query : FastConfirmationStore Root) :
    getLatestTraceResult cfg ext query = get_latest_confirmed cfg ext query := by
  rfl

/-! ## Branch-indexed phase traces -/

/-- Exact provenance for the first phase. -/
inductive GetLatestFinalizedPhase
    (query : FastConfirmationStore Root) : Root → Prop
  | carried
      (guard_false : ¬ getLatestFinalizedRevertGuard cfg ext query) :
      GetLatestFinalizedPhase query query.confirmed_root
  | reverted
      (guard_true : getLatestFinalizedRevertGuard cfg ext query) :
      GetLatestFinalizedPhase query query.store.finalized_checkpoint.root

/-- Exact provenance for the second phase. -/
inductive GetLatestObservedPhase
    (query : FastConfirmationStore Root) (before : Root) : Root → Prop
  | unchanged
      (guard_false : getLatestObservedRestartGuard cfg query before = false) :
      GetLatestObservedPhase query before before
  | restarted
      (guard_true : getLatestObservedRestartGuard cfg query before = true) :
      GetLatestObservedPhase query before
        query.current_epoch_observed_justified_checkpoint.root

/-- Exact provenance for the final phase. -/
inductive GetLatestSelectorPhase
    (query : FastConfirmationStore Root) (input : Root) : Root → Prop
  | unchanged
      (guard_false : ¬ getLatestSelectorGuard cfg query input) :
      GetLatestSelectorPhase query input input
  | selected
      (guard_true : getLatestSelectorGuard cfg query input) :
      GetLatestSelectorPhase query input
        (find_latest_confirmed_descendant cfg ext query input)

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

/-- Complete ordered evaluator trace.  Intermediate roots are data, while
each phase proof fixes their operational provenance independently of any root
equalities. -/
structure GetLatestConfirmedTrace
    (query : FastConfirmationStore Root) where
  afterFinalized : Root
  afterObserved : Root
  result : Root
  finalized : GetLatestFinalizedPhase cfg ext query afterFinalized
  observed : GetLatestObservedPhase cfg query afterFinalized afterObserved
  selector : GetLatestSelectorPhase cfg ext query afterObserved result
  result_eq : result = get_latest_confirmed cfg ext query

/-! ## Canonical evaluator trace and projections -/

/-- Every arbitrary query store has an exact evaluator trace. -/
def getLatestConfirmedTrace
    (query : FastConfirmationStore Root) :
    GetLatestConfirmedTrace cfg ext query := by
  let afterFinalized := getLatestAfterFinalized cfg ext query
  let afterObserved := getLatestAfterObserved cfg ext query
  let result := getLatestTraceResult cfg ext query
  refine {
    afterFinalized := afterFinalized
    afterObserved := afterObserved
    result := result
    finalized := ?_
    observed := ?_
    selector := ?_
    result_eq := ?_
  }
  · dsimp only [afterFinalized, getLatestAfterFinalized]
    by_cases hguard : getLatestFinalizedRevertGuard cfg ext query
    · have hnamed := hguard
      simp only [getLatestFinalizedRevertGuard] at hguard
      rw [if_pos hguard]
      exact .reverted hnamed
    · have hnamed := hguard
      simp only [getLatestFinalizedRevertGuard] at hguard
      rw [if_neg hguard]
      exact .carried hnamed
  · dsimp only [afterObserved, getLatestAfterObserved]
    by_cases hguard : getLatestObservedRestartGuard cfg query
        (getLatestAfterFinalized cfg ext query) = true
    · rw [if_pos hguard]
      exact .restarted hguard
    · have hfalse : getLatestObservedRestartGuard cfg query
          (getLatestAfterFinalized cfg ext query) = false :=
        Bool.eq_false_of_not_eq_true hguard
      rw [if_neg hguard]
      exact .unchanged hfalse
  · dsimp only [result, getLatestTraceResult, afterObserved]
    by_cases hguard : getLatestSelectorGuard cfg query
        (getLatestAfterObserved cfg ext query)
    · have hnamed := hguard
      simp only [getLatestSelectorGuard] at hguard
      rw [if_pos hguard]
      exact .selected hnamed
    · have hnamed := hguard
      simp only [getLatestSelectorGuard] at hguard
      rw [if_neg hguard]
      exact .unchanged hnamed
  · exact getLatestTraceResult_eq_getLatestConfirmed cfg ext query

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

/-- Exhaustive input classification for the selector/unchanged phase.  Guard
priority remains in `trace.finalized` and `trace.observed`; this value-level
projection is only a convenient consumer. -/
theorem selectorInput_cases
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query) :
    trace.afterObserved = query.confirmed_root ∨
      trace.afterObserved = query.store.finalized_checkpoint.root ∨
      trace.afterObserved =
        query.current_epoch_observed_justified_checkpoint.root := by
  rcases trace.observed.branch_cases with ⟨hunchanged, _⟩ |
      ⟨hrestarted, _⟩
  · rcases trace.finalized.branch_cases with ⟨hcarried, _⟩ |
        ⟨hreverted, _⟩
    · exact Or.inl (hunchanged.trans hcarried)
    · exact Or.inr (Or.inl (hunchanged.trans hreverted))
  · exact Or.inr (Or.inr hrestarted)

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

/-- The same arbitrary-store evaluator trace specialized to the exact
variable-updated store used by one execution call. -/
def getLatestConfirmedTraceAt (v : ValidatorIndex) (n : ℕ) :
    GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n) :=
  getLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)

/-- The eventual call induction receives the exact selector input kind while
retaining the stronger ordered branch objects in `getLatestConfirmedTraceAt`.
No reset certificate or payload conclusion is smuggled into this adapter. -/
theorem getLatestConfirmedTraceAt_selectorInput_cases
    (v : ValidatorIndex) (n : ℕ) :
    let trace := E.getLatestConfirmedTraceAt cfg ext v n
    trace.afterObserved = E.confirmed cfg ext v n ∨
      trace.afterObserved =
          (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
        trace.afterObserved =
          (E.fcrStep cfg ext v n
            ).current_epoch_observed_justified_checkpoint.root := by
  dsimp only
  rw [← E.fcrStep_confirmed_root cfg ext v n]
  exact (E.getLatestConfirmedTraceAt cfg ext v n).selectorInput_cases

end Execution


end FastConfirmation.Spec

end
