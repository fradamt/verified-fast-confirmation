module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedCandidateHistoryRecurrence
public import FastConfirmation.Spec.Proof.WeakSelectorInversion
public import FastConfirmation.Spec.Proof.WeakFCRCallContracts

@[expose] public section

/-!
# Spec / Proof / WeakCandidateHistoryRecurrence

Weak twin of `GetLatestConfirmedTrace.lean`'s evaluator trace and of
`AcceptedCandidateHistoryRecurrence.lean`'s exact ordered candidate-history
recurrence, over the weak rule (`Weak.get_latest_confirmed`,
`Weak.find_latest_confirmed_descendant`) and the weak actual-call trajectory
(`E.weakFcr` / `E.weakFcrStep` / `E.weakConfirmed`,
`WeakFCRCallContracts.lean`).

Stage S6 of the `hfilter`-discharge wave needs the candidate-history
induction at a possibly-Byzantine observer; that induction is an induction
over the *observer's own call history*, so it needs the four-way operational
branch classification of one weak call. This file supplies it. It is a
separate module from `WeakCandidateSourceHistory.lean` for exactly the reason
the strong development splits the same two layers: nothing here mentions FFG
semantics, synchrony, honesty, or any assumption bundle — it is pure
evaluator bookkeeping.

## The weak evaluator phases

The finalized-revert phase uses `Weak.is_confirmed_chain_safe`, which checks
the chain with the weak one-confirmation rule. Its guard, candidate function,
and phase relation are weak twins of the strong trace helpers. The observed
restart phase uses the certified head. The final phase uses the weak
descendant selector. Only `getLatestSelectorGuard`, the final recency test,
is reused from the strong layer.

## What is delivered

* `Weak.getLatestTraceResult` (+ `…_eq_getLatestConfirmed`, by `rfl`),
  `Weak.GetLatestSelectorPhase`, `Weak.GetLatestConfirmedTrace`,
  `Weak.getLatestConfirmedTrace` and the four projections.
* `Weak.observedRestartGuard_facts` — the four conjuncts of the (shared)
  observed-restart guard, restated over a bare candidate root so it serves
  both trace layers.
* `Weak.CarriedCandidateInputAt`, `Weak.FinalizedResetCandidateInputAt`,
  `Weak.ObservedResetCandidateInputAt`, `Weak.OrderedCandidateInputOrigin`,
  `Weak.SelectorUnchangedAt`, `Weak.StrictSelectorAdvanceAt`,
  `Weak.CandidateHistoryCallBranch` and the exhaustive classifier
  `Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch`.
* `Weak.StrictSelectorAdvanceGeometryAt` + `Weak.StrictSelectorAdvanceAt.geometry`
  (over `weak_find_latest_confirmed_descendant_ge`,
  `WeakSelectorInversion.lean`).
* the weak trajectory write-back lemmas `Execution.weakConfirmed_zero`,
  `weakConfirmed_succ_of_no_advance`, `weakConfirmed_succ_of_advance`, the
  actual-call trace `Execution.weakGetLatestConfirmedTraceAt`, and the
  recurrence `Execution.WeakActualCandidateHistoryRecurrenceAt` +
  `Execution.weakActualCandidateHistoryRecurrence`.

Note that `Weak.ObservedResetCandidateInputAt` retains, verbatim from the
strong structure, the guard conjunct
`observed_eq_head_unrealized : query.current_epoch_observed_justified_checkpoint
= query.store.unrealized_justifications (get_head cfg query.store).root`.
Under rule delta 5 (head-indexed banking) this conjunct is the *same
equation* the bookkeeping gate installs, which is what makes the weak
Lemma-22 boundary step direct; see `WeakCandidateSourceHistory.lean`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-- The first guard uses the weak chain reconfirmation rule. -/
def getLatestFinalizedRevertGuard
    (query : FastConfirmationStore Root) : Prop :=
  get_block_epoch cfg query.store query.confirmed_root + 1 <
      get_current_store_epoch cfg query.store ∨
    ¬ is_ancestor query.store
      (get_node_for_root (get_head cfg query.store).root)
      (get_node_for_root query.confirmed_root) ∨
    (is_start_slot_at_epoch cfg (get_current_slot cfg query.store) ∧
      ¬ Weak.is_confirmed_chain_safe cfg ext query query.confirmed_root)

/-- Candidate after the weak finalized-revert phase. -/
def getLatestAfterFinalized
    (query : FastConfirmationStore Root) : Root :=
  if get_block_epoch cfg query.store query.confirmed_root + 1 <
        get_current_store_epoch cfg query.store ∨
      ¬ is_ancestor query.store
        (get_node_for_root (get_head cfg query.store).root)
        (get_node_for_root query.confirmed_root) ∨
      (is_start_slot_at_epoch cfg (get_current_slot cfg query.store) ∧
        ¬ Weak.is_confirmed_chain_safe cfg ext query query.confirmed_root) then
    query.store.finalized_checkpoint.root
  else
    query.confirmed_root

/-- Exact provenance for the weak finalized-revert phase. -/
inductive GetLatestFinalizedPhase
    (query : FastConfirmationStore Root) : Root → Prop
  | carried
      (guard_false : ¬ getLatestFinalizedRevertGuard cfg ext query) :
      GetLatestFinalizedPhase query query.confirmed_root
  | reverted
      (guard_true : getLatestFinalizedRevertGuard cfg ext query) :
      GetLatestFinalizedPhase query query.store.finalized_checkpoint.root

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


/-- The second Boolean guard, parameterized by the candidate produced by the
first phase.  In particular, its stale comparison is not made against the
original cached root when the finalized guard fired. -/
def getLatestObservedRestartGuard
    (query : FastConfirmationStore Root) (candidate : Root) : Bool :=
  is_start_slot_at_epoch cfg (get_current_slot cfg query.store) &&
    decide (get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg query.store) &&
    (decide (query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (Weak.get_certified_head cfg ext query.store (get_current_balance_source query))) &&
    Weak.has_head_broadcast_certificate cfg ext query.store (get_current_balance_source query)) &&
    decide (get_block_slot query.store candidate <
      get_block_slot query.store
        query.current_epoch_observed_justified_checkpoint.root)

/-- Candidate after the observed restart and greatest-unrealized reset. -/
def getLatestAfterObserved
    (query : FastConfirmationStore Root) : Root :=
  let afterFinalized := getLatestAfterFinalized cfg ext query
  let restarted :=
    if getLatestObservedRestartGuard cfg ext query afterFinalized then
      query.current_epoch_observed_justified_checkpoint.root
    else afterFinalized
  let greatest := query.current_epoch_greatest_unrealized_checkpoint
  if greatest ≠ get_checkpoint_for_block cfg query.store restarted greatest.epoch then
    query.store.finalized_checkpoint.root
  else restarted

/-- Exact provenance for the restart and the last reset gate. -/
inductive GetLatestObservedPhase
    (query : FastConfirmationStore Root) (before : Root) : Root → Prop
  | unchanged
      (guard_false : getLatestObservedRestartGuard cfg ext query before = false)
      (checkpoint_eq : query.current_epoch_greatest_unrealized_checkpoint =
        get_checkpoint_for_block cfg query.store before
          query.current_epoch_greatest_unrealized_checkpoint.epoch) :
      GetLatestObservedPhase query before before
  | restarted
      (guard_true : getLatestObservedRestartGuard cfg ext query before = true)
      (checkpoint_eq : query.current_epoch_greatest_unrealized_checkpoint =
        get_checkpoint_for_block cfg query.store
          query.current_epoch_observed_justified_checkpoint.root
          query.current_epoch_greatest_unrealized_checkpoint.epoch) :
      GetLatestObservedPhase query before
        query.current_epoch_observed_justified_checkpoint.root
  | greatestReset
      (checkpoint_ne : query.current_epoch_greatest_unrealized_checkpoint ≠
        get_checkpoint_for_block cfg query.store
          (if getLatestObservedRestartGuard cfg ext query before then
            query.current_epoch_observed_justified_checkpoint.root else before)
          query.current_epoch_greatest_unrealized_checkpoint.epoch) :
      GetLatestObservedPhase query before query.store.finalized_checkpoint.root

namespace GetLatestObservedPhase

theorem branch_cases
    {query : FastConfirmationStore Root} {before after : Root}
    (h : GetLatestObservedPhase cfg ext query before after) :
    (after = before ∧
        getLatestObservedRestartGuard cfg ext query before = false) ∨
      (after = query.current_epoch_observed_justified_checkpoint.root ∧
        getLatestObservedRestartGuard cfg ext query before = true) ∨
      after = query.store.finalized_checkpoint.root := by
  cases h with
  | unchanged hfalse _ => exact Or.inl ⟨rfl, hfalse⟩
  | restarted htrue _ => exact Or.inr (Or.inl ⟨rfl, htrue⟩)
  | greatestReset _ => exact Or.inr (Or.inr rfl)

end GetLatestObservedPhase



/-! ## The weak phased evaluator -/

/-- Weak twin of `getLatestTraceResult`: the phased evaluator uses weak
reconfirmation, the certified observed restart, and the weak descendant
selector. -/
def getLatestTraceResult (query : FastConfirmationStore Root) : Root :=
  let candidate := getLatestAfterObserved cfg ext query
  if get_block_epoch cfg query.store candidate + 1 ≥
      get_current_store_epoch cfg query.store then
    Weak.find_latest_confirmed_descendant cfg ext query candidate
  else
    candidate

/-- The named weak phased evaluator is definitionally `Weak.get_latest_confirmed`. -/
theorem getLatestTraceResult_eq_getLatestConfirmed
    (query : FastConfirmationStore Root) :
    Weak.getLatestTraceResult cfg ext query =
      Weak.get_latest_confirmed cfg ext query := by
  rfl

/-- Weak twin of `GetLatestSelectorPhase`. -/
inductive GetLatestSelectorPhase
    (query : FastConfirmationStore Root) (input : Root) : Root → Prop
  | unchanged
      (guard_false : ¬ getLatestSelectorGuard cfg query input) :
      GetLatestSelectorPhase query input input
  | selected
      (guard_true : getLatestSelectorGuard cfg query input) :
      GetLatestSelectorPhase query input
        (Weak.find_latest_confirmed_descendant cfg ext query input)

namespace GetLatestSelectorPhase

theorem branch_cases
    {query : FastConfirmationStore Root} {input result : Root}
    (h : Weak.GetLatestSelectorPhase cfg ext query input result) :
    (result = input ∧ ¬ getLatestSelectorGuard cfg query input) ∨
      (result = Weak.find_latest_confirmed_descendant cfg ext query input ∧
        getLatestSelectorGuard cfg query input) := by
  cases h with
  | unchanged hfalse => exact Or.inl ⟨rfl, hfalse⟩
  | selected htrue => exact Or.inr ⟨rfl, htrue⟩

end GetLatestSelectorPhase

/-- Weak twin of `GetLatestConfirmedTrace`: each phase records the guard
and output of the weak evaluator. -/
structure GetLatestConfirmedTrace (query : FastConfirmationStore Root) where
  afterFinalized : Root
  afterObserved : Root
  result : Root
  finalized : GetLatestFinalizedPhase cfg ext query afterFinalized
  observed : GetLatestObservedPhase cfg ext query afterFinalized afterObserved
  selector : Weak.GetLatestSelectorPhase cfg ext query afterObserved result
  result_eq : result = Weak.get_latest_confirmed cfg ext query

/-- Every query store has an exact weak evaluator trace. -/
def getLatestConfirmedTrace (query : FastConfirmationStore Root) :
    Weak.GetLatestConfirmedTrace cfg ext query := by
  let afterFinalized := getLatestAfterFinalized cfg ext query
  let afterObserved := getLatestAfterObserved cfg ext query
  let result := Weak.getLatestTraceResult cfg ext query
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
    by_cases hreset : query.current_epoch_greatest_unrealized_checkpoint ≠
        get_checkpoint_for_block cfg query.store
          (if getLatestObservedRestartGuard cfg ext query
              (getLatestAfterFinalized cfg ext query) then
            query.current_epoch_observed_justified_checkpoint.root
          else getLatestAfterFinalized cfg ext query)
          query.current_epoch_greatest_unrealized_checkpoint.epoch
    · rw [if_pos hreset]
      exact .greatestReset hreset
    · rw [if_neg hreset]
      have heq := Classical.not_not.mp hreset
      by_cases hguard : getLatestObservedRestartGuard cfg ext query
          (getLatestAfterFinalized cfg ext query) = true
      · rw [if_pos hguard] at heq ⊢
        exact .restarted hguard heq
      · rw [if_neg hguard] at heq ⊢
        exact .unchanged (Bool.eq_false_of_not_eq_true hguard) heq
  · dsimp only [result, Weak.getLatestTraceResult, afterObserved]
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
  · exact Weak.getLatestTraceResult_eq_getLatestConfirmed cfg ext query

namespace GetLatestConfirmedTrace

theorem afterFinalized_cases
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) :
    (trace.afterFinalized = query.confirmed_root ∧
        ¬ getLatestFinalizedRevertGuard cfg ext query) ∨
      (trace.afterFinalized = query.store.finalized_checkpoint.root ∧
        getLatestFinalizedRevertGuard cfg ext query) :=
  trace.finalized.branch_cases

theorem afterObserved_cases
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) :
    (trace.afterObserved = trace.afterFinalized ∧
        getLatestObservedRestartGuard cfg ext query trace.afterFinalized = false) ∨
      (trace.afterObserved =
          query.current_epoch_observed_justified_checkpoint.root ∧
        getLatestObservedRestartGuard cfg ext query trace.afterFinalized = true) ∨
      trace.afterObserved = query.store.finalized_checkpoint.root :=
  trace.observed.branch_cases

theorem selector_cases
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) :
    (trace.result = trace.afterObserved ∧
        ¬ getLatestSelectorGuard cfg query trace.afterObserved) ∨
      (trace.result = Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved ∧
        getLatestSelectorGuard cfg query trace.afterObserved) :=
  trace.selector.branch_cases cfg ext

theorem selectorInput_cases
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) :
    trace.afterObserved = query.confirmed_root ∨
      trace.afterObserved = query.store.finalized_checkpoint.root ∨
      trace.afterObserved =
        query.current_epoch_observed_justified_checkpoint.root := by
  rcases trace.observed.branch_cases with ⟨hunchanged, _⟩ | ⟨hrestarted, _⟩ | hreset
  · rcases trace.finalized.branch_cases with ⟨hcarried, _⟩ | ⟨hreverted, _⟩
    · exact Or.inl (hunchanged.trans hcarried)
    · exact Or.inr (Or.inl (hunchanged.trans hreverted))
  · exact Or.inr (Or.inr hrestarted)
  · exact Or.inr (Or.inl hreset)

end GetLatestConfirmedTrace

/-- The four conjuncts of the (rule-independent) observed-restart guard,
stated over a bare candidate root rather than over a trace field. -/
theorem observedRestartGuard_facts
    {query : FastConfirmationStore Root} {candidate : Root}
    (hactive : getLatestObservedRestartGuard cfg ext query candidate = true) :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∧
      get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store ∧
      query.current_epoch_observed_justified_checkpoint =
        query.store.unrealized_justifications
          (Weak.get_certified_head cfg ext query.store (get_current_balance_source query)) ∧
      get_block_slot query.store candidate <
        get_block_slot query.store
          query.current_epoch_observed_justified_checkpoint.root := by
  simp only [getLatestObservedRestartGuard, Bool.and_eq_true,
    decide_eq_true_eq] at hactive
  exact ⟨hactive.1.1.1, hactive.1.1.2, hactive.1.2.1, hactive.2⟩

/-! ## Exact ordered input origins (weak trace) -/

/-- Weak twin of `CarriedCandidateInputAt`. -/
structure CarriedCandidateInputAt
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop where
  afterFinalized_eq : trace.afterFinalized = query.confirmed_root
  finalized_guard_false : ¬ getLatestFinalizedRevertGuard cfg ext query
  afterObserved_eq : trace.afterObserved = trace.afterFinalized
  observed_guard_false :
    getLatestObservedRestartGuard cfg ext query trace.afterFinalized = false
  input_eq : trace.afterObserved = query.confirmed_root

namespace CarriedCandidateInputAt

/-- A carried input necessarily passed the first guard's stale test. -/
theorem confirmed_recent
    {query : FastConfirmationStore Root}
    {trace : Weak.GetLatestConfirmedTrace cfg ext query}
    (h : Weak.CarriedCandidateInputAt cfg ext query trace) :
    get_block_epoch cfg query.store query.confirmed_root + 1 ≥
      get_current_store_epoch cfg query.store := by
  apply Nat.le_of_not_gt
  intro hstale
  exact h.finalized_guard_false (Or.inl hstale)

end CarriedCandidateInputAt

/-- A finalized selector input can come from either reset gate. -/
structure FinalizedResetCandidateInputAt
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop where
  input_eq : trace.afterObserved = query.store.finalized_checkpoint.root

/-- Weak twin of `ObservedResetCandidateInputAt`. Every conjunct of the
executable guard is projected explicitly, including
`observed_eq_head_unrealized`, which under rule delta 5 is the same equation
the weak bookkeeping installs. -/
structure ObservedResetCandidateInputAt
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop where
  afterFinalized_cases :
    (trace.afterFinalized = query.confirmed_root ∧
        ¬ getLatestFinalizedRevertGuard cfg ext query) ∨
      (trace.afterFinalized = query.store.finalized_checkpoint.root ∧
        getLatestFinalizedRevertGuard cfg ext query)
  afterObserved_eq : trace.afterObserved =
    query.current_epoch_observed_justified_checkpoint.root
  observed_guard_true :
    getLatestObservedRestartGuard cfg ext query trace.afterFinalized = true
  epoch_start :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true
  observed_previous_epoch :
    get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg query.store
  observed_eq_head_unrealized :
    query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (Weak.get_certified_head cfg ext query.store (get_current_balance_source query))
  carrier_certificate : Weak.has_head_broadcast_certificate cfg ext query.store
    (get_current_balance_source query) = true
  afterFinalized_slot_lt_observed :
    get_block_slot query.store trace.afterFinalized <
      get_block_slot query.store
        query.current_epoch_observed_justified_checkpoint.root
  input_eq : trace.afterObserved =
    query.current_epoch_observed_justified_checkpoint.root

/-- Weak twin of `OrderedCandidateInputOrigin`. -/
inductive OrderedCandidateInputOrigin
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop
  | carried : Weak.CarriedCandidateInputAt cfg ext query trace →
      OrderedCandidateInputOrigin query trace
  | finalizedReset : Weak.FinalizedResetCandidateInputAt cfg ext query trace →
      OrderedCandidateInputOrigin query trace
  | observedReset : Weak.ObservedResetCandidateInputAt cfg ext query trace →
      OrderedCandidateInputOrigin query trace

/-! ## Exact final-selector outcomes (weak trace) -/

/-- Weak twin of `SelectorUnchangedAt`. -/
inductive SelectorUnchangedAt
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop
  | skipped
      (result_eq : trace.result = trace.afterObserved)
      (guard_false :
        ¬ getLatestSelectorGuard cfg query trace.afterObserved) :
      SelectorUnchangedAt query trace
  | selectedFixed
      (result_eq : trace.result =
        Weak.find_latest_confirmed_descendant cfg ext query trace.afterObserved)
      (guard_true : getLatestSelectorGuard cfg query trace.afterObserved)
      (fixed : Weak.find_latest_confirmed_descendant cfg ext query
        trace.afterObserved = trace.afterObserved) :
      SelectorUnchangedAt query trace

namespace SelectorUnchangedAt

/-- In either operational unchanged case, the trace result is the selector
input. -/
theorem result_eq_input
    {query : FastConfirmationStore Root}
    {trace : Weak.GetLatestConfirmedTrace cfg ext query}
    (h : Weak.SelectorUnchangedAt cfg ext query trace) :
    trace.result = trace.afterObserved := by
  cases h with
  | skipped hresult _ => exact hresult
  | selectedFixed hresult _ hfixed => exact hresult.trans hfixed

end SelectorUnchangedAt

/-- Weak twin of `StrictSelectorAdvanceAt`. -/
structure StrictSelectorAdvanceAt
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop where
  result_eq : trace.result =
    Weak.find_latest_confirmed_descendant cfg ext query trace.afterObserved
  guard_true : getLatestSelectorGuard cfg query trace.afterObserved
  input_recent :
    get_block_epoch cfg query.store trace.afterObserved + 1 ≥
      get_current_store_epoch cfg query.store
  result_ne_input : trace.result ≠ trace.afterObserved

/-- Weak twin of `CandidateHistoryCallBranch`. -/
inductive CandidateHistoryCallBranch
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop
  | carriedUnchanged
      (input : Weak.CarriedCandidateInputAt cfg ext query trace)
      (selector : Weak.SelectorUnchangedAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace
  | finalizedResetUnchanged
      (input : Weak.FinalizedResetCandidateInputAt cfg ext query trace)
      (selector : Weak.SelectorUnchangedAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace
  | observedResetUnchanged
      (input : Weak.ObservedResetCandidateInputAt cfg ext query trace)
      (selector : Weak.SelectorUnchangedAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace
  | strictSelected
      (input : Weak.OrderedCandidateInputOrigin cfg ext query trace)
      (selector : Weak.StrictSelectorAdvanceAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace

namespace GetLatestConfirmedTrace

/-- An arbitrary weak evaluator trace has the exact four-way candidate
history classification. -/
theorem candidateHistoryCallBranch
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) :
    Weak.CandidateHistoryCallBranch cfg ext query trace := by
  have mkSelector :
      Weak.SelectorUnchangedAt cfg ext query trace ∨
        Weak.StrictSelectorAdvanceAt cfg ext query trace := by
    rcases trace.selector_cases cfg ext with hskipped | hselected
    · exact Or.inl (.skipped hskipped.1 hskipped.2)
    · by_cases hstrict : trace.result ≠ trace.afterObserved
      · exact Or.inr {
          result_eq := hselected.1
          guard_true := hselected.2
          input_recent := hselected.2
          result_ne_input := hstrict
        }
      · have hfixedResult : trace.result = trace.afterObserved := by
          by_contra hne
          exact hstrict hne
        have hfixed : Weak.find_latest_confirmed_descendant cfg ext query
            trace.afterObserved = trace.afterObserved :=
          hselected.1.symm.trans hfixedResult
        exact Or.inl (.selectedFixed hselected.1 hselected.2 hfixed)
  rcases trace.afterObserved_cases cfg ext with hunchanged | hrestarted | hreset
  · rcases trace.afterFinalized_cases cfg ext with hcarried | hfinalized
    · have hinput : Weak.CarriedCandidateInputAt cfg ext query trace := {
        afterFinalized_eq := hcarried.1
        finalized_guard_false := hcarried.2
        afterObserved_eq := hunchanged.1
        observed_guard_false := hunchanged.2
        input_eq := hunchanged.1.trans hcarried.1
      }
      rcases mkSelector with hselector | hselector
      · exact .carriedUnchanged hinput hselector
      · exact .strictSelected (.carried hinput) hselector
    · have hinput : Weak.FinalizedResetCandidateInputAt cfg ext query trace := {
        input_eq := hunchanged.1.trans hfinalized.1
      }
      rcases mkSelector with hselector | hselector
      · exact .finalizedResetUnchanged hinput hselector
      · exact .strictSelected (.finalizedReset hinput) hselector
  · have hfacts := Weak.observedRestartGuard_facts cfg ext hrestarted.2
    have hinput : Weak.ObservedResetCandidateInputAt cfg ext query trace := {
      afterFinalized_cases := trace.afterFinalized_cases cfg ext
      afterObserved_eq := hrestarted.1
      observed_guard_true := hrestarted.2
      epoch_start := hfacts.1
      observed_previous_epoch := hfacts.2.1
      observed_eq_head_unrealized := hfacts.2.2.1
      carrier_certificate := by
        have hg := hrestarted.2
        simp only [getLatestObservedRestartGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
        exact hg.1.2.2
      afterFinalized_slot_lt_observed := hfacts.2.2.2
      input_eq := hrestarted.1
    }
    rcases mkSelector with hselector | hselector
    · exact .observedResetUnchanged hinput hselector
    · exact .strictSelected (.observedReset hinput) hselector
  · have hinput : Weak.FinalizedResetCandidateInputAt cfg ext query trace := ⟨hreset⟩
    rcases mkSelector with hselector | hselector
    · exact .finalizedResetUnchanged hinput hselector
    · exact .strictSelected (.finalizedReset hinput) hselector

end GetLatestConfirmedTrace

/-! ## Minimal query-local geometry for a strict weak branch -/

/-- Weak twin of `StrictSelectorAdvanceGeometryAt`. -/
structure StrictSelectorAdvanceGeometryAt
    (query : FastConfirmationStore Root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query) : Prop where
  result_known : trace.result ∈ query.store.block_roots
  descends_input : is_ancestor query.store
    (get_node_for_root trace.result)
    (get_node_for_root trace.afterObserved) = true
  input_slot_le_result :
    (query.store.blocks trace.afterObserved).slot ≤
      (query.store.blocks trace.result).slot
  input_epoch_le_result :
    get_block_epoch cfg query.store trace.afterObserved ≤
      get_block_epoch cfg query.store trace.result

namespace StrictSelectorAdvanceAt

/-- Weak twin of `StrictSelectorAdvanceAt.geometry`, over
`Weak.weak_find_latest_confirmed_descendant_ge`. -/
theorem geometry
    {query : FastConfirmationStore Root}
    {trace : Weak.GetLatestConfirmedTrace cfg ext query}
    (h : Weak.StrictSelectorAdvanceAt cfg ext query trace)
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : trace.afterObserved ∈ query.store.block_roots) :
    Weak.StrictSelectorAdvanceGeometryAt cfg ext query trace := by
  have hge := weak_find_latest_confirmed_descendant_ge cfg ext query hwf hwalk
    hhead trace.afterObserved hinput
  have hdesc : is_ancestor query.store
      (get_node_for_root trace.result)
      (get_node_for_root trace.afterObserved) = true := by
    rw [h.result_eq]
    exact hge.1
  have hknown : trace.result ∈ query.store.block_roots := by
    rw [h.result_eq]
    exact hge.2
  have hslot : (query.store.blocks trace.afterObserved).slot ≤
      (query.store.blocks trace.result).slot := by
    have hsle := get_ancestor_slot_le hwf
      (hwalk trace.afterObserved hinput trace.result hknown)
    simp only [is_ancestor, get_node_for_root, decide_eq_true_eq] at hdesc
    rw [hdesc] at hsle
    simpa using hsle
  exact {
    result_known := hknown
    descends_input := hdesc
    input_slot_le_result := hslot
    input_epoch_le_result := by
      simp only [get_block_epoch, compute_epoch_at_slot]
      exact Nat.div_le_div_right hslot
  }

end StrictSelectorAdvanceAt

end Weak

/-! ## Exact weak execution write-back -/

namespace Execution

variable (E : Execution Root)

/-- Weak twin of `Execution.confirmed_zero`. -/
theorem weakConfirmed_zero (v : ValidatorIndex) :
    E.weakConfirmed cfg ext v 0 =
      (E.store cfg ext v 0).finalized_checkpoint.root := rfl

/-- Weak twin of `Execution.confirmed_succ_of_no_advance`. -/
theorem weakConfirmed_succ_of_no_advance (v : ValidatorIndex) (n : ℕ)
    (h : ¬ get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    E.weakConfirmed cfg ext v (n + 1) = E.weakConfirmed cfg ext v n := by
  simp only [Execution.weakConfirmed, Execution.weakFcr]
  rw [if_neg h]

/-- Weak twin of `Execution.confirmed_succ_of_advance`. -/
theorem weakConfirmed_succ_of_advance (v : ValidatorIndex) (n : ℕ)
    (h : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    E.weakConfirmed cfg ext v (n + 1) =
      Weak.get_latest_confirmed cfg ext (E.weakFcrStep cfg ext v n) := by
  simp only [Execution.weakConfirmed, Execution.weakFcr]
  rw [if_pos h]
  rfl

/-- The weak evaluator trace specialized to the exact variable-updated store
of one weak execution call. -/
def weakGetLatestConfirmedTraceAt (v : ValidatorIndex) (n : ℕ) :
    Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext v n) :=
  Weak.getLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext v n)

/-- Weak twin of `Execution.ActualCandidateHistoryRecurrenceAt`. -/
structure WeakActualCandidateHistoryRecurrenceAt
    (v : ValidatorIndex) (n : ℕ) : Prop where
  call : E.IsFCRCallAt cfg ext v n
  query_store_eq :
    (E.weakFcrStep cfg ext v n).store = E.store cfg ext v (n + 1)
  query_confirmed_eq :
    (E.weakFcrStep cfg ext v n).confirmed_root = E.weakConfirmed cfg ext v n
  slot_advanced :
    get_current_slot cfg (E.store cfg ext v n) <
      get_current_slot cfg (E.store cfg ext v (n + 1))
  result_writeback :
    E.weakConfirmed cfg ext v (n + 1) =
      (E.weakGetLatestConfirmedTraceAt cfg ext v n).result
  branch : Weak.CandidateHistoryCallBranch cfg ext
    (E.weakFcrStep cfg ext v n)
    (E.weakGetLatestConfirmedTraceAt cfg ext v n)

/-- Weak twin of `Execution.actualCandidateHistoryRecurrence`. -/
theorem weakActualCandidateHistoryRecurrence
    {v : ValidatorIndex} {n : ℕ}
    (hcall : E.IsFCRCallAt cfg ext v n) :
    E.WeakActualCandidateHistoryRecurrenceAt cfg ext v n := by
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext v n
  have hwrite : E.weakConfirmed cfg ext v (n + 1) = trace.result :=
    (E.weakConfirmed_succ_of_advance cfg ext v n hcall).trans trace.result_eq.symm
  exact {
    call := hcall
    query_store_eq := E.weakFcrStep_store cfg ext v n
    query_confirmed_eq := E.weakFcrStep_confirmed_root cfg ext v n
    slot_advanced := hcall
    result_writeback := hwrite
    branch := trace.candidateHistoryCallBranch cfg ext
  }

end Execution

end FastConfirmation.Spec

end
