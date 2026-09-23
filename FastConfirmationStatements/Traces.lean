module
public import FastConfirmationModel

@[expose] public section

/-!
# Traces

Executable call, loop, and selected result traces. Reads the Spec Model. Read Premises/FCRCallPremises next.
-/

section

/-! ## From FCRCallContracts -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
/-- The variable-updated FCR store at a slot boundary: `E.fcr v n` re-seated
on the current store and run through `update_fast_confirmation_variables`,
before `get_latest_confirmed` is evaluated. -/
def fcrStoreAtCall (v : ValidatorIndex) (n : ℕ) : FastConfirmationStore Root :=
  update_fast_confirmation_variables cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- The actual call from `n` to `n+1` advanced a slot. -/
def IsScheduledFCRCallAt (v : ValidatorIndex) (n : ℕ) : Prop :=
  get_current_slot cfg (E.store cfg ext v (n + 1)) >
    get_current_slot cfg (E.store cfg ext v n)

end Execution
end FastConfirmation.Spec

end

section

/-! ## From LatestConfirmedCallTrace -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
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
/- This lemma stays with the statements because the value of
`getLatestConfirmedTrace` uses its proof. -/
theorem getLatestTraceResult_eq_getLatestConfirmed
    (query : FastConfirmationStore Root) :
    getLatestTraceResult cfg ext query = get_latest_confirmed cfg ext query := by
  rfl

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
end GetLatestFinalizedPhase
namespace GetLatestObservedPhase
end GetLatestObservedPhase
namespace GetLatestSelectorPhase
end GetLatestSelectorPhase
/-- Complete ordered evaluator trace.  Intermediate roots are data, while
each phase proof fixes their operational provenance independently of any root
equalities. -/
structure LatestConfirmedCallTrace
    (query : FastConfirmationStore Root) where
  afterFinalized : Root
  afterObserved : Root
  result : Root
  finalized : GetLatestFinalizedPhase cfg ext query afterFinalized
  observed : GetLatestObservedPhase cfg query afterFinalized afterObserved
  selector : GetLatestSelectorPhase cfg ext query afterObserved result
  result_eq : result = get_latest_confirmed cfg ext query

/-- Every arbitrary query store has an exact evaluator trace. -/
def getLatestConfirmedTrace
    (query : FastConfirmationStore Root) :
    LatestConfirmedCallTrace cfg ext query := by
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

namespace LatestConfirmedCallTrace
end LatestConfirmedCallTrace
namespace Execution
variable (E : Execution Root)
/-- The same arbitrary-store evaluator trace specialized to the exact
variable-updated store used by one execution call. -/
def getLatestConfirmedTraceAt (v : ValidatorIndex) (n : ℕ) :
    LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n) :=
  getLatestConfirmedTrace cfg ext (E.fcrStoreAtCall cfg ext v n)

end Execution
end FastConfirmation.Spec

end

section

/-! ## From SelectedFilter -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
/-- Ghost-instrumented previous-epoch loop.  The edge list is oldest to newest
and contains exactly the accumulator transitions that the executable loop
took. -/
def prevEpochLoopTrace (fcrStore : FastConfirmationStore Root) (currentEpoch : Epoch) :
    List Root → Root → Root × List (Root × Root)
  | [], acc => (acc, [])
  | b :: rest, acc =>
      if get_block_epoch cfg fcrStore.store b = currentEpoch then
        (acc, [])
      else if ¬ is_ancestor fcrStore.store
          (get_node_for_root fcrStore.previous_slot_head) (get_node_for_root b) then
        (acc, [])
      else if ¬ is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b then
        (acc, [])
      else
        let tail := prevEpochLoopTrace fcrStore currentEpoch rest b
        (tail.1, (acc, b) :: tail.2)

/-- Ghost-instrumented tentative loop. -/
def tentativeLoopTrace (fcrStore : FastConfirmationStore Root) :
    List Root → Root → Root × List (Root × Root)
  | [], acc => (acc, [])
  | b :: rest, acc =>
      if get_block_epoch cfg fcrStore.store b >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ will_current_target_be_justified cfg ext fcrStore.store then
        (acc, [])
      else if ¬ is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b then
        (acc, [])
      else
        let tail := tentativeLoopTrace fcrStore rest b
        (tail.1, (acc, b) :: tail.2)

end FastConfirmation.Spec

end

section

/-! ## From SelectedFilterBridge -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
/-- Ghost trace of the complete executable wrapper.  The first edge list is
the selected previous-epoch trace.  The second is the tentative trace only
when the wrapper's final acceptance guard keeps its result; if that guard
rejects the tentative accumulator, its edges are erased as well. -/
def findLatestSelectedTrace (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Root × (List (Root × Root) × List (Root × Root)) :=
  let store := fcrStore.store
  let head := (get_head cfg store).root
  let currentEpoch := get_current_store_epoch cfg store
  let previousGuard :=
    get_block_epoch cfg store latestConfirmedRoot + 1 = currentEpoch ∧
        (get_voting_source cfg store fcrStore.previous_slot_head).epoch + 2 ≥
          currentEpoch ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
          (will_no_conflicting_checkpoint_be_justified cfg ext store = true ∧
            ((store.unrealized_justifications fcrStore.previous_slot_head).epoch + 1 ≥
                currentEpoch ∨
              (store.unrealized_justifications head).epoch + 1 ≥ currentEpoch)))
  let previousRoot :=
    if previousGuard then
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore currentEpoch
        (get_ancestor_roots store head latestConfirmedRoot) latestConfirmedRoot
    else
      latestConfirmedRoot
  let previousEdges :=
    if previousGuard then
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots store head latestConfirmedRoot) latestConfirmedRoot).2
    else
      []
  let tentativeGuard :=
    is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
      (store.unrealized_justifications head).epoch + 1 ≥ currentEpoch
  let tentativeRoot :=
    if tentativeGuard then
      find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore
        (get_ancestor_roots store head previousRoot) previousRoot
    else
      previousRoot
  let tentativeAccepted :=
    tentativeGuard ∧
      (get_block_epoch cfg store tentativeRoot = currentEpoch ∨
        ((get_voting_source cfg store tentativeRoot).epoch + 2 ≥ currentEpoch ∧
            (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
              will_no_conflicting_checkpoint_be_justified cfg ext store = true)))
  let tentativeEdges :=
    if tentativeAccepted then
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots store head previousRoot) previousRoot).2
    else
      []
  (find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot,
    (previousEdges, tentativeEdges))

/-- A previous-loop edge retained by the complete wrapper trace. -/
def PreviousEpochSelectedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.1

/-- A selected-path tentative edge which actually crossed to a later block
epoch.  Unlike bare loop instrumentation, this predicate is indexed by the
wrapper input and excludes tentative edges discarded by the final acceptance
guard. -/
def CurrentTargetSelectedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2 ∧
    get_block_epoch cfg fcrStore.store a < get_block_epoch cfg fcrStore.store c

namespace ChainDown
end ChainDown
end FastConfirmation.Spec

end

end
