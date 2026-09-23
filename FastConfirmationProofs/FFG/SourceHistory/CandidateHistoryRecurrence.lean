module
public import Mathlib.Tactic
public import FastConfirmationProofs.FCRRule.GetLatestConfirmedTrace
public import FastConfirmationProofs.Checkpoints.Anchoring
public import FastConfirmationProofs.FFG.SourceHistory.SafeFromInvariant
public import FastConfirmationProofs.FFG.State.ProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Exact candidate-history recurrence for one FCR call

Paper Lemmas 22--23 reason about the ordered candidate updates in one actual
`get_latest_confirmed` call.  A result-only disjunction is too weak for that
induction: roots may coincide, and the final descendant selector may run but
return its input unchanged.

This file keeps the canonical `GetLatestConfirmedTrace` and classifies an
actual `Execution.fcrStep` write-back into exactly four operational outcomes:

1. the carried confirmed candidate is unchanged;
2. a finalized reset candidate is unchanged;
3. an observed restart candidate is unchanged; or
4. the descendant selector strictly advances its exact ordered input.

The first three outcomes retain whether the selector was skipped or ran and
returned a fixed point.  The strict outcome retains the active recency guard,
the exact selector equation, and the ordered input origin.  The observed arm
also exposes every conjunct of its boundary guard.  No source recency,
filter, safety, justification interface, or selected-margin premise appears.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact ordered input origins -/

/-- The first two evaluator phases retained the previous confirmed root.
Both guard failures are recorded, rather than inferred from root equality. -/
structure CarriedCandidateInputAt
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop where
  afterFinalized_eq : trace.afterFinalized = query.confirmed_root
  finalized_guard_false :
    ¬ getLatestFinalizedRevertGuard cfg ext query
  afterObserved_eq : trace.afterObserved = trace.afterFinalized
  observed_guard_false :
    getLatestObservedRestartGuard cfg query trace.afterFinalized = false
  input_eq : trace.afterObserved = query.confirmed_root

namespace CarriedCandidateInputAt

/-- A carried input necessarily passed the first guard's stale test. -/
theorem confirmed_recent
    {query : FastConfirmationStore Root}
    {trace : GetLatestConfirmedTrace cfg ext query}
    (h : CarriedCandidateInputAt cfg ext query trace) :
    get_block_epoch cfg query.store query.confirmed_root + 1 ≥
      get_current_store_epoch cfg query.store := by
  apply Nat.le_of_not_gt
  intro hstale
  exact h.finalized_guard_false (Or.inl hstale)

end CarriedCandidateInputAt

/-- The finalized guard fired and the observed phase retained that reset
candidate.  Operational guard provenance is kept even if roots coincide. -/
structure FinalizedResetCandidateInputAt
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop where
  afterFinalized_eq :
    trace.afterFinalized = query.store.finalized_checkpoint.root
  finalized_guard_true : getLatestFinalizedRevertGuard cfg ext query
  afterObserved_eq : trace.afterObserved = trace.afterFinalized
  observed_guard_false :
    getLatestObservedRestartGuard cfg query trace.afterFinalized = false
  input_eq :
    trace.afterObserved = query.store.finalized_checkpoint.root

/-- The observed restart guard fired.  Besides the ordered phase equations,
all four executable guard conjuncts are projected explicitly: epoch start,
the previous-epoch equation, checkpoint identity, and the strict slot
improvement over the post-finalized candidate. -/
structure ObservedResetCandidateInputAt
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop where
  afterFinalized_cases :
    (trace.afterFinalized = query.confirmed_root ∧
        ¬ getLatestFinalizedRevertGuard cfg ext query) ∨
      (trace.afterFinalized = query.store.finalized_checkpoint.root ∧
        getLatestFinalizedRevertGuard cfg ext query)
  afterObserved_eq : trace.afterObserved =
    query.current_epoch_observed_justified_checkpoint.root
  observed_guard_true :
    getLatestObservedRestartGuard cfg query trace.afterFinalized = true
  epoch_start :
    is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true
  observed_previous_epoch :
    get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg query.store
  observed_eq_head_unrealized :
    query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (get_head cfg query.store).root
  afterFinalized_slot_lt_observed :
    get_block_slot query.store trace.afterFinalized <
      get_block_slot query.store
        query.current_epoch_observed_justified_checkpoint.root
  input_eq : trace.afterObserved =
    query.current_epoch_observed_justified_checkpoint.root

/-- Ordered provenance of the exact input passed to the final descendant
selector. -/
inductive OrderedCandidateInputOrigin
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop
  | carried : CarriedCandidateInputAt cfg ext query trace →
      OrderedCandidateInputOrigin query trace
  | finalizedReset : FinalizedResetCandidateInputAt cfg ext query trace →
      OrderedCandidateInputOrigin query trace
  | observedReset : ObservedResetCandidateInputAt cfg ext query trace →
      OrderedCandidateInputOrigin query trace

/-! ## Exact final-selector outcomes -/

/-- An unchanged final result has two operationally distinct causes.  The
selector may be skipped because its recency guard is false, or it may run and
find no strict descendant.  Keeping both cases is necessary when roots
coincide. -/
inductive SelectorUnchangedAt
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop
  | skipped
      (result_eq : trace.result = trace.afterObserved)
      (guard_false :
        ¬ getLatestSelectorGuard cfg query trace.afterObserved) :
      SelectorUnchangedAt query trace
  | selectedFixed
      (result_eq : trace.result =
        find_latest_confirmed_descendant cfg ext query trace.afterObserved)
      (guard_true : getLatestSelectorGuard cfg query trace.afterObserved)
      (fixed : find_latest_confirmed_descendant cfg ext query
        trace.afterObserved = trace.afterObserved) :
      SelectorUnchangedAt query trace

namespace SelectorUnchangedAt


/-- In either operational unchanged case, the trace result is the selector
input. -/
theorem result_eq_input
    {query : FastConfirmationStore Root}
    {trace : GetLatestConfirmedTrace cfg ext query}
    (h : SelectorUnchangedAt cfg ext query trace) :
    trace.result = trace.afterObserved := by
  cases h with
  | skipped hresult _ => exact hresult
  | selectedFixed hresult _ hfixed => exact hresult.trans hfixed

end SelectorUnchangedAt

/-- Exact non-trivial final-selector outcome.  `input_recent` is merely the
named executable selector guard unfolded; it is not a source-recency fact. -/
structure StrictSelectorAdvanceAt
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop where
  result_eq : trace.result =
    find_latest_confirmed_descendant cfg ext query trace.afterObserved
  guard_true : getLatestSelectorGuard cfg query trace.afterObserved
  input_recent :
    get_block_epoch cfg query.store trace.afterObserved + 1 ≥
      get_current_store_epoch cfg query.store
  result_ne_input : trace.result ≠ trace.afterObserved

/-- The exhaustive four-way operational result classification. -/
inductive CandidateHistoryCallBranch
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop
  | carriedUnchanged
      (input : CarriedCandidateInputAt cfg ext query trace)
      (selector : SelectorUnchangedAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace
  | finalizedResetUnchanged
      (input : FinalizedResetCandidateInputAt cfg ext query trace)
      (selector : SelectorUnchangedAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace
  | observedResetUnchanged
      (input : ObservedResetCandidateInputAt cfg ext query trace)
      (selector : SelectorUnchangedAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace
  | strictSelected
      (input : OrderedCandidateInputOrigin cfg ext query trace)
      (selector : StrictSelectorAdvanceAt cfg ext query trace) :
      CandidateHistoryCallBranch query trace

namespace CandidateHistoryCallBranch


end CandidateHistoryCallBranch

namespace GetLatestConfirmedTrace

/-- An arbitrary canonical evaluator trace has the exact four-way candidate
history classification.  This is purely an ordered evaluator theorem. -/
theorem candidateHistoryCallBranch
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query) :
    CandidateHistoryCallBranch cfg ext query trace := by
  have mkSelector :
      SelectorUnchangedAt cfg ext query trace ∨
        StrictSelectorAdvanceAt cfg ext query trace := by
    rcases trace.selector_cases with hskipped | hselected
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
        have hfixed : find_latest_confirmed_descendant cfg ext query
            trace.afterObserved = trace.afterObserved := by
          exact hselected.1.symm.trans hfixedResult
        exact Or.inl (.selectedFixed hselected.1 hselected.2 hfixed)
  rcases trace.afterObserved_cases with hunchanged | hrestarted
  · rcases trace.afterFinalized_cases with hcarried | hfinalized
    · have hinput : CarriedCandidateInputAt cfg ext query trace := {
        afterFinalized_eq := hcarried.1
        finalized_guard_false := hcarried.2
        afterObserved_eq := hunchanged.1
        observed_guard_false := hunchanged.2
        input_eq := hunchanged.1.trans hcarried.1
      }
      rcases mkSelector with hselector | hselector
      · exact .carriedUnchanged hinput hselector
      · exact .strictSelected (.carried hinput) hselector
    · have hinput : FinalizedResetCandidateInputAt cfg ext query trace := {
        afterFinalized_eq := hfinalized.1
        finalized_guard_true := hfinalized.2
        afterObserved_eq := hunchanged.1
        observed_guard_false := hunchanged.2
        input_eq := hunchanged.1.trans hfinalized.1
      }
      rcases mkSelector with hselector | hselector
      · exact .finalizedResetUnchanged hinput hselector
      · exact .strictSelected (.finalizedReset hinput) hselector
  · have hfacts := trace.observedRestart_facts cfg ext hrestarted.2
    have hinput : ObservedResetCandidateInputAt cfg ext query trace := {
      afterFinalized_cases := trace.afterFinalized_cases
      afterObserved_eq := hrestarted.1
      observed_guard_true := hrestarted.2
      epoch_start := hfacts.1
      observed_previous_epoch := hfacts.2.1
      observed_eq_head_unrealized := hfacts.2.2.1
      afterFinalized_slot_lt_observed := hfacts.2.2.2
      input_eq := hrestarted.1
    }
    rcases mkSelector with hselector | hselector
    · exact .observedResetUnchanged hinput hselector
    · exact .strictSelected (.observedReset hinput) hselector

end GetLatestConfirmedTrace

/-! ## Minimal query-local geometry for a strict branch -/

/-- Geometry available from a strict selector branch once the ordinary
query-local fork-choice domain and input knownness are supplied explicitly.
This adapter does not derive those facts from a broad assumption bundle. -/
structure StrictSelectorAdvanceGeometryAt
    (query : FastConfirmationStore Root)
    (trace : GetLatestConfirmedTrace cfg ext query) : Prop where
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

/-- Enrich the exact strict branch with monotone ancestry and slot/epoch
facts using only explicit query-local geometry. -/
theorem geometry
    {query : FastConfirmationStore Root}
    {trace : GetLatestConfirmedTrace cfg ext query}
    (h : StrictSelectorAdvanceAt cfg ext query trace)
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : trace.afterObserved ∈ query.store.block_roots) :
    StrictSelectorAdvanceGeometryAt cfg ext query trace := by
  have hge := find_latest_confirmed_descendant_ge cfg ext query hwf hwalk
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
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hdesc
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

namespace CandidateHistoryCallBranch


end CandidateHistoryCallBranch

/-! ## Exact execution write-back -/

namespace Execution

variable (E : Execution Root)

/-- One actual FCR call, with its query-store/cache equations, strict slot
advance, exact write-back equation, and exhaustive ordered candidate branch. -/
structure ActualCandidateHistoryRecurrenceAt
    (v : ValidatorIndex) (n : ℕ) : Prop where
  call : E.IsFCRCallAt cfg ext v n
  query_store_eq :
    (E.fcrStep cfg ext v n).store = E.store cfg ext v (n + 1)
  query_confirmed_eq :
    (E.fcrStep cfg ext v n).confirmed_root = E.confirmed cfg ext v n
  slot_advanced :
    get_current_slot cfg (E.store cfg ext v n) <
      get_current_slot cfg (E.store cfg ext v (n + 1))
  result_writeback :
    E.confirmed cfg ext v (n + 1) =
      (E.getLatestConfirmedTraceAt cfg ext v n).result
  branch : CandidateHistoryCallBranch cfg ext
    (E.fcrStep cfg ext v n)
    (E.getLatestConfirmedTraceAt cfg ext v n)

/-- The exact one-second/one-call recurrence consumed by the paper
Lemmas-22--23 candidate-history induction. -/
theorem actualCandidateHistoryRecurrence
    {v : ValidatorIndex} {n : ℕ}
    (hcall : E.IsFCRCallAt cfg ext v n) :
    E.ActualCandidateHistoryRecurrenceAt cfg ext v n := by
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hwrite : E.confirmed cfg ext v (n + 1) = trace.result := by
    exact (E.confirmed_succ_of_advance cfg ext v n hcall).trans
      trace.result_eq.symm
  exact {
    call := hcall
    query_store_eq := E.fcrStep_store cfg ext v n
    query_confirmed_eq := E.fcrStep_confirmed_root cfg ext v n
    slot_advanced := hcall
    result_writeback := hwrite
    branch := trace.candidateHistoryCallBranch cfg ext
  }

/-! ## Accepted installation provenance for the observed reset cache -/

/-- Exact accepted installation of one unrealized-justified checkpoint into
an FCR cache field.  `originSecond = 0` is the initialization case; every
other installation retains the executable "next slot starts an epoch" guard
which copied that second's store-global UJ field. -/
structure AcceptedUJCacheInstallationAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (upper : ℕ) (field : Checkpoint Root) where
  originSecond : ℕ
  origin_le : originSecond ≤ upper
  field_eq : field =
    (E.store cfg ext v originSecond).unrealized_justified_checkpoint
  initialization_or_rotation :
    originSecond = 0 ∨
      is_start_slot_at_epoch cfg
        (get_current_slot cfg (E.store cfg ext v originSecond) + 1) = true
  accepted_origin : AcceptedGlobalUnrealizedJustifiedOrigin B.state
    (E.store cfg ext v originSecond)
    (E.store cfg ext v originSecond).unrealized_justified_checkpoint

/-- Exact previous-greatest field recurrence, stated independently of any
checkpoint realization or history bundle. -/
private theorem fcr_previousGreatest_succ_exact
    (v : ValidatorIndex) (n : ℕ)
    (hcall : E.IsFCRCallAt cfg ext v n) :
    (E.fcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else
        (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  have hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n) := hcall
  simp only [Execution.fcr]
  rw [if_pos hadv]
  change FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
    (update_fast_confirmation_variables cfg
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- The previous-greatest cache always names an exact earlier UJ field and
retains the accepted global origin at the installation store. -/
theorem previousGreatest_acceptedInstallation
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (v : ValidatorIndex) :
    ∀ n : ℕ, Nonempty (E.AcceptedUJCacheInstallationAt cfg ext B v n
      (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint) := by
  intro n
  induction n with
  | zero =>
      have horigin :=
        (B.causalStoreGlobalProjection hgen hanchor
          (E.store_causal cfg ext v 0)).storeGlobal.unrealized_justified
      refine ⟨{
        originSecond := 0
        origin_le := Nat.le_refl 0
        field_eq := ?_
        initialization_or_rotation := Or.inl rfl
        accepted_origin := horigin
      }⟩
      obtain ⟨ast, ablk, hgenEq, _hslot⟩ := hgen
      change E.genesis_store.finalized_checkpoint =
        E.genesis_store.unrealized_justified_checkpoint
      rw [hgenEq]
      simp only [get_forkchoice_store]
  | succ n ih =>
      obtain ⟨ih⟩ := ih
      by_cases hcall : E.IsFCRCallAt cfg ext v n
      · rw [E.fcr_previousGreatest_succ_exact cfg ext v n hcall]
        by_cases hrotate : is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) = true
        · rw [if_pos hrotate]
          exact ⟨{
            originSecond := n + 1
            origin_le := Nat.le_refl _
            field_eq := rfl
            initialization_or_rotation := Or.inr hrotate
            accepted_origin :=
              (B.causalStoreGlobalProjection hgen hanchor
                (E.store_causal cfg ext v (n + 1))).storeGlobal
                  |>.unrealized_justified
          }⟩
        · rw [if_neg hrotate]
          exact ⟨{
            originSecond := ih.originSecond
            origin_le := ih.origin_le.trans (Nat.le_succ n)
            field_eq := ih.field_eq
            initialization_or_rotation := ih.initialization_or_rotation
            accepted_origin := ih.accepted_origin
          }⟩
      · have hfield :
            (E.fcr cfg ext v (n + 1)
              ).previous_epoch_greatest_unrealized_checkpoint =
            (E.fcr cfg ext v n
              ).previous_epoch_greatest_unrealized_checkpoint := by
          have hadv : ¬ get_current_slot cfg
              (E.store cfg ext v (n + 1)) >
              get_current_slot cfg (E.store cfg ext v n) := hcall
          simp only [Execution.fcr, if_neg hadv]
        exact ⟨{
          originSecond := ih.originSecond
          origin_le := ih.origin_le.trans (Nat.le_succ n)
          field_eq := hfield.trans ih.field_eq
          initialization_or_rotation := ih.initialization_or_rotation
          accepted_origin := ih.accepted_origin
        }⟩

/-- `compute_slots_since_epoch_start` is the slot modulo the positive epoch
length. -/
private theorem slotsSinceEpochStart_eq_mod (s : Slot) :
    compute_slots_since_epoch_start cfg s = s % cfg.slots_per_epoch := by
  have h := Nat.div_add_mod s cfg.slots_per_epoch
  simp only [compute_slots_since_epoch_start, compute_start_slot_at_epoch,
    compute_epoch_at_slot]
  rw [Nat.mul_comm (s / cfg.slots_per_epoch) cfg.slots_per_epoch]
  omega

/-- A non-degenerate epoch cannot start at two consecutive slots. -/
private theorem next_not_epochStart_of_epochStart
    (hspe : 1 < cfg.slots_per_epoch) {s : Slot}
    (hstart : is_start_slot_at_epoch cfg s = true) :
    is_start_slot_at_epoch cfg (s + 1) ≠ true := by
  intro hnext
  simp only [is_start_slot_at_epoch, decide_eq_true_eq,
    slotsSinceEpochStart_eq_mod] at hstart hnext
  have hsmod : s % cfg.slots_per_epoch = 0 := hstart
  have hnmod : (s + 1) % cfg.slots_per_epoch = 0 := hnext
  have hsdvd : cfg.slots_per_epoch ∣ s := Nat.dvd_of_mod_eq_zero hsmod
  have hndvd : cfg.slots_per_epoch ∣ s + 1 := Nat.dvd_of_mod_eq_zero hnmod
  have honedvd : cfg.slots_per_epoch ∣ 1 :=
    (Nat.dvd_add_right hsdvd).mp hndvd
  have hone := Nat.le_of_dvd Nat.one_pos honedvd
  omega

/-- At a non-degenerate epoch start, the speculative query's observed field
is exactly the carried previous-greatest field. -/
private theorem fcrStep_observed_eq_previousGreatest_of_start
    (hspe : 1 < cfg.slots_per_epoch)
    (v : ValidatorIndex) (n : ℕ)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
      (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  have hnext := next_not_epochStart_of_epochStart cfg hspe hstart
  rw [Execution.fcrStep]
  simp only [update_fast_confirmation_variables]
  rw [if_neg hnext, if_pos hstart]

/-- Installation provenance attached to the observed-reset arm of an exact
actual query.  In particular, the source second is `k ≤ n`, the cached
checkpoint is exactly `(store v k).unrealized_justified_checkpoint`, the
initialization/rotation tag is retained, and that UJ field has the accepted
global origin `anchor` or `GU(tip)` at the same store. -/
theorem ObservedResetCandidateInputAt.acceptedInstallation
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} {n : ℕ}
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (h : ObservedResetCandidateInputAt cfg ext
      (E.fcrStep cfg ext v n) trace) :
    Nonempty (E.AcceptedUJCacheInstallationAt cfg ext B v n
      (E.fcrStep cfg ext v n
        ).current_epoch_observed_justified_checkpoint) := by
  have hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true := by
    simpa only [E.fcrStep_store] using h.epoch_start
  have hfield := E.fcrStep_observed_eq_previousGreatest_of_start
    cfg ext hspe v n hstart
  obtain ⟨hhistory⟩ := E.previousGreatest_acceptedInstallation
    cfg ext B hgen hanchor v n
  exact ⟨{
    originSecond := hhistory.originSecond
    origin_le := hhistory.origin_le
    field_eq := hfield.trans hhistory.field_eq
    initialization_or_rotation := hhistory.initialization_or_rotation
    accepted_origin := hhistory.accepted_origin
  }⟩

end Execution


end FastConfirmation.Spec

end
