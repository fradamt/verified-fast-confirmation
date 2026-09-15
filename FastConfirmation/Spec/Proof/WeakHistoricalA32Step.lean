import FastConfirmation.Spec.Proof.WeakHistoricalA32Geometry
import FastConfirmation.Spec.Proof.WeakSelectedStrictEdgeFilterSupply
import FastConfirmation.Spec.Proof.WeakEarlyPhaseSourceWiring
import FastConfirmation.Spec.Proof.WeakCandidateHistoryRecurrence

/-!
# Spec / Proof / WeakHistoricalA32Step

The weak-evaluator twin of the exact evaluator-step layer
`AcceptedHistoricalA32Step.lean`.

**Why a twin is needed at all.**  Every statement in the strong step layer is
indexed by the *strong* selector — `find_latest_confirmed_descendant`,
`findLatestSelectedTrace`, `GetLatestConfirmedTrace`, `E.fcrStep` — and rule
delta 5 gives the weak model different selector functions
(`Spec/Model/WeakSynchrony.lean`).  The strong lemmas therefore do not
instantiate at a weak call, even though nothing in them is *about* the
selector's guards beyond the ghost-trace bookkeeping.

**What is reused rather than cloned.**  Everything store-level is both
honesty-free and selector-free and is imported verbatim:

* `Execution.HistoricalA32QueryGeometryAt` (the geometry bundle) and its
  observer-side producers `Weak.historicalA32QueryGeometryAt_at_observer` /
  `Weak.weakFcrStep_historicalA32QueryGeometryAt`
  (`WeakHistoricalA32Geometry.lean`);
* the whole payload side — `Execution.AcceptedHistoricalA32LineageAt`,
  `AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget` /
  `.of_anchor`,
  `AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedSameEpochSegment`
  / `.fixedSource_of_acceptedTargetWalk`;
* the pure store geometry — `SelectedParentTrace`,
  `currentEpochBlock_descends_currentTarget`,
  `current_target_eq_checkpoint_of_current_epoch_ancestor`,
  `get_ancestor_spec`,
  `Execution.knownSameEpochAncestrySegment_of_known_ancestor`,
  `Execution.actualFinalizedReset_currentCheckpoint_eq_anchor`.

**The substitutions.**  `find_latest_confirmed_descendant` →
`Weak.find_latest_confirmed_descendant`; `findLatestSelectedTrace` →
`Weak.findLatestSelectedTrace`; `find_latest_confirmed_descendant_ge` →
`Weak.weak_find_latest_confirmed_descendant_ge`;
`strictSelectedResult_below_head` → `Weak.strictSelectedResult_below_head`;
`GetLatestConfirmedTrace` → `Weak.GetLatestConfirmedTrace`;
`E.fcrStep` / `E.getLatestConfirmedTraceAt` / `E.confirmed` →
`E.weakFcrStep` / `E.weakGetLatestConfirmedTraceAt` / `E.weakConfirmed`;
`SelectedHelperProvisosAt` → `Weak.SelectedHelperProvisosAt`.

**The one gate substitution, and why it costs nothing.**  Rule delta 1 makes
`Weak.will_current_target_be_justified` a genuinely *different* boolean from
the strong one (`Weak.compute_adversarial_weight` drops the store-evidence
equivocation discount), so a weak crossing edge does not literally produce the
antecedent of `Execution.AcceptedCurrentTargetA32GateRealizationProducerAt`.
It produces the *stronger* one: `will_current_target_be_justified_of_weak`
(`WeakRulePredicateBridge.lean`, reused verbatim) converts it.  Hence
`Weak.currentTargetAcceptedEdge_gate_and_support` concludes the strong
boolean, no weak twin of either A3.2 producer type is introduced, and the
producers built by the observer-side call supplier are drop-in.

**The single honesty substitution.**  `grep -n "E.honest"` on the strong
module returns exactly five hits, all of them `hv : v ∈ E.honest` binders on
the four action wrappers and on
`historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory`; honesty is used
*only* inside that last producer.  Every wrapper below therefore takes
`hcoh : E.ObserverCoherence cfg ext obs` (`WeakOneShotSafety.lean`) in place
of `hv` and calls `Weak.weakFcrStep_historicalA32QueryGeometryAt`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## The weak accepted crossing edge -/

/-- Weak twin of `CurrentTargetAcceptedEdge` (`SelectedFilterBridge.lean`): a
weak-selected-path tentative edge which actually crossed to a later block
epoch.  The substitution is exactly `findLatestSelectedTrace` →
`Weak.findLatestSelectedTrace`; the two conjuncts are kept in the same order
and the same shape as the strong abbreviation, so that
`Weak.SelectedHelperProvisosAt.current_target`
(`WeakSelectedStrictEdgeFilterSupply.lean`), which inlines these two
conjuncts as separate arguments, applies to `h.1` and `h.2` directly and no
bridging lemma is needed. -/
def CurrentTargetAcceptedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (Weak.findLatestSelectedTrace cfg ext fcrStore
      latestConfirmedRoot).2.2 ∧
    get_block_epoch cfg fcrStore.store a < get_block_epoch cfg fcrStore.store c

/-- Weak twin of `mem_findLatestSelectedTrace_tentative`
(`SelectedFilterBridge.lean`).  `WeakSelectedTrace.lean` landed the loop-level
`Weak.mem_tentativeLoopTrace` but no wrapper-level projection, so the strong
proof is replayed over `Weak.findLatestSelectedTrace`: unfolding the weak
wrapper and discharging the discarded-edge branches leaves exactly the weak
tentative loop trace, whose two executable guards are the weak
`Weak.is_one_confirmed` and `Weak.will_current_target_be_justified`. -/
theorem mem_findLatestSelectedTrace_tentative
    (fcrStore : FastConfirmationStore Root) (latestConfirmedRoot a c : Root)
    (h : (a, c) ∈
      (Weak.findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) :
    Weak.is_one_confirmed cfg ext fcrStore.store
        (get_current_balance_source fcrStore) c = true ∧
      (get_block_epoch cfg fcrStore.store a <
          get_block_epoch cfg fcrStore.store c →
        Weak.will_current_target_be_justified cfg ext fcrStore.store = true) := by
  simp only [findLatestSelectedTrace] at h
  split_ifs at h <;> try simp at h
  all_goals
    exact mem_tentativeLoopTrace cfg ext fcrStore _ _ a c h

/-- Weak twin of `CurrentTargetAcceptedEdge.current_target_gate`: a crossing
weak tentative edge really did pass the weak executable
`Weak.will_current_target_be_justified` guard.  Substitution: the strong
wrapper projection is replaced by `Weak.mem_findLatestSelectedTrace_tentative`
above. -/
theorem CurrentTargetAcceptedEdge.current_target_gate
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : Weak.CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot
      a c) :
    Weak.will_current_target_be_justified cfg ext fcrStore.store = true :=
  (Weak.mem_findLatestSelectedTrace_tentative cfg ext fcrStore
    latestConfirmedRoot a c h.1).2 h.2

/-- Weak twin of `CurrentTargetAcceptedEdge.one_confirmed`: every crossing
weak tentative edge also passed weak one-confirmation at the query's current
balance source.  Substitution: `is_one_confirmed` → `Weak.is_one_confirmed`,
which additionally reads that balance source. -/
theorem CurrentTargetAcceptedEdge.one_confirmed
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : Weak.CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot
      a c) :
    Weak.is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) c = true :=
  (Weak.mem_findLatestSelectedTrace_tentative cfg ext fcrStore
    latestConfirmedRoot a c h.1).1

/-- Weak twin of `Execution.selectedInput_current_of_result_current_no_crossing`
(`HistoricalCurrentTargetTrajectory.lean`): a current weak-selected result with
no retained epoch-crossing edge necessarily started from a current-epoch input.

Substitutions: `find_latest_confirmed_descendant` →
`Weak.find_latest_confirmed_descendant`, `findLatestSelectedTrace(_fst,
_parentTrace)` → the `Weak.` twins, `PreviousAcceptedEdge` →
`Weak.PreviousAcceptedEdge` (whose `.gates` is a five-conjunct weak record,
but whose first conjunct — the retained previous-epoch child is not current —
is unchanged, and is the only one used here).  The parent-trace geometry
(`SelectedParentTrace.exists_edge_entering_next_epoch`) is selector-free and
reused verbatim. -/
theorem selectedInput_current_of_result_current_no_crossing
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input : Root} (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hresultCurrent : get_block_epoch cfg query.store
      (Weak.find_latest_confirmed_descendant cfg ext query input) =
        get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetAcceptedEdge cfg ext query input a c) :
    get_block_epoch cfg query.store input =
      get_current_store_epoch cfg query.store := by
  rcases hinputEpoch with hcurrent | hprevious
  · exact hcurrent
  · have htrace := findLatestSelectedTrace_parentTrace cfg ext query
      hwf hwalk hhead input hinput
    have hghostCurrent : get_block_epoch cfg query.store
        (Weak.findLatestSelectedTrace cfg ext query input).1 =
          get_current_store_epoch cfg query.store := by
      simpa only [findLatestSelectedTrace_fst] using hresultCurrent
    have hstep : get_block_epoch cfg query.store input + 1 =
        get_block_epoch cfg query.store
          (Weak.findLatestSelectedTrace cfg ext query input).1 :=
      hprevious.trans hghostCurrent.symm
    obtain ⟨a, c, hm, hac, hcCurrent⟩ :=
      htrace.exists_edge_entering_next_epoch cfg hwf hstep
    rcases List.mem_append.mp hm with hprev | htent
    · have hcNotCurrent :=
        (show Weak.PreviousAcceptedEdge cfg ext query input a c from hprev).gates
          cfg ext
      exact False.elim (hcNotCurrent.1 (hcCurrent.trans hghostCurrent))
    · exact False.elim (hnoCrossing ⟨a, c, htent, hac⟩)

/-- Weak twin of `CurrentTargetAcceptedEdge.result_ne_input`
(`HistoricalCurrentTargetTrajectory.lean`): a retained weak current-target edge
makes the weak wrapper result strict.  Substitutions: the ghost trace and its
erasure lemma become `Weak.findLatestSelectedTrace(_parentTrace, _fst)`, the
result becomes `Weak.find_latest_confirmed_descendant`.  The slot arithmetic
on `SelectedParentTrace` is selector-free and reused verbatim. -/
theorem CurrentTargetAcceptedEdge.result_ne_input
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input a c : Root} (hinput : input ∈ query.store.block_roots)
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext query input a c) :
    Weak.find_latest_confirmed_descendant cfg ext query input ≠ input := by
  have htrace := findLatestSelectedTrace_parentTrace cfg ext query
    hwf hwalk hhead input hinput
  have hm : (a, c) ∈
      (Weak.findLatestSelectedTrace cfg ext query input).2.1 ++
        (Weak.findLatestSelectedTrace cfg ext query input).2.2 :=
    List.mem_append.mpr (Or.inr hedge.1)
  have hstartChild := htrace.edge_child_slot_gt_start hwf hm
  have hchildResult := htrace.edge_child_slot_le_result hwf hm
  intro heq
  have hslotLt : (query.store.blocks input).slot <
      (query.store.blocks
        (Weak.findLatestSelectedTrace cfg ext query input).1).slot :=
    hstartChild.trans_le hchildResult
  rw [findLatestSelectedTrace_fst, heq] at hslotLt
  exact (Nat.lt_irrefl _ hslotLt)

/-! ## The weak evaluator trace's selected-result equation -/

namespace GetLatestConfirmedTrace

/-- Weak twin of `GetLatestConfirmedTrace.selected_facts`
(`GetLatestConfirmedTrace.lean`): the exact result equation when the final
selector guard is active.  `WeakCandidateHistoryRecurrence.lean` landed
`Weak.GetLatestConfirmedTrace.selector_cases` but not this one-line
consequence, which every step lemma below opens with; the substitution is
`find_latest_confirmed_descendant` → `Weak.find_latest_confirmed_descendant`.
Like the strong form it is indexed by `trace.afterObserved`, so it applies
unchanged to carried, finalized-reset and observed-reset inputs. -/
theorem selected_facts
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved) :
    trace.result = Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved := by
  rcases trace.selector_cases cfg ext with ⟨_hresult, hfalse⟩ | ⟨hresult, _htrue⟩
  · exact False.elim (hfalse hselector)
  · exact hresult

end GetLatestConfirmedTrace

variable {E : Execution Root}

/-- Weak twin of `Execution.currentTargetAcceptedEdge_gate_and_support`
(`SelectedA32Support.lean`): a retained weak tentative epoch-crossing exposes
exactly the executable gate and the normative target-support proviso attached
to it.

Substitutions: `CurrentTargetAcceptedEdge` → `Weak.CurrentTargetAcceptedEdge`
and `SelectedHelperProvisosAt` → `Weak.SelectedHelperProvisosAt` (the
observer-quantified normative contract).  Because
`Weak.SelectedHelperProvisosAt.current_target` inlines the edge's two conjuncts
as separate arguments, they are supplied as `hedge.1` and `hedge.2` rather
than as a single edge argument.

The gate half is deliberately stated with the *strong*
`will_current_target_be_justified`, not the weak one.  Rule delta 1 makes the
two genuinely different booleans (`Weak.compute_adversarial_weight` drops the
store-evidence equivocation discount, so the weak projected honest FFG support
is no larger), but that is exactly the direction that makes the weak gate the
*stronger* claim: `will_current_target_be_justified_of_weak`
(`WeakRulePredicateBridge.lean`, reused verbatim, not cloned) turns the weak
boolean into the strong one.  Stating the conclusion this way is what lets the
unchanged strong A3.2 producer types
(`Execution.AcceptedCurrentTargetA32GateRealizationProducerAt` and its
fixed-source sibling, whose antecedent is the strong boolean) be reused
without a weak twin, and it is what makes the crossing lemmas below accept the
producers built by the observer-side call supplier.  The weak-spelled gate
remains available as `Weak.CurrentTargetAcceptedEdge.current_target_gate`.
The normative half, `HonestVotesSupportTarget`, is the unchanged strong
predicate. -/
theorem currentTargetAcceptedEdge_gate_and_support
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E v q query
      latestConfirmedRoot)
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext query latestConfirmedRoot
      a c) :
    _root_.FastConfirmation.Spec.will_current_target_be_justified cfg ext
        query.store = true ∧
      HonestVotesSupportTarget cfg E
        (get_current_target cfg query.store) q :=
  ⟨will_current_target_be_justified_of_weak cfg ext query.store
      (Weak.CurrentTargetAcceptedEdge.current_target_gate cfg ext hedge),
    hprovisos.current_target a c hedge.1 hedge.2⟩

/-! ## Selector-input generic inheritance -/

/-- Weak twin of `Execution.selectedCurrentNoCrossingAcceptedSegment`
(`AcceptedHistoricalA32Step.lean`): the no-crossing accepted segment for the
weak final selector phase, independent of which ordered reset phase supplied
its input.

Substitutions: `GetLatestConfirmedTrace` → `Weak.GetLatestConfirmedTrace` (and
`.selected_facts` → the twin above), `CurrentTargetAcceptedEdge` →
`Weak.CurrentTargetAcceptedEdge`, `find_latest_confirmed_descendant` →
`Weak.find_latest_confirmed_descendant`, `find_latest_confirmed_descendant_ge`
→ `weak_find_latest_confirmed_descendant_ge`, and
`selectedInput_current_of_result_current_no_crossing` → the weak twin above.
The epoch arithmetic, the accepted-segment constructor
`Execution.knownSameEpochAncestrySegment_of_known_ancestor` and its
projection to `AcceptedProjectedSameEpochSegment` are selector-free and reused
verbatim. -/
theorem selectedCurrentNoCrossingAcceptedSegment
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetAcceptedEdge cfg ext query trace.afterObserved a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    AcceptedProjectedSameEpochSegment cfg ext E B.state
      trace.afterObserved trace.result := by
  have hresult := trace.selected_facts cfg ext hselector
  have hinputEpochUpper : get_block_epoch cfg query.store
        trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpper
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    by_cases heq : get_block_epoch cfg query.store trace.afterObserved =
        get_current_store_epoch cfg query.store
    · exact Or.inl heq
    · right
      have hguard : get_block_epoch cfg query.store trace.afterObserved + 1 ≥
          get_current_store_epoch cfg query.store := by
        simpa only [getLatestSelectorGuard] using hselector
      exact Nat.le_antisymm
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
        hguard
  have hselectedCurrent : get_block_epoch cfg query.store
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved) =
      get_current_store_epoch cfg query.store := by
    rw [← hresult]
    exact hresultCurrent
  have hinputCurrent : get_block_epoch cfg query.store trace.afterObserved =
      get_current_store_epoch cfg query.store :=
    Weak.selectedInput_current_of_result_current_no_crossing cfg ext
      hparent hwalk hhead hinputKnown hinputEpoch hselectedCurrent hnoCrossing
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hancestor : is_ancestor query.store
      (get_node_for_root trace.result)
      (get_node_for_root trace.afterObserved) = true := by
    rw [hresult]
    exact hselectedFacts.1
  have hlands : get_ancestor query.store (ForkChoiceNode.mk trace.result)
      (query.store.blocks trace.afterObserved).slot =
        ForkChoiceNode.mk trace.afterObserved := by
    simpa only [is_ancestor, decide_eq_true_eq, get_node_for_root]
      using hancestor
  have hsameEpoch : compute_epoch_at_slot cfg
        (query.store.blocks trace.afterObserved).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      hinputCurrent.trans hresultCurrent.symm
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store trace.afterObserved
        trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor cfg hparent
      (hwalk trace.afterObserved hinputKnown trace.result hresultKnown)
      hlands hsameEpoch hstrictNonGenesis
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwfE hcore hstore hknownSegment

/-- Weak twin of `Execution.selectedCurrentNoCrossingLineage`
(`AcceptedHistoricalA32Step.lean`): preserve a historical lineage through a
no-crossing weak selector phase, regardless of whether the input was carried
or supplied by a reset.

Substitutions are the same as for the segment lemma above.  The payload side
(`Execution.AcceptedHistoricalA32LineageAt` and its `.extend`,
`Execution.acceptedBlockAt_of_causal_known`,
`Execution.CausalStore.acceptedBlockAt_iff_eq`,
`acceptedProjectedSameEpochSegment_rootDescends`) is honesty-free and
selector-free and is reused verbatim. -/
noncomputable def selectedCurrentNoCrossingLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetAcceptedEdge cfg ext query trace.afterObserved a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots)
    {e : Epoch}
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      trace.afterObserved e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e := by
  have hsegment := Weak.selectedCurrentNoCrossingAcceptedSegment cfg ext B hwfE
    hcore hstore hparent hwalk hhead trace hinputKnown hinputSlotUpper
      hselector hresultCurrent hnoCrossing hstrictNonGenesis
  have hresult := trace.selected_facts cfg ext hselector
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact (weak_find_latest_confirmed_descendant_ge cfg ext query hparent hwalk
      hhead trace.afterObserved hinputKnown).2
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hresultKnown
  have hinputBlockEq : query.store.blocks trace.afterObserved =
      hprevious.tip_block :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E hwfE hstore
      hinputKnown).mp hprevious.tip_at
  have hinputEpochE : get_block_epoch cfg query.store
      trace.afterObserved = e := by
    simpa only [get_block_epoch, hinputBlockEq] using hprevious.tip_epoch
  have hresultEpochE : get_block_epoch cfg query.store trace.result = e := by
    have hinputCurrent : get_block_epoch cfg query.store trace.afterObserved =
        get_current_store_epoch cfg query.store := by
      have hinputEpochUpper : get_block_epoch cfg query.store
            trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
        simp only [get_block_epoch, get_current_store_epoch,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right hinputSlotUpper
      have hinputEpoch :
          get_block_epoch cfg query.store trace.afterObserved =
              get_current_store_epoch cfg query.store ∨
            get_block_epoch cfg query.store trace.afterObserved + 1 =
              get_current_store_epoch cfg query.store := by
        by_cases heq : get_block_epoch cfg query.store trace.afterObserved =
            get_current_store_epoch cfg query.store
        · exact Or.inl heq
        · right
          exact Nat.le_antisymm
            (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
            (by simpa only [getLatestSelectorGuard] using hselector)
      apply Weak.selectedInput_current_of_result_current_no_crossing cfg ext
        hparent hwalk hhead hinputKnown hinputEpoch
      · rw [← hresult]
        exact hresultCurrent
      · exact hnoCrossing
    exact hresultCurrent.trans (hinputCurrent.symm.trans hinputEpochE)
  exact hprevious.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [get_block_epoch] using hresultEpochE)
    (E.acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-! ## Selector-input generic crossing -/

/-- Weak twin of `Execution.selectedCurrentCrossingAcceptedTargetSegment`
(`AcceptedHistoricalA32Step.lean`): reconstruct the accepted same-epoch segment
from the current target to a current result selected from any weak ordered
evaluator input.

Substitutions: the trace and its `selected_facts`, the edge and its
`result_ne_input`, `find_latest_confirmed_descendant(_ge)` and
`strictSelectedResult_below_head` all become their `Weak.` counterparts.  The
head-chain-to-current-target geometry (`Execution.currentEpochBlock_descends_currentTarget`)
and the accepted-segment constructor are selector-free and reused verbatim. -/
theorem selectedCurrentCrossingAcceptedTargetSegment
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hcurrentWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (htargetEpoch : get_block_epoch cfg query.store
      (get_current_target cfg query.store).root =
        (get_current_target cfg query.store).epoch)
    {a c : Root}
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext query
      trace.afterObserved a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks (get_current_target cfg query.store).root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    AcceptedProjectedSameEpochSegment cfg ext E B.state
      (get_current_target cfg query.store).root trace.result := by
  have hresult := trace.selected_facts cfg ext hselector
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    Weak.CurrentTargetAcceptedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    Weak.strictSelectedResult_below_head cfg ext hparent hwalk hhead
      hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  obtain ⟨htargetKnown, hresultDescendsTarget⟩ :=
    Execution.currentEpochBlock_descends_currentTarget cfg hparent hwalk hhead
      hresultKnown hbelowResult hcurrentWalk hresultCurrent
  have hlands : get_ancestor query.store (ForkChoiceNode.mk trace.result)
      (query.store.blocks (get_current_target cfg query.store).root).slot =
        ForkChoiceNode.mk (get_current_target cfg query.store).root := by
    simpa only [is_ancestor, decide_eq_true_eq, get_node_for_root]
      using hresultDescendsTarget
  have htargetCurrent : (get_current_target cfg query.store).epoch =
      get_current_store_epoch cfg query.store := rfl
  have hsameEpoch : compute_epoch_at_slot cfg
        (query.store.blocks (get_current_target cfg query.store).root).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      htargetEpoch.trans (htargetCurrent.trans hresultCurrent.symm)
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store
        (get_current_target cfg query.store).root trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor cfg hparent
      (hwalk (get_current_target cfg query.store).root htargetKnown
        trace.result hresultKnown)
      hlands hsameEpoch hstrictNonGenesis
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwfE hcore hstore hknownSegment

/-- Weak twin of `Execution.selectedCurrentCrossingLineage`
(`AcceptedHistoricalA32Step.lean`): a current crossing from any weak evaluator
input creates a fresh historical payload at the concrete weak selected result.

Substitutions: the trace/edge/selector families become their `Weak.`
counterparts, `SelectedHelperProvisosAt` becomes `Weak.SelectedHelperProvisosAt`
(the observer-quantified normative contract), and
`currentTargetAcceptedEdge_gate_and_support` becomes the weak twin above — so
the gate handed to the producer is `Weak.will_current_target_be_justified`.
The payload constructors
(`AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedSameEpochSegment`,
`AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget`,
`AcceptedHistoricalA32LineageAt.refl`) and the checkpoint geometry are reused
verbatim. -/
noncomputable def selectedCurrentCrossingLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwfE : WellFormedExecution E)
    (hcore : E.ExactCausalStoreWellFormedCore cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hcurrentWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (htargetEpoch : get_block_epoch cfg query.store
      (get_current_target cfg query.store).root =
        (get_current_target cfg query.store).epoch)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E v q query
      trace.afterObserved)
    {a c : Root}
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext query
      trace.afterObserved a c)
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks (get_current_target cfg query.store).root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
      (get_current_store_epoch cfg query.store) := by
  have hresult := trace.selected_facts cfg ext hselector
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    Weak.CurrentTargetAcceptedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    Weak.strictSelectedResult_below_head cfg ext hparent hwalk hhead
      hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  have htargetCheckpoint :=
    Execution.current_target_eq_checkpoint_of_current_epoch_ancestor cfg hparent
      hbelowResult hresultCurrent hcurrentWalk
  have htarget : get_current_target cfg query.store =
      B.state.C trace.result (get_current_store_epoch cfg query.store) := by
    calc
      get_current_target cfg query.store =
          get_checkpoint_for_block cfg query.store trace.result
            (get_block_epoch cfg query.store trace.result) :=
        htargetCheckpoint
      _ = get_checkpoint_for_block cfg query.store trace.result
            (get_current_store_epoch cfg query.store) := by
        rw [hresultCurrent]
      _ = B.state.C trace.result
            (get_current_store_epoch cfg query.store) :=
        (B.coherence.checkpoint_of_known hstore trace.result hresultKnown
          (get_current_store_epoch cfg query.store)).symm
  have hsegment := Weak.selectedCurrentCrossingAcceptedTargetSegment cfg ext B
    hwfE hcore hstore hparent hwalk hhead hcurrentWalk trace hinputKnown
      hselector hresultCurrent htargetEpoch hedge hstrictNonGenesis
  have hgateAndSupport :=
    Weak.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
  have htargetGate := hproducer hgateAndSupport.1 hgateAndSupport.2
  have htargetCurrent : (get_current_target cfg query.store).epoch =
      get_current_store_epoch cfg query.store := rfl
  have hresultTargetEpoch : get_block_epoch cfg query.store trace.result =
      (get_current_target cfg query.store).epoch :=
    hresultCurrent.trans htargetCurrent.symm
  have hfixed :=
    Execution.AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedSameEpochSegment
      cfg ext B hphase htargetEpoch hresultTargetEpoch hsegment htargetGate
  have hpayload :=
    Execution.AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget cfg ext B
      hstore hresultKnown hresultCurrent htarget hfixed
  exact Execution.AcceptedHistoricalA32LineageAt.refl cfg ext hpayload

/-- Weak twin of
`Execution.selectedCurrentCrossingLineage_of_fixedSourceProducer`
(`AcceptedHistoricalA32Step.lean`): the fresh-crossing constructor at the
fixed-source seam, the form consumed by the weak one-step dispatcher.  Its
producer must already preserve the weak selected result's `VSAt` source, so it
stays valid whether the epoch-boundary checkpoint block is current or old.

Substitutions are exactly those of `Weak.selectedCurrentCrossingLineage`; the
fixed-source producer type itself is the unchanged strong
`Execution.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt`,
which is indexed by a bare query and a bare root and so needs no twin. -/
noncomputable def selectedCurrentCrossingLineage_of_fixedSourceProducer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hcurrentWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root)
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E v q query
      trace.afterObserved)
    {a c : Root}
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext query
      trace.afterObserved a c)
    (hproducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
        cfg ext B.anchor B.state q query trace.result) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result
      (get_current_store_epoch cfg query.store) := by
  have hresult := trace.selected_facts cfg ext hselector
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    Weak.CurrentTargetAcceptedEdge.result_ne_input cfg ext hparent hwalk hhead
      hinputKnown hedge
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    Weak.strictSelectedResult_below_head cfg ext hparent hwalk hhead
      hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  have htargetCheckpoint :=
    Execution.current_target_eq_checkpoint_of_current_epoch_ancestor cfg hparent
      hbelowResult hresultCurrent hcurrentWalk
  have htarget : get_current_target cfg query.store =
      B.state.C trace.result (get_current_store_epoch cfg query.store) := by
    calc
      get_current_target cfg query.store =
          get_checkpoint_for_block cfg query.store trace.result
            (get_block_epoch cfg query.store trace.result) :=
        htargetCheckpoint
      _ = get_checkpoint_for_block cfg query.store trace.result
            (get_current_store_epoch cfg query.store) := by
        rw [hresultCurrent]
      _ = B.state.C trace.result
            (get_current_store_epoch cfg query.store) :=
        (B.coherence.checkpoint_of_known hstore trace.result hresultKnown
          (get_current_store_epoch cfg query.store)).symm
  have hgateAndSupport :=
    Weak.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
  have hfixed := hproducer hgateAndSupport.1 hgateAndSupport.2
  have hpayload :=
    Execution.AcceptedHistoricalA32GatePayloadAt.of_fixedSourceCurrentTarget cfg ext B
      hstore hresultKnown hresultCurrent htarget hfixed
  exact Execution.AcceptedHistoricalA32LineageAt.refl cfg ext hpayload

/-! ## Weak-evaluator query facts -/

/-- Weak twin of
`Execution.GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing`
(`AcceptedHistoricalA32Step.lean`): expose the current-input fact already used
internally by the generic no-crossing constructor.

Substitutions: `GetLatestConfirmedTrace` → `Weak.GetLatestConfirmedTrace` (so
that, unlike the strong declaration, this one really is reachable by dot
notation on a weak trace), `CurrentTargetAcceptedEdge` →
`Weak.CurrentTargetAcceptedEdge`, and the inheritance lemma → the weak twin
above.  The selector guard `getLatestSelectorGuard` is shared between the two
models and is reused verbatim. -/
theorem GetLatestConfirmedTrace.input_current_of_selected_current_no_crossing
    {query : FastConfirmationStore Root}
    (trace : Weak.GetLatestConfirmedTrace cfg ext query)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinputKnown : trace.afterObserved ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks trace.afterObserved).slot ≤
      get_current_slot cfg query.store)
    (hselector : getLatestSelectorGuard cfg query trace.afterObserved)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetAcceptedEdge cfg ext query trace.afterObserved a c) :
    get_block_epoch cfg query.store trace.afterObserved =
      get_current_store_epoch cfg query.store := by
  have hresult := trace.selected_facts cfg ext hselector
  have hinputEpochUpper : get_block_epoch cfg query.store
        trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpper
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    by_cases heq : get_block_epoch cfg query.store trace.afterObserved =
        get_current_store_epoch cfg query.store
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
        (by simpa only [getLatestSelectorGuard] using hselector))
  apply Weak.selectedInput_current_of_result_current_no_crossing cfg ext
    hparent hwalk hhead hinputKnown hinputEpoch
  · rw [← hresult]
    exact hresultCurrent
  · exact hnoCrossing

/-- Weak twin of `Execution.confirmed_current_at_previousStore_of_query`
(`AcceptedHistoricalA32Step.lean`): transport current-epoch status of the
carried root from the weak query store back to the preceding execution store.
Store growth preserves its block, while the preceding clock bound forces
equality of the two current epochs in precisely this case.

Substitutions: `E.confirmed` → `E.weakConfirmed`, `E.fcrStep` →
`E.weakFcrStep`, and `E.fcrStep_store` / `E.fcrStep_confirmed_root` →
`E.weakFcrStep_store` / `E.weakFcrStep_confirmed_root`
(`WeakFCRCallContracts.lean`).  Everything else here is about `E.store`, which
the weak model shares with the strong one verbatim: `store_storeLE`,
`blocks_agree`, `store_blocks_slot_le_current`, `store_current_slot` and
`slot_at_mono` are reused unchanged. -/
theorem confirmed_current_at_previousStore_of_query
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : ℕ}
    (hknownN : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hcurrentQ : get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
        (E.weakFcrStep cfg ext v n).confirmed_root =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) :
    get_block_epoch cfg (E.store cfg ext v n) (E.weakConfirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis
  have hknownN1 : E.weakConfirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.weakConfirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.weakConfirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
  have hinputSlotUpperN :
      ((E.store cfg ext v n).blocks
        (E.weakConfirmed cfg ext v n)).slot ≤
        get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hT.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v n (E.weakConfirmed cfg ext v n) hknownN
  have hcurrentMono : get_current_store_epoch cfg (E.store cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
  have hblockEpochNUpper : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpperN
  have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
        (E.weakConfirmed cfg ext v n) =
      get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.weakConfirmed cfg ext v n) := by
    simp only [get_block_epoch, hblockAgree]
  have hcurrentQ' : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.weakConfirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.weakFcrStep_store, E.weakFcrStep_confirmed_root]
      using hcurrentQ
  have hreverse : get_current_store_epoch cfg
      (E.store cfg ext v (n + 1)) ≤
        get_current_store_epoch cfg (E.store cfg ext v n) := by
    rw [← hcurrentQ', ← hblockEpochAgree]
    exact hblockEpochNUpper
  have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    Nat.le_antisymm hcurrentMono hreverse
  exact hblockEpochAgree.trans (hcurrentQ'.trans hcurrentEq.symm)

/-- Weak twin of `Execution.actualFinalizedResetCurrentAnchorLineage`
(`AcceptedHistoricalA32Step.lean`): the only current-epoch finalized reset
payload is the trusted-anchor payload.  No quorum is synthesized in this
branch.

This is the "store-only" case flagged in the port plan.  The strong statement
and its whole proof mention the evaluator solely through
`(E.fcrStep cfg ext v n).store`, and `Execution.weakFcrStep_store` gives the
weak query the very same `E.store cfg ext v (n + 1)`.  So rather than replay
roughly forty lines of reset classification, this twin *transports* the strong
theorem along `E.weakFcrStep_store` / `E.fcrStep_store`; nothing is cloned and
the reset classifiers of `AcceptedResetCheckpointClassification.lean` are used
only through the strong theorem. -/
noncomputable def actualFinalizedResetCurrentAnchorLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (n : ℕ)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext v n).store
        (E.weakFcrStep cfg ext v n).store.finalized_checkpoint.root =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakFcrStep cfg ext v n).store.finalized_checkpoint.root
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext v n).store) := by
  have hstrong := E.actualFinalizedResetCurrentAnchorLineage cfg ext B hT
    hanchor hboundary v n
    (by simpa only [E.weakFcrStep_store, E.fcrStep_store] using hcurrent)
  simpa only [E.weakFcrStep_store, E.fcrStep_store] using hstrong

/-! ## Observer-facing wrappers -/

/-- Weak twin of
`Execution.acceptedFixedSourceProducerAt_of_selectedCurrentCrossing`
(`AcceptedHistoricalA32Step.lean`): retie the query-local accepted target gate
to the weak selected result, including the skipped-boundary old-target case,
and eta-expand it to the fixed-source producer consumed by the weak historical
dispatcher.

Honesty substitution: the strong wrapper's `hv : v ∈ E.honest` is replaced by
`hcoh : E.ObserverCoherence cfg ext obs`, and its single use — the call to
`E.historicalA32QueryGeometryAt_of_acceptedGlobalTrajectory` — by
`Weak.weakFcrStep_historicalA32QueryGeometryAt`
(`WeakHistoricalA32Geometry.lean`).  That is the only honesty use in the whole
strong step layer.

Selector substitutions: `E.getLatestConfirmedTraceAt` →
`E.weakGetLatestConfirmedTraceAt`, `E.fcrStep` → `E.weakFcrStep`,
`findLatestSelectedTrace(_parentTrace, _fst)` → the `Weak.` twins,
`find_latest_confirmed_descendant(_ge)` → `Weak.…` /
`weak_find_latest_confirmed_descendant_ge`, `strictSelectedResult_below_head`
→ `Weak.strictSelectedResult_below_head`, `CurrentTargetAcceptedEdge` →
`Weak.CurrentTargetAcceptedEdge`.  Both producer types and
`Execution.AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedTargetWalk`
are honesty-free, selector-free and gate-transparent here (the gate arrives as
the producer's own `intro`duced antecedent, never from the weak edge), so they
are reused verbatim. -/
noncomputable def
    acceptedFixedSourceProducerAt_of_selectedCurrentCrossing
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {a c : Root}
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    (htargetProducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)) :
    E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result := by
  let query := E.weakFcrStep cfg ext obs n
  let trace := E.weakGetLatestConfirmedTraceAt cfg ext obs n
  change trace.afterObserved ∈ query.store.block_roots at hinputKnown
  change getLatestSelectorGuard cfg query trace.afterObserved at hselector
  change get_block_epoch cfg query.store trace.result =
    get_current_store_epoch cfg query.store at hresultCurrent
  change Weak.CurrentTargetAcceptedEdge cfg ext query trace.afterObserved a c
    at hedge
  change E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext B.anchor
    B.state (n + 1) query at htargetProducer
  change E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
    cfg ext B.anchor B.state (n + 1) query trace.result
  intro hgate hsupport
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  change E.HistoricalA32QueryGeometryAt cfg ext query at hG
  have hresult := trace.selected_facts cfg ext hselector
  have hselectedFacts := weak_find_latest_confirmed_descendant_ge cfg ext query
    hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hparentTrace := findLatestSelectedTrace_parentTrace cfg ext query
    hG.parent hG.walk hG.head_known trace.afterObserved hinputKnown
  have hm : (a, c) ∈
      (Weak.findLatestSelectedTrace cfg ext query trace.afterObserved).2.1 ++
        (Weak.findLatestSelectedTrace cfg ext query trace.afterObserved).2.2 :=
    List.mem_append.mpr (Or.inr hedge.1)
  have hinputToA : get_block_epoch cfg query.store trace.afterObserved ≤
      get_block_epoch cfg query.store a := by
    simp only [get_block_epoch, compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (hparentTrace.start_slot_le_edge_parent hG.parent hm)
  have hchildToResult : get_block_epoch cfg query.store c ≤
      get_block_epoch cfg query.store trace.result := by
    have hslots := hparentTrace.edge_child_slot_le_result hG.parent hm
    rw [findLatestSelectedTrace_fst, ← hresult] at hslots
    simp only [get_block_epoch, compute_epoch_at_slot]
    exact Nat.div_le_div_right hslots
  have hinputOld : get_block_epoch cfg query.store trace.afterObserved <
      get_current_store_epoch cfg query.store := by
    calc
      get_block_epoch cfg query.store trace.afterObserved ≤
          get_block_epoch cfg query.store a := hinputToA
      _ < get_block_epoch cfg query.store c := hedge.2
      _ ≤ get_block_epoch cfg query.store trace.result := hchildToResult
      _ = get_current_store_epoch cfg query.store := hresultCurrent
  have hcurrentNonGenesis : ∀ r ∈ query.store.block_roots,
      get_block_epoch cfg query.store r =
          (get_current_target cfg query.store).epoch →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hrCurrent
    apply hG.strict_non_genesis trace.afterObserved hinputKnown r hr
    apply Nat.lt_of_not_ge
    intro hrLeInput
    have hepochLe : get_block_epoch cfg query.store r ≤
        get_block_epoch cfg query.store trace.afterObserved := by
      simp only [get_block_epoch, compute_epoch_at_slot]
      exact Nat.div_le_div_right hrLeInput
    have hcurrentLeInput : get_current_store_epoch cfg query.store ≤
        get_block_epoch cfg query.store trace.afterObserved := by
      calc
        get_current_store_epoch cfg query.store =
            (get_current_target cfg query.store).epoch := rfl
        _ = get_block_epoch cfg query.store r := hrCurrent.symm
        _ ≤ get_block_epoch cfg query.store trace.afterObserved := hepochLe
    exact (Nat.not_le_of_gt hinputOld) hcurrentLeInput
  have hstrict : Weak.find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved :=
    Weak.CurrentTargetAcceptedEdge.result_ne_input cfg ext hG.parent hG.walk
      hG.head_known hinputKnown hedge
  have hbelowSelected : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query
          trace.afterObserved)) = true :=
    Weak.strictSelectedResult_below_head cfg ext hG.parent hG.walk
      hG.head_known hinputKnown hstrict
  have hbelowResult : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hresult]
    exact hbelowSelected
  have htargetCheckpoint :=
    Execution.current_target_eq_checkpoint_of_current_epoch_ancestor cfg
      hG.parent hbelowResult hresultCurrent hG.current_walk
  let target := get_current_target cfg query.store
  have heta : get_ancestor query.store (get_head cfg query.store)
      (compute_start_slot_at_epoch cfg target.epoch) =
        get_node_for_root target.root := by
    rfl
  have htargetSpec := get_ancestor_spec hG.parent hG.current_walk
  rw [show compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) =
      compute_start_slot_at_epoch cfg target.epoch by rfl] at htargetSpec
  rw [heta] at htargetSpec
  have hcarrierWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg target.epoch) trace.result := by
    exact (hG.walk target.root htargetSpec.1 trace.result hresultKnown).mono
      htargetSpec.2
  have hlandsRoot :
      (get_ancestor query.store (ForkChoiceNode.mk trace.result)
        (compute_start_slot_at_epoch cfg target.epoch)).root =
          target.root := by
    have hroot := congrArg Checkpoint.root htargetCheckpoint
    simpa only [target, get_checkpoint_for_block, get_checkpoint_block,
      hresultCurrent] using hroot.symm
  have hlands : get_ancestor query.store (ForkChoiceNode.mk trace.result)
      (compute_start_slot_at_epoch cfg target.epoch) =
        ForkChoiceNode.mk target.root := by
    generalize hnode : get_ancestor query.store
      (ForkChoiceNode.mk trace.result)
        (compute_start_slot_at_epoch cfg target.epoch) = node
        at hlandsRoot ⊢
    obtain ⟨r⟩ := node
    change r = target.root at hlandsRoot
    cases hlandsRoot
    rfl
  have hcarrierEpoch : get_block_epoch cfg query.store trace.result =
      target.epoch := hresultCurrent
  have htargetGate := htargetProducer hgate hsupport
  exact
    Execution.AcceptedCurrentTargetA32GateRealization.fixedSource_of_acceptedTargetWalk
      (E := E) cfg ext B hT.wellFormed hG.exact_core hphase hboundaryPhase
        hG.causal hG.parent hcarrierEpoch
        (by simpa only [target] using hcurrentNonGenesis)
        hcarrierWalk hlands htargetGate

/-- Weak twin of
`Execution.selectedCurrentNoCrossingLineageAt_of_acceptedGlobalTrajectory`
(`AcceptedHistoricalA32Step.lean`): the action-facing arbitrary-input
no-crossing wrapper.  Honesty substitution `hv` → `hcoh` through
`Weak.weakFcrStep_historicalA32QueryGeometryAt`, plus the evaluator
substitutions `E.fcrStep` → `E.weakFcrStep` and `E.getLatestConfirmedTraceAt`
→ `E.weakGetLatestConfirmedTraceAt`; the body just re-plumbs the geometry
bundle into `Weak.selectedCurrentNoCrossingLineage`. -/
noncomputable def
    selectedCurrentNoCrossingLineageAt_at_observer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hnoCrossing : ¬ ∃ a c : Root,
      Weak.CurrentTargetAcceptedEdge cfg ext (E.weakFcrStep cfg ext obs n)
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    {e : Epoch}
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result e := by
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  exact Weak.selectedCurrentNoCrossingLineage cfg ext B hT.wellFormed
    hG.exact_core hG.causal hG.parent hG.walk hG.head_known
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) hinputKnown
      (hG.slot_upper _ hinputKnown) hselector hresultCurrent hnoCrossing
      (hG.strict_non_genesis _ hinputKnown) hprevious

/-- Weak twin of
`Execution.selectedCurrentCrossingLineageAt_of_acceptedGlobalTrajectory`
(`AcceptedHistoricalA32Step.lean`): the action-facing arbitrary-input crossing
wrapper.  Same honesty and evaluator substitutions as the no-crossing wrapper,
plus `SelectedHelperProvisosAt` → `Weak.SelectedHelperProvisosAt`, which is the
observer-quantified normative call contract that replaces the honest-quantified
strong one. -/
noncomputable def
    selectedCurrentCrossingLineageAt_at_observer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (htargetEpoch : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
      (get_current_target cfg (E.weakFcrStep cfg ext obs n).store).root =
        (get_current_target cfg (E.weakFcrStep cfg ext obs n).store).epoch)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    {a c : Root}
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) := by
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  exact Weak.selectedCurrentCrossingLineage cfg ext B hT.wellFormed
    hG.exact_core hphase hG.causal hG.parent hG.walk hG.head_known
      hG.current_walk (E.weakGetLatestConfirmedTraceAt cfg ext obs n)
      hinputKnown hselector hresultCurrent htargetEpoch hprovisos hedge
      hproducer
      (hG.strict_non_genesis
        (get_current_target cfg (E.weakFcrStep cfg ext obs n).store).root
        (get_ancestor_spec hG.parent hG.current_walk).1)

/-- Weak twin of
`Execution.selectedCurrentCrossingLineageAt_of_fixedSourceProducer`
(`AcceptedHistoricalA32Step.lean`): the action-facing fixed-source crossing
wrapper used by the weak dispatcher.  The old-target/current-target
distinction is entirely upstream of this seam.  Same honesty and evaluator
substitutions as the two wrappers above. -/
noncomputable def
    selectedCurrentCrossingLineageAt_of_fixedSourceProducer
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinputKnown :
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
        (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : getLatestSelectorGuard cfg (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    (hresultCurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store
        (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    (hprovisos : Weak.SelectedHelperProvisosAt cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved)
    {a c : Root}
    (hedge : Weak.CurrentTargetAcceptedEdge cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved a c)
    (hproducer :
      E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
        cfg ext B.anchor B.state (n + 1) (E.weakFcrStep cfg ext obs n)
          (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result
      (get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) := by
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh hHn1
  exact Weak.selectedCurrentCrossingLineage_of_fixedSourceProducer cfg ext B
    hG.causal hG.parent hG.walk hG.head_known hG.current_walk
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n) hinputKnown hselector
      hresultCurrent hprovisos hedge hproducer

end Weak

end FastConfirmation.Spec
