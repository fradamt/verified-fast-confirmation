module
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32Payload
public import FastConfirmation.Spec.Proof.AcceptedSameEpochSegmentRealization
public import FastConfirmation.Spec.Proof.GetLatestConfirmedTrace
public import FastConfirmation.Spec.Proof.HistoricalCurrentTargetTrajectory

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# First payload-preserving actual evaluator branch

This file closes the carried/no-restart/current/no-crossing branch of the
future outer historical induction.  The exact evaluator trace proves that the
selector input is the prior confirmed root.  The executable selector geometry
proves that this input is current-epoch, and an actual accepted same-epoch
segment extends the prior safety-free lineage.

The theorem consumes the prior lineage as its induction hypothesis.  It does
not consume a fresh historical payload, certificate producer, SIR result,
canonicity interval, or safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact carried-selector branch projection -/

namespace GetLatestConfirmedTrace

/-- When the first two guards are genuinely false and the selector guard is
genuinely true at the carried root, guard priority identifies all three
intermediate values even if the carried/finalized/observed roots happen to be
equal. -/
theorem carriedSelected_facts
    {query : FastConfirmationStore Root}
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext query)
    (hobserved : getLatestObservedRestartGuard cfg query
      query.confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg query query.confirmed_root) :
    trace.afterFinalized = query.confirmed_root ∧
      trace.afterObserved = query.confirmed_root ∧
      trace.result = find_latest_confirmed_descendant cfg ext query
        query.confirmed_root := by
  have hafterFinalized : trace.afterFinalized = query.confirmed_root := by
    rcases trace.afterFinalized_cases with ⟨heq, _⟩ | ⟨_, htrue⟩
    · exact heq
    · exact False.elim (hfinalized htrue)
  have hafterObserved : trace.afterObserved = query.confirmed_root := by
    rcases trace.afterObserved_cases with ⟨heq, _⟩ | ⟨_, htrue⟩
    · exact heq.trans hafterFinalized
    · have : getLatestObservedRestartGuard cfg query
          query.confirmed_root = true := by
        rwa [hafterFinalized] at htrue
      rw [hobserved] at this
      contradiction
  have hresult : trace.result =
      find_latest_confirmed_descendant cfg ext query query.confirmed_root := by
    rcases trace.selector_cases with ⟨_, hfalse⟩ | ⟨heq, _⟩
    · have : ¬ getLatestSelectorGuard cfg query
          query.confirmed_root := by
        rwa [hafterObserved] at hfalse
      exact False.elim (this hselector)
    · simpa only [hafterObserved] using heq
  exact ⟨hafterFinalized, hafterObserved, hresult⟩

end GetLatestConfirmedTrace

namespace Execution

variable {E : Execution Root}

/-! ## Concrete selected ancestry segment -/

/-- A known ancestry walk between equal-epoch endpoints is a concrete
same-epoch segment once every strict child above the first endpoint is known
not to be a trusted genesis root.

The endpoint equality alone is enough for the epoch argument: parent slots
strictly decrease, so every intermediate epoch is squeezed between the two
equal endpoint epochs.  The separate non-genesis premise is intentionally
visible here because root identities can be overwritten in the executable
store; the actual-call specialization below derives it from the fixed anchor
message and anchor-minimal-slot theorem. -/
theorem knownSameEpochAncestrySegment_of_known_ancestor_root
    {store : Store Root}
    (hparent : ParentSlotLt store)
    {first last : Root}
    (hwalk : WalkKnown store (store.blocks first).slot last)
    (hlands : (get_ancestor store (ForkChoiceNode.mk last .pending)
      (store.blocks first).slot).root = first)
    (hsame : compute_epoch_at_slot cfg (store.blocks first).slot =
      compute_epoch_at_slot cfg (store.blocks last).slot)
    (hstrictNonGenesis : ∀ r ∈ store.block_roots,
      (store.blocks first).slot < (store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      store first last := by
  have go : ∀ {tip : Root},
      WalkKnown store (store.blocks first).slot tip →
      (get_ancestor store (ForkChoiceNode.mk tip .pending)
          (store.blocks first).slot).root = first →
      compute_epoch_at_slot cfg (store.blocks first).slot =
          compute_epoch_at_slot cfg (store.blocks tip).slot →
      KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
        store first tip := by
    intro tip htipWalk
    induction htipWalk with
    | @stop r hr hle =>
        intro htipLands _
        have hrEq : r = first := by
          rw [get_ancestor_stop hle] at htipLands
          exact htipLands
        subst r
        exact .refl first hr
    | @step r hr hgt hp ih =>
        intro htipLands htipEpoch
        have hparentLands :
            (get_ancestor store
                (ForkChoiceNode.mk (store.blocks r).parent_root .pending)
                (store.blocks first).slot).root = first := by
          rw [get_ancestor_step hparent hr hgt hp] at htipLands
          exact htipLands
        have hfirstLeParent : (store.blocks first).slot ≤
            (store.blocks (store.blocks r).parent_root).slot := by
          by_contra hnot
          have hparentLe :
              (store.blocks (store.blocks r).parent_root).slot ≤
                (store.blocks first).slot :=
            Nat.le_of_lt (Nat.lt_of_not_ge hnot)
          rw [get_ancestor_stop hparentLe] at hparentLands
          have hpEq : (store.blocks r).parent_root = first :=
            hparentLands
          rw [hpEq] at hnot
          exact hnot (le_refl _)
        have hparentLt :
            (store.blocks (store.blocks r).parent_root).slot <
              (store.blocks r).slot :=
          hparent r hr hp.root_mem
        have hfirstEpochLeParent :
            compute_epoch_at_slot cfg (store.blocks first).slot ≤
              compute_epoch_at_slot cfg
                (store.blocks (store.blocks r).parent_root).slot :=
          Nat.div_le_div_right hfirstLeParent
        have hparentEpochLeTip :
            compute_epoch_at_slot cfg
                (store.blocks (store.blocks r).parent_root).slot ≤
              compute_epoch_at_slot cfg (store.blocks r).slot :=
          Nat.div_le_div_right hparentLt.le
        have hfirstEpochEqParent :
            compute_epoch_at_slot cfg (store.blocks first).slot =
              compute_epoch_at_slot cfg
                (store.blocks (store.blocks r).parent_root).slot :=
          Nat.le_antisymm hfirstEpochLeParent
            (hparentEpochLeTip.trans_eq htipEpoch.symm)
        exact .tail (ih hparentLands hfirstEpochEqParent) hr
          (hstrictNonGenesis r hr hgt) rfl
          (hfirstEpochEqParent.symm.trans htipEpoch)
  exact go hwalk hlands hsame

/-- An equality of nodes implies the root equality used by the proof. -/
theorem knownSameEpochAncestrySegment_of_known_ancestor
    {store : Store Root}
    (hparent : ParentSlotLt store)
    {first last : Root}
    (hwalk : WalkKnown store (store.blocks first).slot last)
    (hlands : get_ancestor store (ForkChoiceNode.mk last .pending)
      (store.blocks first).slot = ForkChoiceNode.mk first .pending)
    (hsame : compute_epoch_at_slot cfg (store.blocks first).slot =
      compute_epoch_at_slot cfg (store.blocks last).slot)
    (hstrictNonGenesis : ∀ r ∈ store.block_roots,
      (store.blocks first).slot < (store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
      store first last := by
  exact E.knownSameEpochAncestrySegment_of_known_ancestor_root cfg hparent hwalk
    (congrArg ForkChoiceNode.root hlands) hsame hstrictNonGenesis

/-! ## Accepted-segment semantic descent -/

/-- One accepted projected edge is an edge of the execution parent graph.
Schedule membership comes from the exact next-event equation carried by the
accepted transition, not from an arbitrary scheduled-root lookup. -/
theorem acceptedProjectedSameEpochTransition_parentEdge
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {parent child : Root}
    (h : AcceptedProjectedSameEpochTransition cfg ext E B.state parent child) :
    E.ParentEdge child parent := by
  obtain ⟨edge⟩ := h
  obtain ⟨hlt, hevent⟩ :=
    List.getElem?_eq_some_iff.mp edge.transition.event_at
  have hmemAt :
      (E.schedule edge.transition.atPrefix.node
        (edge.transition.atPrefix.previousSecond + 1)
      )[edge.transition.atPrefix.processedCount]'hlt ∈
        E.schedule edge.transition.atPrefix.node
          (edge.transition.atPrefix.previousSecond + 1) :=
    List.getElem_mem hlt
  have hmem : Event.block edge.transition.signedBlock ∈
      E.schedule edge.transition.atPrefix.node
        (edge.transition.atPrefix.previousSecond + 1) := by
    rw [hevent] at hmemAt
    exact hmemAt
  exact Or.inr ⟨edge.transition.atPrefix.node,
    edge.transition.atPrefix.previousSecond + 1,
    edge.transition.signedBlock, hmem,
    edge.child_eq.symm, edge.parent_eq.symm⟩

/-- Every accepted same-epoch segment is semantic descent from its last root
to its first root. -/
theorem acceptedProjectedSameEpochSegment_rootDescends
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {first last : Root}
    (h : AcceptedProjectedSameEpochSegment cfg ext E B.state first last) :
    E.RootDescends last first := by
  induction h with
  | refl => exact .refl _
  | tail hprefix hedge ih =>
      exact .step
        (E.acceptedProjectedSameEpochTransition_parentEdge cfg ext hedge) ih

/-! ## Selected-trace accepted segment supplier -/

/-- The concrete carried selector trace supplies its own accepted same-epoch
segment.  Ordinary selector ancestry is first reconstructed as a known
same-epoch parent segment; every edge is then lifted through its actual last
accepted writer.

`hstrictNonGenesis` is the one store-shape input of this generic causal-store
form.  It is discharged from the trusted anchor facts in the actual-call
specialization below. -/
theorem carriedCurrentNoCrossingAcceptedSegment
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
    (hinputKnown : query.confirmed_root ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks query.confirmed_root).slot ≤
      get_current_slot cfg query.store)
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext query)
    (hobserved : getLatestObservedRestartGuard cfg query
      query.confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg query query.confirmed_root)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext query query.confirmed_root a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks query.confirmed_root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots) :
    AcceptedProjectedSameEpochSegment cfg ext E B.state
      query.confirmed_root trace.result := by
  obtain ⟨_afterFinalized, _afterObserved, hresult⟩ :=
    GetLatestConfirmedTrace.carriedSelected_facts cfg ext trace
      hfinalized hobserved hselector
  have hinputEpochUpper : get_block_epoch cfg query.store
        query.confirmed_root ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpper
  have hinputEpoch :
      get_block_epoch cfg query.store query.confirmed_root =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store query.confirmed_root + 1 =
          get_current_store_epoch cfg query.store := by
    by_cases heq : get_block_epoch cfg query.store query.confirmed_root =
        get_current_store_epoch cfg query.store
    · exact Or.inl heq
    · right
      have hguard : get_block_epoch cfg query.store query.confirmed_root + 1 ≥
          get_current_store_epoch cfg query.store := by
        simpa only [getLatestSelectorGuard] using hselector
      exact Nat.le_antisymm
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
        hguard
  have hselectedCurrent : get_block_epoch cfg query.store
        (find_latest_confirmed_descendant cfg ext query query.confirmed_root) =
      get_current_store_epoch cfg query.store := by
    rw [← hresult]
    exact hresultCurrent
  have hinputCurrent : get_block_epoch cfg query.store query.confirmed_root =
      get_current_store_epoch cfg query.store :=
    selectedInput_current_of_result_current_no_crossing cfg ext
      hparent hwalk hhead hinputKnown hinputEpoch hselectedCurrent hnoCrossing
  have hselectedFacts := find_latest_confirmed_descendant_ge cfg ext query
    hparent hwalk hhead query.confirmed_root hinputKnown
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact hselectedFacts.2
  have hancestor : is_ancestor query.store
      (get_node_for_root trace.result)
      (get_node_for_root query.confirmed_root) = true := by
    rw [hresult]
    exact hselectedFacts.1
  have hlands : (get_ancestor query.store (ForkChoiceNode.mk trace.result .pending)
      (query.store.blocks query.confirmed_root).slot).root = query.confirmed_root := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
      using hancestor
  have hsameEpoch : compute_epoch_at_slot cfg
        (query.store.blocks query.confirmed_root).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      hinputCurrent.trans hresultCurrent.symm
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store query.confirmed_root
        trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor_root cfg hparent
      (hwalk query.confirmed_root hinputKnown trace.result hresultKnown)
      hlands hsameEpoch hstrictNonGenesis
  exact E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwfE hcore hstore hknownSegment

/-! ## The carried/current/no-crossing induction branch -/

/-- Extend the historical A3.2 lineage across the first actual evaluator
branch.

The numeric recency guard and the ordinary known-block slot bound give the
current-or-previous input dichotomy.  The complete selector trace plus absence
of a retained current-epoch crossing then forces the carried input to be
current.  Well-formed accepted-message uniqueness identifies the prior
lineage epoch in the query store, and the actual accepted segment extends the
lineage to the selected result.

This low-level composition lemma keeps the accepted segment explicit; the
next theorem supplies it from the same concrete trace by last-writer
provenance. -/
def carriedCurrentNoCrossingLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwfE : WellFormedExecution E)
    {query : FastConfirmationStore Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinputKnown : query.confirmed_root ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks query.confirmed_root).slot ≤
      get_current_slot cfg query.store)
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext query)
    (hobserved : getLatestObservedRestartGuard cfg query
      query.confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg query query.confirmed_root)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext query query.confirmed_root a c)
    {e : Epoch}
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      query.confirmed_root e)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      query.confirmed_root trace.result) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e := by
  obtain ⟨_afterFinalized, _afterObserved, hresult⟩ :=
    GetLatestConfirmedTrace.carriedSelected_facts cfg ext trace
      hfinalized hobserved hselector
  have hinputEpochUpper : get_block_epoch cfg query.store
        query.confirmed_root ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right hinputSlotUpper
  have hinputEpoch :
      get_block_epoch cfg query.store query.confirmed_root =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store query.confirmed_root + 1 =
          get_current_store_epoch cfg query.store := by
    by_cases heq : get_block_epoch cfg query.store query.confirmed_root =
        get_current_store_epoch cfg query.store
    · exact Or.inl heq
    · right
      have hguard : get_block_epoch cfg query.store query.confirmed_root + 1 ≥
          get_current_store_epoch cfg query.store := by
        simpa only [getLatestSelectorGuard] using hselector
      exact Nat.le_antisymm
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hinputEpochUpper heq))
        hguard
  have hselectedCurrent : get_block_epoch cfg query.store
        (find_latest_confirmed_descendant cfg ext query query.confirmed_root) =
      get_current_store_epoch cfg query.store := by
    rw [← hresult]
    exact hresultCurrent
  have hinputCurrent : get_block_epoch cfg query.store query.confirmed_root =
      get_current_store_epoch cfg query.store :=
    selectedInput_current_of_result_current_no_crossing cfg ext
      hparent hwalk hhead hinputKnown hinputEpoch hselectedCurrent hnoCrossing
  have hinputBlockEq : query.store.blocks query.confirmed_root =
      hprevious.tip_block :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E hwfE hstore
      hinputKnown).mp
      hprevious.tip_at
  have hinputEpochE : get_block_epoch cfg query.store query.confirmed_root = e := by
    simpa only [get_block_epoch, hinputBlockEq] using hprevious.tip_epoch
  have heCurrent : e = get_current_store_epoch cfg query.store :=
    hinputEpochE.symm.trans hinputCurrent
  have hresultEpochE : get_block_epoch cfg query.store trace.result = e :=
    hresultCurrent.trans heCurrent.symm
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    rw [hresult]
    exact (find_latest_confirmed_descendant_ge cfg ext query hparent hwalk
      hhead query.confirmed_root hinputKnown).2
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hresultKnown
  exact hprevious.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [get_block_epoch] using hresultEpochE)
    (E.acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-- Payload-preserving carried induction step with no accepted-segment
premise.  The segment is derived from the concrete selector ancestry and
exact last-writer provenance. -/
def carriedCurrentNoCrossingLineage_of_trace
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
    (hinputKnown : query.confirmed_root ∈ query.store.block_roots)
    (hinputSlotUpper : (query.store.blocks query.confirmed_root).slot ≤
      get_current_slot cfg query.store)
    (trace : GetLatestConfirmedTrace cfg ext query)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext query)
    (hobserved : getLatestObservedRestartGuard cfg query
      query.confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg query query.confirmed_root)
    (hresultCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext query query.confirmed_root a c)
    (hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks query.confirmed_root).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots)
    {e : Epoch}
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      query.confirmed_root e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B trace.result e := by
  have hsegment := E.carriedCurrentNoCrossingAcceptedSegment cfg ext B hwfE
    hcore hstore hparent hwalk hhead hinputKnown hinputSlotUpper trace
    hfinalized hobserved hselector hresultCurrent hnoCrossing
    hstrictNonGenesis
  exact E.carriedCurrentNoCrossingLineage cfg ext B hwfE hstore hparent
    hwalk hhead hinputKnown hinputSlotUpper trace hfinalized hobserved
      hselector hresultCurrent hnoCrossing hprevious hsegment

/-! ## Actual execution-call specialization -/

/-- The carried/current/no-crossing lineage step at the exact `fcrStep` call
site.  This is the action-facing form: it has no accepted-segment or abstract
non-genesis premise.

The duplicate trusted-anchor-root corner is discharged concretely.  A root in
the genesis list is the unique anchor root; accepted-message uniqueness fixes
its later store message to the genesis message, while `store_anchor_min_slot`
(which itself uses the unscheduled dangling-parent guard) puts that slot at or
below the carried input.  It therefore cannot be a strict child above the
input on the selected walk. -/
noncomputable def carriedCurrentNoCrossingLineageAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn1 : E.WithinHorizon cfg (n + 1))
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hfinalized : ¬ getLatestFinalizedRevertGuard cfg ext
      (E.fcrStep cfg ext v n))
    (hobserved : getLatestObservedRestartGuard cfg
      (E.fcrStep cfg ext v n) (E.fcrStep cfg ext v n).confirmed_root = false)
    (hselector : getLatestSelectorGuard cfg (E.fcrStep cfg ext v n)
      (E.fcrStep cfg ext v n).confirmed_root)
    (hresultCurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.getLatestConfirmedTraceAt cfg ext v n).result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
        (E.fcrStep cfg ext v n).confirmed_root a c)
    {e : Epoch}
    (hprevious : E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.confirmed cfg ext v n) e) :
    E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.getLatestConfirmedTraceAt cfg ext v n).result e := by
  let ast : BeaconState Root := Classical.choose hA.genesis
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hA.genesis)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hA.genesis)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hslot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hanchorParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot
      hanchorParent).core
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore
      hA.externals_coherence.state_transition_slot hgenCore
  have hstore : E.CausalStore cfg ext (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
  have hparent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hv (n + 1) hHn1
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hinputKnown : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact hknownN1
  have hinputSlotUpper :
      ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot ≤
        get_current_slot cfg (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgen, hslot⟩ v (n + 1) _ hknownN1
  have hstrictNonGenesis : ∀ r ∈
      (E.fcrStep cfg ext v n).store.block_roots,
      ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot <
          ((E.fcrStep cfg ext v n).store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hr
    have hanchorBlock :
        (E.fcrStep cfg ext v n).store.blocks ablk.root = ablk.message := by
      rw [E.fcrStep_store]
      exact E.store_anchor_block cfg ext hA.wellFormed hgen v (n + 1)
        hanchorKnown
    have hanchorLeInput : ablk.message.slot ≤
        ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot := by
      rw [E.fcrStep_confirmed_root, E.fcrStep_store]
      exact E.store_anchor_min_slot cfg ext hA.wellFormed
        hA.externals_coherence hgen hslot hanchorParent v (n + 1)
          (E.confirmed cfg ext v n) hknownN1
    have hbad :
        ((E.fcrStep cfg ext v n).store.blocks
          (E.fcrStep cfg ext v n).confirmed_root).slot <
            ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeInput) hbad
  have hpreviousQ : E.AcceptedHistoricalA32LineageAt cfg ext B
      (E.fcrStep cfg ext v n).confirmed_root e := by
    simpa only [E.fcrStep_confirmed_root] using hprevious
  exact E.carriedCurrentNoCrossingLineage_of_trace cfg ext B
    hA.wellFormed hcore hstore hparent hwalk hhead hinputKnown
      hinputSlotUpper (E.getLatestConfirmedTraceAt cfg ext v n)
      hfinalized hobserved hselector hresultCurrent hnoCrossing
      hstrictNonGenesis hpreviousQ

end Execution


end FastConfirmation.Spec

end
