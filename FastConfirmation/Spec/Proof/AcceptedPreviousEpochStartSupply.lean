module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedHistoricalA32CallSupplier
public import FastConfirmation.Spec.Proof.AcceptedCurrentSameSourceHistory

@[expose] public section

/-!
# Previous-epoch result supply at an actual epoch-start call

An epoch-start strict result cannot uniformly be assigned the current-result
historical-lineage invariant: its ordered selector input may have been an
observed reset rather than the previously cached confirmed root.  This module
keeps that operational distinction.

The observed-reset arm has a stronger direct late-source fact.  Its executable
guard identifies the cached checkpoint with `UJ(head)`; accepted projection
identifies that value with semantic `GU(head)`.  Since both the observed root
and the strict result are in the previous block epoch, the query head is a
known descendant of the result with `GU(head).epoch` at least the result
epoch.  This is exactly the query-GU seed consumed by the late Lemma-43-style
endpoint tail and does not require a fabricated A3.2 lineage.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- Direct accepted GU seed for the observed-reset origin of a strict
previous-epoch result at an actual call.

The epoch-start fact itself is retained by `ObservedResetCandidateInputAt`;
the statement only asks for the exact previous-result equality used by the
phase dispatcher.  No lineage, canonicity, endpoint fact, filter fact, or
safety conclusion is assumed. -/
theorem StrictSelectorAdvanceAt.previousObservedReset_queryGUEpochSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (horigin : ObservedResetCandidateInputAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hprevious : get_block_epoch cfg (E.fcrStep cfg ext v n).store
          trace.result + 1 =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) :
    ∃ seed : Root,
      seed ∈ (E.fcrStep cfg ext v n).store.block_roots ∧
        is_ancestor (E.fcrStep cfg ext v n).store
          (get_node_for_root seed) (get_node_for_root trace.result) = true ∧
        get_block_epoch cfg (E.fcrStep cfg ext v n).store trace.result ≤
          (B.state.GU seed).epoch := by
  let query := E.fcrStep cfg ext v n
  let head := (get_head cfg query.store).root
  have htag := E.actualObservedRestartInputAt cfg ext B hT hanchor
    hboundary v n trace horigin.observed_guard_true
  obtain ⟨hparent, hwalk, _hjustifiedKnown⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure hdomain v hv (n + 1) hHn1
  have hparentQ : ParentSlotLt query.store := by
    simpa only [query, E.fcrStep_store] using hparent
  have hwalkQ : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.fcrStep_store] using hwalk
  have hheadKnown : head ∈ query.store.block_roots := by
    simpa only [query, head, E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hHn1
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, htag.afterObserved_eq] using htag.root_known
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input (hselector.result_eq.trans hfixed)
  have hheadResult : is_ancestor query.store
      (get_node_for_root head) (get_node_for_root trace.result) = true := by
    have hbelow := strictSelectedResult_below_head cfg ext hparentQ hwalkQ
      hheadKnown hinputKnown hstrict
    rw [is_ancestor_node_root] at hbelow
    simpa only [head, hselector.result_eq] using hbelow
  have hprojection : AcceptedFFGStoreProjection B.state query.store := by
    simpa only [query, E.fcrStep_store] using
      (Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection
        B (E.store_causal cfg ext v (n + 1)))
  have hguHead : query.store.unrealized_justifications head =
      B.state.GU head :=
    hprojection.unrealized_justification head hheadKnown
  have hobservedGU :
      query.current_epoch_observed_justified_checkpoint =
        B.state.GU head := by
    exact horigin.observed_eq_head_unrealized.trans hguHead
  have hobservedBlockLe : get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root ≤
      query.current_epoch_observed_justified_checkpoint.epoch := by
    have hscaled : get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root *
            cfg.slots_per_epoch ≤
        query.current_epoch_observed_justified_checkpoint.epoch *
            cfg.slots_per_epoch := by
      exact (start_slot_at_block_epoch_le cfg query.store
        query.current_epoch_observed_justified_checkpoint.root).trans
          htag.realized.root_slot_le_boundary
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hresultEpochEq : get_block_epoch cfg query.store trace.result =
      get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root := by
    have hresultPrevious : get_block_epoch cfg query.store trace.result + 1 =
        get_current_store_epoch cfg query.store := by
      simpa only [query] using hprevious
    have hobservedPrevious : get_block_epoch cfg query.store
          query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store := htag.previous_epoch
    exact Nat.add_right_cancel
      (hresultPrevious.trans hobservedPrevious.symm)
  have hguLower : get_block_epoch cfg query.store trace.result ≤
      (B.state.GU head).epoch := by
    calc
      get_block_epoch cfg query.store trace.result =
          get_block_epoch cfg query.store
            query.current_epoch_observed_justified_checkpoint.root :=
        hresultEpochEq
      _ ≤ query.current_epoch_observed_justified_checkpoint.epoch :=
        hobservedBlockLe
      _ = (B.state.GU head).epoch :=
        congrArg Checkpoint.epoch hobservedGU
  exact ⟨head, hheadKnown, hheadResult, hguLower⟩

/-! ## Carried-input lineage -/

/-- Extend an already retained historical lineage through one actual strict
selector phase when its ordered input and result have the same block epoch.

This is the epoch-neutral form of the existing current-result segment lift.
Every parent edge is recovered from its accepted last writer; the trusted
genesis root is excluded from strict children by the concrete anchor-minimal
slot theorem. -/
noncomputable def
    StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hinputKnown : trace.afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots)
    {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.afterObserved e Cert Supp)
    (hinputEpoch : get_block_epoch cfg (E.fcrStep cfg ext v n).store
      trace.afterObserved = e)
    (hresultEpoch : get_block_epoch cfg (E.fcrStep cfg ext v n).store
      trace.result = e) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result e
      Cert Supp := by
  let query := E.fcrStep cfg ext v n
  let ast : BeaconState Root := Classical.choose hT.genesis_structure
  let ablk : SignedBeaconBlock Root :=
    Classical.choose (Classical.choose_spec hT.genesis_structure)
  have hgenFacts :=
    Classical.choose_spec (Classical.choose_spec hT.genesis_structure)
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk :=
    hgenFacts.1
  have hgenSlot : ast.slot = ablk.message.slot := hgenFacts.2.1
  have hgenParent : ablk.message.parent_root ≠ ablk.root :=
    hgenFacts.2.2
  have hgenCore : WellFormedStoreCore E.genesis_store := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
      hgenParent).core
  have hcore : E.ExactCausalStoreWellFormedCore cfg ext :=
    E.exactCausalStoreWellFormedCore
      hT.externals_coherence.state_transition_slot hgenCore
  have hstore : E.CausalStore cfg ext query.store := by
    simpa only [query, E.fcrStep_store] using
      E.store_causal cfg ext v (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hHn1
  have hinputKnownQ : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query] using hinputKnown
  have hgeometry := hselector.geometry cfg ext hparent hwalk hhead
    hinputKnownQ
  have hlands : (get_ancestor query.store
      (get_node_for_root trace.result)
      (query.store.blocks trace.afterObserved).slot).root =
        trace.afterObserved := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using
      hgeometry.descends_input
  have hinputEpochQ : get_block_epoch cfg query.store
      trace.afterObserved = e := by
    simpa only [query] using hinputEpoch
  have hresultEpochQ : get_block_epoch cfg query.store trace.result = e := by
    simpa only [query] using hresultEpoch
  have hsame : compute_epoch_at_slot cfg
        (query.store.blocks trace.afterObserved).slot =
      compute_epoch_at_slot cfg (query.store.blocks trace.result).slot := by
    simpa only [get_block_epoch] using
      hinputEpochQ.trans hresultEpochQ.symm
  have hstrictNonGenesis : ∀ r ∈ query.store.block_roots,
      (query.store.blocks trace.afterObserved).slot <
          (query.store.blocks r).slot →
        r ∉ E.genesis_store.block_roots := by
    intro r hr hstrict hrGenesis
    have hrEq : r = ablk.root := by
      rw [hgen] at hrGenesis
      simpa only [get_forkchoice_store, List.mem_singleton] using hrGenesis
    subst r
    have hanchorKnown : ablk.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [query, E.fcrStep_store] using hr
    have hanchorBlock : query.store.blocks ablk.root = ablk.message := by
      simpa only [query, E.fcrStep_store] using
        E.store_anchor_block cfg ext hT.wellFormed hgen v (n + 1)
          hanchorKnown
    have hinputKnownN1 : trace.afterObserved ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [query, E.fcrStep_store] using hinputKnownQ
    have hanchorLeInput : ablk.message.slot ≤
        (query.store.blocks trace.afterObserved).slot := by
      simpa only [query, E.fcrStep_store] using
        E.store_anchor_min_slot cfg ext hT.wellFormed
          hT.externals_coherence hgen hgenSlot hgenParent v (n + 1)
            trace.afterObserved hinputKnownN1
    have hbad : (query.store.blocks trace.afterObserved).slot <
        ablk.message.slot := by
      simpa only [hanchorBlock] using hstrict
    exact (Nat.not_lt_of_ge hanchorLeInput) hbad
  have hknownSegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots query.store trace.afterObserved
        trace.result :=
    E.knownSameEpochAncestrySegment_of_known_ancestor_root cfg hparent
      (hwalk trace.afterObserved hinputKnownQ trace.result
        hgeometry.result_known)
      hlands hsame hstrictNonGenesis
  have hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      trace.afterObserved trace.result :=
    E.knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
      hT.wellFormed hcore hstore hknownSegment
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore
      hgeometry.result_known
  exact hlineage.extend cfg ext (query.store.blocks trace.result) hresultAt
    (by simpa only [query, get_block_epoch] using hresultEpoch)
    (E.acceptedProjectedSameEpochSegment_rootDescends cfg ext hsegment)
    hsegment

/-- The carried origin of an epoch-start strict previous result inherits the
completed-prefix lineage from the immediately preceding store and extends it
along the concrete accepted same-epoch selector segment.

The prior cached root is current in the preceding store by the actual
boundary clock and selector recency.  Thus this theorem does not expose a
lineage callback or a previous-result lineage premise. -/
theorem StrictSelectorAdvanceAt.previousCarried_epochStartLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hC : E.AcceptedHistoricalA32CompletedPrefixCallAssumptions cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true)
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (horigin : CarriedCandidateInputAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hprevious : get_block_epoch cfg (E.fcrStep cfg ext v n).store
          trace.result + 1 =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) :
    Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result
      (get_block_epoch cfg (E.fcrStep cfg ext v n).store trace.result)
      (E.LazyCertAt cfg ext B n) (E.LazySupportAt cfg ext B v n)) := by
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hinvariant :=
    E.acceptedHistoricalA32CurrentLineage_invariant_of_completedPrefixes
      cfg ext B hT hC hfit hanchor hboundary v hv n hHn
  have hrecentConfirmed : get_block_epoch cfg
        (E.fcrStep cfg ext v n).store (E.confirmed cfg ext v n) + 1 ≥
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
    simpa only [horigin.input_eq, E.fcrStep_confirmed_root] using
      hselector.input_recent
  have hcurrentN := E.previousConfirmed_current_of_boundary_recent
    cfg ext hT hcall hstart hinvariant.confirmed_known hrecentConfirmed
  obtain ⟨e, ⟨hlineageN⟩⟩ := hinvariant.current_lineage hcurrentN
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1
      hinvariant.confirmed_known
  have hinputKnown : trace.afterObserved ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [horigin.input_eq, E.fcrStep_confirmed_root, E.fcrStep_store]
    exact hknownN1
  have hqueryCausal : E.CausalStore cfg ext
      (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hlineageQ : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.afterObserved e (E.LazyCertAt cfg ext B n)
      (E.LazySupportAt cfg ext B v n) := by
    simpa only [horigin.input_eq, E.fcrStep_confirmed_root] using hlineageN
  have hinputBlockEq : (E.fcrStep cfg ext v n).store.blocks
        trace.afterObserved = hlineageQ.tip_block :=
    (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
      hT.wellFormed hqueryCausal hinputKnown).mp hlineageQ.tip_at
  have hinputEpochE : get_block_epoch cfg
      (E.fcrStep cfg ext v n).store trace.afterObserved = e := by
    simpa only [get_block_epoch, hinputBlockEq] using hlineageQ.tip_epoch
  have hinputPrevious : get_block_epoch cfg
          (E.fcrStep cfg ext v n).store trace.afterObserved + 1 =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
    have hepochSucc := E.actualCall_currentEpoch_succ_of_start
      cfg ext hT hcall hstart
    have hblockAgree : (E.store cfg ext v n).blocks
          (E.confirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.confirmed cfg ext v n) :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext v n)
        (E.blockProvenance cfg ext v (n + 1))
        hinvariant.confirmed_known hknownN1
    calc
      get_block_epoch cfg (E.fcrStep cfg ext v n).store
            trace.afterObserved + 1 =
          get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) + 1 := by
        simp only [horigin.input_eq, E.fcrStep_confirmed_root,
          E.fcrStep_store, get_block_epoch, hblockAgree]
      _ = get_current_store_epoch cfg (E.store cfg ext v n) + 1 := by
        rw [hcurrentN]
      _ = get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
        hepochSucc
      _ = get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
        rw [E.fcrStep_store]
  have hresultEpochE : get_block_epoch cfg
      (E.fcrStep cfg ext v n).store trace.result = e := by
    have hresultInputEpoch : get_block_epoch cfg
          (E.fcrStep cfg ext v n).store trace.result =
        get_block_epoch cfg (E.fcrStep cfg ext v n).store
          trace.afterObserved :=
      Nat.add_right_cancel (hprevious.trans hinputPrevious.symm)
    exact hresultInputEpoch.trans hinputEpochE
  have hextended : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.result e (E.LazyCertAt cfg ext B n)
      (E.LazySupportAt cfg ext B v n) :=
    Execution.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual
      cfg ext B hT hdomain hv hHn1 hselector hinputKnown hlineageQ
        hinputEpochE hresultEpochE
  simpa only [hresultEpochE] using
    (show Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.result e (E.LazyCertAt cfg ext B n)
      (E.LazySupportAt cfg ext B v n)) from ⟨hextended⟩)

/-! ## Finalized-reset input -/

/-- A strict previous-epoch result selected from the finalized-reset input
inherits the trusted-anchor lineage.

The causal two-epoch lag excludes a non-anchor finalized input because the
selector simultaneously requires that exact input to be recent.  In the
remaining anchor case, selector epoch monotonicity forces the anchor root and
the previous result into the same block epoch; boundary alignment identifies
that epoch with the anchor checkpoint epoch.  The lineage is therefore
initialized by the anchor payload and extended through the accepted selector
segment. -/
theorem StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (horigin : FinalizedResetCandidateInputAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStep cfg ext v n) trace)
    (hprevious : get_block_epoch cfg (E.fcrStep cfg ext v n).store
          trace.result + 1 =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hanchorCert : Cert B.anchor)
    (hanchorSupp : ∀ (o : Root) (e' : Epoch),
      B.state.C o e' = B.anchor → Supp o e') :
    Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B trace.result
      (get_block_epoch cfg (E.fcrStep cfg ext v n).store trace.result)
      Cert Supp) := by
  let query := E.fcrStep cfg ext v n
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  have hstore : E.CausalStore cfg ext query.store := by
    simpa only [query, E.fcrStep_store] using
      E.store_causal cfg ext v (n + 1)
  have hfinalizedKnown : query.store.finalized_checkpoint.root ∈
      query.store.block_roots := by
    simpa only [query, E.fcrStep_store] using hrealized.root_known
  have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, horigin.input_eq] using hfinalizedKnown
  have hrecentFinalized : get_block_epoch cfg query.store
        query.store.finalized_checkpoint.root + 1 ≥
      get_current_store_epoch cfg query.store := by
    simpa only [query, horigin.input_eq] using hselector.input_recent
  have hfinalizedAnchor : query.store.finalized_checkpoint = B.anchor := by
    by_contra hne
    have hstale := E.finalizedResetRoot_stale_of_causalLag cfg ext hLag
      hstore (by simpa only [query, E.fcrStep_store] using hrealized) hne
    exact (Nat.not_lt_of_ge hrecentFinalized) hstale
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis_structure hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hHn1
  have hgeometry := hselector.geometry cfg ext hparent hwalk hhead
    hinputKnown
  have hinputResultEpoch : get_block_epoch cfg query.store
        trace.afterObserved =
      get_block_epoch cfg query.store trace.result := by
    have hresultPrevious : get_block_epoch cfg query.store trace.result + 1 =
        get_current_store_epoch cfg query.store := by
      simpa only [query] using hprevious
    have hlower : get_block_epoch cfg query.store trace.result + 1 ≤
        get_block_epoch cfg query.store trace.afterObserved + 1 := by
      calc
        get_block_epoch cfg query.store trace.result + 1 =
            get_current_store_epoch cfg query.store := hresultPrevious
        _ ≤ get_block_epoch cfg query.store trace.afterObserved + 1 :=
          hselector.input_recent
    have hupper : get_block_epoch cfg query.store trace.afterObserved + 1 ≤
        get_block_epoch cfg query.store trace.result + 1 :=
      Nat.add_le_add_right hgeometry.input_epoch_le_result 1
    exact Nat.add_right_cancel (Nat.le_antisymm hupper hlower)
  have hinputRoot : trace.afterObserved = B.anchor.root := by
    calc
      trace.afterObserved = query.store.finalized_checkpoint.root :=
        horigin.input_eq
      _ = B.anchor.root := congrArg Checkpoint.root hfinalizedAnchor
  have hanchorKnown : B.anchor.root ∈ query.store.block_roots := by
    simpa only [hinputRoot] using hinputKnown
  have hanchor0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
    have hroot : B.anchor.root = ablk.root := by
      rw [hanchor, hgen]
      rfl
    rw [hgen, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorBlocks : E.genesis_store.blocks B.anchor.root =
      query.store.blocks B.anchor.root :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v 0)
      (by simpa only [query, E.fcrStep_store] using
        E.blockProvenance cfg ext v (n + 1))
      (by simpa only [show E.store cfg ext v 0 = E.genesis_store from rfl]
        using hanchor0)
      hanchorKnown
  have hanchorSlot := E.trustedAnchor_slot_eq_start_of_trajectory
    cfg ext hT hanchor hboundary
  have hanchorEpoch : get_block_epoch cfg query.store B.anchor.root =
      B.anchor.epoch := by
    simp only [get_block_epoch, ← hanchorBlocks, hanchorSlot,
      compute_start_slot_at_epoch, compute_epoch_at_slot]
    exact Nat.mul_div_cancel _ cfg.slots_per_epoch_pos
  have hinputEpoch : get_block_epoch cfg query.store trace.afterObserved =
      B.anchor.epoch := by
    simpa only [hinputRoot] using hanchorEpoch
  have hresultEpoch : get_block_epoch cfg query.store trace.result =
      B.anchor.epoch := hinputResultEpoch.symm.trans hinputEpoch
  have hanchorAt : E.AcceptedBlockAt cfg ext B.anchor.root
      (query.store.blocks B.anchor.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hanchorKnown
  have hpayload : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B
      B.anchor.root B.anchor.epoch Cert Supp :=
    AcceptedHistoricalA32GatePayloadCoreAt.of_anchor cfg ext B hanchorAt
      (by simpa only [get_block_epoch] using hanchorEpoch)
      hanchorExact.symm hanchorCert hanchorSupp
  have hlineageAnchor : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      B.anchor.root B.anchor.epoch Cert Supp :=
    AcceptedHistoricalA32LineageCoreAt.refl cfg ext hpayload
  have hlineageInput : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.afterObserved B.anchor.epoch Cert Supp := by
    simpa only [hinputRoot] using hlineageAnchor
  have hextended : E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.result B.anchor.epoch Cert Supp :=
    Execution.StrictSelectorAdvanceAt.extendHistoricalLineage_sameEpoch_actual
      cfg ext B hT hdomain hv hHn1 hselector
        (by simpa only [query] using hinputKnown) hlineageInput
        (by simpa only [query] using hinputEpoch)
        (by simpa only [query] using hresultEpoch)
  simpa only [query, hresultEpoch] using
    (show Nonempty (E.AcceptedHistoricalA32LineageCoreAt cfg ext B
      trace.result B.anchor.epoch Cert Supp) from ⟨hextended⟩)

end Execution


end FastConfirmation.Spec

end
