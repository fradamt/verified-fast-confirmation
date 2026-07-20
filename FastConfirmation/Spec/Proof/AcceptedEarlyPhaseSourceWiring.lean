import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedPhaseSourceSupply
import FastConfirmation.Spec.Proof.QueryFilterViability

/-!
# Accepted early-phase source wiring

This module connects the query-local source producers to honest execution
endpoints.  In particular, the epoch-start exclusion needed by the current
query / next-epoch endpoint cell is derived from the successful confirmation's
honest past supporter; it is not a phase assumption.

The current-query / same-epoch endpoint cell is deliberately not handled
here.  Its source lower bound is the separate paper Lemmas 22--26 history
argument.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- Reassemble the lower selected-margin bundle only inside adapter
proofs.  Public early-phase constructors expose independent trajectory,
synchrony, static-registry, economic, and local-domain inputs. -/
private def selectedMarginAssumptions_of_earlyPhaseInputs
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E) :
    SelectedMarginAssumptions cfg ext E :=
  { genesis := hT.genesis
    wellFormed := hT.wellFormed
    whole_seconds := hT.whole_seconds
    honest_behavior := hT.honest_behavior
    synchrony := hsync
    externals_coherence := hT.externals_coherence
    static_validators := hstatic
    byzantine_bound := hbyz
    domain := hdomain }

/-! ## Query-head filter witness without path erasure -/

/-- A query-filter viable leaf retaining both ancestry legs from the actual
query head.  `FilterViableLeafBelow result` erases the intermediate
`tip ⩾ head`; this refinement keeps it so the Lemma-13 GU bound at the head can
be transported to this very source path. -/
def HeadFilterViableLeafBelow
    (store : Store Root) (result : Root) : Prop :=
  ∃ tip : Root,
    tip ∈ store.block_roots ∧
      (get_head cfg store).root ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root tip)
          (get_head cfg store) = true ∧
      is_ancestor store (get_node_for_root tip)
          (get_node_for_root result) = true ∧
      store.block_roots.filter
          (fun r => (store.blocks r).parent_root = tip) = [] ∧
      (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
        (get_voting_source cfg store tip).epoch =
            store.justified_checkpoint.epoch ∨
        (get_voting_source cfg store tip).epoch + 2 ≥
          get_current_store_epoch cfg store) ∧
      (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
        store.finalized_checkpoint.root =
          get_checkpoint_block cfg store tip
            store.finalized_checkpoint.epoch) ∧
      WalkKnown store (store.blocks (get_head cfg store).root).slot tip ∧
      WalkKnown store (store.blocks result).slot tip

/-- The same un-erased query-head viable leaf, now carrying the accepted GU
lower bound obtained by monotonicity from the Lemma-13 query head. -/
def HeadFilterViableLemma13SourceAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (store : Store Root) (result : Root) : Prop :=
  ∃ tip : Root,
    tip ∈ store.block_roots ∧
      (get_head cfg store).root ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root tip)
          (get_head cfg store) = true ∧
      is_ancestor store (get_node_for_root tip)
          (get_node_for_root result) = true ∧
      store.block_roots.filter
          (fun r => (store.blocks r).parent_root = tip) = [] ∧
      (store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
        (get_voting_source cfg store tip).epoch =
            store.justified_checkpoint.epoch ∨
        (get_voting_source cfg store tip).epoch + 2 ≥
          get_current_store_epoch cfg store) ∧
      (store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
        store.finalized_checkpoint.root =
          get_checkpoint_block cfg store tip
            store.finalized_checkpoint.epoch) ∧
      WalkKnown store (store.blocks (get_head cfg store).root).slot tip ∧
      WalkKnown store (store.blocks result).slot tip ∧
      (B.state.GU tip).epoch + 1 ≥ get_current_store_epoch cfg store

/-- The same query-filter tip after ordinary next-epoch relay.  Crucially the
endpoint recent source is witnessed by this exact query tip, so later retained
leaf extension stays on the finalized-check path instead of choosing a
sibling source leaf. -/
def RelayedHeadFilterRecentSourceAt
    (query endpoint : Store Root) (result : Root) : Prop :=
  ∃ tip : Root,
    tip ∈ query.block_roots ∧
      (get_head cfg query).root ∈ query.block_roots ∧
      is_ancestor query (get_node_for_root tip)
          (get_head cfg query) = true ∧
      is_ancestor query (get_node_for_root tip)
          (get_node_for_root result) = true ∧
      query.block_roots.filter
          (fun r => (query.blocks r).parent_root = tip) = [] ∧
      (query.justified_checkpoint.epoch = GENESIS_EPOCH ∨
        (get_voting_source cfg query tip).epoch =
            query.justified_checkpoint.epoch ∨
        (get_voting_source cfg query tip).epoch + 2 ≥
          get_current_store_epoch cfg query) ∧
      (query.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
        query.finalized_checkpoint.root =
          get_checkpoint_block cfg query tip
            query.finalized_checkpoint.epoch) ∧
      WalkKnown query (query.blocks (get_head cfg query).root).slot tip ∧
      WalkKnown query (query.blocks result).slot tip ∧
      tip ∈ endpoint.block_roots ∧
      is_ancestor endpoint (get_node_for_root tip)
          (get_node_for_root result) = true ∧
      (get_voting_source cfg endpoint tip).epoch + 2 ≥
        get_current_store_epoch cfg endpoint

/-- Re-run the query-head filter inversion before the `tip ⩾ head` leg is
erased.  The direct justified-root branch remains an explicit bypass. -/
theorem queryHead_direct_or_headFilterViableLeafBelow
    {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjustified : store.justified_checkpoint.root ∈ store.block_roots)
    {result : Root} (hresult : result ∈ store.block_roots)
    (hheadResult : is_ancestor store (get_head cfg store)
      (get_node_for_root result) = true) :
    is_ancestor store
        (get_node_for_root store.justified_checkpoint.root)
        (get_node_for_root result) = true ∨
      HeadFilterViableLeafBelow cfg store result := by
  have hhead : (get_head cfg store).root ∈
        get_filtered_block_tree cfg store ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg
      ((get_filtered_block_tree cfg store).length + 1)
      (ForkChoiceNode.mk store.justified_checkpoint.root)
  rcases hhead with hheadFiltered | hheadJustified
  · right
    obtain ⟨tip, htip, htipHead, hleaf, hjustifiedCheck,
        hfinalizedCheck⟩ :=
      filtered_member_viableLeafBelow cfg hwf hwalkK hjustified
        hheadFiltered
    have hheadKnown : (get_head cfg store).root ∈ store.block_roots := by
      have houtput : (get_head cfg store).root ∈
          (filter_block_tree_aux cfg store
            (store.block_roots.length + 1)
            store.justified_checkpoint.root).2 := hheadFiltered
      rcases filter_block_tree_aux_output_mem cfg _ _ _ houtput with
        hknown | hbase
      · exact hknown
      · rw [hbase]
        exact hjustified
    have htipResult : is_ancestor store
        (get_node_for_root tip) (get_node_for_root result) = true :=
      is_ancestor_trans hwf
        (hwalkK result hresult tip htip)
        (hwalkK result hresult (get_head cfg store).root hheadKnown)
        htipHead hheadResult
    exact ⟨tip, htip, hheadKnown, htipHead, htipResult, hleaf,
      hjustifiedCheck, hfinalizedCheck,
      hwalkK (get_head cfg store).root hheadKnown tip htip,
      hwalkK result hresult tip htip⟩
  · left
    change is_ancestor store
      (ForkChoiceNode.mk store.justified_checkpoint.root)
      (get_node_for_root result) = true
    rw [← hheadJustified]
    exact hheadResult

/-! ## Executable FCR head-cache knownness -/

/-- The cached current-slot head of the executable FCR recurrence is known in
the recurrence's current store.  At a call it is refreshed from `get_head`;
between calls it is retained while the block domain grows. -/
theorem fcr_currentSlotHead_known
    (hgen : ∃ (anchor_state : BeaconState Root)
      (anchor_block : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block ∧
        anchor_state.slot = anchor_block.message.slot ∧
        anchor_block.message.parent_root ≠ anchor_block.root)
    (hdom : SelectedMarginDomain cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : Nat)
    (hH : E.WithinHorizon cfg n) :
    (E.fcr cfg ext v n).current_slot_head ∈
      (E.store cfg ext v n).block_roots := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hgen
      change (E.genesis_store.finalized_checkpoint.root ∈
        E.genesis_store.block_roots)
      rw [hgenEq]
      simp [get_forkchoice_store]
  | succ n ih =>
      have hnH : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hH
      have hknownN := ih hnH
      by_cases hcall : get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)
      · have hhead := E.head_root_known_of_selectedMarginDomain cfg ext
          hdom hv (n + 1) hH
        simp only [Execution.fcr, hcall, if_true, on_fast_confirmation,
          update_fast_confirmation_variables]
        split_ifs <;> exact hhead
      · have hcarry :=
          (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
        simpa only [Execution.fcr, hcall, if_false] using hcarry

/-- Immediately before an executable `fcrStep`, its previous-slot-head cache
is the preceding recurrence's known current-slot head, hence is known in the
step store as well. -/
theorem fcrStep_previousSlotHead_known
    (hgen : ∃ (anchor_state : BeaconState Root)
      (anchor_block : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block ∧
        anchor_state.slot = anchor_block.message.slot ∧
        anchor_block.message.parent_root ≠ anchor_block.root)
    (hdom : SelectedMarginDomain cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : Nat)
    (hH : E.WithinHorizon cfg (n + 1)) :
    (E.fcrStep cfg ext v n).previous_slot_head ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
  have hnH : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hH
  have hknownN := E.fcr_currentSlotHead_known cfg ext hgen hdom v hv n hnH
  have hknownN1 :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  simp only [Execution.fcrStep, update_fast_confirmation_variables]
  split_ifs <;> exact hknownN1

/-- The step update shifts the preceding cached current head into the exact
previous-slot-head field, independently of both epoch-check branches. -/
theorem fcrStep_previousSlotHead_eq_currentSlotHead
    (v : ValidatorIndex) (n : Nat) :
    (E.fcrStep cfg ext v n).previous_slot_head =
      (E.fcr cfg ext v n).current_slot_head := by
  simp only [Execution.fcrStep, update_fast_confirmation_variables]
  split_ifs <;> rfl

/-! ## A strict current result is not produced at an epoch start -/

/-- The narrow output of the honest-confirmation supporter argument needed
for epoch-start exclusion.  The witness retains only operational block/clock
facts; no selected-margin, source, filter, FFG, or safety interface is a field
of this public boundary. -/
def ConfirmedPastDescendantSlotWitnessAt
    (q : Nat) (store : Store Root) (result : Root) : Prop :=
  ∃ pastSecond descendant,
    E.slot_at cfg pastSecond < E.slot_at cfg q ∧
      descendant ∈ store.block_roots ∧
      is_ancestor store
          (get_node_for_root descendant) (get_node_for_root result) = true ∧
        (store.blocks descendant).slot ≤ E.slot_at cfg pastSecond

/-- Adapter from the existing minimal honest-supporter producer to the narrow
slot witness.  The broad selected-margin bundle is confined to this adapter;
the epoch-start contradiction and accepted source wiring consume only the
projected witness. -/
theorem StrictSelectedResultMechanicalFacts.confirmedPastDescendantSlotWitness
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext v q)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result) :
    E.ConfirmedPastDescendantSlotWitnessAt cfg q query.store result := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA v hv q
      query hquery result hqH
      (by simpa only [hquery] using h.result_known)
      (by simpa only [hquery] using h.parent_known)
      h.confirmed
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hdPast, hdResult⟩ :=
    E.past_descendant_of_honest_supporter_known_minimal cfg ext hA
      v q result hqH i hi lm hlm hsupp
  have hrelayGate : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) := by
    exact (Nat.succ_le_iff.mpr hnuq).trans
      (E.slot_at_mono cfg (Nat.le_succ q))
  have hdQueryE : d ∈ (E.store cfg ext v q).block_roots :=
    hA.synchrony.block_relay u hu nu d hnuH hdPast v hv q hqH hrelayGate
  have hdQuery : d ∈ query.store.block_roots := by
    simpa only [hquery] using hdQueryE
  have hdAgree : (E.store cfg ext u nu).blocks d = query.store.blocks d := by
    simpa only [hquery] using
      hA.wellFormed.blocks_agree
        (E.blockProvenance cfg ext u nu)
        (E.blockProvenance cfg ext v q) hdPast hdQueryE
  have hdSlotLePast : ((E.store cfg ext u nu).blocks d).slot ≤
      E.slot_at cfg nu := by
    have hle := E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      (by
        obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hA.genesis
        exact ⟨ast, ablk, hgen, hslot⟩)
      u nu d hdPast
    simpa only [E.store_current_slot cfg ext u nu] using hle
  refine ⟨nu, d, hnuq, hdQuery, ?_, ?_⟩
  · simpa only [hquery] using hdResult
  · rw [← hdAgree]
    exact hdSlotLePast

/-- A successful strict current-epoch selected result cannot occur at the
start of its epoch, given only the narrow past-descendant witness and ordinary
query-store geometry.

The witness block's slot is at once at least the selected block's epoch
boundary and at most a strictly earlier voting slot, contradicting that the
query itself is exactly at that boundary. -/
theorem StrictSelectedResultMechanicalFacts.not_epochStart_of_current
    {q : Nat} {query : FastConfirmationStore Root} {input result : Root}
    (hclock : get_current_slot cfg query.store = E.slot_at cfg q)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hpast : E.ConfirmedPastDescendantSlotWitnessAt cfg q
      query.store result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store) :
    is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true := by
  intro hstart
  obtain ⟨pastSecond, descendant, hpastLt, hdescendant,
      hdescends, hdescendantSlot⟩ := hpast
  have hresultSlotLeD : (query.store.blocks result).slot ≤
      (query.store.blocks descendant).slot :=
    ancestor_slot_le hparent
      (hwalk result h.result_known descendant hdescendant) hdescends
  have hqueryBoundary : get_current_slot cfg query.store =
      compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) := by
    have hzero : compute_slots_since_epoch_start cfg
        (get_current_slot cfg query.store) = 0 := by
      simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hzero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hzero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hquerySlotLeResult : E.slot_at cfg q ≤
      (query.store.blocks result).slot := by
    rw [← hclock, hqueryBoundary, ← hcurrent]
    exact start_slot_at_block_epoch_le cfg query.store result
  have : E.slot_at cfg q ≤ E.slot_at cfg pastSecond := by
    calc
      E.slot_at cfg q ≤ (query.store.blocks result).slot := hquerySlotLeResult
      _ ≤ (query.store.blocks descendant).slot := hresultSlotLeD
      _ ≤ E.slot_at cfg pastSecond := hdescendantSlot
  exact (Nat.not_le_of_gt hpastLt) this

/-! ## Current-next query carrier on the actual filter path -/

/-- The strict current-result Lemma-13 argument can be kept on the actual
query-filter path.  If `get_head` used the direct justified fallback, that
coverage is returned as a bypass.  Otherwise the concrete viable leaf below
the query head retains both exact filter checks, and accepted GU monotonicity
upgrades the head's Lemma-13 bound to that same leaf.

This is query-local and contains no endpoint filter, finality stability,
source visibility, or safety conclusion. -/
theorem StrictSelectedResultMechanicalFacts.current_direct_or_headFilterLemma13Source
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {query : FastConfirmationStore Root} {input result : Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hprovenance : BlockProvenance E query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hjustified : query.store.justified_checkpoint.root ∈
      query.store.block_roots)
    (hinput : input ∈ query.store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext query input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true) :
    is_ancestor query.store
        (get_node_for_root query.store.justified_checkpoint.root)
        (get_node_for_root result) = true ∨
      E.HeadFilterViableLemma13SourceAt cfg ext B query.store result := by
  have hbelow : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root result) = true := by
    have hstrict' :
        find_latest_confirmed_descendant cfg ext query input ≠ input := by
      simpa only [hout] using hstrict
    simpa only [hout] using
      strictSelectedResult_below_head cfg ext hparent hwalk hhead
        hinput hstrict'
  have hguHead : (B.state.GU (get_head cfg query.store).root).epoch + 1 ≥
      get_current_store_epoch cfg query.store := by
    rcases h.trace_origin with
      ⟨_a, hedge, _hentry, _hrecent, _hdesc⟩ |
        ⟨_a, _hedge, hentry, _hfinal⟩
    · exact False.elim ((hedge.gates cfg ext).1 hcurrent)
    · rcases hentry with hstart | hgu
      · exact False.elim (hnotStart hstart)
      · have hprojection :=
          Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection
            B hstore
        have hguEq : query.store.unrealized_justifications
            (get_head cfg query.store).root =
          B.state.GU (get_head cfg query.store).root :=
          hprojection.unrealized_justification _ hhead
        simpa only [hguEq] using hgu
  rcases queryHead_direct_or_headFilterViableLeafBelow cfg hparent hwalk
      hjustified h.result_known hbelow with hdirect | hviable
  · exact Or.inl hdirect
  · right
    obtain ⟨tip, htip, hheadKnown, htipHead, htipResult, hleaf,
        hjustifiedCheck, hfinalizedCheck, htipHeadWalk,
        htipResultWalk⟩ := hviable
    have hsemantic : E.RootDescends tip (get_head cfg query.store).root :=
      E.rootDescends_of_store_ancestor hprovenance hparent htipHeadWalk
        htipHead
    have hheadAccepted :=
      E.acceptedRoot_of_causal_known cfg ext hstore hheadKnown
    have htipAccepted := E.acceptedRoot_of_causal_known cfg ext hstore htip
    have hguMono : (B.state.GU (get_head cfg query.store).root).epoch ≤
        (B.state.GU tip).epoch :=
      B.state.gu_epoch_le_of_descends cfg ext hheadAccepted htipAccepted
        hsemantic
    exact ⟨tip, htip, hheadKnown, htipHead, htipResult, hleaf,
      hjustifiedCheck, hfinalizedCheck, htipHeadWalk, htipResultWalk,
      hguHead.trans (Nat.add_le_add_right hguMono 1)⟩

/-- Relay the exact query-filter Lemma-13 tip to a next-epoch endpoint.  The
endpoint selector is on its old-block branch and therefore reads `GU(tip)`;
the output keeps that same `tip` together with the query finalized check and
both path walks. -/
theorem HeadFilterViableLemma13SourceAt.relay_endpointNext
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hgenSlot : ast.slot = ablk.message.slot)
    (hgenParent : ablk.message.parent_root ≠ ablk.root)
    {query : Store Root} {w : ValidatorIndex} {m : Nat} {result : Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext (E.store cfg ext w m))
    (hqueryParent : ParentSlotLt query)
    (hqueryProvenance : BlockProvenance E query)
    (hqueryNonfuture : BlocksSlotLe (get_current_slot cfg query) query)
    (hresultQ : result ∈ query.block_roots)
    (hrelay : ∀ r, r ∈ query.block_roots →
      r ∈ (E.store cfg ext w m).block_roots)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query + 1)
    (h : E.HeadFilterViableLemma13SourceAt cfg ext B query result) :
    RelayedHeadFilterRecentSourceAt cfg query (E.store cfg ext w m) result := by
  obtain ⟨tip, htipQ, hheadQ, htipHeadQ, htipResultQ, hleaf,
      hjustifiedCheck, hfinalizedCheck, htipHeadWalk,
      htipResultWalk, hguRecent⟩ := h
  have htipM : tip ∈ (E.store cfg ext w m).block_roots := hrelay tip htipQ
  have hsemantic : E.RootDescends tip result :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      htipResultWalk htipResultQ
  have htipResultM : is_ancestor (E.store cfg ext w m) (get_node_for_root tip)
      (get_node_for_root result) = true := by
    have hresultRoot : E.ExecutionRoot result :=
      by
        rcases hqueryProvenance result hresultQ with
          hgenesis | ⟨sb, ⟨sw, sn, hsched⟩, hroot, hblock⟩
        · exact ⟨query.blocks result, Or.inl ⟨hgenesis.1, hgenesis.2⟩⟩
        · exact ⟨query.blocks result,
            Or.inr ⟨sw, sn, sb, hsched, hroot, hblock.symm⟩⟩
    exact (E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hwf hec hgen hgenSlot hgenParent htipM hresultRoot
      hsemantic).2
  have htipEpochLe : get_block_epoch cfg query tip ≤
      get_current_store_epoch cfg query :=
    ce_mono cfg (hqueryNonfuture tip htipQ)
  have hqueryAt : E.AcceptedBlockAt cfg ext tip (query.blocks tip) :=
    E.acceptedBlockAt_of_causal_known cfg ext hquery htipQ
  have hendpointAt : E.AcceptedBlockAt cfg ext tip
      ((E.store cfg ext w m).blocks tip) :=
    E.acceptedBlockAt_of_causal_known cfg ext hendpoint htipM
  have hblock : query.blocks tip = (E.store cfg ext w m).blocks tip :=
    hqueryAt.unique cfg ext E hwf hendpointAt
  have htipOld : get_current_store_epoch cfg (E.store cfg ext w m) >
      get_block_epoch cfg (E.store cfg ext w m) tip := by
    rw [hnextEpoch]
    simp only [get_block_epoch, ← hblock]
    exact Nat.lt_succ_of_le htipEpochLe
  have hsourceEq : get_voting_source cfg (E.store cfg ext w m) tip =
      B.state.GU tip := by
    rw [hendpoint.getVotingSource_eq_acceptedSelector cfg ext B htipM]
    exact if_pos htipOld
  have hrecentM :
      (get_voting_source cfg (E.store cfg ext w m) tip).epoch + 2 ≥
        get_current_store_epoch cfg (E.store cfg ext w m) := by
    rw [hsourceEq, hnextEpoch]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      Nat.add_le_add_right hguRecent 1
  exact ⟨tip, htipQ, hheadQ, htipHeadQ, htipResultQ, hleaf,
    hjustifiedCheck, hfinalizedCheck, htipHeadWalk, htipResultWalk,
    htipM, htipResultM, hrecentM⟩

/-! ## Ordinary cross-store endpoint wiring -/

/-- Same-epoch source transport for one explicit seed.  Unlike the more
convenient bulk adapter, this theorem asks only for the chosen seed's endpoint
knownness; call-facing constructors below derive that knownness from
`Synchrony` rather than postulating a whole-store inclusion. -/
theorem recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hgenSlot : ast.slot = ablk.message.slot)
    (hgenParent : ablk.message.parent_root ≠ ablk.root)
    {query : Store Root} {w : ValidatorIndex} {m : Nat}
    {selected seed : Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext (E.store cfg ext w m))
    (hqueryParent : ParentSlotLt query)
    (hqueryProvenance : BlockProvenance E query)
    (hqueryWalk : WalkKnown query (query.blocks selected).slot seed)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hseedQ : seed ∈ query.block_roots)
    (hseedM : seed ∈ (E.store cfg ext w m).block_roots)
    (hseedSelectedQ : is_ancestor query (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hclock : get_current_store_epoch cfg query ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query)
    (hrecentQ : (get_voting_source cfg query seed).epoch + 2 ≥
      get_current_store_epoch cfg query) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      hqueryWalk hseedSelectedQ
  have hseedSelectedM : is_ancestor (E.store cfg ext w m)
      (get_node_for_root seed) (get_node_for_root selected) = true :=
    E.store_ancestor_of_rootDescends_for_storeReflection cfg ext hwf hec
      hgen hgenSlot hgenParent hseedM hselectedM hsemantic
  have hsourceMono := E.acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hwf hquery hendpoint hseedQ hseedM hclock
  refine ⟨seed, hseedM, hseedSelectedM, ?_⟩
  rw [hsameEpoch]
  exact hrecentQ.trans (Nat.add_le_add_right hsourceMono 2)

/-- Actual-call previous cell.  The selected root is relayed through its
honest confirmation supporter.  In the previous-loop arm, the exact cached
seed is known before the call and the slot advance makes `Synchrony.block_relay`
applicable even at another honest node's same-slot endpoint.  In the tentative
arm the selected root itself is the seed.

The public signature lists the independent lower contracts; it does not
export `SelectedMarginAssumptions` as a completion premise. -/
theorem StrictSelectedResultMechanicalFacts.fcrStep_previous_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {input result : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input result)
    (hprevious : get_block_epoch cfg (E.fcrStep cfg ext v n).store result + 1 =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnm : n + 1 ≤ m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) result := by
  let hA := E.selectedMarginAssumptions_of_earlyPhaseInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hnH : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hn1H
  have hslotForward : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    E.slot_at_mono cfg hnm
  have hselectedM : result ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_minimal cfg ext hA
      v hv (n + 1) (E.fcrStep cfg ext v n)
      (E.fcrStep_store cfg ext v n) result hn1H
      (by simpa only [E.fcrStep_store] using h.result_known)
      (by simpa only [E.fcrStep_store] using h.parent_known)
      h.confirmed w hw m hslotForward hmH
  have hqueryCausal : E.CausalStore cfg ext
      (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv (n + 1) hn1H
  have hqueryParent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hqueryProvenance : BlockProvenance E
      (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using E.blockProvenance cfg ext v (n + 1)
  have hqueryWalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hclock : get_current_store_epoch cfg (E.fcrStep cfg ext v n).store ≤
      get_current_store_epoch cfg (E.store cfg ext w m) :=
    Nat.le_of_eq hsameEpoch.symm
  rcases h.trace_origin with
    ⟨_a, _hedge, _hentry, hrecent, hdesc⟩ |
      ⟨_a, _hedge, _hentry, hfinal⟩
  · have hseedQ := E.fcrStep_previousSlotHead_known cfg ext
      hT.genesis hdomain v hv n hn1H
    have hseedN : (E.fcrStep cfg ext v n).previous_slot_head ∈
        (E.store cfg ext v n).block_roots := by
      rw [E.fcrStep_previousSlotHead_eq_currentSlotHead]
      exact E.fcr_currentSlotHead_known cfg ext hT.genesis hdomain
        v hv n hnH
    have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
      unfold IsFCRCallAt at hcall
      simpa only [E.store_current_slot cfg ext v (n + 1),
        E.store_current_slot cfg ext v n] using hcall
    have hrelayGate : E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) :=
      (Nat.succ_le_iff.mpr hslotAdvance).trans
        (E.slot_at_mono cfg
          (hnm.trans (Nat.le_succ m)))
    have hseedM : (E.fcrStep cfg ext v n).previous_slot_head ∈
        (E.store cfg ext w m).block_roots :=
      hsync.block_relay v hv n _ hnH hseedN w hw m hmH hrelayGate
    exact E.recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
      cfg ext B hT.wellFormed hT.externals_coherence
      hgen hgenSlot hgenParent hqueryCausal hendpointCausal
      hqueryParent hqueryProvenance
      (hqueryWalk result h.result_known _ hseedQ)
      hselectedM hseedQ hseedM hdesc hclock hsameEpoch hrecent
  · unfold TentativeSelectedResultWitness at hfinal
    rcases hfinal with hcurrent | ⟨hrecent, _houter⟩
    · have hbad : get_block_epoch cfg (E.fcrStep cfg ext v n).store result + 1 =
          get_block_epoch cfg (E.fcrStep cfg ext v n).store result :=
        hprevious.trans hcurrent.symm
      exact False.elim ((Nat.ne_of_gt (Nat.lt_succ_self _)) hbad)
    · exact E.recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
        cfg ext B hT.wellFormed hT.externals_coherence
        hgen hgenSlot hgenParent hqueryCausal hendpointCausal
        hqueryParent hqueryProvenance
        (hqueryWalk result h.result_known result h.result_known)
        hselectedM h.result_known hselectedM
        (is_ancestor_refl _ _) hclock hsameEpoch hrecent

/-- Actual `fcrStep` current/next cell.  Epoch-start exclusion is derived from
the narrow honest past-descendant witness.  The strict epoch gap itself gives
the `Synchrony.block_relay` clock gate for every query seed, so neither
selected-root nor seed endpoint knownness is a premise. -/
theorem StrictSelectedResultMechanicalFacts.fcrStep_currentNext_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input result : Root}
    (hinput : input ∈ (E.fcrStep cfg ext v n).store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext
      (E.fcrStep cfg ext v n) input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input result)
    (hcurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store result =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.fcrStep cfg ext v n).store + 1) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) result := by
  let hA := E.selectedMarginAssumptions_of_earlyPhaseInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hqueryCausal : E.CausalStore cfg ext
      (E.fcrStep cfg ext v n).store := by
    rw [E.fcrStep_store]
    exact E.store_causal cfg ext v (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv (n + 1) hn1H
  have hqueryParent : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hparentN1
  have hqueryWalk : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    simpa only [E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hn1H
  have hpast := h.confirmedPastDescendantSlotWitness cfg ext hA hv hn1H
    (E.fcrStep_store cfg ext v n)
  have hnotStart := h.not_epochStart_of_current cfg ext
    (q := n + 1)
    (by rw [E.fcrStep_store, E.store_current_slot cfg ext v (n + 1)])
    hqueryParent hqueryWalk hpast hcurrent
  have hlemma := h.current_lemma13SourceSeed_of_notStart cfg ext B
    hqueryCausal hqueryParent hqueryWalk hhead hinput hout hstrict hcurrent
      hnotStart
  have hnextSlots : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) + 1 := by
    simpa only [get_current_store_epoch, E.fcrStep_store,
      E.store_current_slot cfg ext w m,
      E.store_current_slot cfg ext v (n + 1)] using hnextEpoch
  have hslotLt : E.slot_at cfg (n + 1) < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg (n + 1) :=
      Nat.le_of_not_gt hnot
    have hepochLe := ce_mono cfg hle
    rw [hnextSlots] at hepochLe
    exact (Nat.not_succ_le_self _) hepochLe
  have hrelayGate : E.slot_at cfg (n + 1) + 1 ≤
      E.slot_at cfg (m + 1) :=
    (Nat.succ_le_iff.mpr hslotLt).trans
      (E.slot_at_mono cfg (Nat.le_succ m))
  have hseedM : ∀ seed,
      seed ∈ (E.fcrStep cfg ext v n).store.block_roots →
      seed ∈ (E.store cfg ext w m).block_roots := by
    intro seed hseed
    apply hsync.block_relay v hv (n + 1) seed hn1H
      (by simpa only [E.fcrStep_store] using hseed) w hw m hmH hrelayGate
  have hqueryNonfuture : BlocksSlotLe
      (get_current_slot cfg (E.fcrStep cfg ext v n).store)
      (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hgenSlot⟩ v (n + 1)
  exact E.recentSourceSeedAt_endpointNext_of_lemma13 cfg ext B
    hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
    hqueryCausal hendpointCausal hqueryParent
    (by simpa only [E.fcrStep_store] using
      E.blockProvenance cfg ext v (n + 1))
    hqueryWalk hqueryNonfuture h.result_known (hseedM result h.result_known)
    hseedM hnextEpoch hlemma

/-- Convenience adapter for the existing minimal assumption package.  Public
accepted wiring should prefer `not_epochStart_of_current` with the narrow
projected witness. -/
theorem StrictSelectedResultMechanicalFacts.not_epochStart_of_current_of_selectedMargin
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext v q)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store) :
    is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true := by
  obtain ⟨hparentQ, hwalkQ, _hjustifiedQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  apply h.not_epochStart_of_current cfg ext
    (q := q)
    (by rw [hquery, E.store_current_slot cfg ext v q])
    (by simpa only [hquery] using hparentQ)
    (by simpa only [hquery] using hwalkQ)
    (h.confirmedPastDescendantSlotWitness cfg ext hA hv hqH hquery)
    hcurrent


end Execution

end FastConfirmation.Spec
