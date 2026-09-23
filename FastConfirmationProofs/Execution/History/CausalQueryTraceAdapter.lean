module
public import FastConfirmationProofs.FCRRule.AllowedFCRCallTrace
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetFutureSupport
public import FastConfirmationProofs.Discount.SelectedMarginConstruction
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Execution / History / CausalQueryTraceAdapter

Builds exact-position query evidence from scheduled event prefixes.

This module contains the safety-free evidence adapters needed by a query that
occurs at an exact global action position.  In particular, execution seconds
do not order a vote and a query that occur in the same second.  The production
interface therefore keeps the cast materialization/order obligation explicit.

The conclusion is the existing whole-slot `HonestVotesSupportTarget` premise;
no head-safety or strict-selection result is claimed here.
-/

namespace FastConfirmation.Spec
namespace CausalQueryEvidence

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

open AllowedFCRCalls








end CausalQueryEvidence
end FastConfirmation.Spec

/-!
# Legal-query trace adapters

This module contains `ScheduledEventPrefix.current_slot`, `ScheduledPrefixPremises.genesis_structure`, `ScheduledPrefixPremises.of_selectedMarginAssumptions` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Exact scheduled-prefix store classification -/





/-- The clock of an exact prefix is the execution clock of its scheduled
second, independently of how many events of that second were folded. -/
theorem ScheduledEventPrefix.current_slot (p : E.ScheduledEventPrefix) :
    get_current_slot cfg (p.store cfg ext) =
      E.slot_at cfg (p.previousSecond + 1) := by
  rw [ScheduledEventPrefix.store, foldl_get_current_slot]
  have hgenesis :
      (on_tick cfg (E.store cfg ext p.node p.previousSecond)
        (E.time_at (p.previousSecond + 1))).genesis_time =
        E.genesis_store.genesis_time := by
    rw [← (on_tick_storeLE cfg (E.store cfg ext p.node p.previousSecond)
      (E.time_at (p.previousSecond + 1))).2.1,
      E.store_genesis_time cfg ext p.node p.previousSecond]
  rw [get_current_slot, get_slots_since_genesis, on_tick_time, hgenesis,
    Execution.slot_at]

/-! ## Mechanical trajectory evidence at a scheduled prefix -/

/-- Structural initialization facts used by store invariant proofs. The
anchor commitment remains a separate conjunct of `genesis`. -/
theorem ScheduledPrefixPremises.genesis_structure
    {cfg : Config} {ext : Externals Root} {E : Execution Root}
    (hT : E.ScheduledPrefixPremises cfg ext) :
    ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root := by
  obtain ⟨anchorState, anchorBlock, hstore, hslot, _hcommit, hparent⟩ := hT.genesis
  exact ⟨anchorState, anchorBlock, hstore, hslot, hparent⟩

/-- The legacy selected-margin bundle supplies the operational fields. Its
anchor facts must also carry the explicit commitment required here. -/
theorem ScheduledPrefixPremises.of_selectedMarginAssumptions
    (hA : SelectedMarginAssumptions cfg ext E)
    (hgen : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root) :
    E.ScheduledPrefixPremises cfg ext :=
  { whole_seconds := hA.whole_seconds
    wellFormed := hA.wellFormed
    externals_coherence := hA.externals_coherence
    honest_behavior := hA.honest_behavior
    genesis := hgen }

/-- Store facts inherited by an honest node's in-horizon scheduled prefix. These
are operational/provenance facts only; in particular the record contains no
confirmation, base strip, recorded-epoch domination, replay, or target
agreement. -/
structure ScheduledPrefixOperationalEvidence
    (store : Store Root) (querySecond : ℕ) : Prop where
  causal : E.CausalStore cfg ext store
  current_slot : get_current_slot cfg store = E.slot_at cfg querySecond
  scheduled_provenance : SchedLMProv E cfg store
  latest_message_provenance :
    LatestMessageProvenance E cfg (get_current_slot cfg store) store
  parent_slot_lt : ParentSlotLt store
  blocks_slot_le_current : BlocksSlotLe (get_current_slot cfg store) store
  honest_not_equivocating :
    ∀ i ∈ E.honest, i ∉ store.equivocating_indices

/-- Schedule-connected latest-message provenance holds at every exact
scheduled prefix. -/
theorem ScheduledEventPrefix.schedLMProv
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix) :
    SchedLMProv E cfg (p.store cfg ext) := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  rw [ScheduledEventPrefix.store]
  refine sched_foldl cfg ext _ _ ?_ ?_
  · intro attestation fromBlock hmem
    exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hmem⟩
  · exact schedLMProv_of_latest_eq cfg
      (E.schedLMProv cfg ext ⟨anchorState, anchorBlock, hgen⟩
        p.node p.previousSecond)
      (on_tick_latest cfg (E.store cfg ext p.node p.previousSecond)
        (E.time_at (p.previousSecond + 1)))

/-- Each shorter prefix of an honest in-horizon scheduled prefix is in the
validation domain. -/
theorem ScheduledEventPrefix.honestCausal_take
    (p : E.ScheduledEventPrefix) (hp : p.node ∈ E.honest)
    (hn : E.WithinHorizon cfg (p.previousSecond + 1))
    (k : ℕ)
    (hk : k ≤ ((E.schedule p.node (p.previousSecond + 1)).take
      p.processedCount).length) :
    E.HonestCausalStore cfg ext
      ((((E.schedule p.node (p.previousSecond + 1)).take p.processedCount).take k).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext p.node p.previousSecond)
            (E.time_at (p.previousSecond + 1)))) := by
  have hkCount : k ≤ p.processedCount := by
    rw [List.length_take] at hk
    omega
  have hkSchedule : k ≤ (E.schedule p.node (p.previousSecond + 1)).length := by
    rw [List.length_take] at hk
    omega
  have hshort : E.HonestCausalStore cfg ext
      (({ p with processedCount := k, count_le := hkSchedule } :
        E.ScheduledEventPrefix).store cfg ext) :=
    .scheduledPrefix _ hp hn
  simpa only [ScheduledEventPrefix.store, List.take_take,
    Nat.min_eq_left hkCount, Nat.min_eq_right hkCount] using hshort

/-- Latest-message provenance at an honest node's in-horizon prefix, with the
prefix store's exact current slot as ambient bound. -/
theorem ScheduledEventPrefix.latestMessageProvenance
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix) (hp : p.node ∈ E.honest)
    (hn : E.WithinHorizon cfg (p.previousSecond + 1)) :
    LatestMessageProvenance E cfg (get_current_slot cfg (p.store cfg ext))
      (p.store cfg ext) := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hcur : get_current_slot cfg
      (on_tick cfg (E.store cfg ext p.node p.previousSecond)
        (E.time_at (p.previousSecond + 1))) =
      E.slot_at cfg (p.previousSecond + 1) := by
    have hp := p.current_slot cfg ext
    rwa [ScheduledEventPrefix.store, foldl_get_current_slot] at hp
  have hresult : LatestMessageProvenance E cfg
      (E.slot_at cfg (p.previousSecond + 1)) (p.store cfg ext) := by
    rw [ScheduledEventPrefix.store]
    refine LMP_foldl cfg ext hT.wellFormed hT.externals_coherence _ _ ?_ ?_ ?_ ?_ ?_
    · intro block hmem
      exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hmem⟩
    · exact on_tick_blockProvenance cfg _ _
        (E.blockProvenance cfg ext p.node p.previousSecond)
    · exact le_of_eq hcur
    · exact on_tick_LMP cfg _ _
        ((E.latestMessageProvenance cfg ext hT.wellFormed
            hT.externals_coherence ⟨anchorState, anchorBlock, hgen⟩
            p.node p.previousSecond hp
            (E.withinHorizon_mono cfg (Nat.le_succ _) hn)).mono_sl
          (E.slot_at_mono cfg (Nat.le_succ p.previousSecond)))
    · exact ScheduledEventPrefix.honestCausal_take cfg ext E p hp hn
  rwa [p.current_slot cfg ext]

/-- Every block known at a scheduled prefix is no later than that prefix's
current slot. -/
theorem ScheduledEventPrefix.blocksSlotLeCurrent
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix) :
    BlocksSlotLe (get_current_slot cfg (p.store cfg ext))
      (p.store cfg ext) := by
  obtain ⟨anchorState, anchorBlock, hgen, hslot, _hparent⟩ := hT.genesis_structure
  have hcur : get_current_slot cfg
      (on_tick cfg (E.store cfg ext p.node p.previousSecond)
        (E.time_at (p.previousSecond + 1))) =
      E.slot_at cfg (p.previousSecond + 1) := by
    have hp := p.current_slot cfg ext
    rwa [ScheduledEventPrefix.store, foldl_get_current_slot] at hp
  have hresult : BlocksSlotLe (E.slot_at cfg (p.previousSecond + 1))
      (p.store cfg ext) := by
    rw [ScheduledEventPrefix.store]
    refine blocksSlotLe_foldl cfg ext _ _ (le_of_eq hcur) ?_
    exact (on_tick_sameBlocks cfg (E.store cfg ext p.node p.previousSecond)
      (E.time_at (p.previousSecond + 1))).blocksSlotLe
        ((E.store_blocksSlotLe cfg ext hT.whole_seconds
          ⟨anchorState, anchorBlock, hgen, hslot⟩
          p.node p.previousSecond).mono_sl
            (E.slot_at_mono cfg (Nat.le_succ p.previousSecond)))
  rwa [p.current_slot cfg ext]

/-- Parent slots strictly decrease at every exact scheduled prefix. -/
theorem ScheduledEventPrefix.parentSlotLt
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix) :
    ParentSlotLt (p.store cfg ext) := by
  obtain ⟨anchorState, anchorBlock, hgen, hslot, hparent⟩ := hT.genesis_structure
  have hgenFull : ∃ (anchorState : BeaconState Root)
      (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
        anchorState.slot = anchorBlock.message.slot ∧
        anchorBlock.message.parent_root ≠ anchorBlock.root :=
    ⟨anchorState, anchorBlock, hgen, hslot, hparent⟩
  have hgenStore : WellFormedStore E.genesis_store := by
    rw [hgen]
    exact wellFormedStore_get_forkchoice_store cfg anchorState anchorBlock
      hslot hparent
  have hparentUnscheduled : ∀ w n (block : SignedBeaconBlock Root),
      Event.block block ∈ E.schedule w n →
        block.root ≠ anchorBlock.message.parent_root := by
    intro w n block hmem
    have hanchorKnown : anchorBlock.root ∈ E.genesis_store.block_roots := by
      rw [hgen]
      simp [get_forkchoice_store]
    have hanchorParent :
        (E.genesis_store.blocks anchorBlock.root).parent_root =
          anchorBlock.message.parent_root := by
      rw [hgen]
      simp [get_forkchoice_store]
    rw [← hanchorParent]
    exact hT.wellFormed.anchor_parent_unscheduled anchorBlock.root
      hanchorKnown w n block hmem
  have hparentKnown : ParentInRootsOr anchorBlock.message.parent_root
      (E.store cfg ext p.node p.previousSecond) := by
    intro root hroot
    rcases E.store_nonAnchorParentKnown cfg ext hgen p.node
        p.previousSecond root hroot with hanchor | hknown
    · right
      subst root
      rw [E.store_anchor_block cfg ext hT.wellFormed hgen p.node
        p.previousSecond hroot]
    · exact Or.inl hknown
  have hbase : WFPlus anchorBlock.message.parent_root E
      (E.store cfg ext p.node p.previousSecond) :=
    ⟨E.store_wellFormedStoreCore cfg ext
        hT.externals_coherence.state_transition_slot hgenStore.core
        p.node p.previousSecond,
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        hgenFull hT.wellFormed.anchor_parent_unscheduled
        p.node p.previousSecond,
      hparentKnown,
      E.blockProvenance cfg ext p.node p.previousSecond⟩
  have hprefix : WFPlus anchorBlock.message.parent_root E
      (p.store cfg ext) := by
    rw [ScheduledEventPrefix.store]
    refine WFPlus_foldl cfg ext anchorBlock.message.parent_root
      hT.wellFormed hT.externals_coherence.state_transition_slot
      hT.externals_coherence.state_transition_pre_slot_lt hparentUnscheduled
      _ _ ?_ ?_
    · intro block hmem
      exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hmem⟩
    · exact on_tick_WFPlus cfg anchorBlock.message.parent_root _ _ hbase
  exact hprefix.2.1

/-- No honest validator is marked equivocating at an honest node's
in-horizon scheduled prefix. -/
theorem ScheduledEventPrefix.honest_not_equivocating
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix) (hp : p.node ∈ E.honest)
    (hn : E.WithinHorizon cfg (p.previousSecond + 1)) :
    ∀ i ∈ E.honest, i ∉ (p.store cfg ext).equivocating_indices := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  intro i hi
  rw [ScheduledEventPrefix.store]
  refine honest_not_equiv_foldl cfg ext hT.honest_behavior
    hT.externals_coherence hi _ _ ?_ ?_ ?_
  · rw [on_tick_equiv]
    exact E.honest_not_equivocating cfg ext hT.honest_behavior
      hT.externals_coherence ⟨anchorState, anchorBlock, hgen⟩ hi
      p.node p.previousSecond hp
      (E.withinHorizon_mono cfg (Nat.le_succ _) hn)
  · exact on_tick_unknownBlockStatesDefault cfg _ _
      (E.unknownBlockStatesDefault_store cfg ext
        ⟨anchorState, anchorBlock, hgen⟩ p.node p.previousSecond)
  · exact ScheduledEventPrefix.honestCausal_take cfg ext E p hp hn

/-- Assemble the inherited facts at an honest node's in-horizon prefix. -/
theorem ScheduledEventPrefix.operationalEvidence
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix) (hp : p.node ∈ E.honest)
    (hn : E.WithinHorizon cfg (p.previousSecond + 1)) :
    E.ScheduledPrefixOperationalEvidence cfg ext (p.store cfg ext)
      (p.previousSecond + 1) :=
  { causal := .scheduledPrefix p
    current_slot := p.current_slot cfg ext
    scheduled_provenance :=
      ScheduledEventPrefix.schedLMProv cfg ext E hT p
    latest_message_provenance :=
      ScheduledEventPrefix.latestMessageProvenance cfg ext E hT p hp hn
    parent_slot_lt :=
      ScheduledEventPrefix.parentSlotLt cfg ext E hT p
    blocks_slot_le_current :=
      ScheduledEventPrefix.blocksSlotLeCurrent cfg ext E hT p
    honest_not_equivocating :=
      ScheduledEventPrefix.honest_not_equivocating cfg ext E hT p hp hn }

end Execution

namespace AllowedFCRCalls

open Execution

/-! ## Whole-second runtime coherence -/







/- The local interpreter preserves the exact second relation. -/


/-! ## Accepted local-query simulation boundary -/







end AllowedFCRCalls

namespace Execution

variable (E : Execution Root)

/-! ## Exact residual for the query-store base evidence -/



end Execution

namespace AllowedFCRCalls

open Execution


/-! ## Global cast materialization and exact pre-query order -/











/-! ## One global query tied to one exact scheduled prefix -/












end AllowedFCRCalls
end FastConfirmation.Spec

end
