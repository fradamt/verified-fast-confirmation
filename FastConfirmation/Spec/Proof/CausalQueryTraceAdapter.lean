import FastConfirmation.Spec.Proof.CausalQueryEvidence
import FastConfirmation.Spec.Proof.SelectedMarginConstruction

/-!
# Legal-query trace adapters

The low call interpreter accepts operational schedules that are more general
than `Execution.store`: events may be received independently of the execution
schedule and a queued event may be processed after a later clock tick.  Trace
legality alone therefore does not identify the runtime store with an execution
boundary or an exact per-second prefix.

This module makes that simulation boundary explicit.  A
`ScheduledQueryPrefixCompatibility` contains an accepted `QuerySnapshot` and
identifies its exact pre-query store with an `Execution.ScheduledEventPrefix`.
It contains no `CausalStore`, safety, margin, class-transport, recorded-epoch,
or target-agreement premise.  Once supplied, the existing prefix model gives
causal reachability and the store-local trajectory invariants mechanically.

Inbox origin and expected-proposer identity are deliberately not inferred.
`Execution.schedule` has no receive position or expected-proposer tag, while
`QueuedEvent` has no proposer identity to compare.  Those are narrow external
simulation obligations when establishing `store_eq`; they are not fork-choice
evidence fields.  In particular, `LegalTrace` alone does not rule out a queued
event being processed after later ticks and therefore cannot prove the
scheduled-prefix simulation boundary.

The global-action half similarly keeps the erased low-to-high fact explicit:
every relevant pre-query `Execution.vote` is materialized either in the
initial cast log or by a cast action in the interpreted prefix.  Strict action
ordering is then derived from `globalRun?`; it is not assumed as membership in
the final runtime.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Exact scheduled-prefix store classification -/

/-- An exact execution-second prefix which has not yet folded every event in
that second's schedule.  The pending event may carry an attestation for an
older slot; delay is about application order, not the attestation's data slot.
-/
def DelayedScheduledPrefixStore (store : Store Root) : Prop :=
  ∃ scheduledPrefix : E.ScheduledEventPrefix,
    scheduledPrefix.processedCount <
        (E.schedule scheduledPrefix.node
          (scheduledPrefix.previousSecond + 1)).length ∧
      store = scheduledPrefix.store cfg ext

/-- Exact classification of a store identified with a scheduled prefix.  A
full prefix is the ordinary execution boundary; a strict prefix is the named
delayed case. -/
inductive ScheduledPrefixStoreClass (store : Store Root) : Prop where
  | completed (node : ValidatorIndex) (previousSecond : ℕ)
      (store_eq : store = E.store cfg ext node (previousSecond + 1))
  | delayed (evidence : E.DelayedScheduledPrefixStore cfg ext store)

/-- Every classified scheduled-prefix store is in the existing causal-store
domain. -/
theorem ScheduledPrefixStoreClass.causal
    {store : Store Root}
    (h : E.ScheduledPrefixStoreClass cfg ext store) :
    E.CausalStore cfg ext store := by
  cases h with
  | completed node previousSecond hstore =>
      rw [hstore]
      exact E.store_causal cfg ext node (previousSecond + 1)
  | delayed evidence =>
      obtain ⟨scheduledPrefix, _hincomplete, hstore⟩ := evidence
      rw [hstore]
      exact .scheduledPrefix scheduledPrefix

/-- A scheduled prefix is either complete or a strict delayed prefix. -/
theorem ScheduledEventPrefix.store_class (p : E.ScheduledEventPrefix) :
    E.ScheduledPrefixStoreClass cfg ext (p.store cfg ext) := by
  rcases Nat.eq_or_lt_of_le p.count_le with hcomplete | hincomplete
  · apply ScheduledPrefixStoreClass.completed p.node p.previousSecond
    rw [ScheduledEventPrefix.store, hcomplete, List.take_length]
    rfl
  · exact .delayed
      ⟨p, hincomplete, rfl⟩

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

/-- The exact trajectory assumptions used to replay store-local invariants to
an in-second prefix. These are the operational fields of
`SelectedMarginAssumptions`, with an explicit anchor commitment. No Byzantine
estimate, selected-margin domain, or head conclusion is included. -/
structure ScheduledPrefixTrajectoryAssumptions : Prop where
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  wellFormed : WellFormedExecution E
  externals_coherence : ExternalsCoherence cfg ext E
  honest_behavior : HonestBehavior cfg ext E
  genesis : ∃ (anchorState : BeaconState Root)
      (anchorBlock : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root

/-- Structural initialization facts used by store invariant proofs. The
anchor commitment remains a separate conjunct of `genesis`. -/
theorem ScheduledPrefixTrajectoryAssumptions.genesis_structure
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext) :
    ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root := by
  obtain ⟨anchorState, anchorBlock, hstore, hslot, _hcommit, hparent⟩ := hT.genesis
  exact ⟨anchorState, anchorBlock, hstore, hslot, hparent⟩

/-- The legacy selected-margin bundle supplies the operational fields. Its
anchor facts must also carry the explicit commitment required here. -/
theorem ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions
    (hA : SelectedMarginAssumptions cfg ext E)
    (hgen : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root) :
    E.ScheduledPrefixTrajectoryAssumptions cfg ext :=
  { whole_seconds := hA.whole_seconds
    wellFormed := hA.wellFormed
    externals_coherence := hA.externals_coherence
    honest_behavior := hA.honest_behavior
    genesis := hgen }

/-- Store facts mechanically inherited by an exact scheduled prefix.  These
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
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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

/-- Ordinary latest-message provenance, with the prefix store's exact current
slot as ambient bound. -/
theorem ScheduledEventPrefix.latestMessageProvenance
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (p : E.ScheduledEventPrefix) :
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
    refine LMP_foldl cfg ext hT.wellFormed hT.externals_coherence _ _ ?_ ?_ ?_ ?_
    · intro block hmem
      exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hmem⟩
    · exact on_tick_blockProvenance cfg _ _
        (E.blockProvenance cfg ext p.node p.previousSecond)
    · exact le_of_eq hcur
    · exact on_tick_LMP cfg _ _
        ((E.latestMessageProvenance cfg ext hT.wellFormed
            hT.externals_coherence ⟨anchorState, anchorBlock, hgen⟩
            p.node p.previousSecond).mono_sl
          (E.slot_at_mono cfg (Nat.le_succ p.previousSecond)))
  rwa [p.current_slot cfg ext]

/-- Every block known at a scheduled prefix is no later than that prefix's
current slot. -/
theorem ScheduledEventPrefix.blocksSlotLeCurrent
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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

/-- No honest validator is marked equivocating at an exact scheduled prefix.
-/
theorem ScheduledEventPrefix.honest_not_equivocating
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (p : E.ScheduledEventPrefix) :
    ∀ i ∈ E.honest, i ∉ (p.store cfg ext).equivocating_indices := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  intro i hi
  rw [ScheduledEventPrefix.store]
  refine honest_not_equiv_foldl cfg ext hT.honest_behavior
    hT.externals_coherence hi _ _ ?_
  rw [on_tick_equiv]
  exact E.honest_not_equivocating cfg ext hT.honest_behavior
    hT.externals_coherence ⟨anchorState, anchorBlock, hgen⟩ hi
    p.node p.previousSecond

/-- Assemble all mechanically inherited prefix facts. -/
theorem ScheduledEventPrefix.operationalEvidence
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (p : E.ScheduledEventPrefix) :
    E.ScheduledPrefixOperationalEvidence cfg ext (p.store cfg ext)
      (p.previousSecond + 1) :=
  { causal := .scheduledPrefix p
    current_slot := p.current_slot cfg ext
    scheduled_provenance :=
      ScheduledEventPrefix.schedLMProv cfg ext E hT p
    latest_message_provenance :=
      ScheduledEventPrefix.latestMessageProvenance cfg ext E hT p
    parent_slot_lt :=
      ScheduledEventPrefix.parentSlotLt cfg ext E hT p
    blocks_slot_le_current :=
      ScheduledEventPrefix.blocksSlotLeCurrent cfg ext E hT p
    honest_not_equivocating :=
      ScheduledEventPrefix.honest_not_equivocating cfg ext E hT p }

end Execution

namespace AllowedFCRCalls

open Execution

/-! ## Whole-second runtime coherence -/

/-- The runtime's millisecond counter and its fork-choice store name the same
whole second.  Slot-level `clockAligned` is strictly weaker when a slot spans
several seconds. -/
def WholeSecondAligned (runtime : Runtime Root) : Prop :=
  runtime.fcrStore.store.time =
    runtime.fcrStore.store.genesis_time + runtime.elapsedMs / 1000

/-- Whole-second offset of relative execution second zero from beacon-chain
genesis.  It is nonzero for a checkpoint-sync execution start. -/
def executionInitialElapsedSecond (E : Execution Root) : ℕ :=
  E.genesis_store.time - E.genesis_store.genesis_time

/-- Exact arithmetic domain on which `initRuntime`'s guarded
`seconds_to_milliseconds` conversion round-trips. -/
def InitStoreTimeRepresentable (store : Store Root) : Prop :=
  store.genesis_time ≤ store.time ∧
    store.time - store.genesis_time ≤ UINT64_MAX / 1000

omit [LinearOrder Root] [Inhabited Root] in
/-- Initialization establishes whole-second alignment exactly when its input
store time is nonnegative relative to genesis and the millisecond conversion
does not take the overflow branch. -/
theorem wholeSecondAligned_initRuntime
    (fcrStore : FastConfirmationStore Root) (mode : StartupMode)
    (htime : InitStoreTimeRepresentable fcrStore.store) :
    WholeSecondAligned (initRuntime cfg fcrStore mode) := by
  rw [WholeSecondAligned]
  simp only [initRuntime]
  rw [storeElapsedMs, seconds_to_milliseconds,
    if_neg (Nat.not_lt_of_ge htime.2)]
  rw [Nat.mul_div_left _ (by decide : 0 < 1000)]
  exact (Nat.add_sub_of_le htime.1).symm

@[simp] private theorem apply_event_getD_time
    (store : Store Root) (event : Event Root) :
    ((apply_event cfg ext store event).getD store).time = store.time := by
  cases h : apply_event cfg ext store event with
  | none => rfl
  | some next => exact apply_event_time cfg ext h

@[simp] private theorem apply_event_getD_genesis_time
    (store : Store Root) (event : Event Root) :
    ((apply_event cfg ext store event).getD store).genesis_time =
      store.genesis_time := by
  cases h : apply_event cfg ext store event with
  | none => rfl
  | some next => exact (apply_event_storeLE cfg ext h).2.1.symm

/- The local interpreter preserves the exact second relation. -/
theorem wholeSecondAligned_step
    {runtime after : Runtime Root} {action : Action Root}
    (haligned : WholeSecondAligned runtime)
    (hstep : step? cfg ext runtime action = some after) :
    WholeSecondAligned after := by
  cases action with
  | elapseTo elapsedMs =>
      simp only [step?] at hstep
      split at hstep
      · contradiction
      split at hstep
      · split at hstep
        · cases hstep
          rw [WholeSecondAligned]
          change
            (on_tick cfg runtime.fcrStore.store
                (runtime.fcrStore.store.genesis_time + elapsedMs / 1000)).time =
              (on_tick cfg runtime.fcrStore.store
                (runtime.fcrStore.store.genesis_time + elapsedMs / 1000)).genesis_time +
                elapsedMs / 1000
          rw [on_tick_time, ← (on_tick_storeLE cfg runtime.fcrStore.store
            (runtime.fcrStore.store.genesis_time + elapsedMs / 1000)).2.1]
        · contradiction
      · contradiction
  | receive queued =>
      simp only [step?] at hstep
      split at hstep
      · contradiction
      · cases hstep
        exact haligned
  | processNext =>
      simp only [step?] at hstep
      split at hstep
      · contradiction
      · cases hpending : runtime.pending with
        | nil =>
            simp only [hpending] at hstep
            contradiction
        | cons queued rest =>
            simp only [hpending] at hstep
            cases htag : queued.expectedProposerFor with
            | none =>
                simp only [htag] at hstep
                cases hstep
                rw [WholeSecondAligned]
                change
                  ((apply_event cfg ext runtime.fcrStore.store queued.event).getD
                        runtime.fcrStore.store).time =
                    ((apply_event cfg ext runtime.fcrStore.store queued.event).getD
                          runtime.fcrStore.store).genesis_time +
                      runtime.elapsedMs / 1000
                rw [apply_event_getD_time, apply_event_getD_genesis_time]
                exact haligned
            | some slot =>
                simp only [htag] at hstep
                cases hevent : queued.event with
                | block block =>
                    simp only [hevent] at hstep
                    cases happly : apply_event cfg ext runtime.fcrStore.store
                        (.block block) with
                    | none =>
                        simp only [happly] at hstep
                        contradiction
                    | some nextStore =>
                        simp only [happly] at hstep
                        split at hstep
                        · cases hstep
                          rw [WholeSecondAligned]
                          change nextStore.time = nextStore.genesis_time +
                            runtime.elapsedMs / 1000
                          rw [apply_event_time cfg ext happly,
                            ← (apply_event_storeLE cfg ext happly).2.1]
                          exact haligned
                        · contradiction
                | attestation attestation isFromBlock =>
                    simp only [hevent] at hstep
                    contradiction
                | attester_slashing slashing =>
                    simp only [hevent] at hstep
                    contradiction
  | updateVariables =>
      simp only [step?] at hstep
      split at hstep
      · cases hstep
        rw [WholeSecondAligned]
        change
          (update_fast_confirmation_variables cfg runtime.fcrStore).store.time =
            (update_fast_confirmation_variables cfg runtime.fcrStore).store.genesis_time +
              runtime.elapsedMs / 1000
        rw [update_fast_confirmation_variables_store]
        exact haligned
      · contradiction
  | query kind =>
      cases kind with
      | mandatory =>
          simp only [step?] at hstep
          split at hstep
          · cases hstep
            exact haligned
          · contradiction
      | extra =>
          simp only [step?] at hstep
          split at hstep
          · contradiction
          · cases hstep
            exact haligned

/-- Every accepted local action prefix preserves whole-second alignment. -/
theorem wholeSecondAligned_run
    {runtime after : Runtime Root} {actions : List (Action Root)}
    (haligned : WholeSecondAligned runtime)
    (hrun : run? cfg ext runtime actions = some after) :
    WholeSecondAligned after := by
  induction actions generalizing runtime with
  | nil =>
      simp only [run?] at hrun
      cases hrun
      exact haligned
  | cons action actions ih =>
      simp only [run?] at hrun
      cases hstep : step? cfg ext runtime action with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          exact ih (wholeSecondAligned_step cfg ext haligned hstep) hrun

/-! ## Accepted local-query simulation boundary -/

/-- An accepted local query whose exact pre-query store is an exact prefix of
one concrete execution second.  `store_eq` is the explicit operational
simulation boundary: it is not derived from `LegalTrace` or `QuerySnapshot`.
-/
structure ScheduledQueryPrefixCompatibility
    (E : Execution Root)
    (runtime : Runtime Root) (actions : List (Action Root))
    (position : ℕ) (before after : Runtime Root)
    (querySecond : ℕ) (scheduledPrefix : E.ScheduledEventPrefix) : Prop where
  snapshot : QuerySnapshot cfg ext runtime actions position before after
  scheduled_second : scheduledPrefix.previousSecond + 1 = querySecond
  store_eq : before.fcrStore.store = scheduledPrefix.store cfg ext
  clock_aligned : clockAligned cfg before

/-- The exact store evaluated by a compatible accepted query is causal. -/
theorem ScheduledQueryPrefixCompatibility.queryStore_causal
    {E : Execution Root}
    {runtime : Runtime Root} {actions : List (Action Root)}
    {position : ℕ} {before after : Runtime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : ScheduledQueryPrefixCompatibility cfg ext E runtime actions position
      before after querySecond scheduledPrefix) :
    E.CausalStore cfg ext before.fcrStore.store := by
  rw [h.store_eq]
  exact .scheduledPrefix scheduledPrefix

/-- The exact store evaluated by a compatible query is either a completed
execution boundary or a strict delayed scheduled prefix. -/
theorem ScheduledQueryPrefixCompatibility.queryStore_class
    {E : Execution Root}
    {runtime : Runtime Root} {actions : List (Action Root)}
    {position : ℕ} {before after : Runtime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : ScheduledQueryPrefixCompatibility cfg ext E runtime actions position
      before after querySecond scheduledPrefix) :
    E.ScheduledPrefixStoreClass cfg ext before.fcrStore.store := by
  rw [h.store_eq]
  exact scheduledPrefix.store_class cfg ext

/-- The compatible query store's whole-second clock is the named execution
second. -/
theorem ScheduledQueryPrefixCompatibility.queryStore_current_slot
    {E : Execution Root}
    {runtime : Runtime Root} {actions : List (Action Root)}
    {position : ℕ} {before after : Runtime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : ScheduledQueryPrefixCompatibility cfg ext E runtime actions position
      before after querySecond scheduledPrefix) :
    get_current_slot cfg before.fcrStore.store = E.slot_at cfg querySecond := by
  rw [h.store_eq, scheduledPrefix.current_slot cfg ext,
    h.scheduled_second]

/-- The runtime wall slot agrees with the scheduled execution second.  This
uses the explicit clock-simulation field; accepted extra queries do not check
clock alignment themselves. -/
theorem ScheduledQueryPrefixCompatibility.query_wall_slot
    {E : Execution Root}
    {runtime : Runtime Root} {actions : List (Action Root)}
    {position : ℕ} {before after : Runtime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : ScheduledQueryPrefixCompatibility cfg ext E runtime actions position
      before after querySecond scheduledPrefix) :
    wallSlot cfg before.elapsedMs = E.slot_at cfg querySecond := by
  rw [← h.clock_aligned]
  exact h.queryStore_current_slot cfg ext

/-- The accepted query inherits all safety-free scheduled-prefix trajectory
facts at its exact pre-query store. -/
theorem ScheduledQueryPrefixCompatibility.operationalEvidence
    {E : Execution Root}
    {runtime : Runtime Root} {actions : List (Action Root)}
    {position : ℕ} {before after : Runtime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : ScheduledQueryPrefixCompatibility cfg ext E runtime actions position
      before after querySecond scheduledPrefix)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext) :
    E.ScheduledPrefixOperationalEvidence cfg ext before.fcrStore.store
      querySecond := by
  have hp := ScheduledEventPrefix.operationalEvidence cfg ext E hT
    scheduledPrefix
  rwa [← h.store_eq, h.scheduled_second] at hp

end AllowedFCRCalls

namespace Execution

variable (E : Execution Root)

/-! ## Exact residual for the query-store base evidence -/

/-- Facts not supplied merely by replaying the scheduled fork-choice prefix.

The result block, parent, and `is_one_confirmed` facts come from the concrete
selector/query consumer.  Balance-source coherence depends on the FCR cache's
operational origin, which `Store` does not retain.  The supporter walk is the
remaining arbitrary-prefix domain adapter.  The final two inequalities are
the current accounting theorems' execution-boundary restriction.  None of
these fields asserts the resulting base strip itself. -/
structure QueryStoreBaseStripTraceResidual
    (queryStore : Store Root) (bs : BeaconState Root)
    (b : Root) (lo es : Slot) (querySecond : ℕ) : Prop where
  query_horizon : E.WithinHorizon cfg querySecond
  block_known : b ∈ queryStore.block_roots
  parent_known : (queryStore.blocks b).parent_root ∈ queryStore.block_roots
  lo_eq : lo = (queryStore.blocks (queryStore.blocks b).parent_root).slot + 1
  cutoff_eq : es = get_current_slot cfg queryStore - 1
  balance_validators : bs.validators = E.registry
  total_active : get_total_active_balance cfg bs = E.total_active cfg
  supporter_walk : ∀ i ∈ AttSupporters cfg queryStore
      (get_node_for_root b) bs, ∀ lm,
    queryStore.latest_messages i = some lm →
      WalkKnown queryStore (queryStore.blocks b).slot lm.root
  confirmation : is_one_confirmed cfg ext queryStore bs b = true
  byzantine_support_le_adversarial :
    (((AttSupporters cfg queryStore (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      get_adversarial_weight cfg ext queryStore bs b
  support_discount_le_parent_stuck :
    get_support_discount cfg ext queryStore bs b ≤
      E.weight (ParentStuck cfg E queryStore bs b)

/-- Mechanical scheduled-prefix facts plus the exact residual fields assemble
the existing query-store base-evidence interface. -/
theorem ScheduledPrefixOperationalEvidence.toQueryStoreBaseStripEvidence
    {queryStore : Store Root} {bs : BeaconState Root}
    {b : Root} {lo es : Slot} {querySecond : ℕ}
    (hop : E.ScheduledPrefixOperationalEvidence cfg ext queryStore querySecond)
    (hres : E.QueryStoreBaseStripTraceResidual cfg ext queryStore bs b lo es
      querySecond) :
    E.QueryStoreBaseStripEvidence cfg ext queryStore bs b lo es := by
  have hblockCurrent : (queryStore.blocks b).slot ≤
      get_current_slot cfg queryStore :=
    hop.blocks_slot_le_current b hres.block_known
  have hblockH : E.SlotWithinHorizon cfg (queryStore.blocks b).slot := by
    apply E.slotWithinHorizon_of_le cfg
    · rw [hop.current_slot] at hblockCurrent
      exact hblockCurrent
    · exact hres.query_horizon
  have hloBlock : lo ≤ (queryStore.blocks b).slot := by
    rw [hres.lo_eq]
    exact Nat.succ_le_of_lt
      (hop.parent_slot_lt b hres.block_known hres.parent_known)
  have hloH : E.SlotWithinHorizon cfg lo := by
    exact E.slotWithinHorizon_mono cfg hloBlock hblockH
  have hesCurrent : es ≤ get_current_slot cfg queryStore := by
    rw [hres.cutoff_eq]
    exact Nat.sub_le _ _
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_of_le cfg
    · rw [hop.current_slot] at hesCurrent
      exact hesCurrent
    · exact hres.query_horizon
  exact
    { block_known := hres.block_known
      parent_known := hres.parent_known
      parent_slot_lt := hop.parent_slot_lt
      block_slot_le_current := hblockCurrent
      block_horizon := hblockH
      lo_horizon := hloH
      es_horizon := hesH
      lo_eq := hres.lo_eq
      cutoff_eq := hres.cutoff_eq
      balance_validators := hres.balance_validators
      total_active := hres.total_active
      scheduled_provenance := hop.scheduled_provenance
      latest_message_provenance := hop.latest_message_provenance
      supporter_walk := hres.supporter_walk
      confirmation := hres.confirmation
      byzantine_support_le_adversarial :=
        hres.byzantine_support_le_adversarial
      support_discount_le_parent_stuck :=
        hres.support_discount_le_parent_stuck }

end Execution

namespace AllowedFCRCalls

open Execution

/-- A real accepted legal query consumes the simulation adapter: trajectory
facts are derived at its exact `before` store and only the classified residual
is supplied to construct `QueryStoreBaseStripEvidence`. -/
theorem ScheduledQueryPrefixCompatibility.queryStoreBaseStripEvidence
    {E : Execution Root}
    {runtime : Runtime Root} {actions : List (Action Root)}
    {position : ℕ} {before after : Runtime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : ScheduledQueryPrefixCompatibility cfg ext E runtime actions position
      before after querySecond scheduledPrefix)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {bs : BeaconState Root} {b : Root} {lo es : Slot}
    (hres : E.QueryStoreBaseStripTraceResidual cfg ext before.fcrStore.store bs
      b lo es querySecond) :
    E.QueryStoreBaseStripEvidence cfg ext before.fcrStore.store bs b lo es :=
  ScheduledPrefixOperationalEvidence.toQueryStoreBaseStripEvidence cfg ext E
    (h.operationalEvidence cfg ext hT) hres

/-! ## Global cast materialization and exact pre-query order -/

/-- Every cast already recorded in a global runtime has a position strictly
below the runtime's next position.  Initial runtimes supplied by an external
trace adapter must establish this once; `globalRun?` preserves it. -/
def CastPositionsBeforeNext (runtime : GlobalRuntime Root) : Prop :=
  ∀ cast ∈ runtime.voteCasts,
    cast.actionPosition < runtime.nextGlobalActionPosition

/-- The genuinely erased low-to-high fact: a relevant ground vote cast before
`querySecond` is either already represented in the initial cast log or its
matching cast action occurs in the exact action-list prefix before the query.

No target agreement is included, and no final-runtime membership or action
position inequality is assumed. -/
def PreQueryVoteActionMaterialization
    (E : Execution Root) (runtime : GlobalRuntime Root)
    (actions : List (GlobalAction Root))
    (position querySecond : ℕ) : Prop :=
  ∀ validator ∈ E.honest, ∀ slot : Slot, E.SlotWithinHorizon cfg slot →
    ∀ castSecond attestation,
      E.vote validator slot = some (castSecond, attestation) →
      castSecond < querySecond →
      (∃ cast ∈ runtime.voteCasts,
        cast.validator = validator ∧ cast.slot = slot ∧
          cast.executionSecond = castSecond) ∨
      GlobalAction.honestVoteCast validator slot castSecond ∈
        actions.take position

/-- Every node runtime in a global interleaving has an exact whole-second
store/millisecond relation. -/
def GlobalWholeSecondAligned (runtime : GlobalRuntime Root) : Prop :=
  ∀ actor, WholeSecondAligned (runtime.nodeState actor)

/-- One accepted global action preserves whole-second alignment at every
node.  A node action uses the local preservation theorem after re-seating only
its action counter; a cast action does not modify any node state. -/
theorem globalWholeSecondAligned_step
    {runtime after : GlobalRuntime Root} {action : GlobalAction Root}
    (haligned : GlobalWholeSecondAligned runtime)
    (hstep : globalStep? cfg ext runtime action = some after) :
    GlobalWholeSecondAligned after := by
  cases action with
  | nodeAction actor nodeAction =>
      cases hlocal : step? cfg ext
          { runtime.nodeState actor with
            nextActionPosition := runtime.nextGlobalActionPosition }
          nodeAction with
      | none =>
          simp only [globalStep?, hlocal] at hstep
          cases hstep
      | some next =>
          simp only [globalStep?, hlocal] at hstep
          cases hstep
          intro queriedActor
          change WholeSecondAligned
            (Function.update runtime.nodeState actor next queriedActor)
          by_cases hactor : queriedActor = actor
          · subst queriedActor
            rw [Function.update_self]
            apply wholeSecondAligned_step cfg ext _ hlocal
            simpa only [WholeSecondAligned] using haligned actor
          · simpa only [Function.update, hactor, ↓reduceIte] using
              haligned queriedActor
  | honestVoteCast validator slot executionSecond =>
      simp only [globalStep?] at hstep
      cases hstep
      exact haligned

/-- Every accepted global action prefix preserves the all-node whole-second
invariant. -/
theorem globalWholeSecondAligned_run
    {runtime after : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    (haligned : GlobalWholeSecondAligned runtime)
    (hrun : globalRun? cfg ext runtime actions = some after) :
    GlobalWholeSecondAligned after := by
  induction actions generalizing runtime with
  | nil =>
      simp only [globalRun?] at hrun
      cases hrun
      exact haligned
  | cons action actions ih =>
      simp only [globalRun?] at hrun
      cases hstep : globalStep? cfg ext runtime action with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          exact ih (globalWholeSecondAligned_step cfg ext haligned hstep) hrun

/-- Operational identification of the actual node query with one execution
second.  The action equality ties `actor` to the query projected by the global
snapshot.  Store time is aligned exactly, rather than merely by slot: several
execution seconds can inhabit one slot.  Genesis-time and runtime clock
alignment then derive the absolute elapsed second, its relative execution
second after subtracting the checkpoint-start offset, and both slot
agreements mechanically.
-/
def GlobalQueryMomentAlignment
    (E : Execution Root) (actions : List (GlobalAction Root))
    (position : ℕ) (before : GlobalRuntime Root) (querySecond : ℕ) : Prop :=
  ∃ actor kind,
    actions.getD position (.honestVoteCast 0 0 0) =
        .nodeAction actor (.query kind) ∧
      (before.nodeState actor).fcrStore.store.time = E.time_at querySecond ∧
      (before.nodeState actor).fcrStore.store.genesis_time =
        E.genesis_store.genesis_time ∧
      E.genesis_store.genesis_time ≤ E.genesis_store.time ∧
      clockAligned cfg (before.nodeState actor)

omit [LinearOrder Root] [Inhabited Root] in
/-- The queried node's store and millisecond wall clocks are the slot of the
exactly aligned execution second. -/
theorem GlobalQueryMomentAlignment.clock_agreement
    {E : Execution Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before : GlobalRuntime Root} {querySecond : ℕ}
    (h : GlobalQueryMomentAlignment cfg E actions position before querySecond)
    (hwhole : GlobalWholeSecondAligned before) :
    ∃ actor kind,
      actions.getD position (.honestVoteCast 0 0 0) =
          .nodeAction actor (.query kind) ∧
        (before.nodeState actor).elapsedMs / 1000 =
            executionInitialElapsedSecond E + querySecond ∧
        (before.nodeState actor).elapsedMs / 1000 -
            executionInitialElapsedSecond E = querySecond ∧
        get_current_slot cfg (before.nodeState actor).fcrStore.store =
          E.slot_at cfg querySecond ∧
        wallSlot cfg (before.nodeState actor).elapsedMs =
          E.slot_at cfg querySecond := by
  obtain ⟨actor, kind, haction, htime, hgenesis, hstart, hclock⟩ := h
  have hsecond := hwhole actor
  rw [WholeSecondAligned, htime, hgenesis, Execution.time_at]
    at hsecond
  have habsolute : (before.nodeState actor).elapsedMs / 1000 =
      executionInitialElapsedSecond E + querySecond := by
    rw [executionInitialElapsedSecond]
    omega
  have hrelative : (before.nodeState actor).elapsedMs / 1000 -
      executionInitialElapsedSecond E = querySecond := by
    rw [habsolute]
    omega
  have hstore :
      get_current_slot cfg (before.nodeState actor).fcrStore.store =
        E.slot_at cfg querySecond := by
    rw [get_current_slot, get_slots_since_genesis, htime, hgenesis,
      Execution.slot_at]
  exact ⟨actor, kind, haction, habsolute, hrelative, hstore,
    hclock.symm.trans hstore⟩

/-- Execution compatibility for an actual accepted global query.  The
snapshot supplies legality and the exact `before` runtime.  `query_moment`
ties the named execution second to the actor/action and exact operational
clock evaluated there.  The remaining fields carry the initial all-node
whole-second invariant, initial-position invariant, and ground-vote
materialization fact erased by the high execution model. -/
structure GlobalQueryActionCompatibility
    (E : Execution Root)
    (runtime : GlobalRuntime Root) (actions : List (GlobalAction Root))
    (position : ℕ) (before after : GlobalRuntime Root)
    (querySecond : ℕ) : Prop where
  snapshot : GlobalQuerySnapshot cfg ext runtime actions position before after
  query_moment : GlobalQueryMomentAlignment cfg E actions position before
    querySecond
  initial_whole_seconds : GlobalWholeSecondAligned runtime
  initial_positions : CastPositionsBeforeNext runtime
  prequery_materialization : PreQueryVoteActionMaterialization cfg E runtime
    actions position querySecond

/-- Recover the actual query actor/action, absolute and relative elapsed
seconds, and both slot equalities from the combined compatibility object. -/
theorem GlobalQueryActionCompatibility.clock_agreement
    {E : Execution Root}
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    (h : GlobalQueryActionCompatibility cfg ext E runtime actions position
      before after querySecond) :
    ∃ actor kind,
      actions.getD position (.honestVoteCast 0 0 0) =
          .nodeAction actor (.query kind) ∧
        (before.nodeState actor).elapsedMs / 1000 =
            executionInitialElapsedSecond E + querySecond ∧
        (before.nodeState actor).elapsedMs / 1000 -
            executionInitialElapsedSecond E = querySecond ∧
        get_current_slot cfg (before.nodeState actor).fcrStore.store =
          E.slot_at cfg querySecond ∧
        wallSlot cfg (before.nodeState actor).elapsedMs =
          E.slot_at cfg querySecond :=
  h.query_moment.clock_agreement cfg
    (globalWholeSecondAligned_run cfg ext h.initial_whole_seconds
      h.snapshot.prefixRun)

/-- Specialize relative exact-second alignment to any actor/kind proof for the
query action.  The checkpoint-start elapsed offset is subtracted before this
second is compared with relative `Execution.vote` cast seconds.  Constructor
injectivity identifies the action with the actor extracted from
`query_moment`. -/
theorem GlobalQueryActionCompatibility.query_elapsed_second
    {E : Execution Root}
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    (h : GlobalQueryActionCompatibility cfg ext E runtime actions position
      before after querySecond)
    (actor : ValidatorIndex) (kind : QueryKind)
    (haction : actions.getD position (.honestVoteCast 0 0 0) =
      .nodeAction actor (.query kind)) :
    (before.nodeState actor).elapsedMs / 1000 -
      executionInitialElapsedSecond E = querySecond := by
  obtain ⟨actualActor, actualKind, hactual, _habsolute, hrelative,
      _hstore, _hwall⟩ :=
    h.clock_agreement cfg ext
  have heq : GlobalAction.nodeAction actor (.query kind) =
      .nodeAction actualActor (.query actualKind) :=
    haction.symm.trans hactual
  cases heq
  exact hrelative

/-! ## One global query tied to one exact scheduled prefix -/

/-- Combined operational compatibility for the actual global query actor.
The global half supplies accepted action order and exact-second coherence;
the scheduled half explicitly identifies that actor's pre-query store with
one execution schedule prefix.  `query_store_eq` is a simulation premise and
is not derived from `LegalTrace`/`GlobalQuerySnapshot`. -/
structure GlobalScheduledQueryPrefixCompatibility
    (E : Execution Root)
    (runtime : GlobalRuntime Root) (actions : List (GlobalAction Root))
    (position : ℕ) (before after : GlobalRuntime Root)
    (querySecond : ℕ) (scheduledPrefix : E.ScheduledEventPrefix) : Prop where
  action_compatibility : GlobalQueryActionCompatibility cfg ext E runtime
    actions position before after querySecond
  scheduled_second : scheduledPrefix.previousSecond + 1 = querySecond
  query_store_eq : ∀ actor kind,
    actions.getD position (.honestVoteCast 0 0 0) =
        .nodeAction actor (.query kind) →
      (before.nodeState actor).fcrStore.store =
        scheduledPrefix.store cfg ext

/-- The exact store read by the named global query actor is causal. -/
theorem GlobalScheduledQueryPrefixCompatibility.queryStore_causal
    {E : Execution Root}
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : GlobalScheduledQueryPrefixCompatibility cfg ext E runtime actions
      position before after querySecond scheduledPrefix)
    (actor : ValidatorIndex) (kind : QueryKind)
    (haction : actions.getD position (.honestVoteCast 0 0 0) =
      .nodeAction actor (.query kind)) :
    E.CausalStore cfg ext (before.nodeState actor).fcrStore.store := by
  rw [h.query_store_eq actor kind haction]
  exact .scheduledPrefix scheduledPrefix

/-- Safety-free scheduled-prefix trajectory facts at the exact global query
actor's store. -/
theorem GlobalScheduledQueryPrefixCompatibility.operationalEvidence
    {E : Execution Root}
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : GlobalScheduledQueryPrefixCompatibility cfg ext E runtime actions
      position before after querySecond scheduledPrefix)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (actor : ValidatorIndex) (kind : QueryKind)
    (haction : actions.getD position (.honestVoteCast 0 0 0) =
      .nodeAction actor (.query kind)) :
    E.ScheduledPrefixOperationalEvidence cfg ext
      (before.nodeState actor).fcrStore.store querySecond := by
  have hp := ScheduledEventPrefix.operationalEvidence cfg ext E hT
    scheduledPrefix
  rwa [← h.query_store_eq actor kind haction, h.scheduled_second] at hp

/-- The combined global/scheduled adapter feeds the existing query-store base
interface with only the previously classified residual fields. -/
theorem GlobalScheduledQueryPrefixCompatibility.queryStoreBaseStripEvidence
    {E : Execution Root}
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    {scheduledPrefix : E.ScheduledEventPrefix}
    (h : GlobalScheduledQueryPrefixCompatibility cfg ext E runtime actions
      position before after querySecond scheduledPrefix)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (actor : ValidatorIndex) (kind : QueryKind)
    (haction : actions.getD position (.honestVoteCast 0 0 0) =
      .nodeAction actor (.query kind))
    {bs : BeaconState Root} {b : Root} {lo es : Slot}
    (hres : E.QueryStoreBaseStripTraceResidual cfg ext
      (before.nodeState actor).fcrStore.store bs b lo es querySecond) :
    E.QueryStoreBaseStripEvidence cfg ext
      (before.nodeState actor).fcrStore.store bs b lo es :=
  ScheduledPrefixOperationalEvidence.toQueryStoreBaseStripEvidence cfg ext E
    (h.operationalEvidence cfg ext hT actor kind haction) hres

/-- A global step never removes a recorded cast. -/
theorem globalStep_voteCasts_subset
    {runtime after : GlobalRuntime Root} {action : GlobalAction Root}
    (hstep : globalStep? cfg ext runtime action = some after) :
    runtime.voteCasts ⊆ after.voteCasts := by
  cases action with
  | nodeAction actor nodeAction =>
      cases hlocal : step? cfg ext
          { runtime.nodeState actor with
            nextActionPosition := runtime.nextGlobalActionPosition }
          nodeAction with
      | none =>
          simp only [globalStep?, hlocal] at hstep
          cases hstep
      | some next =>
          simp only [globalStep?, hlocal] at hstep
          cases hstep
          exact fun _ hmem => hmem
  | honestVoteCast validator slot executionSecond =>
      simp only [globalStep?] at hstep
      cases hstep
      intro cast hmem
      exact List.mem_append_left _ hmem

/-- A global run never removes a cast present in its initial runtime. -/
theorem globalRun_voteCasts_subset
    {runtime after : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    (hrun : globalRun? cfg ext runtime actions = some after) :
    runtime.voteCasts ⊆ after.voteCasts := by
  induction actions generalizing runtime with
  | nil =>
      simp only [globalRun?] at hrun
      cases hrun
      exact fun _ hmem => hmem
  | cons action actions ih =>
      simp only [globalRun?] at hrun
      cases hstep : globalStep? cfg ext runtime action with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          exact (globalStep_voteCasts_subset cfg ext hstep).trans (ih hrun)

/-- The strict-position invariant is preserved by one global step. -/
theorem castPositionsBeforeNext_globalStep
    {runtime after : GlobalRuntime Root} {action : GlobalAction Root}
    (hpositions : CastPositionsBeforeNext runtime)
    (hstep : globalStep? cfg ext runtime action = some after) :
    CastPositionsBeforeNext after := by
  cases action with
  | nodeAction actor nodeAction =>
      cases hlocal : step? cfg ext
          { runtime.nodeState actor with
            nextActionPosition := runtime.nextGlobalActionPosition }
          nodeAction with
      | none =>
          simp only [globalStep?, hlocal] at hstep
          cases hstep
      | some next =>
          simp only [globalStep?, hlocal] at hstep
          cases hstep
          intro cast hmem
          exact (hpositions cast hmem).trans (Nat.lt_succ_self _)
  | honestVoteCast validator slot executionSecond =>
      simp only [globalStep?] at hstep
      cases hstep
      intro cast hmem
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hprevious | hnew
      · exact (hpositions cast hprevious).trans (Nat.lt_succ_self _)
      · subst cast
        exact Nat.lt_succ_self _

/-- The strict-position invariant is preserved by an interpreted prefix. -/
theorem castPositionsBeforeNext_globalRun
    {runtime after : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    (hpositions : CastPositionsBeforeNext runtime)
    (hrun : globalRun? cfg ext runtime actions = some after) :
    CastPositionsBeforeNext after := by
  induction actions generalizing runtime with
  | nil =>
      simp only [globalRun?] at hrun
      cases hrun
      exact hpositions
  | cons action actions ih =>
      simp only [globalRun?] at hrun
      cases hstep : globalStep? cfg ext runtime action with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          exact ih (castPositionsBeforeNext_globalStep cfg ext hpositions hstep)
            hrun

/-- Executing a cast action records the matching cast observation. -/
theorem globalStep_honestVoteCast_mem
    (runtime after : GlobalRuntime Root)
    (validator : ValidatorIndex) (slot : Slot) (executionSecond : ℕ)
    (hstep : globalStep? cfg ext runtime
      (.honestVoteCast validator slot executionSecond) = some after) :
    ∃ cast ∈ after.voteCasts,
      cast.validator = validator ∧ cast.slot = slot ∧
        cast.executionSecond = executionSecond := by
  simp only [globalStep?] at hstep
  cases hstep
  let cast : VoteCastObservation :=
    { validator := validator
      slot := slot
      executionSecond := executionSecond
      actionPosition := runtime.nextGlobalActionPosition }
  exact ⟨cast, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl,
    rfl⟩

/-- A matching cast action anywhere in an interpreted list is materialized in
the resulting runtime. -/
theorem globalRun_voteCast_of_mem
    {runtime after : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {validator : ValidatorIndex} {slot : Slot} {executionSecond : ℕ}
    (hrun : globalRun? cfg ext runtime actions = some after)
    (hmem : GlobalAction.honestVoteCast validator slot executionSecond ∈
      actions) :
    ∃ cast ∈ after.voteCasts,
      cast.validator = validator ∧ cast.slot = slot ∧
        cast.executionSecond = executionSecond := by
  induction actions generalizing runtime with
  | nil => simp at hmem
  | cons action actions ih =>
      simp only [globalRun?] at hrun
      cases hstep : globalStep? cfg ext runtime action with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst action
            obtain ⟨cast, hcast, hvalidator, hslot, hsecond⟩ :=
              globalStep_honestVoteCast_mem cfg ext runtime next validator slot
                executionSecond hstep
            exact ⟨cast, globalRun_voteCasts_subset cfg ext hrun hcast,
              hvalidator, hslot, hsecond⟩
          · exact ih hrun htail

/-- The action-list materialization relation plus an accepted global query
derives the production `PreexistingVoteActionCoverage`: every relevant ground
vote has a matching cast in the exact pre-query runtime, and its recorded
global action position is strictly before the query's next action position.
-/
theorem GlobalQueryActionCompatibility.preexistingVoteActionCoverage
    {E : Execution Root}
    {runtime : GlobalRuntime Root} {actions : List (GlobalAction Root)}
    {position : ℕ} {before after : GlobalRuntime Root} {querySecond : ℕ}
    (h : GlobalQueryActionCompatibility cfg ext E runtime actions position
      before after querySecond) :
    CausalQueryEvidence.PreexistingVoteActionCoverage cfg E before
      before.nextGlobalActionPosition querySecond := by
  have hpositions : CastPositionsBeforeNext before :=
    castPositionsBeforeNext_globalRun cfg ext h.initial_positions
      h.snapshot.prefixRun
  have hinitial : runtime.voteCasts ⊆ before.voteCasts :=
    globalRun_voteCasts_subset cfg ext h.snapshot.prefixRun
  intro validator hhonest slot hslotH castSecond attestation hvote hcastSecond
  rcases h.prequery_materialization validator hhonest slot hslotH castSecond
      attestation hvote hcastSecond with hinitialCast | hprefixCast
  · obtain ⟨cast, hcast, hvalidator, hslot, hsecond⟩ := hinitialCast
    have hcastBefore := hinitial hcast
    exact ⟨cast, hcastBefore, hvalidator, hslot, hsecond,
      hpositions cast hcastBefore⟩
  · obtain ⟨cast, hcast, hvalidator, hslot, hsecond⟩ :=
      globalRun_voteCast_of_mem cfg ext h.snapshot.prefixRun hprefixCast
    exact ⟨cast, hcast, hvalidator, hslot, hsecond,
      hpositions cast hcast⟩

end AllowedFCRCalls
end FastConfirmation.Spec
