import FastConfirmation.Spec.Proof.FCRCallContracts

/-!
# Allowed fast-confirmation call traces

The executable `Execution.fcr` recurrence chooses one legal implementation
schedule: update the cached variables at the first whole second of a slot and
immediately write back `get_latest_confirmed`.  The pinned source permits the
update to happen later (but before the attestation deadline) and permits extra
pure queries during the slot.

This module is deliberately below all safety and canonicality developments.
It gives an ordered action trace and an executable small-step interpreter.  A
query snapshot is *derived* from a successfully interpreted trace prefix; it
is not an assumption record into which downstream safety premises can be put.

An action-list index is relative to the supplied list.  The runtime's
`nextActionPosition`/`nextGlobalActionPosition` is the absolute counter, and
query observations record that counter.  The two coincide only when the
initial counter is zero.  In either case, list order gives two actions at the
same millisecond a definite order; this is the missing distinction in the
second-bucket `Execution.store` model.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace AllowedFCRCalls

/-! ## Trace vocabulary -/

/-- Startup is explicit.  Normal initialization does not itself execute
`update_fast_confirmation_variables`, so a fresh implementation must update
the initial slot.  An adapter attaching after that slot's deadline may mark
only that first, partial slot exempt; public guarantees must then start with
the next non-exempt slot. -/
inductive StartupMode where
  | updateInitialSlot
  | exemptInitialPartialSlot
deriving DecidableEq

/-- A queued wire event.  The optional slot tag is operational evidence from
the implementation adapter that a block came from the expected proposer for
that slot.  `SignedBeaconBlock` deliberately projects away proposer identity,
so the low FCR model can check that the event is a block for the tagged slot
and that `on_block` accepts it, while the adapter must discharge identity.
-/
structure QueuedEvent (Root : Type*) where
  event : Event Root
  expectedProposerFor : Option Slot := none

/-- The mandatory query is the query immediately following the unique cached
variable update.  Extra queries implement the source's permission to call
`get_latest_confirmed` at any other point in the slot. -/
inductive QueryKind where
  | mandatory
  | extra
deriving DecidableEq

/-- Write-back is not left implicit.  The mandatory handler query writes the
protocol `confirmed_root`; an extra direct call to the pure
`get_latest_confirmed` function exposes its result without changing that
field. -/
inductive QueryWriteBack where
  | confirmedRoot
  | exposeOnly
deriving DecidableEq

/-- Ordered scheduler actions.  `elapseTo` uses milliseconds since genesis;
the fork-choice store's second clock is ticked to the containing whole second.
List order resolves all actions sharing a millisecond. -/
inductive Action (Root : Type*) where
  | elapseTo (elapsedMs : ℕ)
  | receive (event : QueuedEvent Root)
  | processNext
  | updateVariables
  | query (kind : QueryKind)

/-- An exact query observation produced by the interpreter. -/
structure QueryObservation (Root : Type*) where
  actionPosition : ℕ
  elapsedMs : ℕ
  slot : Slot
  kind : QueryKind
  inputConfirmedRoot : Root
  result : Root
  writeBack : QueryWriteBack

/-- Interpreter state.  `awaitingMandatoryQuery` enforces immediate adjacency:
while it is true, no time, event, update, or extra-query action is accepted.
-/
structure Runtime (Root : Type*) where
  fcrStore : FastConfirmationStore Root
  pending : List (QueuedEvent Root)
  elapsedMs : ℕ
  nextActionPosition : ℕ
  initialSlot : Slot
  startupMode : StartupMode
  updatedSlots : Finset Slot
  expectedProposerProcessed : Finset Slot
  awaitingMandatoryQuery : Bool
  observations : List (QueryObservation Root)

/-- Millisecond-level slot, measured from genesis. -/
def wallSlot (elapsedMs : ℕ) : Slot :=
  GENESIS_SLOT + elapsedMs / cfg.slot_duration_ms

/-- Milliseconds elapsed in the current slot. -/
def slotPhaseMs (elapsedMs : ℕ) : ℕ :=
  elapsedMs % cfg.slot_duration_ms

/-- The millisecond position represented by a fork-choice store's whole-second
clock. -/
def storeElapsedMs (store : Store Root) : ℕ :=
  seconds_to_milliseconds (store.time - store.genesis_time)

/-- Initialize trace execution from an already constructed FCR store.
Initialization does not silently consume the initial slot's update. -/
def initRuntime (fcrStore : FastConfirmationStore Root) (mode : StartupMode) :
    Runtime Root :=
  let elapsedMs := storeElapsedMs fcrStore.store
  { fcrStore := fcrStore
    pending := []
    elapsedMs := elapsedMs
    nextActionPosition := 0
    initialSlot := wallSlot cfg elapsedMs
    startupMode := mode
    updatedSlots := ∅
    expectedProposerProcessed := ∅
    awaitingMandatoryQuery := false
    observations := [] }

/-- Only the explicitly partial initial slot may be exempt. -/
def updateRequiredIn (runtime : Runtime Root) (slot : Slot) : Bool :=
  decide ¬(runtime.startupMode = .exemptInitialPartialSlot ∧ slot = runtime.initialSlot)

/-- Every required slot completed by a clock jump has already had its unique
update.  This supplies the "at least once" half of once-per-slot; membership in
`updatedSlots` supplies the "at most once" half. -/
def completedSlotsUpdated (runtime : Runtime Root) (newSlot : Slot) : Bool :=
  decide (∀ slot ∈ Finset.Ico (wallSlot cfg runtime.elapsedMs) newSlot,
    updateRequiredIn runtime slot = true → slot ∈ runtime.updatedSlots)

/-- Is this a still-pending attestation from a slot before `currentSlot`? -/
def pendingPastAttestation (currentSlot : Slot) (queued : QueuedEvent Root) : Bool :=
  match queued.event with
  | .attestation attestation _ => decide (attestation.data.slot < currentSlot)
  | _ => false

/-- The source's "past-slot attestations have been applied" condition is
represented operationally: none remains in the received-event queue. -/
def pastAttestationsApplied (runtime : Runtime Root) (currentSlot : Slot) : Bool :=
  !(runtime.pending.any (pendingPastAttestation currentSlot))

/-- Whole-second `Store.time` and the millisecond trace name the same slot.
An adapter from `Execution.store` proves this using the configured
whole-second slot alignment; it is an operational clock fact, not a safety
premise. -/
def clockAligned (runtime : Runtime Root) : Prop :=
  get_current_slot cfg runtime.fcrStore.store = wallSlot cfg runtime.elapsedMs

/-- Observable evidence that the optional expected-proposer wait occurred. -/
def WaitedForExpectedProposer (runtime : Runtime Root) (slot : Slot) : Prop :=
  slot ∈ runtime.expectedProposerProcessed

/-- Pure operational guard for the unique cached-variable update.  It contains
no ancestry, canonicality, source, filter, takeover, or future-head premise. -/
def canUpdate (runtime : Runtime Root) : Bool :=
  let currentSlot := wallSlot cfg runtime.elapsedMs
  !runtime.awaitingMandatoryQuery &&
    decide (get_current_slot cfg runtime.fcrStore.store = currentSlot) &&
    decide (currentSlot ∉ runtime.updatedSlots) &&
    decide (0 < get_attestation_due_ms cfg) &&
    decide (slotPhaseMs cfg runtime.elapsedMs < get_attestation_due_ms cfg) &&
    pastAttestationsApplied runtime currentSlot

private def bump (runtime : Runtime Root) : Runtime Root :=
  { runtime with nextActionPosition := runtime.nextActionPosition + 1 }

private def reseatStore (runtime : Runtime Root) (store : Store Root) : Runtime Root :=
  { runtime with fcrStore := { runtime.fcrStore with store := store } }

private def setElapsed (runtime : Runtime Root) (elapsedMs : ℕ) : Runtime Root :=
  { runtime with elapsedMs := elapsedMs }

/-- Execute one scheduler action.  `none` means that the proposed action order
violates the source call discipline (or that an expected-proposer-tagged block
was rejected by `on_block`). -/
def step? (runtime : Runtime Root) : Action Root → Option (Runtime Root)
  | .elapseTo elapsedMs =>
      if runtime.awaitingMandatoryQuery then none
      else if runtime.elapsedMs ≤ elapsedMs then
        let newSlot := wallSlot cfg elapsedMs
        if completedSlotsUpdated (cfg := cfg) runtime newSlot then
          let tickTime := runtime.fcrStore.store.genesis_time + elapsedMs / 1000
          let ticked := on_tick cfg runtime.fcrStore.store tickTime
          some (bump (setElapsed (reseatStore runtime ticked) elapsedMs))
        else none
      else none
  | .receive queued =>
      if runtime.awaitingMandatoryQuery then none
      else some (bump { runtime with pending := runtime.pending ++ [queued] })
  | .processNext =>
      if runtime.awaitingMandatoryQuery then none
      else
        match runtime.pending with
        | [] => none
        | queued :: rest =>
            let applied := apply_event cfg ext runtime.fcrStore.store queued.event
            match queued.expectedProposerFor with
            | none =>
                let nextStore := applied.getD runtime.fcrStore.store
                some (bump {
                  reseatStore runtime nextStore with pending := rest })
            | some slot =>
                match queued.event, applied with
                | .block block, some nextStore =>
                    if slot = wallSlot cfg runtime.elapsedMs ∧ block.message.slot = slot then
                      some (bump {
                        reseatStore runtime nextStore with
                          pending := rest
                          expectedProposerProcessed :=
                            insert slot runtime.expectedProposerProcessed })
                    else none
                | _, _ => none
  | .updateVariables =>
      if canUpdate cfg runtime then
        let currentSlot := wallSlot cfg runtime.elapsedMs
        let updated := update_fast_confirmation_variables cfg runtime.fcrStore
        some (bump {
          runtime with
            fcrStore := updated
            updatedSlots := insert currentSlot runtime.updatedSlots
            awaitingMandatoryQuery := true })
      else none
  | .query .mandatory =>
      if runtime.awaitingMandatoryQuery then
        let input := runtime.fcrStore.confirmed_root
        let result := get_latest_confirmed cfg ext runtime.fcrStore
        let observation : QueryObservation Root :=
          { actionPosition := runtime.nextActionPosition
            elapsedMs := runtime.elapsedMs
            slot := wallSlot cfg runtime.elapsedMs
            kind := .mandatory
            inputConfirmedRoot := input
            result := result
            writeBack := .confirmedRoot }
        some (bump {
          runtime with
            fcrStore := { runtime.fcrStore with confirmed_root := result }
            awaitingMandatoryQuery := false
            observations := runtime.observations ++ [observation] })
      else none
  | .query .extra =>
      if runtime.awaitingMandatoryQuery then none
      else
        let input := runtime.fcrStore.confirmed_root
        let result := get_latest_confirmed cfg ext runtime.fcrStore
        let observation : QueryObservation Root :=
          { actionPosition := runtime.nextActionPosition
            elapsedMs := runtime.elapsedMs
            slot := wallSlot cfg runtime.elapsedMs
            kind := .extra
            inputConfirmedRoot := input
            result := result
            writeBack := .exposeOnly }
        some (bump {
          runtime with observations := runtime.observations ++ [observation] })
/-- Interpret an ordered action list. -/
def run? (runtime : Runtime Root) : List (Action Root) → Option (Runtime Root)
  | [] => some runtime
  | action :: rest => do
      let next ← step? cfg ext runtime action
      run? next rest

/-- A legal trace is exactly one accepted by the operational interpreter. -/
def LegalTrace (runtime : Runtime Root) (actions : List (Action Root)) : Prop :=
  (run? cfg ext runtime actions).isSome

/-! ## Derived exact query snapshots -/

/-- Query snapshots are projections of accepted prefixes, never free-standing
assumption bundles.  `before` is the exact state whose store and cache fields
the query evaluates, and `after` contains the recorded result/write-back. -/
structure QuerySnapshot
    (runtime : Runtime Root) (actions : List (Action Root))
    (position : ℕ) (before after : Runtime Root) : Prop where
  prefixRun : run? cfg ext runtime (actions.take position) = some before
  action : ∃ kind, position < actions.length ∧
    actions.getD position (Action.query .extra) = Action.query kind
  accepted : step? cfg ext before (actions.getD position (.query .extra)) = some after

/-! ## Global positions and the current-slot vote timing adapter -/

/-- A vote-cast action retains both the execution's second and the exact
global action position.  The latter distinguishes a vote before a query from
one after the query in the same whole second. -/
structure VoteCastObservation where
  validator : ValidatorIndex
  slot : Slot
  executionSecond : ℕ
  actionPosition : ℕ

/-- A global action either advances one node's legal call runtime or records
an honest vote cast.  An adapter proves that `honestVoteCast` actions exactly
cover the relevant `Execution.vote` records. -/
inductive GlobalAction (Root : Type*) where
  | nodeAction (actor : ValidatorIndex) (action : Action Root)
  | honestVoteCast (validator : ValidatorIndex) (slot : Slot) (executionSecond : ℕ)

/-- Globally interleaved node states.  When a node action is executed, its
local `nextActionPosition` is re-seated to `nextGlobalActionPosition`; query
observations therefore carry the global position. -/
structure GlobalRuntime (Root : Type*) where
  nodeState : ValidatorIndex → Runtime Root
  voteCasts : List VoteCastObservation
  nextGlobalActionPosition : ℕ

/-- Execute one globally positioned action. -/
def globalStep? (runtime : GlobalRuntime Root) :
    GlobalAction Root → Option (GlobalRuntime Root)
  | .nodeAction actor action =>
      let nodeRuntime := {
        runtime.nodeState actor with
          nextActionPosition := runtime.nextGlobalActionPosition }
      match step? cfg ext nodeRuntime action with
      | none => none
      | some next =>
          some {
            nodeState := Function.update runtime.nodeState actor next
            voteCasts := runtime.voteCasts
            nextGlobalActionPosition := runtime.nextGlobalActionPosition + 1 }
  | .honestVoteCast validator slot executionSecond =>
      let cast : VoteCastObservation :=
        { validator := validator
          slot := slot
          executionSecond := executionSecond
          actionPosition := runtime.nextGlobalActionPosition }
      some {
        runtime with
          voteCasts := runtime.voteCasts ++ [cast]
          nextGlobalActionPosition := runtime.nextGlobalActionPosition + 1 }

/-- Execute a globally ordered action trace. -/
def globalRun? (runtime : GlobalRuntime Root) :
    List (GlobalAction Root) → Option (GlobalRuntime Root)
  | [] => some runtime
  | action :: rest => do
      let next ← globalStep? cfg ext runtime action
      globalRun? next rest

/-- Exact query-return snapshot in the global interleaving.  Other nodes'
states in `before`/`after` give a precise same-moment comparison point. -/
structure GlobalQuerySnapshot
    (runtime : GlobalRuntime Root) (actions : List (GlobalAction Root))
    (position : ℕ) (before after : GlobalRuntime Root) : Prop where
  prefixRun : globalRun? cfg ext runtime (actions.take position) = some before
  action : ∃ actor kind, position < actions.length ∧
    actions.getD position (.honestVoteCast 0 0 0) = .nodeAction actor (.query kind)
  accepted :
    globalStep? cfg ext before (actions.getD position (.honestVoteCast 0 0 0)) = some after

/-- Adapter coverage: every recorded execution vote by an honest validator has
a globally positioned cast action.  This is deliberately independent of the
vote's target and of every safety/canonicality predicate. -/
def VoteCastTraceCoversExecution
    (E : Execution Root) (runtime : GlobalRuntime Root) : Prop :=
  ∀ validator ∈ E.honest, ∀ slot executionSecond attestation,
    E.vote validator slot = some (executionSecond, attestation) →
    ∃ cast ∈ runtime.voteCasts,
      cast.validator = validator ∧ cast.slot = slot ∧
        cast.executionSecond = executionSecond

/-- Named adapter invariant needed by predictor branches: the query action
precedes all honest casts for its current slot, including casts in the same
whole second.  The pinned pre-due condition alone does not prove this fact. -/
def CallBeforeCurrentSlotHonestVotes
    (E : Execution Root) (runtime : GlobalRuntime Root)
    (queryPosition querySecond : ℕ) : Prop :=
  VoteCastTraceCoversExecution E runtime ∧
    ∀ cast ∈ runtime.voteCasts, cast.validator ∈ E.honest →
      cast.slot = E.slot_at cfg querySecond → queryPosition < cast.actionPosition

/-- The adapter invariant exposes the exact missing temporal fact for every
concrete `Execution.vote` record in the query's current slot. -/
theorem query_position_lt_current_slot_honest_vote
    (E : Execution Root) (runtime : GlobalRuntime Root)
    (queryPosition querySecond : ℕ)
    (hbefore : CallBeforeCurrentSlotHonestVotes cfg E runtime
      queryPosition querySecond)
    {validator : ValidatorIndex} (hhonest : validator ∈ E.honest)
    {executionSecond : ℕ} {attestation : Attestation Root}
    (hvote : E.vote validator (E.slot_at cfg querySecond) =
      some (executionSecond, attestation)) :
    ∃ cast ∈ runtime.voteCasts,
      cast.validator = validator ∧
      cast.slot = E.slot_at cfg querySecond ∧
      cast.executionSecond = executionSecond ∧
      queryPosition < cast.actionPosition := by
  obtain ⟨hcoverage, hposition⟩ := hbefore
  obtain ⟨cast, hcast, hvalidator, hslot, hsecond⟩ :=
    hcoverage validator hhonest (E.slot_at cfg querySecond)
      executionSecond attestation hvote
  exact ⟨cast, hcast, hvalidator, hslot, hsecond,
    hposition cast hcast (hvalidator ▸ hhonest) hslot⟩

/-! ## Small representability and embedding checks -/

/-- Starting exactly at genesis is explicitly slot zero. -/
theorem fresh_genesis_starts_in_slot_zero
    (fcrStore : FastConfirmationStore Root)
    (hstart : fcrStore.store.time = fcrStore.store.genesis_time) :
    (initRuntime cfg fcrStore .updateInitialSlot).initialSlot = GENESIS_SLOT := by
  have hzero : storeElapsedMs fcrStore.store = 0 := by
    simp [storeElapsedMs, hstart, seconds_to_milliseconds]
  simp [initRuntime, hzero, wallSlot]

/-- Initialization is not mistaken for the initial slot's required update. -/
theorem fresh_start_requires_initial_update
    (fcrStore : FastConfirmationStore Root) :
    updateRequiredIn (initRuntime cfg fcrStore .updateInitialSlot)
      (initRuntime cfg fcrStore .updateInitialSlot).initialSlot = true := by
  simp [updateRequiredIn, initRuntime]

/-- The only startup exemption is the explicitly partial initial slot. -/
theorem partial_start_exempts_only_initial_slot
    (fcrStore : FastConfirmationStore Root) :
    updateRequiredIn (initRuntime cfg fcrStore .exemptInitialPartialSlot)
      (initRuntime cfg fcrStore .exemptInitialPartialSlot).initialSlot = false := by
  simp [updateRequiredIn, initRuntime]

/-- A received expected-proposer-tagged block at the head of the queue is
recorded as processed only when it is a block for the current slot and
`on_block` accepts it.  Proposer identity itself is an adapter obligation
because the projected wire block has no proposer field. -/
theorem process_expected_proposer_records_wait
    (runtime : Runtime Root) (block : SignedBeaconBlock Root)
    (slot : Slot) (rest : List (QueuedEvent Root)) (nextStore : Store Root)
    (hready : runtime.awaitingMandatoryQuery = false)
    (hpending : runtime.pending =
      { event := .block block, expectedProposerFor := some slot } :: rest)
    (hcurrent : slot = wallSlot cfg runtime.elapsedMs)
    (hblock : block.message.slot = slot)
    (hvalid : apply_event cfg ext runtime.fcrStore.store (.block block) = some nextStore) :
    ∃ processed,
      step? cfg ext runtime .processNext = some processed ∧
      WaitedForExpectedProposer processed slot := by
  simp [step?, hready, hpending, hvalid, hcurrent, hblock,
    WaitedForExpectedProposer, bump]

/-- Once the low operational update guard holds, the required update/query
pair is accepted.  This is the executable form of the mandatory call order. -/
theorem update_then_mandatory_representable
    (runtime : Runtime Root) (hupdate : canUpdate cfg runtime = true) :
    ∃ after, run? cfg ext runtime
      [.updateVariables, .query .mandatory] = some after := by
  simp only [run?, step?, hupdate, if_true, Option.bind_eq_bind]
  exact ⟨_, rfl⟩

/-- Processing an expected-proposer block and then taking the mandatory pair
is a legal ordered trace whenever the resulting operational update guard
holds. -/
theorem expected_proposer_then_update_representable
    (runtime processed : Runtime Root)
    (hprocess : step? cfg ext runtime .processNext = some processed)
    (hupdate : canUpdate cfg processed = true) :
    ∃ after, run? cfg ext runtime
      [.processNext, .updateVariables, .query .mandatory] = some after := by
  obtain ⟨after, htail⟩ := update_then_mandatory_representable cfg ext processed hupdate
  refine ⟨after, ?_⟩
  rw [run?]
  simp only [hprocess]
  exact htail

/-- Any number of extra pure queries is representable after the mandatory
write-back.  This two-query witness also checks that the extra query does not
change `confirmed_root`. -/
theorem extra_query_is_pure
    (runtime : Runtime Root) (hready : runtime.awaitingMandatoryQuery = false) :
    ∃ after,
      run? cfg ext runtime [.query .extra, .query .extra] = some after ∧
      after.fcrStore.confirmed_root = runtime.fcrStore.confirmed_root ∧
      after.observations.length = runtime.observations.length + 2 := by
  simp only [run?, step?, hready, Bool.false_eq_true, if_false]
  refine ⟨_, rfl, rfl, ?_⟩
  simp [bump]

/-- The mandatory pair can be followed immediately by an extra pure query. -/
theorem update_mandatory_extra_representable
    (runtime : Runtime Root) (hupdate : canUpdate cfg runtime = true) :
    ∃ after, run? cfg ext runtime
      [.updateVariables, .query .mandatory, .query .extra] = some after := by
  simp [run?, step?, hupdate, bump]

/-- A positive in-slot delay followed by update, mandatory write-back, and an
extra pure query is representable whenever the two executable operational
guards accept the delay and the resulting update. -/
theorem delayed_update_and_extra_query_representable
    (runtime delayed : Runtime Root) (elapsedMs : ℕ)
    (hstrict : runtime.elapsedMs < elapsedMs)
    (helapse : step? cfg ext runtime (.elapseTo elapsedMs) = some delayed)
    (hupdate : canUpdate cfg delayed = true) :
    ∃ after, run? cfg ext runtime
      [.elapseTo elapsedMs, .updateVariables, .query .mandatory, .query .extra] =
        some after := by
  have _ := hstrict
  obtain ⟨after, htail⟩ := update_mandatory_extra_representable cfg ext delayed hupdate
  refine ⟨after, ?_⟩
  rw [run?]
  simp only [helapse]
  exact htail

/-- The update followed by its mandatory query is definitionally the pinned
`on_fast_confirmation` handler. -/
theorem mandatory_pair_runs_handler
    (runtime : Runtime Root) (hupdate : canUpdate cfg runtime = true)
    {after : Runtime Root}
    (hrun : run? cfg ext runtime [.updateVariables, .query .mandatory] = some after) :
    after.fcrStore = on_fast_confirmation cfg ext runtime.fcrStore := by
  simp only [run?, step?, hupdate, if_true] at hrun
  cases hrun
  rfl

/-- The existing boundary recurrence is one instance of the ordered trace:
start after that second's fork-choice events, update the cached variables, and
immediately run/write back `get_latest_confirmed`.  The only additional
premise is the low scheduler guard (positive deadline, aligned boundary,
empty past-attestation queue, and no prior update in the slot). -/
theorem execution_boundary_recurrence_embeds
    (E : Execution Root) (v : ValidatorIndex) (n : ℕ)
    (hadvance : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n))
    (runtime : Runtime Root)
    (hruntime : runtime.fcrStore =
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) })
    (hupdate : canUpdate cfg runtime = true) :
    ∃ after,
      run? cfg ext runtime [.updateVariables, .query .mandatory] = some after ∧
      after.fcrStore = E.fcr cfg ext v (n + 1) := by
  obtain ⟨after, hrun⟩ := update_then_mandatory_representable cfg ext runtime hupdate
  refine ⟨after, hrun, ?_⟩
  rw [mandatory_pair_runs_handler cfg ext runtime hupdate hrun, hruntime]
  simp only [Execution.fcr]
  rw [if_pos hadvance]

end AllowedFCRCalls

end FastConfirmation.Spec
