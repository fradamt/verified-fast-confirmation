module
public import FastConfirmationWitnesses.NonVacuity.TwelveSecondSynchrony
public import FastConfirmationWitnesses.NonVacuity.FFGEvidence

@[expose] public section

namespace FastConfirmation.Spec.FullTwelveEnvelopeWitness

open AcceptedActualFCRJointNonVacuityBase
abbrev R := WitnessRoot

def cfg : Config := TwelveSecondSynchronyWitness.cfg
def childEnvelope : SignedExecutionPayloadEnvelope R :=
  { message := { beacon_block_root := childRoot
                 parent_beacon_block_root := anchorRoot
                 identity := childRoot }
    signature := childRoot }

def payloadObservation : EnvelopeObservation R := { identity := childRoot }

def ext : BeaconFunctionInterface WitnessRoot :=
  { TwelveSecondSynchronyWitness.ext with
    is_data_available := fun r _ => decide (r = childRoot)
    verify_execution_payload_envelope := fun _ signed _ => decide (signed = childEnvelope) }

def schedule (w n : ℕ) : List (Event WitnessRoot) :=
  if n = 4 ∧ w = 0 then [.attestation vote0 false]
  else if n = 6 ∧ w = 1 then [.attestation vote0 false]
  else if n = 12 then
    if w = 1 then [.attestation vote0 false]
    else [.block childSignedBlock, .attestation vote0 false]
  else if n = 14 ∧ w = 1 then [.block childSignedBlock]
  else if n = 96 then
    [.attestation vote7 false, .block carrierSignedBlock,
      .attestation vote4 true, .attestation vote5 true,
      .attestation vote6 true]
  else if n = 24 then [.attestation vote1 false]
  else if n = 36 then [.attestation vote2 false]
  else if n = 48 then [.attestation vote3 false]
  else if n = 60 then [.attestation vote4 false]
  else if n = 72 then [.attestation vote5 false]
  else if n = 84 then [.attestation vote6 false]
  else if n = 108 then [.attestation vote8 false]
  else if n = 120 then [.attestation vote9 false]
  else if n = 132 then [.attestation vote10 false]
  else if n = 144 then [.attestation vote11 false]
  else if n = 156 then [.attestation vote12 false]
  else if n = 168 then
    if w = 1 then [.attestation vote13 false]
    else [.execution_payload_envelope childEnvelope payloadObservation,
      .attestation vote13 false]
  else if n = 170 ∧ w = 1 then
    [.execution_payload_envelope childEnvelope payloadObservation]
  else if n = 180 then
    [.execution_payload_envelope childEnvelope payloadObservation,
      .attestation vote14 false]
  else if n = 192 then [.attestation vote15 false]
  else []

def recordedVote (v s : ℕ) : Option (ℕ × Attestation WitnessRoot) :=
  if s < 16 ∧ v = s % 4 then some (12 * s + 3, vote s) else none

def run : Execution WitnessRoot :=
  { verification_horizon := 4
    genesis_store := get_forkchoice_store cfg anchorState anchorSignedBlock
    schedule := schedule
    honest := {0, 1, 2, 3}
    committee := witnessCommittee
    vote := recordedVote }

set_option maxRecDepth 50000 in
theorem confirmed_at_13 : run.confirmed cfg ext 0 13 = anchorRoot := by decide

set_option maxRecDepth 50000 in
theorem confirmed_at_25 : run.confirmed cfg ext 0 25 = childRoot := by decide

def childPrefix : run.ScheduledEventPrefix where
  node := 0
  previousSecond := 11
  processedCount := 0
  count_le := by decide

def childPostPrefix : run.ScheduledEventPrefix :=
  childPrefix.successor (by decide)

set_option maxRecDepth 50000 in
theorem child_on_block_accepted :
    on_block cfg ext (childPrefix.store cfg ext) childSignedBlock =
      some (childPostPrefix.store cfg ext) := by rfl

def carrierPrefix : run.ScheduledEventPrefix where
  node := 0
  previousSecond := 95
  processedCount := 1
  count_le := by decide

def carrierPostPrefix : run.ScheduledEventPrefix :=
  carrierPrefix.successor (by decide)

set_option maxRecDepth 50000 in
theorem carrier_on_block_accepted :
    on_block cfg ext (carrierPrefix.store cfg ext) carrierSignedBlock =
      some (carrierPostPrefix.store cfg ext) := by rfl

def childTransition : run.SuccessfulScheduledBlockImport cfg ext where
  atPrefix := childPrefix
  signedBlock := childSignedBlock
  event_at := by rfl
  postStore := childPostPrefix.store cfg ext
  accepted := child_on_block_accepted

def carrierTransition : run.SuccessfulScheduledBlockImport cfg ext where
  atPrefix := carrierPrefix
  signedBlock := carrierSignedBlock
  event_at := by rfl
  postStore := carrierPostPrefix.store cfg ext
  accepted := carrier_on_block_accepted

theorem child_accepted : run.RootKnownInScheduledPrefix cfg ext childRoot := by
  simpa [childSignedBlock] using childTransition.root_accepted

theorem carrier_accepted : run.RootKnownInScheduledPrefix cfg ext carrierRoot := by
  simpa [carrierSignedBlock] using carrierTransition.root_accepted

theorem delayed_receipts_are_first :
    Event.block childSignedBlock ∈ run.schedule 0 12 ∧
    Event.block childSignedBlock ∈ run.schedule 1 14 ∧
    (∀ n < 14, Event.block childSignedBlock ∉ run.schedule 1 n) ∧
    Event.attestation vote0 false ∈ run.schedule 0 4 ∧
    Event.attestation vote0 false ∈ run.schedule 1 6 ∧
    (∀ n < 6, Event.attestation vote0 false ∉ run.schedule 1 n) := by
  constructor
  · simp [run, schedule]
  constructor
  · simp [run, schedule]
  constructor
  · intro n hn
    interval_cases n <;> simp [run, schedule]
  constructor
  · simp [run, schedule]
  constructor
  · simp [run, schedule]
  · intro n hn
    interval_cases n <;> simp [run, schedule]

theorem delayed_block_in_stores :
    childRoot ∈ (run.store cfg ext 0 12).block_roots ∧
    childRoot ∉ (run.store cfg ext 1 12).block_roots ∧
    childRoot ∈ (run.store cfg ext 1 14).block_roots := by
  set_option maxRecDepth 50000 in decide

theorem changed_confirmed_root :
    run.confirmed cfg ext 0 23 = anchorRoot ∧
    run.confirmed cfg ext 0 24 = childRoot ∧
    run.IsScheduledFCRCallAt cfg ext 0 23 := by
  constructor
  · set_option maxRecDepth 50000 in decide
  constructor
  · set_option maxRecDepth 50000 in decide
  · change get_current_slot cfg (run.store cfg ext 0 24) >
      get_current_slot cfg (run.store cfg ext 0 23)
    set_option maxRecDepth 50000 in decide

theorem slot_at_eq (n : ℕ) : run.slot_at cfg n = n / 12 := by
  simp [Execution.slot_at, Execution.time_at, run, cfg,
    TwelveSecondSynchronyWitness.cfg, anchorState, stateAt,
    anchorSignedBlock, get_forkchoice_store, GENESIS_SLOT]
  simpa only [show (12000 : ℕ) = 12 * 1000 by decide] using
    (Nat.mul_div_mul_right n 12 (by decide : 0 < 1000))

theorem slot_start_eq (s : Slot) : run.slot_start cfg s = 12 * s := by
  simp [Execution.slot_start, run, cfg, TwelveSecondSynchronyWitness.cfg,
    anchorState, stateAt, anchorSignedBlock, get_forkchoice_store]
  omega

theorem due_eq : get_attestation_due_ms cfg = 3000 := by decide

theorem horizon_time {n : ℕ} (hn : run.WithinHorizon cfg n) : n < 192 := by
  have he := hn.2.2
  rw [slot_at_eq] at he
  change n / 12 / 4 < 4 at he
  omega

theorem horizon_slot {s : Slot} (hs : run.SlotWithinHorizon cfg s) :
    s < 16 := by
  have he := hs.2
  change s / 4 < 4 at he
  have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp he
  omega

theorem time_within {n : ℕ} (hn : n < 192) :
    run.WithinHorizon cfg n := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Execution.time_at, run, anchorState, stateAt,
      anchorSignedBlock, get_forkchoice_store]
    norm_num [UINT64_MAX]
    omega
  · rw [slot_at_eq]
    exact (Nat.div_le_self n 12).trans
      ((Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX]))
  · rw [slot_at_eq]
    change n / 12 / 4 < 4
    omega

theorem recorded_vote_some_iff {v s n : ℕ} {a : Attestation R} :
    run.vote v s = some (n, a) ↔
      s < 16 ∧ v = s % 4 ∧ n = 12 * s + 3 ∧ a = vote s := by
  change (if s < 16 ∧ v = s % 4 then some (12 * s + 3, vote s) else none) =
    some (n, a) ↔ _
  by_cases h : s < 16 ∧ v = s % 4
  · rw [if_pos h]
    constructor
    · intro heq
      have hp := Option.some.inj heq
      exact ⟨h.1, h.2, (congrArg Prod.fst hp).symm,
        (congrArg Prod.snd hp).symm⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rw [if_neg h]
    constructor
    · intro himpossible
      contradiction
    · rintro ⟨hs, hv, -, -⟩
      exact (h ⟨hs, hv⟩).elim

theorem vote_head_at_deadline {s : Slot} (hs : s < 16) :
    run.vote (s % 4) s =
      some (12 * s + 3,
        honest_attestation cfg ext (run.store cfg ext (s % 4) (12 * s + 3))
          s 0 (s % 4)) := by
  interval_cases s <;>
    set_option maxRecDepth 50000 in decide

end FastConfirmation.Spec.FullTwelveEnvelopeWitness

end
