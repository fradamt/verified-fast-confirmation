module
public import FastConfirmationWitnesses.NonVacuity.ScheduledRun

@[expose] public section

/-! A four-validator, twelve-second-slot run with two-second block and vote receipt delays. -/

namespace FastConfirmation.Spec.TwelveSecondSynchronyWitness

open AcceptedActualFCRJointNonVacuityBase
abbrev R := WitnessRoot

def cfg : Config :=
  { witnessConfig with
    slot_duration_ms := 12000
    slot_duration_ms_pos := by decide
    attestation_due_bps := 2500 }

def ext : BeaconFunctionInterface R :=
  { witnessExternals with
    process_slots := fun st s =>
      if compute_epoch_at_slot cfg st.slot < compute_epoch_at_slot cfg s then
        { witnessPJF st with slot := s }
      else { st with slot := s } }

def schedule (w n : ℕ) : List (Event R) :=
  if n = 4 ∧ w = 0 then [.attestation vote0 false]
  else if n = 6 ∧ w = 1 then [.attestation vote0 false]
  else if n = 12 then
    if w = 1 then [.attestation vote0 false]
    else [.block childSignedBlock, .attestation vote0 false]
  else if n = 14 ∧ w = 1 then [.block childSignedBlock]
  else if n = 24 then [.attestation vote1 false]
  else if n = 36 then [.attestation vote2 false]
  else if n = 48 then [.attestation vote3 false]
  else []

def recordedVote (v s : ℕ) : Option (ℕ × Attestation R) :=
  if s < 4 ∧ v = s % 4 then some (12 * s + 3, vote s) else none

def run : Execution R :=
  { verification_horizon := 1
    genesis_store := get_forkchoice_store cfg anchorState anchorSignedBlock
    schedule := schedule
    honest := {0, 1, 2, 3}
    committee := witnessCommittee
    vote := recordedVote }

theorem slot_at_eq (n : ℕ) : run.slot_at cfg n = n / 12 := by
  simp [Execution.slot_at, Execution.time_at, run, cfg,
    anchorState, stateAt, anchorSignedBlock,
    get_forkchoice_store, GENESIS_SLOT]
  simpa only [show (12000 : ℕ) = 12 * 1000 by decide] using
    (Nat.mul_div_mul_right n 12 (by decide : 0 < 1000))

theorem slot_start_eq (s : Slot) : run.slot_start cfg s = 12 * s := by
  simp [Execution.slot_start, run, cfg, anchorState, stateAt,
    anchorSignedBlock, get_forkchoice_store]
  omega

theorem due_eq : get_attestation_due_ms cfg = 3000 := by decide

theorem delayed_block :
    Event.block childSignedBlock ∈ run.schedule 0 12 ∧
    Event.block childSignedBlock ∈ run.schedule 1 14 ∧
    12 < 14 := by simp [run, schedule]

theorem delayed_vote :
    Event.attestation vote0 false ∈ run.schedule 0 4 ∧
    Event.attestation vote0 false ∈ run.schedule 1 6 ∧
    4 < 6 := by simp [run, schedule]

theorem delayed_receipts_are_first :
    (∀ n < 14, Event.block childSignedBlock ∉ run.schedule 1 n) ∧
    (∀ n < 6, Event.attestation vote0 false ∉ run.schedule 1 n) := by
  constructor
  · intro n hn
    interval_cases n <;> simp [run, schedule]
  · intro n hn
    interval_cases n <;> simp [run, schedule]

theorem horizon_time {n : ℕ} (hn : run.WithinHorizon cfg n) : n < 48 := by
  have he := hn.2.2
  rw [slot_at_eq] at he
  change n / 12 / 4 < 1 at he
  omega

theorem horizon_slot {s : Slot} (hs : run.SlotWithinHorizon cfg s) : s < 4 := by
  have he := hs.2
  change s / 4 < 1 at he
  have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp he
  omega

theorem time_within {n : ℕ} (hn : n < 48) : run.WithinHorizon cfg n := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Execution.time_at, run, anchorState, stateAt,
      anchorSignedBlock, get_forkchoice_store]
    norm_num [UINT64_MAX]
    omega
  · rw [slot_at_eq]
    exact (Nat.div_le_self n 12).trans
      ((Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX]))
  · rw [slot_at_eq]
    change n / 12 / 4 < 1
    omega

theorem recorded_vote_some_iff {v s n : ℕ} {a : Attestation R} :
    run.vote v s = some (n, a) ↔
      s < 4 ∧ v = s % 4 ∧ n = 12 * s + 3 ∧ a = vote s := by
  change (if s < 4 ∧ v = s % 4 then some (12 * s + 3, vote s) else none) =
    some (n, a) ↔ _
  by_cases h : s < 4 ∧ v = s % 4
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

theorem block_event_child {w n : ℕ} {b : SignedBeaconBlock R}
    (h : Event.block b ∈ run.schedule w n) : b = childSignedBlock := by
  change Event.block b ∈ schedule w n at h
  unfold schedule at h
  split_ifs at h <;> simp_all

theorem scheduled_attestation (w n : ℕ) (a : Attestation R) (ifb : Bool)
    (h : Event.attestation a ifb ∈ run.schedule w n) :
    (a = vote0 ∧ 3 ≤ n) ∨
    (a = vote1 ∧ 15 ≤ n) ∨
    (a = vote2 ∧ 27 ≤ n) ∨
    (a = vote3 ∧ 39 ≤ n) := by
  change Event.attestation a ifb ∈ schedule w n at h
  unfold schedule at h
  split_ifs at h <;> simp_all <;> omega

theorem vote_head_at_deadline {s : Slot} (hs : s < 4) :
    run.vote (s % 4) s =
      some (12 * s + 3,
        honest_attestation cfg ext (run.store cfg ext (s % 4) (12 * s + 3))
          s 0 (s % 4)) := by
  interval_cases s <;>
    set_option maxRecDepth 50000 in decide

theorem honest_behavior : HonestBehavior cfg ext run := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := horizon_slot hs
    have hvmod : v = s % 4 := by
      simpa [run, witnessCommittee] using hcommittee
    subst v
    have htime : 12 * s + 3 < 48 := by
      interval_cases s <;> decide
    refine ⟨12 * s + 3, 0, time_within htime, ?_, vote_head_at_deadline hslt⟩
    rw [slot_at_eq]
    interval_cases s <;> decide
  · intro v hv s n a hvote
    obtain ⟨hs, _, rfl, _⟩ := recorded_vote_some_iff.mp hvote
    rw [slot_start_eq, due_eq]
    omega
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨na, hna⟩
    rcases na with ⟨n, a⟩
    obtain ⟨hs, hvmod, _, _⟩ := recorded_vote_some_iff.mp hna
    simpa [run, witnessCommittee, hvmod]
  · intro w n a ifb hschedule v hv hvin
    rcases scheduled_attestation w n a ifb hschedule with
      ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · have hvmod : v = 0 := by simpa [vote0, vote] using hvin
      refine ⟨3, vote0, hn, ?_, rfl⟩
      simp [run, recordedVote, hvmod, vote0, vote_data_slot]
    · have hvmod : v = 1 := by simpa [vote1, vote] using hvin
      refine ⟨15, vote1, hn, ?_, rfl⟩
      simp [run, recordedVote, hvmod, vote1, vote_data_slot]
    · have hvmod : v = 2 := by simpa [vote2, vote] using hvin
      refine ⟨27, vote2, hn, ?_, rfl⟩
      simp [run, recordedVote, hvmod, vote2, vote_data_slot]
    · have hvmod : v = 3 := by simpa [vote3, vote] using hvin
      refine ⟨39, vote3, hn, ?_, rfl⟩
      simp [run, recordedVote, hvmod, vote3, vote_data_slot]
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hs, hvmod, hn, ha⟩ := recorded_vote_some_iff.mp hvote
    obtain ⟨hs', hvmod', hn', ha'⟩ := recorded_vote_some_iff.mp hvote'
    subst n
    subst a
    subst n'
    subst a'
    interval_cases s <;> interval_cases s' <;>
      simp_all [vote, voteData, is_slashable_attestation_data,
        anchorCheckpoint, childEpochOneCheckpoint]
  · intro v hv
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by simpa [run] using hv) with
      rfl | rfl | rfl | rfl <;> decide

theorem well_formed : WellFormedExecution run := by
  constructor
  · intro w n b hb w' n' b' hb' _
    rw [block_event_child hb, block_event_child hb']
  · intro w n b hb hgen
    rw [block_event_child hb] at hgen ⊢
    simp [run, anchorState, stateAt, anchorSignedBlock,
      childSignedBlock, get_forkchoice_store] at hgen
    exact (by decide : childRoot ≠ anchorRoot) hgen |>.elim
  · intro r hr w n b hb
    rw [block_event_child hb]
    have hr' : r = anchorRoot := by
      simpa [run, anchorState, stateAt, anchorSignedBlock,
        get_forkchoice_store] using hr
    subst r
    decide

theorem root_kind {v n : ℕ} {r : R}
    (hr : r ∈ (run.store cfg ext v n).block_roots) :
    r = anchorRoot ∨ r = childRoot := by
  rcases (run.blockProvenance cfg ext v n) r hr with
    ⟨hg, _⟩ | ⟨b, ⟨w, m, hb⟩, hbr, _⟩
  · left
    simpa [run, anchorState, stateAt, anchorSignedBlock,
      get_forkchoice_store] using hg
  · right
    rw [block_event_child hb] at hbr
    exact hbr.symm

theorem child_known_at14 {w : ℕ} (hw : w ∈ run.honest) :
    childRoot ∈ (run.store cfg ext w 14).block_roots := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by simpa [run] using hw) with
    rfl | rfl | rfl | rfl
  all_goals set_option maxRecDepth 50000 in decide

theorem anchor_known {w m : ℕ} :
    anchorRoot ∈ (run.store cfg ext w m).block_roots := by
  have h0 : anchorRoot ∈ (run.store cfg ext w 0).block_roots := by
    simp [Execution.store, run, anchorState, stateAt,
      anchorSignedBlock, get_forkchoice_store]
  exact (run.store_storeLE cfg ext w (Nat.zero_le m)).1 h0

theorem child_known_after14 {w m : ℕ} (hw : w ∈ run.honest) (hm : 14 ≤ m) :
    childRoot ∈ (run.store cfg ext w m).block_roots :=
  (run.store_storeLE cfg ext w hm).1 (child_known_at14 hw)

theorem child_absent_at11 {w : ℕ} (hw : w ∈ run.honest) :
    childRoot ∉ (run.store cfg ext w 11).block_roots := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by simpa [run] using hw) with
    rfl | rfl | rfl | rfl
  all_goals set_option maxRecDepth 50000 in decide

theorem child_source_after12 {v n : ℕ} (hv : v ∈ run.honest)
    (hr : childRoot ∈ (run.store cfg ext v n).block_roots) : 12 ≤ n := by
  by_contra h
  have hn : n ≤ 11 := by omega
  exact child_absent_at11 hv ((run.store_storeLE cfg ext v hn).1 hr)

theorem boundary_after_child {n : ℕ} (hn : 12 ≤ n) :
    24 ≤ run.slot_start cfg (run.slot_at cfg n + 1) := by
  rw [slot_start_eq, slot_at_eq]
  have hdiv : 1 ≤ n / 12 := by omega
  omega

theorem vote_at_boundary {v s n : ℕ} {a : Attestation R}
    (hvote : run.vote v s = some (n, a)) (w : ℕ) :
    Event.attestation a false ∈ run.schedule w (run.slot_start cfg (s + 1)) := by
  obtain ⟨hs, _, _, rfl⟩ := recorded_vote_some_iff.mp hvote
  rw [slot_start_eq]
  interval_cases s <;> simp [run, schedule, vote0, vote1, vote2, vote3]
    <;> split_ifs <;> simp

theorem deadline_block_relay : DeadlineBlockRelay cfg ext run := by
  intro v hv n r hn hr _hdeadline w hw m hm hboundary _hlt
  left
  rcases root_kind hr with rfl | rfl
  · exact anchor_known
  · have hchild := child_source_after12 hv hr
    have hb := boundary_after_child hchild
    exact child_known_after14 hw (by omega)

theorem boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext run := by
  intro v hv n r hn hr _hdeadline w hw boundary hHboundary hlt
    a before after _hschedule _hnotExcluded
  have hb : boundary = run.slot_start cfg (run.slot_at cfg n + 1) := rfl
  have hpred : r ∈ (run.store cfg ext w (boundary - 1)).block_roots := by
    rcases root_kind hr with rfl | rfl
    · exact anchor_known
    · have hchild := child_source_after12 hv hr
      have hboundary := boundary_after_child hchild
      exact child_known_after14 hw (by omega)
  have htick : r ∈
      (on_tick cfg (run.store cfg ext w (boundary - 1))
        (run.time_at boundary)).block_roots :=
    (on_tick_storeLE cfg _ _).1 hpred
  exact (foldl_storeLE cfg ext before _).1 htick

theorem event_kind {w n : ℕ} {e : Event R}
    (he : e ∈ run.schedule w n) :
    (∃ b, e = Event.block b) ∨
      (∃ a, e = Event.attestation a false) := by
  change e ∈ schedule w n at he
  unfold schedule at he
  split_ifs at he <;> simp_all
  all_goals rcases he with rfl | rfl <;> simp

theorem event_equiv (store : Store R) {w n : ℕ} {e : Event R}
    (he : e ∈ run.schedule w n) :
    ((apply_event cfg ext store e).getD store).equivocating_indices =
      store.equivocating_indices := by
  rcases event_kind he with ⟨b, rfl⟩ | ⟨a, rfl⟩
  · cases h : on_block cfg ext store b with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_block_equiv cfg ext h
  · cases h : on_attestation cfg ext store a false with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_attestation_equiv cfg ext h

theorem schedule_fold_equiv (w n : ℕ) (store : Store R) :
    ((run.schedule w n).foldl
      (fun s e => (apply_event cfg ext s e).getD s) store).equivocating_indices =
      store.equivocating_indices := by
  have fold (events : List (Event R)) (hsub : ∀ e ∈ events, e ∈ run.schedule w n)
      (s : Store R) :
      (events.foldl (fun st e => (apply_event cfg ext st e).getD st) s).equivocating_indices =
        s.equivocating_indices := by
    induction events generalizing s with
    | nil => rfl
    | cons e tail ih =>
        simp only [List.foldl_cons]
        rw [ih (by
          intro x hx
          exact hsub x (List.mem_cons_of_mem e hx))]
        exact event_equiv s (hsub e List.mem_cons_self)
  exact fold _ (fun e he => he) store

theorem no_evidence (w n : ℕ) :
    (run.store cfg ext w n).equivocating_indices = ∅ := by
  induction n with
  | zero =>
      simp [Execution.store, run, anchorState, stateAt,
        anchorSignedBlock, get_forkchoice_store]
  | succ n ih =>
      change ((run.schedule w (n + 1)).foldl
        (fun s e => (apply_event cfg ext s e).getD s)
        (on_tick cfg (run.store cfg ext w n) (run.time_at (n + 1)))).equivocating_indices = ∅
      rw [schedule_fold_equiv, on_tick_equiv, ih]

theorem attester_slashing_relay : DeadlineAttesterSlashingRelay cfg ext run := by
  intro v hv n i hn hi _hdeadline w hw m hm _hnext _hlt
  rw [no_evidence] at hi
  simp at hi

theorem schedule_no_envelope {w n : ℕ} {e : Event R}
    (he : e ∈ run.schedule w n) (signed : SignedExecutionPayloadEnvelope R)
    (observation : EnvelopeObservation R) :
    e ≠ Event.execution_payload_envelope signed observation := by
  rcases event_kind he with ⟨b, rfl⟩ | ⟨a, rfl⟩ <;> simp

theorem event_payloads (store : Store R) {w n : ℕ} {e : Event R}
    (he : e ∈ run.schedule w n) :
    ((apply_event cfg ext store e).getD store).payloads = store.payloads := by
  rcases event_kind he with ⟨b, rfl⟩ | ⟨a, rfl⟩
  · cases h : on_block cfg ext store b with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_block_payloads cfg ext h
  · cases h : on_attestation cfg ext store a false with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_attestation_payloads cfg ext h

theorem schedule_fold_payloads (w n : ℕ) (store : Store R) :
    ((run.schedule w n).foldl
      (fun s e => (apply_event cfg ext s e).getD s) store).payloads =
      store.payloads := by
  have fold (events : List (Event R)) (hsub : ∀ e ∈ events, e ∈ run.schedule w n)
      (s : Store R) :
      (events.foldl (fun st e => (apply_event cfg ext st e).getD st) s).payloads =
        s.payloads := by
    induction events generalizing s with
    | nil => rfl
    | cons e tail ih =>
        simp only [List.foldl_cons]
        rw [ih (by
          intro x hx
          exact hsub x (List.mem_cons_of_mem e hx))]
        exact event_payloads s (hsub e List.mem_cons_self)
  exact fold _ (fun e he => he) store

theorem payloads_empty (w n : ℕ) :
    (run.store cfg ext w n).payloads = run.genesis_store.payloads := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((run.schedule w (n + 1)).foldl
        (fun s e => (apply_event cfg ext s e).getD s)
        (on_tick cfg (run.store cfg ext w n) (run.time_at (n + 1)))).payloads =
          run.genesis_store.payloads
      rw [schedule_fold_payloads, on_tick_payloads, ih]

theorem no_verified_payload (w n : ℕ) (r : R) :
    is_payload_verified (run.store cfg ext w n) r = false := by
  have hempty := payloads_empty w n
  have hnone : run.genesis_store.payloads r = none := rfl
  simp only [is_payload_verified, hempty, hnone, Option.isSome_none]

theorem synchrony : Synchrony cfg ext run := by
  refine {
    delta := ⟨2000, by decide, by decide⟩
    attestation_delivery := ?_
    deadline_block_relay := deadline_block_relay
    boundary_block_prefix := boundary_block_prefix
    attester_slashing_relay := attester_slashing_relay
  }
  intro v hv s n a hs hn hvote _hdeadline _hdelivery w hw
  exact vote_at_boundary hvote w

theorem next_slot_synchrony : NextSlotSynchronyPremises cfg ext run := by
  apply synchrony.toPaperSafetySynchrony cfg ext
  · intro v hv n r hn hr
    rw [no_verified_payload] at hr
    cases hr
  · intro v hv k n signed observation hk hn hevent havailable
    exact (schedule_no_envelope hevent signed observation rfl).elim

theorem delayed_block_in_stores :
    childRoot ∈ (run.store cfg ext 0 12).block_roots ∧
    childRoot ∉ (run.store cfg ext 1 12).block_roots ∧
    childRoot ∈ (run.store cfg ext 1 14).block_roots := by
  set_option maxRecDepth 50000 in decide

theorem joint_witness :
    WellFormedExecution run ∧ HonestBehavior cfg ext run ∧
      Synchrony cfg ext run ∧ NextSlotSynchronyPremises cfg ext run :=
  ⟨well_formed, honest_behavior, synchrony, next_slot_synchrony⟩

theorem delivery_lookahead : HorizonVoteDeliveryLookahead cfg run := by
  constructor
  intro v hv s n a hs hn hvote _hdeadline w hw
  exact vote_at_boundary hvote w

theorem static_validators : StaticValidatorSet cfg run := by
  constructor
  · exact time_within (by decide)
  · intro i e e' he he'
    change e < 1 at he
    change e' < 1 at he'
    have he0 : e = 0 := by interval_cases e <;> decide
    have he'0 : e' = 0 := by interval_cases e' <;> decide
    rw [he0, he'0]

set_option maxRecDepth 20000 in
theorem byzantine_bound : ByzantineWeightPremises cfg run := by
  constructor
  · intro i
    cases i with
    | zero => decide
    | succ i =>
        cases i with
        | zero => decide
        | succ i =>
            cases i with
            | zero => decide
            | succ i =>
                cases i with
                | zero => decide
                | succ i =>
                    simp [Execution.weight_of, Execution.registry,
                      Execution.anchor_state, run, anchorState,
                      stateAt, anchorSignedBlock, witnessValidator,
                      cfg, witnessConfig, get_forkchoice_store]
                    exact dvd_zero 100
  · intro a b ha hb
    have halt := horizon_slot ha
    have hblt := horizon_slot hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 50000 in decide
  · intro a b ha hb
    have halt := horizon_slot ha
    have hblt := horizon_slot hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 50000 in decide

theorem phase0_source : Phase0SourceCoherence cfg ext := by
  constructor
  · intro st target hlt hepoch
    simp only [ext]
    have hnot : ¬ compute_epoch_at_slot cfg st.slot <
        compute_epoch_at_slot cfg target := by
      intro hstrict
      exact (Nat.ne_of_lt hstrict) hepoch
    rw [if_neg hnot]
  · intro pre sb post htransition hepoch
    simp only [ext, witnessExternals, witnessTransition] at htransition
    split at htransition
    · next hguard =>
        simp only [Option.some.injEq] at htransition
        subst post
        have hpre : pre = anchorState := sameProjectedState_iff_eq.mp hguard.1
        subst pre
        rfl
    · split at htransition
      · next hguard =>
          simp only [Option.some.injEq] at htransition
          subst post
          have hpre : pre = childState := sameProjectedState_iff_eq.mp hguard.1
          subst pre
          rfl
      · contradiction

theorem phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext := by
  refine Phase0BoundarySourceCoherence.of_eager ?_ ?_ (fun st => by simpa only [ext, cfg] using witnessPJF_current_epoch_le st)
  · intro st target hlt hcross
    simp only [ext]
    rw [if_pos hcross]
    rfl
  · intro pre sb post htransition hcross
    simp only [ext, witnessExternals, witnessTransition] at htransition
    split at htransition
    · next hguard =>
        simp only [Option.some.injEq] at htransition
        subst post
        have hpre : pre = anchorState := sameProjectedState_iff_eq.mp hguard.1
        subst pre
        rw [hguard.2] at hcross
        norm_num [anchorState, stateAt, anchorSignedBlock, childSignedBlock,
          cfg, witnessConfig, compute_epoch_at_slot] at hcross
    · split at htransition
      · next hguard =>
          simp only [Option.some.injEq] at htransition
          subst post
          have hpre : pre = childState := sameProjectedState_iff_eq.mp hguard.1
          subst pre
          rfl
      · contradiction

theorem balance_floor :
    2 * cfg.effective_balance_increment ≤
      run.weight (run.currentTargetAnchorActive cfg) := by decide

theorem epoch_ends_fit : EpochEndsFitUint64 cfg := by
  refine ⟨2 ^ 62, ?_⟩
  norm_num [EpochEndsFitUint64, UINT64_MAX, cfg, witnessConfig]

theorem anchor_boundary :
    Execution.InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := run) (anchor := anchorCheckpoint) := by
  unfold Execution.InitialAnchorAtEpochBoundary
  decide

end FastConfirmation.Spec.TwelveSecondSynchronyWitness

end
