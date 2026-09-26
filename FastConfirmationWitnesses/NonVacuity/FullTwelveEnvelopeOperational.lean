module
public import FastConfirmationWitnesses.NonVacuity.FullTwelveEnvelope

@[expose] public section

/-! The twelve-second execution satisfies operational premises through a finite slot table. -/

namespace FastConfirmation.Spec.FullTwelveEnvelopeWitness

open AcceptedActualFCRJointNonVacuityBase


/-- Ordinary boundary events plus three within-slot receipts. -/
def slotEvents (w s o : ℕ) : List (Event R) :=
  if s = 0 ∧ o = 4 ∧ w = 0 then [.attestation vote0 false]
  else if s = 0 ∧ o = 6 ∧ w = 1 then [.attestation vote0 false]
  else if s = 1 ∧ o = 2 ∧ w = 1 then [.block childSignedBlock]
  else if s = 14 ∧ o = 2 ∧ w = 1 then
    [.execution_payload_envelope childEnvelope payloadObservation]
  else if o = 0 then
    if s = 1 ∧ w = 1 then [.attestation vote0 false]
    else if s = 14 then
      if w = 1 then [.attestation vote13 false]
      else [.execution_payload_envelope childEnvelope payloadObservation,
        .attestation vote13 false]
    else if s = 15 then
      [.execution_payload_envelope childEnvelope payloadObservation,
        .attestation vote14 false]
    else witnessSchedule w s
  else []

private theorem schedule_at_slot (w s o : ℕ) (ho : o < 12) :
    schedule w (12 * s + o) = slotEvents w s o := by
  by_cases hs : s ≤ 16
  · interval_cases s <;> interval_cases o <;>
      simp [schedule, slotEvents, witnessSchedule, vote0, vote1, vote2,
        vote3, vote4, vote5, vote6, vote7, vote8, vote9, vote10,
        vote11, vote12, vote13, vote14, vote15]
  · have hlarge : 192 < 12 * s + o := by omega
    have h0 : s ≠ 0 := by omega
    have h1 : s ≠ 1 := by omega
    have h7 : s ≠ 8 := by omega
    have h14 : s ≠ 14 := by omega
    have h15 : s ≠ 15 := by omega
    have hnot : ¬ (2 ≤ s ∧ s ≤ 16) := by omega
    simp [schedule, slotEvents, witnessSchedule, h0, h1, h7, h14, h15, hnot,
      show 12 * s + o ≠ 4 by omega, show 12 * s + o ≠ 6 by omega,
      show 12 * s + o ≠ 12 by omega, show 12 * s + o ≠ 14 by omega,
      show 12 * s + o ≠ 84 by omega, show 12 * s + o ≠ 24 by omega,
      show 12 * s + o ≠ 36 by omega, show 12 * s + o ≠ 48 by omega,
      show 12 * s + o ≠ 60 by omega, show 12 * s + o ≠ 72 by omega,
      show 12 * s + o ≠ 96 by omega, show 12 * s + o ≠ 108 by omega,
      show 12 * s + o ≠ 120 by omega, show 12 * s + o ≠ 132 by omega,
      show 12 * s + o ≠ 144 by omega, show 12 * s + o ≠ 156 by omega,
      show 12 * s + o ≠ 168 by omega, show 12 * s + o ≠ 170 by omega,
      show 12 * s + o ≠ 180 by omega,
      show 12 * s + o ≠ 192 by omega]

theorem schedule_by_slot (w n : ℕ) :
    run.schedule w n = slotEvents w (n / 12) (n % 12) := by
  change schedule w n = _
  have h := schedule_at_slot w (n / 12) (n % 12) (Nat.mod_lt _ (by decide))
  simpa only [Nat.div_add_mod] using h

private theorem boundary_vote_before {w q a ifb}
    (h : Event.attestation a ifb ∈ witnessSchedule w q) :
    ∃ s, s < 16 ∧ a = vote s ∧ s < q := by
  unfold witnessSchedule at h
  split_ifs at h with h1 h7 hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Event.attestation.injEq] at h
    rcases h with h | h | h | h
    · refine ⟨7, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
    · refine ⟨4, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
    · refine ⟨5, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
    · refine ⟨6, by decide, h.1, ?_⟩
      (simp only [Slot] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨q - 1, ?_, h.1, ?_⟩ <;> (simp only [Slot] at *; omega)
  · simp at h

theorem scheduled_attestation {w n a ifb}
    (h : Event.attestation a ifb ∈ run.schedule w n) :
    ∃ s, s < 16 ∧ a = vote s ∧ 12 * s + 3 ≤ n := by
  rw [schedule_by_slot] at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 ho h0 h1 hslot14 hw1 hslot15
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h
  · simp at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.attestation.injEq] at h
    refine ⟨0, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h
    refine ⟨13, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h
    refine ⟨13, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h
    refine ⟨14, by decide, h.1, ?_⟩
    (simp only [Slot] at *; omega)
  · obtain ⟨s, hs, ha, hsq⟩ := boundary_vote_before h
    refine ⟨s, hs, ha, ?_⟩
    (simp only [Slot] at *; omega)
  · simp at h

theorem honest_behavior : HonestBehavior cfg ext run := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := horizon_slot hs
    have hvmod : v = s % 4 := by
      simpa [run, witnessCommittee] using hcommittee
    subst v
    refine ⟨12 * s + 3, 0, time_within ?_, ?_,
      vote_head_at_deadline hslt⟩
    · (simp only [Slot] at *; omega)
    · rw [slot_at_eq]
      (simp only [Slot] at *; omega)
  · intro v hv s n a hvote
    obtain ⟨_, _, rfl, _⟩ := recorded_vote_some_iff.mp hvote
    rw [slot_start_eq, due_eq]
    (simp only [Slot] at *; omega)
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨⟨n, a⟩, hna⟩
    obtain ⟨hs, hvmod, _, _⟩ := recorded_vote_some_iff.mp hna
    simpa [run, witnessCommittee, hvmod]
  · intro w n a ifb hschedule v hv hvin
    obtain ⟨s, hs, rfl, hsent⟩ := scheduled_attestation hschedule
    have hvmod : v = s % 4 := by simpa [vote] using hvin
    refine ⟨12 * s + 3, vote s, hsent, ?_, rfl⟩
    rw [vote_data_slot]
    exact recorded_vote_some_iff.mpr ⟨hs, hvmod, rfl, rfl⟩
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hs, hvmod, _, rfl⟩ := recorded_vote_some_iff.mp hvote
    obtain ⟨hs', hvmod', _, rfl⟩ := recorded_vote_some_iff.mp hvote'
    exact witnessHonestBehavior.not_slashable v hv s s' s s'
      (vote s) (vote s') (witness_vote_some_iff.mpr ⟨hs, hvmod, rfl, rfl⟩)
      (witness_vote_some_iff.mpr ⟨hs', hvmod', rfl, rfl⟩)
  · intro v hv
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by simpa [run] using hv) with
      rfl | rfl | rfl | rfl <;> decide


theorem block_event_cases {w n : ℕ} {b : SignedBeaconBlock R}
    (h : Event.block b ∈ run.schedule w n) :
    (b = childSignedBlock ∧ 12 ≤ n) ∨
      (b = carrierSignedBlock ∧ n = 96) := by
  rw [schedule_by_slot] at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 ho h0 h1 hslot14 hw1 hslot15
  · simp at h
  · simp at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Event.block.injEq] at h
    exact Or.inl ⟨h, by omega⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rcases (block_mem_schedule_iff (w := w)).mp h with ⟨hs, hb⟩ | ⟨hs, hb⟩
    · exact Or.inl ⟨hb, by omega⟩
    · exact Or.inr ⟨hb, by omega⟩
  · simp at h

theorem scheduledBlock_cases {b : SignedBeaconBlock R}
    (h : IsScheduledBlock run b) : b = childSignedBlock ∨ b = carrierSignedBlock := by
  obtain ⟨w, n, h⟩ := h
  exact (block_event_cases h).imp And.left And.left

theorem well_formed : WellFormedExecution run := by
  constructor
  · intro w n b hb w' n' b' hb' hroot
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl <;>
      rcases scheduledBlock_cases ⟨w', n', hb'⟩ with rfl | rfl
    · rfl
    · exact False.elim ((by decide : childRoot ≠ carrierRoot) hroot)
    · exact False.elim ((by decide : carrierRoot ≠ childRoot) hroot)
    · rfl
  · intro w n b hb hgen
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl
    all_goals simp [run, get_forkchoice_store, anchorSignedBlock,
      childSignedBlock, carrierSignedBlock, anchorRoot, childRoot, carrierRoot] at hgen
  · intro r hr w n b hb
    have hr' : r = anchorRoot := by
      simpa [run, anchorSignedBlock, get_forkchoice_store] using hr
    subst r
    rcases scheduledBlock_cases ⟨w, n, hb⟩ with rfl | rfl <;> decide

/-- Nodes have three schedule classes, including nodes outside the honest set. -/
def nodeClass (w : ℕ) : ℕ := if w = 0 then 0 else if w = 1 then 1 else 2

theorem nodeClass_lt (w : ℕ) : nodeClass w < 3 := by
  unfold nodeClass
  split_ifs <;> decide

private theorem schedule_nodeClass (w n : ℕ) :
    run.schedule w n = run.schedule (nodeClass w) n := by
  simp only [schedule_by_slot]
  by_cases h0 : w = 0
  · subst w; rfl
  by_cases h1 : w = 1
  · subst w; rfl
  simp [slotEvents, nodeClass, h0, h1, witnessSchedule]

theorem store_nodeClass (w n : ℕ) :
    run.store cfg ext w n = run.store cfg ext (nodeClass w) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Execution.store, schedule_nodeClass w (n + 1), ih]

theorem root_kind {v n : ℕ} {r : R}
    (hr : r ∈ (run.store cfg ext v n).block_roots) :
    r = anchorRoot ∨ r = childRoot ∨ r = carrierRoot := by
  rcases (run.blockProvenance cfg ext v n) r hr with
    ⟨hg, _⟩ | ⟨b, hb, hbr, _⟩
  · left
    simpa [run, anchorSignedBlock, get_forkchoice_store] using hg
  · rcases scheduledBlock_cases hb with rfl | rfl
    · exact Or.inr (Or.inl hbr.symm)
    · exact Or.inr (Or.inr hbr.symm)

theorem anchor_known {w m : ℕ} :
    anchorRoot ∈ (run.store cfg ext w m).block_roots := by
  have h0 : anchorRoot ∈ (run.store cfg ext w 0).block_roots := by
    simp [Execution.store, run, anchorSignedBlock, get_forkchoice_store]
  exact (run.store_storeLE cfg ext w (Nat.zero_le m)).1 h0

private theorem root_timing_table : ∀ w : Fin 3,
    childRoot ∉ (run.store cfg ext w 11).block_roots ∧
    childRoot ∈ (run.store cfg ext w 14).block_roots ∧
    carrierRoot ∉ (run.store cfg ext w 95).block_roots ∧
    carrierRoot ∈ (run.store cfg ext w 96).block_roots := by
  set_option maxRecDepth 50000 in decide

theorem child_known_after14 (w : ℕ) {m : ℕ} (hm : 14 ≤ m) :
    childRoot ∈ (run.store cfg ext w m).block_roots := by
  have h := (root_timing_table ⟨nodeClass w, nodeClass_lt w⟩).2.1
  rw [← store_nodeClass w 14] at h
  exact (run.store_storeLE cfg ext w hm).1 h

theorem carrier_known_after96 (w : ℕ) {m : ℕ} (hm : 96 ≤ m) :
    carrierRoot ∈ (run.store cfg ext w m).block_roots := by
  have h := (root_timing_table ⟨nodeClass w, nodeClass_lt w⟩).2.2.2
  rw [← store_nodeClass w 96] at h
  exact (run.store_storeLE cfg ext w hm).1 h

theorem child_source_after12 {v n : ℕ}
    (hr : childRoot ∈ (run.store cfg ext v n).block_roots) : 12 ≤ n := by
  by_contra h
  have hno := (root_timing_table ⟨nodeClass v, nodeClass_lt v⟩).1
  rw [← store_nodeClass v 11] at hno
  exact hno ((run.store_storeLE cfg ext v (by omega : n ≤ 11)).1 hr)

theorem carrier_source_after96 {v n : ℕ}
    (hr : carrierRoot ∈ (run.store cfg ext v n).block_roots) : 96 ≤ n := by
  by_contra h
  have hno := (root_timing_table ⟨nodeClass v, nodeClass_lt v⟩).2.2.1
  rw [← store_nodeClass v 95] at hno
  exact hno ((run.store_storeLE cfg ext v (by omega : n ≤ 95)).1 hr)

private theorem root_known_before_boundary {v n : ℕ} {r : R}
    (hr : r ∈ (run.store cfg ext v n).block_roots) (w : ℕ) :
    r ∈ (run.store cfg ext w (run.slot_start cfg (run.slot_at cfg n + 1) - 1)).block_roots := by
  rcases root_kind hr with rfl | rfl | rfl
  · exact anchor_known
  · apply child_known_after14
    have hn := child_source_after12 hr
    rw [slot_start_eq, slot_at_eq]
    omega
  · apply carrier_known_after96
    have hn := carrier_source_after96 hr
    rw [slot_start_eq, slot_at_eq]
    omega

theorem deadline_block_relay : DeadlineBlockRelay cfg ext run := by
  intro v hv n r hn hr _hdeadline w hw m hm hboundary _hlt
  left
  exact (run.store_storeLE cfg ext w (by omega)).1 (root_known_before_boundary hr w)

theorem boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext run := by
  intro v hv n r hn hr _hdeadline w hw boundary hHboundary hlt
    a before after _hschedule _hnotExcluded
  have hpred := root_known_before_boundary hr w
  exact (foldl_storeLE cfg ext before _).1 ((on_tick_storeLE cfg _ _).1 hpred)

theorem event_kind {w n : ℕ} {e : Event R}
    (he : e ∈ run.schedule w n) :
    (∃ b, e = Event.block b) ∨
    (∃ a ifb, e = Event.attestation a ifb) ∨
    (∃ signed observation,
      e = Event.execution_payload_envelope signed observation) := by
  rw [schedule_by_slot] at he
  unfold slotEvents at he
  split_ifs at he <;> try simp only [witnessSchedule] at he
  all_goals (try split_ifs at he) <;> simp_all
  all_goals rcases he with rfl | rfl | rfl | rfl | rfl <;> simp

theorem vote_at_boundary {v s n : ℕ} {a : Attestation R}
    (hvote : run.vote v s = some (n, a)) (w : ℕ) :
    Event.attestation a false ∈ run.schedule w (run.slot_start cfg (s + 1)) := by
  obtain ⟨hs, _, _, rfl⟩ := recorded_vote_some_iff.mp hvote
  rw [slot_start_eq]
  change Event.attestation (vote s) false ∈ schedule w (12 * (s + 1))
  rw [show 12 * (s + 1) = 12 * (s + 1) + 0 by omega, schedule_at_slot w (s + 1) 0 (by decide)]
  by_cases hs0 : s = 0
  · subst s; simp [slotEvents, witnessSchedule, vote0]; split_ifs <;> simp
  · by_cases hs13 : s = 13
    · subst s; simp [slotEvents, vote13]; split_ifs <;> simp
    by_cases hs14 : s = 14
    · subst s; simp [slotEvents, witnessSchedule, vote14]
    have hne : s + 1 ≠ 1 := by omega
    have hb := witness_vote_false_delivery hs w
    rw [AcceptedActualFCRJointNonVacuityBase.slot_start_eq] at hb
    change Event.attestation (vote s) false ∈ witnessSchedule w (s + 1) at hb
    simpa [slotEvents, hs0, hs13, hs14] using hb

theorem event_equiv (store : Store R) {w n : ℕ} {e : Event R}
    (he : e ∈ run.schedule w n) :
    ((apply_event cfg ext store e).getD store).equivocating_indices =
      store.equivocating_indices := by
  rcases event_kind he with ⟨b, rfl⟩ | ⟨a, ifb, rfl⟩ |
    ⟨signed, observation, rfl⟩
  · cases h : on_block cfg ext store b with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_block_equiv cfg ext h
  · cases h : on_attestation cfg ext store a ifb with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using on_attestation_equiv cfg ext h
  · cases h : on_execution_payload_envelope ext store signed observation with
    | none => simp [apply_event, h]
    | some next =>
        simpa [apply_event, h] using
          (on_execution_payload_envelope_frame ext h).equivocating_indices

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

theorem scheduled_envelope_cases {w n : ℕ}
    {signed : SignedExecutionPayloadEnvelope R}
    {observation : EnvelopeObservation R}
    (h : Event.execution_payload_envelope signed observation ∈ run.schedule w n) :
    signed = childEnvelope ∧ observation = payloadObservation ∧
      (n = 168 ∨ n = 170 ∨ n = 180) := by
  rw [schedule_by_slot] at h
  have htime := Nat.div_add_mod n 12
  unfold slotEvents at h
  split_ifs at h with h4 h6 h14 h170 h0 h1 hslot14 hw1 hslot15
  · simp at h
  · simp at h
  · simp at h
  · simp at h
    exact ⟨h.1, h.2, Or.inr (Or.inl (by omega))⟩
  · simp at h
  · simp at h
  · simp at h
    exact ⟨h.1, h.2, Or.inl (by omega)⟩
  · simp at h
    exact ⟨h.1, h.2, Or.inr (Or.inr (by omega))⟩
  · unfold witnessSchedule at h
    split_ifs at h <;> simp at h
  · simp at h

private theorem no_verified_at_167 :
    ∀ w : Fin 3, ∀ r : R,
      is_payload_verified (run.store cfg ext w.val 167) r = false := by
  set_option maxRecDepth 50000 in decide

private theorem no_verified_at_169_node1 :
    is_payload_verified (run.store cfg ext 1 169) childRoot = false := by
  set_option maxRecDepth 50000 in decide

private theorem only_child_verified_at_191 :
    ∀ w : Fin 3, ∀ r : R, r ≠ childRoot →
      is_payload_verified (run.store cfg ext w.val 191) r = false := by
  set_option maxRecDepth 50000 in decide

theorem verified_requires_168 {v n : ℕ} {r : R}
    (h : is_payload_verified (run.store cfg ext v n) r = true) :
    168 ≤ n := by
  by_contra hn
  have hlate := run.is_payload_verified_mono cfg ext v
    (show n ≤ 167 by omega) h
  rw [store_nodeClass] at hlate
  have hfalse := no_verified_at_167 ⟨nodeClass v, nodeClass_lt v⟩ r
  rw [hfalse] at hlate
  cases hlate

theorem verified_root_child {v n : ℕ} {r : R}
    (hn : n < 192)
    (h : is_payload_verified (run.store cfg ext v n) r = true) :
    r = childRoot := by
  by_contra hne
  have hlate := run.is_payload_verified_mono cfg ext v
    (show n ≤ 191 by omega) h
  rw [store_nodeClass] at hlate
  have hfalse := only_child_verified_at_191
    ⟨nodeClass v, nodeClass_lt v⟩ r hne
  rw [hfalse] at hlate
  cases hlate

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

theorem envelope_delivery : DeadlineEnvelopeDelivery cfg ext run := by
  intro v hv n r hn hverified _hr _hdeadline w hw m hm hboundary _hlt
  have hn192 := horizon_time hn
  have hm192 := horizon_time hm
  have hn168 := verified_requires_168 hverified
  have hrchild := verified_root_child hn192 hverified
  subst r
  have hslot14 : n / 12 = 14 := by
    have hb := hboundary
    rw [slot_start_eq, slot_at_eq] at hb
    omega
  have hn180 : n < 180 := by omega
  have hboundary180 :
      run.slot_start cfg (run.slot_at cfg n + 1) = 180 := by
    rw [slot_start_eq, slot_at_eq, hslot14]
  have hm180 : 180 ≤ m := by simpa [hboundary180] using hboundary
  have hsource : ∃ k, k ≤ n ∧
      Event.execution_payload_envelope childEnvelope payloadObservation ∈
        run.schedule v k := by
    by_cases hv1 : v = 1
    · subst v
      have hn170 : 170 ≤ n := by
        by_contra hlt
        have hlate := run.is_payload_verified_mono cfg ext 1
          (show n ≤ 169 by omega) hverified
        rw [no_verified_at_169_node1] at hlate
        cases hlate
      exact ⟨170, hn170, by simp [run, schedule]⟩
    · exact ⟨168, by omega, by simp [run, schedule, hv1]⟩
  obtain ⟨k, hk, hsourceEvent⟩ := hsource
  right
  refine ⟨180, k, childEnvelope, payloadObservation, payloadObservation,
    [], [.attestation vote14 false], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact hk
  · exact hsourceEvent
  · rfl
  · simp [ext]
  · simp [ext]
  · simp [run, schedule]
  · simpa using (on_tick_storeLE cfg
      (run.store cfg ext w 179) (run.time_at 180)).1
        (child_known_after14 w (by decide : 14 ≤ 179))
  · intro hd a pre suf hs
    have hs' :
        [Event.execution_payload_envelope childEnvelope payloadObservation,
          Event.attestation vote14 false] =
            pre ++ Event.attestation a false :: suf := by
      simpa [run, schedule] using hs
    cases pre with
    | nil => simp at hs'
    | cons e tail =>
        cases tail with
        | nil =>
            simp at hs'
            rcases hs' with ⟨rfl, rfl, rfl⟩
            exact ⟨[], rfl⟩
        | cons e' tail' => simp at hs'

theorem data_availability_relay : DeadlineDataAvailabilityRelay cfg ext run := by
  intro v hv k n signed sourceObservation hk hn hevent havailable hdeadline
    w hw m hm hboundary hlt receiverSigned receiverObservation hroot hreceiver
  obtain ⟨rfl, _, _⟩ := scheduled_envelope_cases hevent
  simp [ext, childEnvelope]

theorem delivery_lookahead : HorizonVoteDeliveryLookahead cfg run := by
  constructor
  intro v hv s n a hs hn hvote _hdeadline w hw
  exact vote_at_boundary hvote w

theorem next_slot_synchrony : NextSlotSynchronyPremises cfg ext run := by
  exact synchrony.toPaperSafetySynchrony cfg ext
    delivery_lookahead envelope_delivery data_availability_relay

theorem static_validators : StaticValidatorSet cfg run :=
  ⟨time_within (by decide), witnessStaticValidatorSet.activity_constant⟩

theorem byzantine_bound : ByzantineWeightPremises cfg run := by
  constructor
  · exact witnessByzantineBound.effective_balance_quantized
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

theorem phase0_source : Phase0SourceCoherence cfg ext :=
  ⟨TwelveSecondSynchronyWitness.phase0_source.process_slots_current_justified,
    TwelveSecondSynchronyWitness.phase0_source.state_transition_current_justified⟩

theorem phase0_boundary_source : Phase0BoundarySourceCoherence cfg ext :=
  ⟨TwelveSecondSynchronyWitness.phase0_boundary_source.process_slots_one_boundary,
    TwelveSecondSynchronyWitness.phase0_boundary_source.process_slots_same_target_epoch,
    TwelveSecondSynchronyWitness.phase0_boundary_source.state_transition_process_slots,
    TwelveSecondSynchronyWitness.phase0_boundary_source.process_slots_checkpoint_epoch,
    TwelveSecondSynchronyWitness.phase0_boundary_source.process_slots_two_boundaries⟩

theorem balance_floor : 2 * cfg.effective_balance_increment ≤
    run.weight (run.anchorActiveValidators cfg) := by decide

theorem epoch_ends_fit : EpochEndsFitUint64 cfg := TwelveSecondSynchronyWitness.epoch_ends_fit

theorem anchor_boundary : Execution.InitialAnchorAtEpochBoundary
    (cfg := cfg) (E := run) (anchor := anchorCheckpoint) := by
  unfold Execution.InitialAnchorAtEpochBoundary
  decide

theorem witnessStore_registryConstant (v : ValidatorIndex) (n : ℕ) :
    RegistryConstant run.registry
      (run.store cfg ext v n) := by
  induction n with
  | zero =>
      exact run.genesis_registryConstant cfg
        ⟨anchorState, anchorSignedBlock, rfl⟩
  | succ n ih =>
      change RegistryConstant run.registry
        ((run.schedule v (n + 1)).foldl
          (fun store event =>
            (apply_event cfg ext store event).getD store)
          (on_tick cfg
            (run.store cfg ext v n)
            (run.time_at (n + 1))))
      refine registryConstant_foldl
        (fun store event hstore => apply_event_getD_registryConstant
          cfg ext witnessTransition_registry
          witnessProcessSlots_registry store event hstore) _ _ ?_
      exact on_tick_registryConstant cfg _ _ ih

theorem witnessCausalStore_registryConstant {store : Store WitnessRoot}
    (hstore : run.ScheduledPrefixStore cfg ext store) :
    RegistryConstant run.registry store := by
  cases hstore with
  | genesis =>
      exact run.genesis_registryConstant cfg
        ⟨anchorState, anchorSignedBlock, rfl⟩
  | scheduledPrefix p =>
      unfold Execution.ScheduledEventPrefix.store
      refine registryConstant_foldl
        (fun store event hstore => apply_event_getD_registryConstant
          cfg ext witnessTransition_registry
          witnessProcessSlots_registry store event hstore) _ _ ?_
      exact on_tick_registryConstant cfg _ _
        (witnessStore_registryConstant p.node p.previousSecond)

theorem witnessReachableValidationState_nonempty {state : BeaconState WitnessRoot}
    (hstate : run.ReachableValidationState
      cfg ext state) : state.validators ≠ [] := by
  obtain ⟨store, hstore, hstate⟩ := hstate
  have hreg := witnessCausalStore_registryConstant
    (hstore.causal cfg ext)
  have heq : state.validators = run.registry := by
    rcases hstate with ⟨root, hroot, rfl⟩ | ⟨checkpoint, hcheckpoint, rfl⟩
    · exact hreg.1 root hroot
    · exact hreg.2 checkpoint hcheckpoint
  rw [heq]
  decide

theorem extCoherence :
    BeaconExternalsPremises cfg ext run := by
  have hregistry : ∀ state, run.ReachableValidationState cfg ext state →
      state.validators = run.registry := by
    intro state hstate
    obtain ⟨store, hstore, hstate⟩ := hstate
    have hreg := witnessCausalStore_registryConstant (hstore.causal cfg ext)
    rcases hstate with ⟨root, hroot, rfl⟩ | ⟨checkpoint, hcheckpoint, rfl⟩
    · exact hreg.1 root hroot
    · exact hreg.2 checkpoint hcheckpoint
  constructor
  · exact witnessExternalsCoherence.process_slots_slot
  · intro state hscope
    rcases hscope with hreachable | ⟨base, slot, hreachable, _hslot, rfl⟩
    · exact hregistry state hreachable
    · simp only [ext, TwelveSecondSynchronyWitness.ext]
      split_ifs
      · simp only [witnessPJF]
        split_ifs <;> simpa using (hregistry base hreachable)
      · simpa using (hregistry base hreachable)
  · exact witnessExternalsCoherence.state_transition_slot
  · exact witnessExternalsCoherence.state_transition_pre_slot_lt
  · exact witnessExternalsCoherence.state_transition_checkpoint_epoch
  · exact witnessExternalsCoherence.pjf_checkpoint_epoch
  · exact witnessExternalsCoherence.anchor_state_checkpoint_epoch
  · intro v hv n s hn hs
    simp [get_slot_committee, ext, TwelveSecondSynchronyWitness.ext, witnessExternals, run,
      witnessCommittee]
  · intro state a hreachable v hv hsingle hcommittee hvote
    rcases hvote with ⟨m, a', hvote, hdata⟩
    let s := a.data.slot
    have hvoteS : run.vote v s = some (m, a') := by
      simpa [s] using hvote
    obtain ⟨hs, hvmod, hm, ha'⟩ := recorded_vote_some_iff.mp hvoteS
    subst m
    subst a'
    have ha : a = vote s := by
      cases a
      simp_all [vote]
    have hmem : a ∈ groundVotes := by
      rw [ha]
      exact vote_mem_ground hs
    exact (witness_valid_iff state a).2
      ⟨witnessReachableValidationState_nonempty hreachable, hmem⟩
  · intro state a _hreachable hvalid v hv hvin
    have haGround := ((witness_valid_iff state a).mp hvalid).2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    have hvmod : v = s % 4 := by simpa [vote] using hvin
    refine ⟨12 * s + 3, vote s, ?_, rfl⟩
    rw [vote_data_slot]
    exact recorded_vote_some_iff.mpr ⟨hs, hvmod, rfl, rfl⟩
  · intro store store' a ifb _hpost hh i hi
    simp only [on_attestation] at hh
    split_ifs at hh with hv hvi
    cases hh
    have haGround := ((witness_valid_iff _ a).mp hvi).2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    have hi' : i = s % 4 := by simpa [vote] using hi
    rw [vote_data_slot]
    simpa [run, witnessCommittee, hi']
  · exact witnessExternalsCoherence.committee_assignment_unique
  · exact witnessExternalsCoherence.committee_coverage
  · exact witnessExternalsCoherence.committee_members_active

  · exact witnessExternalsCoherence.valid_attestation_default
  · intro state slot a _hreachable _hlt _hslotH _hreg
    change decide ((witnessExternals.process_slots state slot).validators ≠ [] ∧
      a ∈ groundVotes) = decide (state.validators ≠ [] ∧ a ∈ groundVotes)
    rw [witnessProcessSlots_registry]
  · intro state signed o o'
    rfl

theorem scheduled_prefix_premises : run.ScheduledExecutionPremises cfg ext := by
  exact
    { whole_seconds := by decide
      wellFormed := well_formed
      externals_coherence := extCoherence
      honest_behavior := honest_behavior
      genesis := ⟨anchorState, anchorSignedBlock, rfl, rfl, ⟨rfl, rfl⟩, by decide⟩ }

end FastConfirmation.Spec.FullTwelveEnvelopeWitness
end
