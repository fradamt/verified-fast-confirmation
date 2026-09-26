module
public import FastConfirmationInternal.FFG.ConcreteJustification

@[expose] public section

/-! Proves result characterizations and field frames of the concrete FFG
transition functions: ring reads, slot and epoch processing, justification
weighing, attestation flags, and block processing. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-- Runs `omega` after unfolding the `ℕ` abbreviations of the beacon types. -/
macro "beacon_omega" : tactic =>
  `(tactic| ((try dsimp only [Epoch, Slot, Gwei, ValidatorIndex, CommitteeIndex] at *); omega))

theorem except_bind_eq_ok {ε : Type u} {α β : Type v} {x : Except ε α} {f : α → Except ε β}
    {b : β} : x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem except_pure_eq_ok {ε : Type u} {α : Type v} {a b : α} :
    (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem guard_eq_ok {c : Bool} {e : Error} {u : PUnit} : guard c e = .ok u ↔ c = true := by
  cases c <;> simp [guard]

/-! ### Ring reads -/

theorem get_block_root_at_slot_eq_ok {preset : FFGPreset} {state : FFGBeaconState Root}
    {slot : Slot} {root : Root} :
    get_block_root_at_slot preset state slot = .ok root ↔
      slot + preset.slots_per_historical_root ≤ UINT64_MAX ∧ slot < state.slot ∧
      state.slot ≤ slot + preset.slots_per_historical_root ∧
      state.block_roots.length = preset.slots_per_historical_root ∧
      state.block_roots[slot % preset.slots_per_historical_root]? = some root := by
  unfold get_block_root_at_slot
  simp only [except_bind_eq_ok, guard_eq_ok, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨_, h1, _, ⟨h2, h3⟩, _, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    revert h5
    cases state.block_roots[slot % preset.slots_per_historical_root]? <;>
      simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨⟩, h1, ⟨⟩, ⟨h2, h3⟩, ⟨⟩, h4, ?_⟩
    rw [h5]
    rfl

theorem get_block_root_eq_ok {cfg : Config} {preset : FFGPreset} {state : FFGBeaconState Root}
    {epoch : Epoch} {root : Root} :
    get_block_root cfg preset state epoch = .ok root ↔
      epoch * cfg.slots_per_epoch ≤ UINT64_MAX ∧
      get_block_root_at_slot preset state (compute_start_slot_at_epoch cfg epoch) = .ok root := by
  unfold get_block_root
  simp only [except_bind_eq_ok, guard_eq_ok, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟩, h1, h2⟩

/-- Ring reads depend only on the slot and the ring. -/
theorem get_block_root_congr {cfg : Config} {preset : FFGPreset}
    {state other : FFGBeaconState Root} (hslot : other.slot = state.slot)
    (hroots : other.block_roots = state.block_roots) (epoch : Epoch) :
    get_block_root cfg preset other epoch = get_block_root cfg preset state epoch := by
  unfold get_block_root get_block_root_at_slot
  rw [hslot, hroots]

/-! ### Slot processing -/

theorem process_slot_eq_ok {preset : FFGPreset} {state next : FFGBeaconState Root} :
    process_slot preset state = .ok next ↔
      state.block_roots.length = preset.slots_per_historical_root ∧
      state.execution_payload_availability.length = preset.slots_per_historical_root ∧
      next = { state with
        block_roots := state.block_roots.set (state.slot % preset.slots_per_historical_root)
          state.latest_block_header.root
        execution_payload_availability := state.execution_payload_availability.set
          ((state.slot + 1) % preset.slots_per_historical_root) false } := by
  unfold process_slot
  simp only [except_bind_eq_ok, guard_eq_ok, Bool.and_eq_true, beq_iff_eq, except_pure_eq_ok]
  constructor
  · rintro ⟨_, ⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟩, ⟨h1, h2⟩, h3.symm⟩

/-- One iteration of the `process_slots` loop. -/
def slotStep (cfg : Config) (preset : FFGPreset) (state : FFGBeaconState Root) :
    Checked (FFGBeaconState Root) := do
  let state ← process_slot preset state
  let state ← if (state.slot + 1) % cfg.slots_per_epoch == 0 then
    process_epoch cfg preset state else .ok state
  return { state with slot := state.slot + 1 }

theorem process_slots_eq_ok {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {target : Slot} :
    process_slots cfg preset state target = .ok next ↔
      target ≤ UINT64_MAX ∧ state.slot < target ∧
      (List.range (target - state.slot)).foldlM (fun s _ => slotStep cfg preset s) state =
        .ok next := by
  unfold process_slots
  simp only [except_bind_eq_ok, guard_eq_ok, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h1, _, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟩, h1, ⟨⟩, h2, h3⟩

/-! ### Epoch processing -/

theorem process_epoch_eq_ok {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} :
    process_epoch cfg preset state = .ok next ↔
      ∃ mid, process_justification_and_finalization cfg preset state = .ok mid ∧
        next = process_participation_flag_updates mid := by
  unfold process_epoch
  simp only [except_bind_eq_ok, except_pure_eq_ok, process_inactivity_updates,
    process_rewards_and_penalties, process_registry_updates, process_slashings,
    process_eth1_data_reset, process_pending_deposits, process_pending_consolidations,
    process_builder_pending_payments, process_effective_balance_updates,
    process_slashings_reset, process_randao_mixes_reset,
    process_historical_summaries_update, process_sync_committee_updates,
    process_proposer_lookahead, process_ptc_window]
  constructor
  · rintro ⟨mid, h1, h2⟩
    exact ⟨mid, h1, h2.symm⟩
  · rintro ⟨mid, h1, h2⟩
    exact ⟨mid, h1, h2.symm⟩

theorem process_justification_and_finalization_eq_ok {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root}
    (h : process_justification_and_finalization cfg preset state = .ok next) :
    (compute_epoch_at_slot cfg state.slot ≤ 1 ∧ next = state) ∨
    (2 ≤ compute_epoch_at_slot cfg state.slot ∧
      ∃ previous current,
        get_unslashed_participating_indices cfg state 1 (get_previous_epoch cfg state) =
          .ok previous ∧
        get_unslashed_participating_indices cfg state 1
          (compute_epoch_at_slot cfg state.slot) = .ok current ∧
        weigh_justification_and_finalization cfg preset state
          (ConcreteFFG.get_total_active_balance cfg state)
          (ConcreteFFG.get_total_balance cfg state previous)
          (ConcreteFFG.get_total_balance cfg state current) = .ok next) := by
  unfold process_justification_and_finalization at h
  by_cases hE : compute_epoch_at_slot cfg state.slot ≤ 1
  · left
    simp only [hE, if_true] at h
    exact ⟨hE, (except_pure_eq_ok.mp h).symm⟩
  · right
    simp only [hE, if_false, except_bind_eq_ok] at h
    obtain ⟨_, -, previous, hp, current, hc, hw⟩ := h
    exact ⟨Nat.lt_of_not_le hE, previous, current, hp, hc, hw⟩

/-- The outcome of `weigh_justification_and_finalization`: the previous
justified checkpoint takes the old current one; the new current checkpoint is
the old one or a checkpoint read at the previous or current epoch after a
passing two-thirds test; the finalized checkpoint is the old one or one of the
two old justified checkpoints. -/
theorem weigh_justification_and_finalization_eq_ok {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {total previous current : Gwei}
    (h : weigh_justification_and_finalization cfg preset state total previous current =
      .ok next) :
    ∃ bits justified finalized,
      next = { state with
        justification_bits := bits
        previous_justified_checkpoint := state.current_justified_checkpoint
        current_justified_checkpoint := justified
        finalized_checkpoint := finalized } ∧
      (justified = state.current_justified_checkpoint ∨
        (total * 2 ≤ previous * 3 ∧ justified.epoch = get_previous_epoch cfg state ∧
          get_block_root cfg preset state justified.epoch = .ok justified.root) ∨
        (total * 2 ≤ current * 3 ∧ justified.epoch = compute_epoch_at_slot cfg state.slot ∧
          get_block_root cfg preset state justified.epoch = .ok justified.root)) ∧
      (finalized = state.finalized_checkpoint ∨
        finalized = state.previous_justified_checkpoint ∨
        finalized = state.current_justified_checkpoint) := by
  unfold weigh_justification_and_finalization at h
  rw [except_bind_eq_ok] at h
  obtain ⟨_, -, h⟩ := h
  dsimp only at h
  simp only [pure_bind] at h
  by_cases c1 : previous * 3 ≥ total * 2
  · rw [if_pos c1] at h
    rw [except_bind_eq_ok] at h
    obtain ⟨root1, hr1, h⟩ := h
    by_cases c2 : current * 3 ≥ total * 2
    · rw [if_pos c2] at h
      rw [except_bind_eq_ok] at h
      obtain ⟨root2, hr2, h⟩ := h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨_, _, _, rfl, Or.inr (Or.inr ⟨c2, rfl, hr2⟩), ?_⟩
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · rw [if_neg c2] at h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨_, _, _, rfl, Or.inr (Or.inl ⟨c1, rfl, hr1⟩), ?_⟩
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  · rw [if_neg c1] at h
    by_cases c2 : current * 3 ≥ total * 2
    · rw [if_pos c2] at h
      rw [except_bind_eq_ok] at h
      obtain ⟨root2, hr2, h⟩ := h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨_, _, _, rfl, Or.inr (Or.inr ⟨c2, rfl, hr2⟩), ?_⟩
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · rw [if_neg c2] at h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨_, _, _, rfl, Or.inl rfl, ?_⟩
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

/-! ### Attestation flags -/

theorem checkpoint_eq_of_beq [DecidableEq Root] {a b : Checkpoint Root}
    (h : (a.epoch == b.epoch && a.root == b.root) = true) : a = b := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases a; cases b
  simp_all

/-- The flag computation asserts the source check. Its target flag is set
exactly when the target root equals the epoch checkpoint root read from the
state. All flag indices are below three. -/
theorem get_attestation_participation_flag_indices_eq_ok [DecidableEq Root]
    {cfg : Config} {preset : FFGPreset} {state : FFGBeaconState Root}
    {data : AttestationData Root} {delay parentSlot : ℕ} {flags : List ℕ}
    (h : get_attestation_participation_flag_indices cfg preset state data delay parentSlot =
      .ok flags) :
    data.source = (if data.target.epoch = compute_epoch_at_slot cfg state.slot then
        state.current_justified_checkpoint else state.previous_justified_checkpoint) ∧
    (∀ f ∈ flags, f ≤ 2) ∧
    (1 ∈ flags ↔ get_block_root cfg preset state data.target.epoch = .ok data.target.root) := by
  unfold get_attestation_participation_flag_indices at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨targetRoot, hroot, same, -, h⟩ := h
  have hsrc : ∀ {u : PUnit}, guard
      (data.source.epoch ==
          (if (data.target.epoch == compute_epoch_at_slot cfg state.slot) = true then
              state.current_justified_checkpoint
            else state.previous_justified_checkpoint).epoch &&
        data.source.root ==
          (if (data.target.epoch == compute_epoch_at_slot cfg state.slot) = true then
              state.current_justified_checkpoint
            else state.previous_justified_checkpoint).root) Error.source = .ok u →
      data.source = (if data.target.epoch = compute_epoch_at_slot cfg state.slot then
        state.current_justified_checkpoint else state.previous_justified_checkpoint) := by
    intro u hu
    have := checkpoint_eq_of_beq (guard_eq_ok.mp hu)
    rw [this]
    simp only [beq_iff_eq]
  have hroot' : ∀ r, get_block_root cfg preset state data.target.epoch = .ok r ↔
      r = targetRoot := by
    intro r
    rw [hroot]
    constructor
    · intro e; cases e; rfl
    · intro e; rw [e]
  rw [hroot' data.target.root]
  split at h
  · simp only [except_bind_eq_ok, pure_bind] at h
    obtain ⟨_, -, headRoot, -, _, hs, h⟩ := h
    refine ⟨hsrc hs, ?_⟩
    have hs' := guard_eq_ok.mp hs
    simp only [hs', Bool.true_and] at h
    repeat' split at h
    all_goals
      simp only [except_pure_eq_ok] at h
      subst h
      simp_all
  · simp only [except_bind_eq_ok, pure_bind] at h
    obtain ⟨headRoot, -, _, hs, h⟩ := h
    refine ⟨hsrc hs, ?_⟩
    have hs' := guard_eq_ok.mp hs
    simp only [hs', Bool.true_and] at h
    repeat' split at h
    all_goals
      simp only [except_pure_eq_ok] at h
      subst h
      simp_all

theorem has_flag_add_flag {x f : ℕ} (hf : f ≤ 2) :
    has_flag (add_flag x f) 1 = true ↔ has_flag x 1 = true ∨ f = 1 := by
  interval_cases f <;> simp only [add_flag, has_flag, beq_iff_eq, Nat.reducePow, Nat.div_one] <;>
    split_ifs <;> simp only [or_false, or_true, Nat.reduceEqDiff, iff_true] <;> omega

theorem has_flag_foldl_add_flag {flags : List ℕ} (hflags : ∀ f ∈ flags, f ≤ 2) (x : ℕ) :
    has_flag (flags.foldl add_flag x) 1 = true ↔ has_flag x 1 = true ∨ 1 ∈ flags := by
  induction flags generalizing x with
  | nil => simp
  | cons f flags ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih (fun g hg => hflags g (List.mem_cons_of_mem f hg)),
      has_flag_add_flag (hflags f List.mem_cons_self)]
    constructor
    · rintro ((hx | rfl) | hm)
      · exact Or.inl hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hm)
    · rintro (hx | rfl | hm)
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hm

/-- The participation write of `process_attestation`. -/
def participationUpdate (flags : List ℕ) (indices : List ValidatorIndex)
    (participation : List ℕ) : List ℕ :=
  indices.foldl (fun values i => values.set i (flags.foldl add_flag (values.getD i 0)))
    participation

theorem participationUpdate_length (flags : List ℕ) (indices : List ValidatorIndex)
    (participation : List ℕ) :
    (participationUpdate flags indices participation).length = participation.length := by
  induction indices generalizing participation with
  | nil => rfl
  | cons i indices ih =>
    simp only [participationUpdate, List.foldl_cons] at ih ⊢
    rw [ih, List.length_set]

theorem has_flag_participationUpdate {flags : List ℕ} (hflags : ∀ f ∈ flags, f ≤ 2)
    (indices : List ValidatorIndex) (participation : List ℕ) (i : ℕ) :
    has_flag ((participationUpdate flags indices participation).getD i 0) 1 = true ↔
      has_flag (participation.getD i 0) 1 = true ∨
        (i ∈ indices ∧ i < participation.length ∧ 1 ∈ flags) := by
  induction indices generalizing participation with
  | nil => simp [participationUpdate]
  | cons j indices ih =>
    simp only [participationUpdate, List.foldl_cons] at ih ⊢
    rw [ih, List.length_set]
    by_cases hij : i = j
    · subst hij
      by_cases hlt : i < participation.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt, Option.getD_some,
          List.mem_cons, true_or, hlt, true_and]
        rw [has_flag_foldl_add_flag hflags]
        tauto
      · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hlt)]
        simp [hlt]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hij), List.mem_cons,
        hij, false_or]

/-! ### Attestation processing -/

/-- A successful `process_attestation` call: the flags come from the state on
which it ran, the target is in the current or previous epoch, every named
validator is in the registry, and only the matching participation array
receives the flags. -/
theorem process_attestation_eq_ok [DecidableEq Root] {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {vote : FFGWireAttestation Root} {parentSlot : Slot}
    (h : process_attestation cfg preset schedule state vote parentSlot = .ok next) :
    ∃ flags,
      get_attestation_participation_flag_indices cfg preset state vote.data
        (state.slot - vote.data.slot) parentSlot = .ok flags ∧
      (vote.data.target.epoch = compute_epoch_at_slot cfg state.slot ∨
        vote.data.target.epoch = get_previous_epoch cfg state) ∧
      (∀ i ∈ get_attesting_indices schedule vote, i < state.validators.length) ∧
      (vote.data.target.epoch = compute_epoch_at_slot cfg state.slot →
        state.current_epoch_participation.length = state.validators.length ∧
        next = { state with current_epoch_participation := (participationUpdate flags
          ((get_attesting_indices schedule vote).sort (· ≤ ·))
          state.current_epoch_participation) }) ∧
      (vote.data.target.epoch ≠ compute_epoch_at_slot cfg state.slot →
        state.previous_epoch_participation.length = state.validators.length ∧
        next = { state with previous_epoch_participation := (participationUpdate flags
          ((get_attesting_indices schedule vote).sort (· ≤ ·))
          state.previous_epoch_participation) }) := by
  unfold process_attestation at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨_, htarget, _, -, _, -, _, -, _, -, _, -, _, -, _, -, flags, hflags, _, hvalid,
    _, hlen, h⟩ := h
  refine ⟨flags, hflags, ?_, ?_, ?_, ?_⟩
  · have := guard_eq_ok.mp htarget
    simpa only [Bool.or_eq_true, beq_iff_eq] using this
  · intro i hi
    have := guard_eq_ok.mp hvalid
    simp only [is_valid_indexed_attestation, get_indexed_attestation, Bool.and_eq_true,
      List.all_eq_true, decide_eq_true_eq] at this
    exact this.2 i ((Finset.mem_sort _).mpr hi)
  · intro hcur
    have hl := guard_eq_ok.mp hlen
    simp only [hcur, beq_self_eq_true, if_true, beq_iff_eq] at hl h
    exact ⟨hl, (except_pure_eq_ok.mp h).symm⟩
  · intro hcur
    have hl := guard_eq_ok.mp hlen
    have hne : (vote.data.target.epoch == compute_epoch_at_slot cfg state.slot) = false := by
      simpa using hcur
    simp only [hne, Bool.false_eq_true, if_false, beq_iff_eq] at hl h
    exact ⟨hl, (except_pure_eq_ok.mp h).symm⟩

/-! ### Block processing -/

theorem process_parent_execution_payload_eq_ok [DecidableEq Root] {preset : FFGPreset}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    (h : process_parent_execution_payload preset state block = .ok next) :
    ∃ availability hash, next = { state with
      execution_payload_availability := availability
      latest_block_hash := hash } := by
  unfold process_parent_execution_payload at h
  split at h
  · simp only [except_bind_eq_ok, except_pure_eq_ok] at h
    obtain ⟨_, -, rfl⟩ := h
    exact ⟨_, _, rfl⟩
  · simp only [except_bind_eq_ok, except_pure_eq_ok, pure_bind] at h
    obtain ⟨_, -, rfl⟩ := h
    exact ⟨_, _, rfl⟩

theorem process_block_header_eq_ok [DecidableEq Root] {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root} (h : process_block_header state block = .ok next) :
    block.slot = state.slot ∧ state.latest_block_header.slot < block.slot ∧
      block.parent_root = state.latest_block_header.root ∧
      next = { state with latest_block_header :=
        ⟨block.slot, block.proposer_index, block.parent_root, block.root⟩ } := by
  unfold process_block_header at h
  simp only [except_bind_eq_ok, except_pure_eq_ok] at h
  obtain ⟨_, h1, _, h2, _, h3, _, -, _, -, h⟩ := h
  have h1 := guard_eq_ok.mp h1
  have h2 := guard_eq_ok.mp h2
  have h3 := guard_eq_ok.mp h3
  simp only [beq_iff_eq, decide_eq_true_eq] at h1 h2 h3
  exact ⟨h1, h2, h3, h.symm⟩

theorem process_operations_eq_ok [DecidableEq Root] {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root} {parentSlot : Slot}
    (h : process_operations cfg preset schedule state block parentSlot = .ok next) :
    block.attestations.foldlM (fun state vote =>
      process_attestation cfg preset schedule state vote parentSlot) state = .ok next := by
  unfold process_operations at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨_, -, _, -, h⟩ := h
  exact h

theorem process_block_eq_ok [DecidableEq Root] {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root}
    (h : process_block cfg preset schedule state block = .ok next) :
    ∃ paid headed,
      process_parent_execution_payload preset state block = .ok paid ∧
      process_block_header paid block = .ok headed ∧
      block.attestations.foldlM (fun s vote =>
        process_attestation cfg preset schedule s vote state.latest_block_header.slot)
        (process_execution_payload_bid headed block) = .ok next := by
  unfold process_block at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨paid, hpaid, headed, hheaded, h⟩ := h
  exact ⟨paid, headed, hpaid, hheaded, process_operations_eq_ok h⟩

theorem state_transition_eq_ok [DecidableEq Root] {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {oracle : BlockValidityOracle Root}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    (h : state_transition cfg preset schedule oracle state block = .ok next) :
    ∃ atSlot, process_slots cfg preset state block.slot = .ok atSlot ∧
      process_block cfg preset schedule atSlot block = .ok next ∧
      oracle.accepts atSlot block next = true := by
  unfold state_transition at h
  simp only [except_bind_eq_ok, except_pure_eq_ok] at h
  obtain ⟨_, -, _, -, atSlot, hslots, result, hblock, _, hacc, rfl⟩ := h
  exact ⟨atSlot, hslots, hblock, guard_eq_ok.mp hacc⟩

/-- The recorded body votes of a successful transition are the ordered calls
of its attestation fold. -/
theorem blockVotes_eq [DecidableEq Root] {S : FFGSetup Root}
    {state atSlot paid headed : FFGBeaconState Root} {block : FFGWireBlock Root}
    (hslots : process_slots S.cfg S.preset state block.slot = .ok atSlot)
    (hpaid : process_parent_execution_payload S.preset atSlot block = .ok paid)
    (hheaded : process_block_header paid block = .ok headed) :
    blockVotes S state block = attestationVotes S block atSlot.latest_block_header.slot
      (process_execution_payload_bid headed block) block.attestations := by
  have hb : (process_parent_execution_payload S.preset atSlot block >>=
      fun state => process_block_header state block) = .ok headed := by
    rw [hpaid]
    exact hheaded
  unfold blockVotes
  rw [hslots]
  dsimp only
  rw [hb]

end FastConfirmation.Spec.ConcreteFFG

end
