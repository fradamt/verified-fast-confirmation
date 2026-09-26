module
public import FastConfirmationProofs.FFG.Concrete.FinalizationSoundness

@[expose] public section

/-! Proves the current-justified results of concrete slot processing on
reachable states in the fixed scope. One PJF pass sets the checkpoint by the
formula `cjFormula` of the two participation tests. `process_slots` applies
this formula once per crossed epoch boundary (`cjRun`), and both calls
succeed. These are the Python timing facts behind the Phase0 source laws:
realized versus eager justification, the epoch 0/1 return, and skipped
boundaries. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### Array lengths of reachable states -/

/-- The fixed array lengths that the transition guards check. -/
structure LengthsOK (S : FFGSetup Root) (state : FFGBeaconState Root) : Prop where
  bits : state.justification_bits.length = 4
  previous : state.previous_epoch_participation.length = state.validators.length
  current : state.current_epoch_participation.length = state.validators.length
  roots : state.block_roots.length = S.preset.slots_per_historical_root
  availability : state.execution_payload_availability.length =
    S.preset.slots_per_historical_root

omit [DecidableEq Root] in
theorem lengthsOK_genesis (S : FFGSetup Root) : LengthsOK S S.genesis where
  bits := rfl
  previous := by simp [FFGSetup.genesis, FFGBeaconState.genesis]
  current := by simp [FFGSetup.genesis, FFGBeaconState.genesis]
  roots := by simp [FFGSetup.genesis, FFGBeaconState.genesis]
  availability := by simp [FFGSetup.genesis, FFGBeaconState.genesis]

omit [DecidableEq Root] in
theorem lengthsOK_pjf {S : FFGSetup Root} {state next : FFGBeaconState Root}
    (hlen : LengthsOK S state)
    (h : process_justification_and_finalization S.cfg S.preset state = .ok next) :
    LengthsOK S next := by
  by_cases hE : 2 ≤ compute_epoch_at_slot S.cfg state.slot
  · obtain ⟨_, _, _, _, _, _, _, _, _, hbits, _, _⟩ :=
      process_justification_and_finalization_bits h hE
    obtain ⟨_, _, _, _, rfl, _⟩ := process_justification_and_finalization_outcome h
    exact ⟨by rw [hbits]; rfl, hlen.previous, hlen.current, hlen.roots, hlen.availability⟩
  · rcases process_justification_and_finalization_eq_ok h with ⟨-, rfl⟩ | ⟨hE', -⟩
    · exact hlen
    · exact absurd hE' hE

omit [DecidableEq Root] in
theorem lengthsOK_slotStep {S : FFGSetup Root} {state next : FFGBeaconState Root}
    (hlen : LengthsOK S state) (h : slotStep S.cfg S.preset state = .ok next) :
    LengthsOK S next := by
  obtain ⟨s1, hs1, hcase⟩ := slotStep_eq_ok h
  obtain ⟨-, -, rfl⟩ := process_slot_eq_ok.mp hs1
  have h1 : LengthsOK S { state with
      block_roots := state.block_roots.set (state.slot % S.preset.slots_per_historical_root)
        state.latest_block_header.root
      execution_payload_availability := state.execution_payload_availability.set
        ((state.slot + 1) % S.preset.slots_per_historical_root) false } :=
    ⟨hlen.bits, hlen.previous, hlen.current, by simp [hlen.roots],
      by simp [hlen.availability]⟩
  rcases hcase with ⟨-, rfl⟩ | ⟨-, mid, hmid, rfl⟩
  · exact ⟨h1.bits, h1.previous, h1.current, h1.roots, h1.availability⟩
  · have h2 := lengthsOK_pjf h1 hmid
    obtain ⟨_, _, _, _, hmideq, -⟩ := process_justification_and_finalization_outcome hmid
    exact ⟨h2.bits, h2.current, by simp [process_participation_flag_updates], h2.roots,
      h2.availability⟩

omit [DecidableEq Root] in
theorem lengthsOK_slotFold {S : FFGSetup Root} :
    ∀ (steps : List ℕ) (state next : FFGBeaconState Root), LengthsOK S state →
      steps.foldlM (fun s _ => slotStep S.cfg S.preset s) state = .ok next →
      LengthsOK S next := by
  intro steps
  induction steps with
  | nil =>
    intro state next hlen h
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    exact hlen
  | cons _ steps ih =>
    intro state next hlen h
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    exact ih mid next (lengthsOK_slotStep hlen hmid) hrest

omit [DecidableEq Root] in
theorem lengthsOK_process_slots {S : FFGSetup Root} {state next : FFGBeaconState Root}
    {target : Slot} (hlen : LengthsOK S state)
    (h : process_slots S.cfg S.preset state target = .ok next) : LengthsOK S next := by
  obtain ⟨-, -, hfold⟩ := process_slots_eq_ok.mp h
  exact lengthsOK_slotFold _ _ _ hlen hfold

theorem lengthsOK_attestationFold {S : FFGSetup Root} {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state next : FFGBeaconState Root),
      LengthsOK S state →
      attestations.foldlM (fun s vote =>
        process_attestation S.cfg S.preset S.schedule s vote parentSlot) state = .ok next →
      LengthsOK S next := by
  intro attestations
  induction attestations with
  | nil =>
    intro state next hlen h
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    exact hlen
  | cons vote attestations ih =>
    intro state next hlen h
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    refine ih mid next ?_ hrest
    obtain ⟨flags, -, -, -, hcur, hprev⟩ := process_attestation_eq_ok hmid
    by_cases hE : vote.data.target.epoch = compute_epoch_at_slot S.cfg state.slot
    · obtain ⟨-, rfl⟩ := hcur hE
      exact ⟨hlen.bits, hlen.previous, by rw [participationUpdate_length]; exact hlen.current,
        hlen.roots, hlen.availability⟩
    · obtain ⟨-, rfl⟩ := hprev hE
      exact ⟨hlen.bits, by rw [participationUpdate_length]; exact hlen.previous, hlen.current,
        hlen.roots, hlen.availability⟩

theorem lengthsOK_process_block {S : FFGSetup Root} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root} (hlen : LengthsOK S state)
    (h : process_block S.cfg S.preset S.schedule state block = .ok next) : LengthsOK S next := by
  obtain ⟨paid, headed, hpaid, hheaded, hfold⟩ := process_block_eq_ok h
  have hpaidlen : LengthsOK S paid := by
    unfold process_parent_execution_payload at hpaid
    split at hpaid
    · simp only [except_bind_eq_ok, except_pure_eq_ok] at hpaid
      obtain ⟨_, -, rfl⟩ := hpaid
      exact hlen
    · simp only [except_bind_eq_ok, except_pure_eq_ok, pure_bind] at hpaid
      obtain ⟨_, -, rfl⟩ := hpaid
      exact ⟨hlen.bits, hlen.previous, hlen.current, hlen.roots,
        by simp [apply_parent_execution_payload, hlen.availability]⟩
  obtain ⟨-, -, -, rfl⟩ := process_block_header_eq_ok hheaded
  refine lengthsOK_attestationFold _ _ _ ?_ hfold
  exact ⟨hpaidlen.bits, hpaidlen.previous, hpaidlen.current, hpaidlen.roots,
    hpaidlen.availability⟩

theorem lengthsOK_state_transition {S : FFGSetup Root} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root} (hlen : LengthsOK S state)
    (h : state_transition S.cfg S.preset S.schedule S.oracle state block = .ok next) :
    LengthsOK S next := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  exact lengthsOK_process_block (lengthsOK_process_slots hlen hslots) hblock

theorem lengthsOK_of_reachable {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {state : FFGBeaconState Root}
    (h : Reachable S blocks votes state) : LengthsOK S state := by
  induction h with
  | genesis => exact lengthsOK_genesis S
  | slots _ hslots ih => exact lengthsOK_process_slots ih hslots
  | block _ _ htrans ih => exact lengthsOK_state_transition ih htrans

/-! ### The checkpoint formula of one PJF pass -/

open Classical in
/-- Registry validators that are active at `epoch`, unslashed, and named by a
target-included body vote of target epoch `epoch`. -/
noncomputable def participants (S : FFGSetup Root) (votes : List (IncludedVote Root))
    (epoch : Epoch) : Finset ValidatorIndex :=
  (Finset.range S.scope.validators.length).filter fun i =>
    is_active_validator (S.scope.validators.getD i default) epoch = true ∧
    (S.scope.validators.getD i default).slashed = false ∧
    ∃ r, TargetIncluded S votes r ∧ i ∈ r.attesters S ∧ r.vote.data.target.epoch = epoch

/-- The two-thirds test of PJF for `epoch`, with the Python increment floor. -/
def EpochTest (S : FFGSetup Root) (votes : List (IncludedVote Root)) (epoch : Epoch) : Prop :=
  max S.cfg.effective_balance_increment S.scope.activeBalance * 2 ≤
    max S.cfg.effective_balance_increment (S.scope.weight (participants S votes epoch)) * 3

open Classical in
/-- The current justified checkpoint after one PJF pass at `epoch` from `c`:
the epoch 0/1 return, then the current-epoch test, then the previous-epoch
test. -/
noncomputable def cjFormula (S : FFGSetup Root) (blocks : List (FFGWireBlock Root))
    (votes : List (IncludedVote Root)) (epoch : Epoch) (c : Checkpoint Root) : Checkpoint Root :=
  if epoch ≤ 1 then c
  else if EpochTest S votes epoch then chainCheckpoint S blocks epoch
  else if EpochTest S votes (epoch - 1) then chainCheckpoint S blocks (epoch - 1)
  else c

/-- The current justified checkpoint after `n` epoch boundaries from epoch
`epoch`, one PJF pass per boundary. -/
noncomputable def cjRun (S : FFGSetup Root) (blocks : List (FFGWireBlock Root))
    (votes : List (IncludedVote Root)) : Epoch → ℕ → Checkpoint Root → Checkpoint Root
  | _, 0, c => c
  | epoch, n + 1, c => cjRun S blocks votes (epoch + 1) n (cjFormula S blocks votes epoch c)

omit [DecidableEq Root] in
theorem slot_mem_epoch {cfg : Config} (x : Slot) :
    compute_epoch_at_slot cfg x * cfg.slots_per_epoch ≤ x ∧
      x < compute_epoch_at_slot cfg x * cfg.slots_per_epoch + cfg.slots_per_epoch := by
  unfold compute_epoch_at_slot
  exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add cfg.slots_per_epoch_pos⟩

omit [DecidableEq Root] in
/-- The current justified checkpoint of one weighing pass. -/
theorem weigh_current_justified {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {total previous current : Gwei}
    (h : weigh_justification_and_finalization cfg preset state total previous current =
      .ok next) :
    (total * 2 ≤ current * 3 →
      next.current_justified_checkpoint.epoch = compute_epoch_at_slot cfg state.slot ∧
      get_block_root cfg preset state (compute_epoch_at_slot cfg state.slot) =
        .ok next.current_justified_checkpoint.root) ∧
    (¬ total * 2 ≤ current * 3 → total * 2 ≤ previous * 3 →
      next.current_justified_checkpoint.epoch = get_previous_epoch cfg state ∧
      get_block_root cfg preset state (get_previous_epoch cfg state) =
        .ok next.current_justified_checkpoint.root) ∧
    (¬ total * 2 ≤ current * 3 → ¬ total * 2 ≤ previous * 3 →
      next.current_justified_checkpoint = state.current_justified_checkpoint) := by
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
        exact ⟨fun _ => ⟨rfl, hr2⟩, fun h => absurd c2 h, fun h => absurd c2 h⟩
    · rw [if_neg c2] at h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        exact ⟨fun h => absurd h c2, fun _ _ => ⟨rfl, hr1⟩, fun _ h => absurd c1 h⟩
  · rw [if_neg c1] at h
    by_cases c2 : current * 3 ≥ total * 2
    · rw [if_pos c2] at h
      rw [except_bind_eq_ok] at h
      obtain ⟨root2, hr2, h⟩ := h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        exact ⟨fun _ => ⟨rfl, hr2⟩, fun h => absurd c2 h, fun h => absurd c2 h⟩
    · rw [if_neg c2] at h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        exact ⟨fun h => absurd h c2, fun _ h => absurd h c1, fun _ _ => rfl⟩

omit [DecidableEq Root] in
/-- A weighing pass succeeds when the bits are well formed and every root read
that a passing test performs succeeds. -/
theorem weigh_ok {cfg : Config} {preset : FFGPreset} {state : FFGBeaconState Root}
    {total previous current : Gwei} (hbits : state.justification_bits.length = 4)
    (hcur : total * 2 ≤ current * 3 → ∃ root,
      get_block_root cfg preset state (compute_epoch_at_slot cfg state.slot) = .ok root)
    (hprev : total * 2 ≤ previous * 3 → ∃ root,
      get_block_root cfg preset state (get_previous_epoch cfg state) = .ok root) :
    ∃ next, weigh_justification_and_finalization cfg preset state total previous current =
      .ok next := by
  unfold weigh_justification_and_finalization
  have hg : guard (state.justification_bits.length == 4) Error.state = .ok ⟨⟩ :=
    guard_eq_ok.mpr (by simp [hbits])
  rw [hg]
  simp only [bind, Except.bind]
  by_cases c1 : previous * 3 ≥ total * 2
  · obtain ⟨root1, hr1⟩ := hprev c1
    rw [if_pos c1, hr1]
    by_cases c2 : current * 3 ≥ total * 2
    · obtain ⟨root2, hr2⟩ := hcur c2
      simp only [if_pos c2, hr2, pure, Except.pure]
      repeat' split
      all_goals exact ⟨_, rfl⟩
    · simp only [if_neg c2, pure, Except.pure]
      repeat' split
      all_goals exact ⟨_, rfl⟩
  · rw [if_neg c1]
    by_cases c2 : current * 3 ≥ total * 2
    · obtain ⟨root2, hr2⟩ := hcur c2
      simp only [if_pos c2, hr2, pure, Except.pure]
      repeat' split
      all_goals exact ⟨_, rfl⟩
    · simp only [if_neg c2, pure, Except.pure]
      repeat' split
      all_goals exact ⟨_, rfl⟩

/-! ### PJF on a state with invariant participation -/

/-- The participating set that PJF computes on a state `t` with the flags of an
invariant state `X` is `participants`. -/
theorem participating_eq {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {X t : FFGBeaconState Root}
    (hinv : ProvenanceInvariant S blocks votes X) (hslot : t.slot = X.slot)
    (hval : t.validators = X.validators)
    (hcur : t.current_epoch_participation = X.current_epoch_participation)
    (hprev : t.previous_epoch_participation = X.previous_epoch_participation)
    {epoch : Epoch} (hepoch : epoch = compute_epoch_at_slot S.cfg X.slot ∨
      epoch + 1 = compute_epoch_at_slot S.cfg X.slot)
    {set : Finset ValidatorIndex}
    (hset : get_unslashed_participating_indices S.cfg t 1 epoch = .ok set) :
    set = participants S votes epoch := by
  classical
  ext i
  rw [get_unslashed_participating_indices_mem hset i, hslot, hval, hcur, hprev,
    hinv.validators_eq]
  unfold participants
  rw [Finset.mem_filter, Finset.mem_range]
  rcases hepoch with h | h
  · rw [if_pos h, hinv.current_flags i, h]
    tauto
  · have hne : epoch ≠ compute_epoch_at_slot S.cfg X.slot := by beacon_omega
    rw [if_neg hne, hinv.previous_flags i]
    have hiff : ∀ r : IncludedVote Root, r.vote.data.target.epoch + 1 =
        compute_epoch_at_slot S.cfg X.slot ↔ r.vote.data.target.epoch = epoch := by
      intro r; constructor <;> intro h' <;> beacon_omega
    simp only [hiff]
    tauto

/-- The PJF test on `t` is `EpochTest`. -/
theorem test_iff {S : FFGSetup Root} (hS : S.Admissible) {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {X t : FFGBeaconState Root}
    (hinv : ProvenanceInvariant S blocks votes X)
    (hH : compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch)
    (hslot : t.slot = X.slot) (hval : t.validators = X.validators) (epoch : Epoch) :
    ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
        ConcreteFFG.get_total_balance S.cfg t (participants S votes epoch) * 3 ↔
      EpochTest S votes epoch := by
  have hscope : t.validators = S.scope.validators := hval.trans hinv.validators_eq
  rw [total_active_balance_eq hS hscope (by rw [hslot]; exact hH), total_balance_eq hscope]
  rfl

/-- A passing test has a participant: the increment floor alone fails it. -/
theorem participants_nonempty_of_test {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {epoch : Epoch} (h : EpochTest S votes epoch) :
    (participants S votes epoch).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  unfold EpochTest at h
  rw [hne] at h
  have hinc := S.cfg.effective_balance_increment_pos
  have hfloor := hS.balance_floor
  have hw : S.scope.weight ∅ = 0 := by simp [FixedFFGScope.weight]
  rw [hw, max_eq_left (Nat.zero_le _), max_eq_right (by omega)] at h
  omega

/-- A participant has a target-included vote whose target epoch start precedes
the invariant state's slot. -/
theorem start_lt_of_participant {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {X : FFGBeaconState Root}
    (hinv : ProvenanceInvariant S blocks votes X) {epoch : Epoch}
    (hne : (participants S votes epoch).Nonempty) :
    compute_start_slot_at_epoch S.cfg epoch < X.slot := by
  classical
  obtain ⟨i, hi⟩ := hne
  unfold participants at hi
  rw [Finset.mem_filter] at hi
  obtain ⟨-, -, -, r, hr, -, hre⟩ := hi
  have := (hinv.target_on_chain r hr).1
  rw [hre] at this
  exact this

/-- **One PJF pass.** On a state `t` with the slot, registry, participation and
current justified checkpoint of an invariant state `X`, whose passing root
reads return chain roots, PJF sets the current justified checkpoint by
`cjFormula`. -/
theorem pjf_current_justified {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X t Y : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes X)
    (hH : compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch)
    (hslot : t.slot = X.slot) (hval : t.validators = X.validators)
    (hcur : t.current_epoch_participation = X.current_epoch_participation)
    (hprev : t.previous_epoch_participation = X.previous_epoch_participation)
    (hcj : t.current_justified_checkpoint = X.current_justified_checkpoint)
    (hread : ∀ k root, (k = compute_epoch_at_slot S.cfg X.slot ∨
        k + 1 = compute_epoch_at_slot S.cfg X.slot) →
      get_block_root S.cfg S.preset t k = .ok root →
      root = chainRootAt S.genesisRoot blocks (compute_start_slot_at_epoch S.cfg k))
    (h : process_justification_and_finalization S.cfg S.preset t = .ok Y) :
    Y.current_justified_checkpoint =
      cjFormula S blocks votes (compute_epoch_at_slot S.cfg X.slot)
        X.current_justified_checkpoint := by
  set E := compute_epoch_at_slot S.cfg X.slot with hEdef
  have hEt : compute_epoch_at_slot S.cfg t.slot = E := by rw [hslot]
  rcases process_justification_and_finalization_eq_ok h with ⟨hE, rfl⟩ |
    ⟨hE, previous, current, hp, hc, hw⟩
  · rw [hEt] at hE
    unfold cjFormula
    rw [if_pos hE, hcj]
  · rw [hEt] at hE
    have hprevE : get_previous_epoch S.cfg t = E - 1 := by
      unfold get_previous_epoch; rw [hEt]
    rw [hprevE] at hp
    have hpset := participating_eq hinv hslot hval hcur hprev (Or.inr (by beacon_omega)) hp
    have hcset := participating_eq hinv hslot hval hcur hprev (Or.inl rfl) (hEt ▸ hc)
    subst hpset hcset
    obtain ⟨hw1, hw2, hw3⟩ := weigh_current_justified hw
    simp only [hEt, hprevE, test_iff hS hinv hH hslot hval] at hw1 hw2 hw3
    unfold cjFormula
    rw [if_neg (by beacon_omega)]
    by_cases t1 : EpochTest S votes E
    · rw [if_pos t1]
      obtain ⟨he, hr⟩ := hw1 t1
      exact checkpoint_eq_of he (hread _ _ (Or.inl rfl) hr)
    · rw [if_neg t1]
      by_cases t2 : EpochTest S votes (E - 1)
      · rw [if_pos t2]
        obtain ⟨he, hr⟩ := hw2 t1 t2
        exact checkpoint_eq_of he (hread _ _ (Or.inr (by beacon_omega)) hr)
      · rw [if_neg t2, hw3 t1 t2, hcj]

omit [DecidableEq Root] in
/-- The participating-set computation succeeds on the current or previous
epoch of a state with well-formed participation arrays. -/
theorem get_unslashed_participating_indices_ok {cfg : Config} {state : FFGBeaconState Root}
    (hprev : state.previous_epoch_participation.length = state.validators.length)
    (hcur : state.current_epoch_participation.length = state.validators.length)
    {epoch : Epoch} (hepoch : epoch = compute_epoch_at_slot cfg state.slot ∨
      epoch = get_previous_epoch cfg state) :
    ∃ set, get_unslashed_participating_indices cfg state 1 epoch = .ok set := by
  unfold get_unslashed_participating_indices
  have h1 : guard (epoch == compute_epoch_at_slot cfg state.slot ||
      epoch == get_previous_epoch cfg state) Error.target = .ok ⟨⟩ := by
    apply guard_eq_ok.mpr
    rcases hepoch with h | h <;> simp [h]
  have h2 : guard ((if epoch == compute_epoch_at_slot cfg state.slot then
      state.current_epoch_participation else state.previous_epoch_participation).length ==
        state.validators.length) Error.state = .ok ⟨⟩ := by
    apply guard_eq_ok.mpr
    split <;> simp [hprev, hcur]
  simp only [bind, Except.bind] at h1 h2 ⊢
  rw [h1]
  dsimp only
  rw [h2]
  exact ⟨_, rfl⟩

omit [DecidableEq Root] in
/-- A ring read of an epoch start succeeds inside its window. -/
theorem get_block_root_ok {cfg : Config} {preset : FFGPreset} {state : FFGBeaconState Root}
    {epoch : Epoch} (hroots : state.block_roots.length = preset.slots_per_historical_root)
    (hu : epoch * cfg.slots_per_epoch + preset.slots_per_historical_root ≤ UINT64_MAX)
    (hlt : compute_start_slot_at_epoch cfg epoch < state.slot)
    (hle : state.slot ≤ compute_start_slot_at_epoch cfg epoch + preset.slots_per_historical_root) :
    ∃ root, get_block_root cfg preset state epoch = .ok root := by
  have hidx : compute_start_slot_at_epoch cfg epoch % preset.slots_per_historical_root <
      state.block_roots.length := by
    rw [hroots]; exact Nat.mod_lt _ preset.ring_pos
  refine ⟨state.block_roots[compute_start_slot_at_epoch cfg epoch %
    preset.slots_per_historical_root], ?_⟩
  refine get_block_root_eq_ok.mpr ⟨by beacon_omega, get_block_root_at_slot_eq_ok.mpr
    ⟨by unfold compute_start_slot_at_epoch; beacon_omega, hlt, hle, hroots, ?_⟩⟩
  exact List.getElem?_eq_getElem hidx

/-- **PJF succeeds** on a state `t` with the slot, registry and participation
of an invariant state in the fixed scope, when the ring has its length and the
scope satisfies the `uint64` bound. -/
theorem pjf_ok {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X t : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes X)
    (hH : compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch)
    (hlen : LengthsOK S t) (hslot : t.slot = X.slot) (hval : t.validators = X.validators)
    (hcur : t.current_epoch_participation = X.current_epoch_participation)
    (hprev : t.previous_epoch_participation = X.previous_epoch_participation) :
    ∃ Y, process_justification_and_finalization S.cfg S.preset t = .ok Y := by
  set E := compute_epoch_at_slot S.cfg X.slot with hEdef
  have hEt : compute_epoch_at_slot S.cfg t.slot = E := by rw [hslot]
  unfold process_justification_and_finalization
  by_cases hE : compute_epoch_at_slot S.cfg t.slot ≤ 1
  · rw [if_pos hE]
    exact ⟨t, rfl⟩
  rw [if_neg hE]
  rw [hEt] at hE
  have hprevE : get_previous_epoch S.cfg t = E - 1 := by
    unfold get_previous_epoch; rw [hEt]
  obtain ⟨pset, hp⟩ := get_unslashed_participating_indices_ok (cfg := S.cfg) hlen.previous
    hlen.current (Or.inr rfl)
  obtain ⟨cset, hc⟩ := get_unslashed_participating_indices_ok (cfg := S.cfg) hlen.previous
    hlen.current (Or.inl rfl)
  have hp' := hp
  rw [hprevE] at hp'
  have hc' := hc
  rw [hEt] at hc'
  have hpset := participating_eq hinv hslot hval hcur hprev (Or.inr (by beacon_omega)) hp'
  have hcset := participating_eq hinv hslot hval hcur hprev (Or.inl rfl) hc'
  simp only [bind, Except.bind, pure, Except.pure, TIMELY_TARGET_FLAG_INDEX]
  rw [hp]
  dsimp only
  rw [hc]
  dsimp only
  have hspe := S.cfg.slots_per_epoch_pos
  have hN := hS.ring_covers_two_epochs
  obtain ⟨hx1, hx2⟩ := slot_mem_epoch (cfg := S.cfg) X.slot
  rw [← hEdef] at hx1 hx2
  have hEL : E * S.cfg.slots_per_epoch + S.preset.slots_per_historical_root ≤ UINT64_MAX := by
    have : E * S.cfg.slots_per_epoch ≤ (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch :=
      Nat.mul_le_mul_right _ (by beacon_omega)
    beacon_omega
  apply weigh_ok hlen.bits
  · intro htest
    rw [hcset, test_iff hS hinv hH hslot hval] at htest
    have := start_lt_of_participant hinv (participants_nonempty_of_test hS htest)
    rw [hEt]
    refine get_block_root_ok hlen.roots hEL (by rw [hslot]; exact this) ?_
    rw [hslot]; unfold compute_start_slot_at_epoch; beacon_omega
  · intro _
    rw [hprevE]
    have hE1 : (E - 1) * S.cfg.slots_per_epoch + S.cfg.slots_per_epoch =
        E * S.cfg.slots_per_epoch := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by beacon_omega)]
    refine get_block_root_ok hlen.roots ?_ ?_ ?_
    · have : (E - 1) * S.cfg.slots_per_epoch ≤ E * S.cfg.slots_per_epoch :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      beacon_omega
    · rw [hslot]; unfold compute_start_slot_at_epoch; beacon_omega
    · rw [hslot]; unfold compute_start_slot_at_epoch; beacon_omega

/-! ### Root reads -/

/-- Every successful ring read of an invariant state returns the chain root. -/
theorem read_eager {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {X : FFGBeaconState Root}
    (hinv : ProvenanceInvariant S blocks votes X) {k : Epoch} {root : Root}
    (h : get_block_root S.cfg S.preset X k = .ok root) :
    root = chainRootAt S.genesisRoot blocks (compute_start_slot_at_epoch S.cfg k) := by
  obtain ⟨-, hread⟩ := get_block_root_eq_ok.mp h
  obtain ⟨-, hlt, hle, -, hcell⟩ := get_block_root_at_slot_eq_ok.mp hread
  rw [hinv.ring _ hlt hle] at hcell
  exact (Option.some.inj hcell).symm

/-- At an epoch end, the ring reads of the current and previous epoch after
`process_slot` return the chain roots. -/
theorem read_boundary {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X s1 : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes X)
    (hbound : (X.slot + 1) % S.cfg.slots_per_epoch = 0)
    (hs1 : process_slot S.preset X = .ok s1) {k : Epoch} {root : Root}
    (hk : k = compute_epoch_at_slot S.cfg X.slot ∨ k + 1 = compute_epoch_at_slot S.cfg X.slot)
    (h : get_block_root S.cfg S.preset s1 k = .ok root) :
    root = chainRootAt S.genesisRoot blocks (compute_start_slot_at_epoch S.cfg k) := by
  obtain ⟨hlen, -, rfl⟩ := process_slot_eq_ok.mp hs1
  set E := compute_epoch_at_slot S.cfg X.slot with hEdef
  set x := X.slot with hxdef
  set N := S.preset.slots_per_historical_root with hNdef
  set spe := S.cfg.slots_per_epoch with hspedef
  have hring2 : 2 * spe ≤ N := hS.ring_covers_two_epochs
  have hx : x + 1 = (E + 1) * spe := boundary_slot_eq hbound
  have hstart : compute_start_slot_at_epoch S.cfg k = k * spe := rfl
  rw [hstart]
  obtain ⟨-, hread⟩ := get_block_root_eq_ok.mp h
  obtain ⟨-, hlt, -, -, hcell⟩ := get_block_root_at_slot_eq_ok.mp hread
  rw [hstart] at hlt hcell
  change k * spe < x at hlt
  have hlt' : x < k * spe + N := by
    rcases hk with h | h
    · rw [h] at hlt ⊢
      have : (E + 1) * spe = E * spe + spe := Nat.succ_mul E spe
      beacon_omega
    · rw [← h] at hx
      have : (k + 1 + 1) * spe = k * spe + 2 * spe := by ring
      beacon_omega
  change (X.block_roots.set (x % N) X.latest_block_header.root)[k * spe % N]? =
    some root at hcell
  rw [List.getElem?_set_ne (mod_ne_of_lt_of_lt_add hlt hlt')] at hcell
  rw [hinv.ring _ hlt (by beacon_omega)] at hcell
  exact (Option.some.inj hcell).symm

/-- **Eager PJF.** PJF on an invariant state in the fixed scope succeeds and
sets the current justified checkpoint by `cjFormula`. -/
theorem eager_pjf {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes X)
    (hlen : LengthsOK S X) (hH : compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch) :
    ∃ Y, process_justification_and_finalization S.cfg S.preset X = .ok Y ∧
      Y.current_justified_checkpoint =
        cjFormula S blocks votes (compute_epoch_at_slot S.cfg X.slot)
          X.current_justified_checkpoint := by
  obtain ⟨Y, hY⟩ := pjf_ok hS hnum hinv hH hlen rfl rfl rfl rfl
  exact ⟨Y, hY, pjf_current_justified hS hinv hH rfl rfl rfl rfl rfl
    (fun _ _ _ h => read_eager hinv h) hY⟩

/-! ### Slot steps and runs -/

/-- One slot step on an invariant state in the fixed scope succeeds. Its
current justified checkpoint follows `cjFormula` at an epoch end and is
unchanged otherwise. -/
theorem slotStep_ok {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes X)
    (hlen : LengthsOK S X) (hH : compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch) :
    ∃ next, slotStep S.cfg S.preset X = .ok next ∧
      next.current_justified_checkpoint =
        (if (X.slot + 1) % S.cfg.slots_per_epoch = 0 then
          cjFormula S blocks votes (compute_epoch_at_slot S.cfg X.slot)
            X.current_justified_checkpoint
        else X.current_justified_checkpoint) := by
  have hs1 : process_slot S.preset X = .ok { X with
      block_roots := X.block_roots.set (X.slot % S.preset.slots_per_historical_root)
        X.latest_block_header.root
      execution_payload_availability := X.execution_payload_availability.set
        ((X.slot + 1) % S.preset.slots_per_historical_root) false } :=
    process_slot_eq_ok.mpr ⟨hlen.roots, hlen.availability, rfl⟩
  set s1 := { X with
      block_roots := X.block_roots.set (X.slot % S.preset.slots_per_historical_root)
        X.latest_block_header.root
      execution_payload_availability := X.execution_payload_availability.set
        ((X.slot + 1) % S.preset.slots_per_historical_root) false } with hs1def
  have hlen1 : LengthsOK S s1 :=
    ⟨hlen.bits, hlen.previous, hlen.current, by simp [s1, hlen.roots],
      by simp [s1, hlen.availability]⟩
  by_cases hb : (X.slot + 1) % S.cfg.slots_per_epoch = 0
  · obtain ⟨mid, hmid⟩ := pjf_ok (t := s1) hS hnum hinv hH hlen1 rfl rfl rfl rfl
    have hcj := pjf_current_justified (t := s1) hS hinv hH rfl rfl rfl rfl rfl
      (fun _ _ hk h => read_boundary hS hinv hb hs1 hk h) hmid
    refine ⟨{ process_participation_flag_updates mid with
      slot := (process_participation_flag_updates mid).slot + 1 }, ?_, ?_⟩
    · unfold slotStep
      rw [except_bind_eq_ok]
      refine ⟨s1, hs1, ?_⟩
      have hc : ((s1.slot + 1) % S.cfg.slots_per_epoch == 0) = true := by
        simp [s1, hb]
      simp only [hc, if_true]
      rw [except_bind_eq_ok]
      exact ⟨_, process_epoch_eq_ok.mpr ⟨mid, hmid, rfl⟩, rfl⟩
    · rw [if_pos hb]
      exact hcj
  · refine ⟨{ s1 with slot := s1.slot + 1 }, ?_, ?_⟩
    · unfold slotStep
      rw [except_bind_eq_ok]
      refine ⟨s1, hs1, ?_⟩
      have hc : ((s1.slot + 1) % S.cfg.slots_per_epoch == 0) = false := by
        simp [s1, hb]
      simp only [hc, Bool.false_eq_true, if_false]
      rfl
    · rw [if_neg hb]

/-- The current justified checkpoint after `n` boundaries: `cjRun` unfolds one
boundary. -/
theorem cjRun_succ_of_lt {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {e f : Epoch} (c : Checkpoint Root) (h : e < f) :
    cjRun S blocks votes e (f - e) c =
      cjRun S blocks votes (e + 1) (f - (e + 1)) (cjFormula S blocks votes e c) := by
  obtain ⟨n, hn⟩ : ∃ n, f - e = n + 1 := ⟨f - e - 1, by beacon_omega⟩
  rw [hn, cjRun]
  congr 1
  beacon_omega

/-- **Slot runs.** From an invariant state in the fixed scope, the slot loop to
a target in the scope succeeds. Its current justified checkpoint is `cjRun`
over the crossed boundaries. -/
theorem slotFold_ok {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} :
    ∀ (steps : List ℕ) (X : FFGBeaconState Root), ProvenanceInvariant S blocks votes X →
      LengthsOK S X →
      compute_epoch_at_slot S.cfg (X.slot + steps.length) ≤ S.scope.last_epoch →
      ∃ next, steps.foldlM (fun s _ => slotStep S.cfg S.preset s) X = .ok next ∧
        ProvenanceInvariant S blocks votes next ∧ LengthsOK S next ∧
        next.slot = X.slot + steps.length ∧
        next.current_justified_checkpoint =
          cjRun S blocks votes (compute_epoch_at_slot S.cfg X.slot)
            (compute_epoch_at_slot S.cfg (X.slot + steps.length) -
              compute_epoch_at_slot S.cfg X.slot) X.current_justified_checkpoint := by
  intro steps
  induction steps with
  | nil =>
    intro X hinv hlen _
    refine ⟨X, rfl, hinv, hlen, rfl, ?_⟩
    simp [cjRun]
  | cons _ steps ih =>
    intro X hinv hlen hH
    simp only [List.length_cons] at hH
    have hHX : compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch :=
      Nat.le_trans (compute_epoch_at_slot_mono (by beacon_omega)) hH
    obtain ⟨mid, hmid, hcj⟩ := slotStep_ok hS hnum hinv hlen hHX
    obtain ⟨hinv', hslot'⟩ := provenanceInvariant_slotStep hS hinv hHX hmid
    have hlen' := lengthsOK_slotStep hlen hmid
    obtain ⟨next, hnext, hinvn, hlenn, hslotn, hcjn⟩ :=
      ih mid hinv' hlen' (by rw [hslot']; convert hH using 2; beacon_omega)
    refine ⟨next, ?_, hinvn, hlenn, ?_, ?_⟩
    · simp only [List.foldlM_cons, except_bind_eq_ok]
      exact ⟨mid, hmid, hnext⟩
    · rw [hslotn, hslot', List.length_cons]; beacon_omega
    · simp only [List.length_cons]
      rw [hcjn, hslot', hcj]
      have hend : X.slot + 1 + steps.length = X.slot + (steps.length + 1) := by beacon_omega
      rw [hend]
      by_cases hb : (X.slot + 1) % S.cfg.slots_per_epoch = 0
      · rw [if_pos hb, epoch_succ_of_boundary hb]
        have hlt : compute_epoch_at_slot S.cfg X.slot <
            compute_epoch_at_slot S.cfg (X.slot + (steps.length + 1)) := by
          have := compute_epoch_at_slot_mono (cfg := S.cfg)
            (show X.slot + 1 ≤ X.slot + (steps.length + 1) by beacon_omega)
          rw [epoch_succ_of_boundary hb] at this
          beacon_omega
        rw [cjRun_succ_of_lt _ hlt]
      · rw [if_neg hb, epoch_succ_of_not_boundary hb]

/-- **`process_slots`** from an invariant state to a later target in the
fixed scope succeeds, and its current justified checkpoint is `cjRun`. -/
theorem process_slots_ok {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes X)
    (hlen : LengthsOK S X) {target : Slot} (hlt : X.slot < target)
    (hH : compute_epoch_at_slot S.cfg target ≤ S.scope.last_epoch) :
    ∃ next, process_slots S.cfg S.preset X target = .ok next ∧
      ProvenanceInvariant S blocks votes next ∧ LengthsOK S next ∧
      next.current_justified_checkpoint =
        cjRun S blocks votes (compute_epoch_at_slot S.cfg X.slot)
          (compute_epoch_at_slot S.cfg target - compute_epoch_at_slot S.cfg X.slot)
          X.current_justified_checkpoint := by
  have hsum : X.slot + (List.range (target - X.slot)).length = target := by
    rw [List.length_range]; beacon_omega
  obtain ⟨next, hfold, hinvn, hlenn, -, hcj⟩ :=
    slotFold_ok hS hnum (List.range (target - X.slot)) X hinv hlen (by rw [hsum]; exact hH)
  rw [hsum] at hcj
  refine ⟨next, process_slots_eq_ok.mpr ⟨?_, hlt, hfold⟩, hinvn, hlenn, hcj⟩
  obtain ⟨-, hx2⟩ := slot_mem_epoch (cfg := S.cfg) target
  have : compute_epoch_at_slot S.cfg target * S.cfg.slots_per_epoch + S.cfg.slots_per_epoch ≤
      (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch := by
    rw [Nat.succ_mul]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hH) _
  beacon_omega

/-! ### Boundaries after the last vote -/

/-- No participant at an epoch after every recorded target epoch. -/
theorem not_test_of_late {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {k : Epoch}
    (hlate : ∀ r ∈ votes, r.vote.data.target.epoch < k) : ¬ EpochTest S votes k := by
  classical
  intro htest
  obtain ⟨i, hi⟩ := participants_nonempty_of_test hS htest
  unfold participants at hi
  rw [Finset.mem_filter] at hi
  obtain ⟨-, -, -, r, hr, -, hre⟩ := hi
  have := hlate r hr.1
  beacon_omega

open Classical in
/-- The first boundary after every recorded target epoch can only repeat the
previous-epoch justification. -/
theorem cjFormula_late {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} {k : Epoch}
    (hlate : ∀ r ∈ votes, r.vote.data.target.epoch < k) (hk : 2 ≤ k) (c : Checkpoint Root) :
    cjFormula S blocks votes k c =
      if EpochTest S votes (k - 1) then chainCheckpoint S blocks (k - 1) else c := by
  unfold cjFormula
  rw [if_neg (by beacon_omega), if_neg (not_test_of_late hS hlate)]

/-- Later boundaries keep the checkpoint. -/
theorem cjRun_very_late {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} :
    ∀ (n : ℕ) (k : Epoch) (c : Checkpoint Root),
      (∀ r ∈ votes, r.vote.data.target.epoch + 1 < k) → cjRun S blocks votes k n c = c := by
  intro n
  induction n with
  | zero => intro k c _; rfl
  | succ n ih =>
    intro k c hlate
    rw [cjRun, ih (k + 1) _ (fun r hr => by have := hlate r hr; beacon_omega)]
    unfold cjFormula
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd h2 (not_test_of_late hS (fun r hr => by have := hlate r hr; beacon_omega))
    · exact absurd h3 (not_test_of_late hS (fun r hr => by have := hlate r hr; beacon_omega))
    · rfl

/-- **Two or more boundaries** from an epoch `E ≥ 2` holding every recorded
target give the checkpoint of the first boundary. -/
theorem cjRun_two_boundaries {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} {E : Epoch}
    (hvotes : ∀ r ∈ votes, r.vote.data.target.epoch ≤ E) (hE : 2 ≤ E) {n : ℕ} (hn : 2 ≤ n)
    (c : Checkpoint Root) :
    cjRun S blocks votes E n c = cjFormula S blocks votes E c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by beacon_omega⟩
  rw [cjRun, cjRun, cjRun_very_late hS m (E + 1 + 1) _
    (fun r hr => by have := hvotes r hr; beacon_omega),
    cjFormula_late hS (fun r hr => by have := hvotes r hr; beacon_omega) (by beacon_omega)]
  rw [show E + 1 - 1 = E by beacon_omega]
  split_ifs with ht
  · unfold cjFormula
    rw [if_neg (by beacon_omega), if_pos ht]
  · rfl

/-- The checkpoint after any number of boundaries is the start checkpoint or has
an epoch at most the start epoch `E`, when `E` holds every recorded target. -/
theorem cjRun_epoch_le {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} {E : Epoch}
    (hvotes : ∀ r ∈ votes, r.vote.data.target.epoch ≤ E) (n : ℕ) (c : Checkpoint Root) :
    cjRun S blocks votes E n c = c ∨ (cjRun S blocks votes E n c).epoch ≤ E := by
  have hform : ∀ c : Checkpoint Root, cjFormula S blocks votes E c = c ∨
      (cjFormula S blocks votes E c).epoch ≤ E := by
    intro c
    unfold cjFormula
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Nat.le_refl _)
    · exact Or.inr (Nat.sub_le _ _)
    · exact Or.inl rfl
  match n with
  | 0 => exact Or.inl rfl
  | 1 => exact hform c
  | m + 2 =>
    rw [cjRun, cjRun, cjRun_very_late hS m (E + 1 + 1) _
      (fun r hr => by have := hvotes r hr; beacon_omega)]
    by_cases hE : 1 ≤ E
    · rw [cjFormula_late hS (fun r hr => by have := hvotes r hr; beacon_omega)
        (by beacon_omega)]
      split_ifs
      · exact Or.inr (by change E + 1 - 1 ≤ E; beacon_omega)
      · exact hform c
    · have hE0 : E = 0 := by beacon_omega
      subst hE0
      unfold cjFormula
      rw [if_pos (by beacon_omega), if_pos (by beacon_omega)]
      exact Or.inl rfl

end FastConfirmation.Spec.ConcreteFFG

end
