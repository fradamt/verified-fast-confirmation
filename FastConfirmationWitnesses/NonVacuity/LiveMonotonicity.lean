module
public import Mathlib.Tactic
public import FastConfirmationWitnesses.NonVacuity.NextSlotPremises
public import FastConfirmationProofs.Monotonicity.LiveConfirmation
public import FastConfirmationStatements.Premises.InterpretationFidelity
@[expose] public section

namespace FastConfirmation.Spec
namespace LiveMonotonicityWitness

abbrev Root := Fin 3

def junk : Root := 0
def anchor : Root := 1
def child : Root := 2

def cfg : Config where
  slots_per_epoch := 2
  slots_per_epoch_pos := by decide
  slot_duration_ms := 1000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 0
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 0
  min_seed_lookahead := 0

def anchorCheckpoint : Checkpoint Root := ⟨0, anchor⟩
def val : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH }
def state (slot : Slot) : BeaconState Root :=
  { genesis_time := 0
    slot := slot
    validators := [val, val]
    current_justified_checkpoint := anchorCheckpoint
    finalized_checkpoint := anchorCheckpoint }
def anchorBlock : SignedBeaconBlock Root :=
  { message := { slot := 0, parent_root := junk }, root := anchor }
def childBlock : SignedBeaconBlock Root :=
  { message := { slot := 1, parent_root := anchor }, root := child }
def vote (s : Slot) : Attestation Root :=
  { attesting_indices := [s % 2], data := { slot := s, index := 0, beacon_block_root := (if s = 0 then anchor else child), source := anchorCheckpoint, target := (if s < 2 then anchorCheckpoint else ⟨1, child⟩) } }
def pjf (st : BeaconState Root) : BeaconState Root :=
  { st with current_justified_checkpoint := anchorCheckpoint }
def processSlots (st : BeaconState Root) (target : Slot) : BeaconState Root :=
  if compute_epoch_at_slot cfg st.slot < compute_epoch_at_slot cfg target then
    { pjf st with slot := target }
  else
    { st with slot := target }
def SameProjectedState (a b : BeaconState Root) : Prop :=
  a.genesis_time = b.genesis_time ∧
    a.slot = b.slot ∧
    a.validators = b.validators ∧
    a.current_justified_checkpoint = b.current_justified_checkpoint ∧
    a.finalized_checkpoint = b.finalized_checkpoint ∧
    a.beacon_committee_reads = b.beacon_committee_reads ∧
    a.committee_count_reads = b.committee_count_reads ∧
    a.source_identity = b.source_identity

instance (a b : BeaconState Root) : Decidable (SameProjectedState a b) := by
  unfold SameProjectedState
  infer_instance

theorem sameProjectedState_iff_eq {a b : BeaconState Root} :
    SameProjectedState a b ↔ a = b := by
  constructor
  · rintro ⟨hgen, hslot, hvalidators, hj, hf, hcommittees, hcounts, hidentity⟩
    cases a
    cases b
    simp_all
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def transition (st : BeaconState Root) (b : SignedBeaconBlock Root) : Option (BeaconState Root) :=
  if SameProjectedState st (state 0) ∧ b = childBlock then some (state 1) else none

def ext : Externals Root where
  AnchorCommitsToState := fun b st => b = anchorBlock.message ∧ st = state 0
  get_beacon_committee := fun _ s _ => [s % 2]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := processSlots
  state_transition := transition
  process_justification_and_finalization := pjf
  is_valid_indexed_attestation := fun st a => decide (st.validators ≠ [] ∧ a ∈ [vote 0, vote 1, vote 2, vote 3])

def schedule (_w : ValidatorIndex) (n : ℕ) : List (Event Root) :=
  if n = 1 then [Event.block childBlock, Event.attestation (vote 0) false]
  else if 2 ≤ n ∧ n ≤ 4 then [Event.attestation (vote (n - 1)) false]
  else []

def E : Execution Root where
  verification_horizon := 2
  genesis_store := get_forkchoice_store cfg (state 0) anchorBlock
  schedule := schedule
  honest := {0, 1}
  committee := fun s => {s % 2}
  vote := fun v s => if v = s % 2 ∧ s < 4 then some (s, vote s) else none

set_option maxRecDepth 50000 in
theorem confirmed_at_one : E.confirmed cfg ext 0 1 = anchor := by decide
set_option maxRecDepth 50000 in
theorem confirmed_at_two : E.confirmed cfg ext 0 2 = child := by decide
set_option maxRecDepth 50000 in
example : E.confirmed cfg ext 0 3 = child := by decide
set_option maxRecDepth 50000 in
example : (E.store cfg ext 0 2).unrealized_justified_checkpoint = anchorCheckpoint := by decide
set_option maxRecDepth 50000 in
example : (E.store cfg ext 0 2).unrealized_justifications (get_head cfg (E.store cfg ext 0 2)).root = anchorCheckpoint := by decide


theorem slot_at_eq (n : ℕ) : E.slot_at cfg n = n := by
  norm_num [Execution.slot_at, Execution.time_at, E, cfg, state,
    anchorBlock, get_forkchoice_store, GENESIS_SLOT]

theorem slot_start_eq (s : Slot) : E.slot_start cfg s = s := by
  norm_num [Execution.slot_start, E, cfg, state, anchorBlock,
    get_forkchoice_store]

theorem within_two : E.WithinHorizon cfg 2 := by
  unfold Execution.WithinHorizon
  rw [slot_at_eq]
  norm_num [Execution.time_at, E, cfg, state, anchorBlock,
    get_forkchoice_store, compute_epoch_at_slot, UINT64_MAX]

theorem anchorBlockAt : E.BlockAt anchor anchorBlock.message := by
  left
  constructor
  · decide
  · rfl

theorem childBlockAt : E.BlockAt child childBlock.message := by
  right
  exact ⟨0, 1, childBlock, by simp [E, schedule], rfl, rfl⟩

theorem honest_eq_zero_or_one {v : ValidatorIndex} (hv : v ∈ E.honest) :
    v = 0 ∨ v = 1 := by
  simpa [E] using hv

set_option maxRecDepth 50000 in
theorem livePremises : LiveMonotonicityPremises cfg ext E 0 1 2 := by
  constructor
  · intro s hs0 hs2
    rw [slot_at_eq] at hs0 hs2
    interval_cases s
    · refine ⟨anchor, anchorBlock.message, anchorBlockAt, rfl, by decide, ?_, ?_⟩
      · intro w hw
        rcases honest_eq_zero_or_one hw with rfl | rfl <;>
          rw [slot_start_eq] <;> decide
      · intro i hi t k a hst htm hvote
        rw [slot_at_eq] at htm
        rcases honest_eq_zero_or_one hi with rfl | rfl <;>
          interval_cases t <;>
          simp [E, vote] at hvote <;>
          rcases hvote with ⟨rfl, rfl⟩ <;>
          constructor <;> decide
    · refine ⟨child, childBlock.message, childBlockAt, rfl, by decide, ?_, ?_⟩
      · intro w hw
        rcases honest_eq_zero_or_one hw with rfl | rfl <;>
          rw [slot_start_eq] <;> decide
      · intro i hi t k a hst htm hvote
        have ht : t = 1 := by
          rw [slot_at_eq] at htm
          exact Nat.le_antisymm (Nat.le_of_lt_succ htm) hst
        subst t
        rcases honest_eq_zero_or_one hi with rfl | rfl <;>
          simp [E, vote] at hvote <;>
          rcases hvote with ⟨rfl, rfl⟩ <;>
          constructor <;> decide
  · intro e he0 hedone
    rw [slot_at_eq] at hedone
    have he : e = 0 := by
      change (e + 1) * 2 ≤ 2 at hedone
      cases e with
      | zero => rfl
      | succ e =>
          have hfour : 4 ≤ (Nat.succ e + 1) * 2 := by
            change 2 * 2 ≤ (Nat.succ e + 1) * 2
            exact Nat.mul_le_mul_right 2 (by simp)
          have : 4 ≤ 2 := hfour.trans hedone
          exact False.elim ((by decide : ¬ 4 ≤ 2) this)
    subst e
    refine ⟨anchorCheckpoint, rfl, ⟨anchor, anchorBlock.message,
      anchorBlockAt, rfl, rfl⟩, ?_⟩
    intro w hw
    rcases honest_eq_zero_or_one hw with rfl | rfl <;> decide


/-! ## Operational facts for the accepted bundle -/

theorem time_at_eq (n : ℕ) : E.time_at n = n := by
  norm_num [Execution.time_at, E, cfg, state, anchorBlock,
    get_forkchoice_store]

theorem time_lt_four {n : ℕ} (hn : E.WithinHorizon cfg n) : n < 4 := by
  have hepoch := hn.2.2
  rw [slot_at_eq] at hepoch
  change n / 2 < 2 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)] at hepoch

theorem slot_lt_four {s : Slot} (hs : E.SlotWithinHorizon cfg s) : s < 4 := by
  have hepoch := hs.2
  change s / 2 < 2 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)] at hepoch

theorem time_within_of_lt_four {n : ℕ} (hn : n < 4) :
    E.WithinHorizon cfg n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [time_at_eq]
    exact (Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    exact (Nat.le_of_lt hn).trans (by norm_num [UINT64_MAX])
  · rw [slot_at_eq]
    change n / 2 < 2
    rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]

theorem slot_within_of_lt_four {s : Slot} (hs : s < 4) :
    E.SlotWithinHorizon cfg s := by
  refine ⟨(Nat.le_of_lt hs).trans (by norm_num [UINT64_MAX]), ?_⟩
  change s / 2 < 2
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]

theorem vote_some_iff {v : ValidatorIndex} {s : Slot}
    {n : ℕ} {a : Attestation Root} :
    E.vote v s = some (n, a) ↔
      v = s % 2 ∧ s < 4 ∧ n = s ∧ a = vote s := by
  change (if v = s % 2 ∧ s < 4 then some (s, vote s) else none) = some (n, a) ↔ _
  by_cases h : v = s % 2 ∧ s < 4
  · rw [if_pos h]
    constructor
    · intro heq
      have hp : (s, vote s) = (n, a) := Option.some.inj heq
      exact ⟨h.1, h.2, (congrArg Prod.fst hp).symm,
        (congrArg Prod.snd hp).symm⟩
    · rintro ⟨_, _, rfl, rfl⟩
      rfl
  · rw [if_neg h]
    constructor
    · intro himpossible
      contradiction
    · rintro ⟨hv, hs, -, -⟩
      exact (h ⟨hv, hs⟩).elim

def groundVotes : List (Attestation Root) :=
  [vote 0, vote 1, vote 2, vote 3]

theorem vote_mem_ground {s : Slot} (hs : s < 4) : vote s ∈ groundVotes := by
  interval_cases s <;> decide

theorem groundVote_exists {a : Attestation Root} (ha : a ∈ groundVotes) :
    ∃ s : Slot, s < 4 ∧ a = vote s := by
  simp [groundVotes] at ha
  rcases ha with h | h | h | h
  · exact ⟨0, by decide, h⟩
  · exact ⟨1, by decide, h⟩
  · exact ⟨2, by decide, h⟩
  · exact ⟨3, by decide, h⟩

theorem valid_iff (st : BeaconState Root) (a : Attestation Root) :
    ext.is_valid_indexed_attestation st a = true ↔
      st.validators ≠ [] ∧ a ∈ groundVotes := by
  simp [ext, groundVotes]

theorem block_mem_schedule_iff {w n} {b : SignedBeaconBlock Root} :
    Event.block b ∈ E.schedule w n ↔ n = 1 ∧ b = childBlock := by
  by_cases h1 : n = 1
  · subst n
    simp [E, schedule]
  · by_cases h2 : 2 ≤ n ∧ n ≤ 4
    · simp [E, schedule, h1, h2]
    · simp [E, schedule, h1, h2]

theorem attestation_mem_schedule_ground {w n a ifb}
    (h : Event.attestation a ifb ∈ E.schedule w n) : a ∈ groundVotes := by
  by_cases h1 : n = 1
  · subst n
    have ha : a = vote 0 := by
      exact (show a = vote 0 ∧ ifb = false by simpa [E, schedule] using h).1
    rw [ha]
    decide
  · by_cases h2 : 2 ≤ n ∧ n ≤ 4
    · have ha : a = vote (n - 1) := by
        exact (show a = vote (n - 1) ∧ ifb = false by
          simpa [E, schedule, h1, h2] using h).1
      rw [ha]
      have hn : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hn with rfl | rfl | rfl <;> decide
    · simp [E, schedule, h1, h2] at h

theorem store_symmetric (v w : ValidatorIndex) (n : ℕ) :
    E.store cfg ext v n = E.store cfg ext w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Execution.store]
      rw [ih]
      rfl

theorem wellFormed : WellFormedExecution E := by
  constructor
  · intro w n b hb w' n' b' hb' hroot
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩
    rcases block_mem_schedule_iff.mp hb' with ⟨rfl, rfl⟩
    rfl
  · intro w n b hb hgen
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩
    simp [E, state, anchorBlock, childBlock, get_forkchoice_store] at hgen
    exact False.elim ((by decide : child ≠ anchor) hgen)
  · intro r hr w n b hb
    have hr' : r = anchor := by
      simpa [E, state, anchorBlock, get_forkchoice_store] using hr
    subst r
    rcases block_mem_schedule_iff.mp hb with ⟨rfl, rfl⟩
    decide

theorem vote_data_slot (s : Slot) : (vote s).data.slot = s := by rfl

theorem vote_false_delivery {s : Slot} (hs : s < 4) (w : ValidatorIndex) :
    Event.attestation (vote s) false ∈ E.schedule w (E.slot_start cfg (s + 1)) := by
  rw [slot_start_eq]
  interval_cases s <;> simp [E, schedule]

theorem honest_vote_recorded {s : Slot} (hs : s < 4) :
    E.vote (s % 2) s = some (s, honest_attestation cfg ext
      (E.store cfg ext (s % 2) s) s 0 (s % 2)) := by
  interval_cases s <;> set_option maxRecDepth 50000 in rfl


theorem scheduled_vote_sent_before {w n s ifb}
    (h : Event.attestation (vote s) ifb ∈ E.schedule w n) : s ≤ n := by
  have vote_slot_eq {t : Slot} (heq : vote s = vote t) : s = t := by
    have hslot := congrArg (fun a : Attestation Root => a.data.slot) heq
    simpa only [vote_data_slot] using hslot
  change Event.attestation (vote s) ifb ∈ schedule w n at h
  by_cases h1 : n = 1
  · subst n
    simp [schedule] at h
    have hs := vote_slot_eq h.1
    rw [hs]
    decide
  · by_cases hb : 2 ≤ n ∧ n ≤ 4
    · simp [schedule, h1, hb] at h
      have hs := vote_slot_eq h.1
      rw [hs]
      exact Nat.sub_le n 1
    · simp [schedule, h1, hb] at h

theorem recorded_vote_of_attester {s : Slot} (hs : s < 4)
    {v : ValidatorIndex} (hvin : v ∈ (vote s).attesting_indices) :
    ∃ m a', E.vote v (vote s).data.slot = some (m, a') ∧
      (vote s).data = a'.data := by
  have hv : v = s % 2 := by simpa [vote] using hvin
  refine ⟨s, vote s, ?_, rfl⟩
  rw [vote_data_slot]
  simp [E, hs, hv]

theorem honestBehavior : HonestBehavior cfg ext E := by
  constructor
  · intro v hv s hcommittee hs _hs0
    have hslt := slot_lt_four hs
    have hvmod : v = s % 2 := by simpa [E] using hcommittee
    subst v
    exact ⟨s, 0, time_within_of_lt_four hslt, slot_at_eq s,
      honest_vote_recorded hslt⟩
  · intro v hv s n a hvote
    obtain ⟨_, _, rfl, _⟩ := vote_some_iff.mp hvote
    rw [slot_start_eq]
    simp
  · intro v hv s hvote
    rcases Option.ne_none_iff_exists'.mp hvote with ⟨na, hna⟩
    rcases na with ⟨n, a⟩
    obtain ⟨hvmod, hs, _, _⟩ := vote_some_iff.mp hna
    simpa [E, hvmod]
  · intro w n a ifb hschedule v hv hvin
    obtain ⟨s, hs, rfl⟩ := groundVote_exists
      (attestation_mem_schedule_ground hschedule)
    have hvmod : v = s % 2 := by simpa [vote] using hvin
    refine ⟨s, vote s, scheduled_vote_sent_before hschedule, ?_, rfl⟩
    rw [vote_data_slot]
    simp [E, hs, hvmod]
  · intro v hv s s' n n' a a' hvote hvote'
    obtain ⟨hsmod, hs, hn, ha⟩ := vote_some_iff.mp hvote
    obtain ⟨hsmod', hs', hn', ha'⟩ := vote_some_iff.mp hvote'
    subst n
    subst a
    subst n'
    subst a'
    interval_cases s <;> interval_cases s' <;>
      simp_all [vote, is_slashable_attestation_data,
        anchorCheckpoint, anchor, child]
  · intro v hv
    rcases honest_eq_zero_or_one hv with rfl | rfl <;> decide


theorem pjf_current_epoch_le (st : BeaconState Root) :
    (pjf st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg st.slot := by
  simp [pjf, anchorCheckpoint]

theorem active_index_lt_two {i : ValidatorIndex} {e : Epoch}
    (hactive : is_active_validator (E.registry.getD i default) e = true) :
    i < 2 := by
  cases i with
  | zero => decide
  | succ i =>
      cases i with
      | zero => decide
      | succ i =>
          simp [Execution.registry, Execution.anchor_state, E, state,
            anchorBlock, val, get_forkchoice_store,
            is_active_validator] at hactive
          have hexit : (default : Validator).exit_epoch = 0 := rfl
          rw [hexit] at hactive
          exact (Nat.not_lt_zero e hactive.2).elim

theorem committee_coverage_at {i : ValidatorIndex} {e : Epoch}
    (hi : i < 2) (he : e < 2) :
    ∃ s : Slot, E.SlotWithinHorizon cfg s ∧
      compute_epoch_at_slot cfg s = e ∧ i ∈ E.committee s := by
  have hslt : e * 2 + i < 4 := by
    interval_cases e <;> interval_cases i <;> decide
  refine ⟨e * 2 + i, slot_within_of_lt_four hslt, ?_, ?_⟩
  all_goals interval_cases e <;> interval_cases i <;> decide

theorem processSlots_registry (st : BeaconState Root) (s : Slot) :
    (ext.process_slots st s).validators = st.validators := by
  simp only [ext, processSlots]
  split <;> rfl

theorem transition_registry (st : BeaconState Root)
    (b : SignedBeaconBlock Root) (st' : BeaconState Root)
    (h : ext.state_transition st b = some st') :
    st'.validators = st.validators := by
  simp only [ext, transition] at h
  split at h
  · next hguard =>
      simp only [Option.some.injEq] at h
      subst st'
      have hst : st = state 0 := sameProjectedState_iff_eq.mp hguard.1
      subst st
      rfl
  · contradiction

theorem store_registryConstant (v : ValidatorIndex) (n : ℕ) :
    RegistryConstant E.registry (E.store cfg ext v n) := by
  induction n with
  | zero =>
      exact E.genesis_registryConstant cfg ⟨state 0, anchorBlock, rfl⟩
  | succ n ih =>
      change RegistryConstant E.registry
        ((E.schedule v (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
      refine registryConstant_foldl
        (fun store event hstore => apply_event_getD_registryConstant
          cfg ext transition_registry processSlots_registry store event hstore)
        _ _ ?_
      exact on_tick_registryConstant cfg _ _ ih

theorem causalStore_registryConstant {store : Store Root}
    (hstore : E.CausalStore cfg ext store) :
    RegistryConstant E.registry store := by
  cases hstore with
  | genesis =>
      exact E.genesis_registryConstant cfg ⟨state 0, anchorBlock, rfl⟩
  | scheduledPrefix p =>
      unfold Execution.ScheduledEventPrefix.store
      refine registryConstant_foldl
        (fun store event hstore => apply_event_getD_registryConstant
          cfg ext transition_registry processSlots_registry store event hstore)
        _ _ ?_
      exact on_tick_registryConstant cfg _ _
        (store_registryConstant p.node p.previousSecond)

theorem reachableValidationState_nonempty {st : BeaconState Root}
    (hstate : E.ReachableValidationState cfg ext st) : st.validators ≠ [] := by
  obtain ⟨store, hstore, hstate⟩ := hstate
  have hreg := causalStore_registryConstant
    (hstore.causal cfg ext)
  have heq : st.validators = E.registry := by
    rcases hstate with ⟨root, hroot, rfl⟩ | ⟨checkpoint, hcheckpoint, rfl⟩
    · exact hreg.1 root hroot
    · exact hreg.2 checkpoint hcheckpoint
  rw [heq]
  decide

theorem externalsCoherence : BeaconExternalsPremises cfg ext E := by
  constructor
  · intro st s hlt
    simp only [ext, processSlots]
    split <;> rfl
  · intro st s
    exact processSlots_registry st s
  · intro st b st' h
    simp only [ext, transition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        rw [hguard.2]
        rfl
    · contradiction
  · intro st b st' h
    exact transition_registry st b st' h
  · intro st b st' h
    simp only [ext, transition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        have hst : st = state 0 := sameProjectedState_iff_eq.mp hguard.1
        subst st
        rw [hguard.2]
        decide
    · contradiction
  · intro st b st' h
    simp only [ext, transition] at h
    split at h
    · next hguard =>
        simp only [Option.some.injEq] at h
        subst st'
        rw [hguard.2]
        decide
    · contradiction
  · intro st
    exact pjf_current_epoch_le st
  · intro v hv n s hn hs
    simp [get_slot_committee, ext, E]
  · intro st a hreachable v hv hsingle hcommittee hvote
    rcases hvote with ⟨m, a', hvote, hdata⟩
    let s := a.data.slot
    have hvoteS : E.vote v s = some (m, a') := by simpa [s] using hvote
    obtain ⟨hsmod, hs, hm, ha'⟩ := vote_some_iff.mp hvoteS
    subst m
    subst a'
    have ha : a = vote s := by
      cases a
      simp_all [vote]
    have hmem : a ∈ groundVotes := by
      rw [ha]
      exact vote_mem_ground hs
    exact (valid_iff st a).2
      ⟨reachableValidationState_nonempty hreachable, hmem⟩
  · intro st a _hreachable hvalid v hv hvin
    have haGround := ((valid_iff st a).mp hvalid).2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    exact recorded_vote_of_attester hs hvin
  · intro st a _hreachable hvalid i hi
    have haGround := ((valid_iff st a).mp hvalid).2
    obtain ⟨s, hs, rfl⟩ := groundVote_exists haGround
    have hi' : i = s % 2 := by simpa [vote] using hi
    rw [vote_data_slot]
    simpa [E, hi']
  · intro i s s' hs hs' hepoch
    have his : i = s % 2 := by simpa [E] using hs
    have his' : i = s' % 2 := by simpa [E] using hs'
    have hmod : s % 2 = s' % 2 := his.symm.trans his'
    have hdiv : s / 2 = s' / 2 := by
      simpa [cfg, compute_epoch_at_slot] using hepoch
    calc
      s = s % 2 + 2 * (s / 2) := (Nat.mod_add_div s 2).symm
      _ = s' % 2 + 2 * (s' / 2) := by rw [hmod, hdiv]
      _ = s' := Nat.mod_add_div s' 2
  · intro i e he hactive
    have helt : e < 2 := by simpa [E] using he
    exact committee_coverage_at (active_index_lt_two hactive) helt
  · intro i s hs hi
    have hslt := slot_lt_four hs
    interval_cases s <;>
      simp [E] at hi <;>
      subst i <;> decide
  · intro a
    have hdefault : (default : BeaconState Root).validators = [] := rfl
    simp [ext, hdefault]
  · intro st slot a _hreachable _hlt
    change decide ((ext.process_slots st slot).validators ≠ [] ∧
      a ∈ groundVotes) = decide (st.validators ≠ [] ∧ a ∈ groundVotes)
    rw [processSlots_registry]
  · intro st signed o o'
    rfl


theorem staticValidatorSet : StaticValidatorSet cfg E := by
  constructor
  · exact time_within_of_lt_four (by decide)
  · intro i e e' he he'
    have helt : e < 2 := by simpa [E] using he
    have helt' : e' < 2 := by simpa [E] using he'
    interval_cases e <;> interval_cases e'
    all_goals
      cases i with
      | zero => decide
      | succ i =>
          cases i with
          | zero => decide
          | succ i => rfl

set_option maxRecDepth 20000 in
theorem byzantineBound : ByzantineWeightPremises cfg E := by
  constructor
  · intro i
    cases i with
    | zero => decide
    | succ i =>
        cases i with
        | zero => decide
        | succ i =>
            simp [Execution.weight_of, Execution.registry,
              Execution.anchor_state, E, state, anchorBlock,
              val, cfg, get_forkchoice_store]
            exact dvd_zero 100
  · intro a b ha hb
    have halt := slot_lt_four ha
    have hblt := slot_lt_four hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 50000 in decide
  · intro a b ha hb
    have halt := slot_lt_four ha
    have hblt := slot_lt_four hb
    interval_cases a <;> interval_cases b <;>
      set_option maxRecDepth 50000 in decide

theorem synchrony : Synchrony cfg ext E := by
  refine {
    delta := ⟨500, by decide, by decide⟩
    attestation_delivery := ?_
    deadline_block_relay := ?_
    boundary_block_prefix := ?_
    attester_slashing_relay := ?_
  }
  · intro v hv s n a hs hn hvote _hdeadline hdelivery w hw
    obtain ⟨hvmod, hslt, hn', ha⟩ := vote_some_iff.mp hvote
    subst n
    subst a
    exact vote_false_delivery hslt w
  · intro v hv n r hn hr _hdeadline w hw m hm _hnext hlt
    left
    rw [← store_symmetric v w m]
    exact (E.store_storeLE cfg ext v hlt.le).1 hr
  · intro v hv n r hn hr _hdeadline w hw boundary hHboundary hlt
      a before after _hschedule _hnotExcluded
    have hnpred : n ≤ boundary - 1 := by omega
    have hrootPred : r ∈ (E.store cfg ext w (boundary - 1)).block_roots := by
      rw [← store_symmetric v w (boundary - 1)]
      exact (E.store_storeLE cfg ext v hnpred).1 hr
    have hrootTick : r ∈
        (on_tick cfg (E.store cfg ext w (boundary - 1))
          (E.time_at boundary)).block_roots :=
      (on_tick_storeLE cfg _ _).1 hrootPred
    exact (foldl_storeLE cfg ext before _).1 hrootTick
  · intro v hv n i hn hi _hdue w hw m hm _hnext hlt
    have hnm : n ≤ m := hlt.le
    rw [← store_symmetric v w m]
    exact (E.store_storeLE cfg ext v hnm).2.2.1 hi

private theorem schedule_no_envelope (v n : ℕ) (event : Event Root)
    (hmem : event ∈ schedule v n) :
    ∀ signed observation,
      event ≠ Event.execution_payload_envelope signed observation := by
  intro signed observation heq
  subst event
  simp [schedule] at hmem
  split_ifs at hmem <;> simp_all

private theorem other_event_payloads (store : Store Root) (event : Event Root)
    (hne : ∀ signed observation,
      event ≠ Event.execution_payload_envelope signed observation) :
    ((apply_event cfg ext store event).getD store).payloads = store.payloads := by
  cases event with
  | block block =>
      cases h : on_block cfg ext store block with
      | none => simp [apply_event, h]
      | some next => simpa [apply_event, h] using on_block_payloads cfg ext h
  | attestation attestation fromBlock =>
      cases h : on_attestation cfg ext store attestation fromBlock with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using on_attestation_payloads cfg ext h
  | attester_slashing slashing =>
      cases h : on_attester_slashing ext store slashing with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using on_attester_slashing_payloads ext h
  | execution_payload_envelope signed observation =>
      exact (hne signed observation rfl).elim
  | payload_attestation_message message fromBlock =>
      cases h : on_payload_attestation_message cfg ext store message fromBlock with
      | none => simp [apply_event, h]
      | some next =>
          simpa [apply_event, h] using
            on_payload_attestation_message_payloads cfg ext h

private theorem fold_no_envelope (events : List (Event Root))
    (store : Store Root)
    (hno : ∀ event ∈ events, ∀ signed observation,
      event ≠ Event.execution_payload_envelope signed observation) :
    (events.foldl
      (fun s event => (apply_event cfg ext s event).getD s)
      store).payloads = store.payloads := by
  induction events generalizing store with
  | nil => rfl
  | cons event tail ih =>
      simp only [List.foldl_cons]
      have he := hno event (List.mem_cons_self)
      have ht : ∀ e ∈ tail, ∀ signed observation,
          e ≠ Event.execution_payload_envelope signed observation := by
        intro e he'
        exact hno e (List.mem_cons_of_mem event he')
      exact (ih _ ht).trans (other_event_payloads store event he)

private theorem schedule_fold_payloads (v n : ℕ) (store : Store Root) :
    ((schedule v n).foldl
      (fun s event => (apply_event cfg ext s event).getD s)
      store).payloads = store.payloads := by
  apply fold_no_envelope
  intro event hmem
  exact schedule_no_envelope v n event hmem

private theorem payloads_empty (v n : ℕ) :
    (E.store cfg ext v n).payloads = E.genesis_store.payloads := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [Execution.store] using
        (schedule_fold_payloads v (n + 1)
          (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1)))).trans
          ((on_tick_payloads cfg _ _).trans ih)

theorem paperSafetySynchrony : NextSlotSynchronyPremises cfg ext E := by
  apply synchrony.toPaperSafetySynchrony cfg ext
  · intro v hv n r hn hr
    have hempty := payloads_empty v n
    have hnone : E.genesis_store.payloads r = none := rfl
    have hfalse : is_payload_verified (E.store cfg ext v n) r = false := by
      simp only [is_payload_verified, hempty, hnone, Option.isSome_none]
    rw [hfalse] at hr
    cases hr
  · intro v hv k n signed sourceObservation hk hn hevent havailable
    have hno := schedule_no_envelope v k _ hevent signed sourceObservation
    exact (hno rfl).elim

theorem voteDeliveryLookahead : HorizonVoteDeliveryLookahead cfg E := by
  constructor
  intro v hv s n a hs hn hvote _hdeadline w hw
  obtain ⟨hvmod, hslt, hn', ha⟩ := vote_some_iff.mp hvote
  subst n
  subst a
  exact vote_false_delivery hslt w

theorem trajectory : E.ScheduledPrefixPremises cfg ext := by
  exact
    { whole_seconds := by decide
      wellFormed := wellFormed
      externals_coherence := externalsCoherence
      honest_behavior := honestBehavior
      genesis := ⟨state 0, anchorBlock, rfl, rfl, ⟨rfl, rfl⟩, by decide⟩ }

theorem phase0SourceCoherence : Phase0SourceCoherence cfg ext := by
  constructor
  · intro st target hlt hepoch
    simp only [ext, processSlots]
    have hnot : ¬ compute_epoch_at_slot cfg st.slot <
        compute_epoch_at_slot cfg target := by
      intro hstrict
      exact (Nat.ne_of_lt hstrict) hepoch
    rw [if_neg hnot]
  · intro pre sb post htransition hepoch
    simp only [ext, transition] at htransition
    split at htransition
    · next hguard =>
        simp only [Option.some.injEq] at htransition
        subst post
        have hpre : pre = state 0 := sameProjectedState_iff_eq.mp hguard.1
        subst pre
        rfl
    · contradiction

theorem phase0BoundarySourceCoherence : Phase0BoundarySourceCoherence cfg ext := by
  constructor
  · intro st target hlt hcross
    simp only [ext, processSlots]
    rw [if_pos hcross]
  · intro pre sb post htransition hcross
    simp only [ext, transition] at htransition
    split at htransition
    · next hguard =>
        simp only [Option.some.injEq] at htransition
        subst post
        have hpre : pre = state 0 := sameProjectedState_iff_eq.mp hguard.1
        subst pre
        rw [hguard.2] at hcross
        norm_num [state, anchorBlock, childBlock, cfg,
          compute_epoch_at_slot] at hcross
    · contradiction

theorem balanceFloor : cfg.effective_balance_increment ≤
    E.weight (E.currentTargetAnchorActive cfg) := by decide

theorem epochEndsFit : EpochEndsFitUint64 cfg := by
  refine ⟨2 ^ 63, ?_⟩
  norm_num [EpochEndsFitUint64, UINT64_MAX, cfg]

theorem anchorEquality : E.genesis_store.justified_checkpoint =
    anchorCheckpoint := by decide

theorem anchorBoundary : Execution.TrustedAnchorBoundaryAligned
    (cfg := cfg) (E := E) (anchor := anchorCheckpoint) := by
  unfold Execution.TrustedAnchorBoundaryAligned
  decide


/-! ## Accepted FFG interpretation -/

def childPrefix : E.ScheduledEventPrefix where
  node := 0
  previousSecond := 0
  processedCount := 0
  count_le := by decide

def childPostPrefix : E.ScheduledEventPrefix :=
  childPrefix.successor (by decide)

set_option maxRecDepth 50000 in
theorem child_on_block_accepted :
    on_block cfg ext (childPrefix.store cfg ext) childBlock =
      some (childPostPrefix.store cfg ext) := by rfl

def childTransition : E.AcceptedBlockTransition cfg ext where
  atPrefix := childPrefix
  signedBlock := childBlock
  event_at := by rfl
  postStore := childPostPrefix.store cfg ext
  accepted := child_on_block_accepted

theorem anchor_accepted : E.AcceptedRoot cfg ext anchor := by
  refine ⟨E.genesis_store, .genesis, ?_⟩
  simp [E, get_forkchoice_store, anchorBlock]

theorem child_accepted : E.AcceptedRoot cfg ext child := by
  simpa [childBlock] using childTransition.root_accepted

theorem child_acceptedBlockAt : E.AcceptedBlockAt cfg ext child
    childBlock.message := by
  refine ⟨childTransition.postStore, childTransition.post_causal, ?_, ?_⟩
  · simpa [childBlock] using childTransition.root_known
  · simpa [childBlock] using
      childTransition.inserted_message_fresh (by decide)

theorem scheduledBlock_eq_child {b : SignedBeaconBlock Root}
    (h : IsScheduledBlock E b) : b = childBlock := by
  obtain ⟨w, n, hmem⟩ := h
  exact (block_mem_schedule_iff.mp hmem).2

theorem causal_known_table {store : Store Root}
    (hstore : E.CausalStore cfg ext store)
    {r : Root} (hr : r ∈ store.block_roots) :
    (r = anchor ∧ store.blocks r = anchorBlock.message) ∨
      (r = child ∧ store.blocks r = childBlock.message) := by
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · have hrAnchor : r = anchor := by
      simpa [E, get_forkchoice_store, anchorBlock] using hgen.1
    left
    refine ⟨hrAnchor, ?_⟩
    rw [hgen.2, hrAnchor]
    simp [E, get_forkchoice_store, anchorBlock]
  · obtain ⟨b, hb, hroot, hmessage⟩ := hsched
    have hbchild := scheduledBlock_eq_child hb
    subst b
    right
    exact ⟨hroot.symm, hmessage⟩

theorem causal_anchor_known {store : Store Root}
    (hstore : E.CausalStore cfg ext store) :
    anchor ∈ store.block_roots := by
  cases hstore with
  | genesis => simp [E, get_forkchoice_store, anchorBlock]
  | scheduledPrefix p =>
      apply (p.genesisStoreLE cfg ext).1
      simp [E, get_forkchoice_store, anchorBlock]

theorem causal_anchor_message {store : Store Root}
    (hstore : E.CausalStore cfg ext store) :
    store.blocks anchor = anchorBlock.message := by
  have hknown := causal_anchor_known hstore
  rcases causal_known_table hstore hknown with h | h
  · exact h.2
  · exact False.elim ((by decide : anchor ≠ child) h.1)

theorem causal_child_message {store : Store Root}
    (hstore : E.CausalStore cfg ext store)
    (hknown : child ∈ store.block_roots) :
    store.blocks child = childBlock.message := by
  rcases causal_known_table hstore hknown with h | h
  · exact False.elim ((by decide : child ≠ anchor) h.1)
  · exact h.2

theorem acceptedRoot_cases {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    r = anchor ∨ r = child := by
  obtain ⟨store, hstore, hknown⟩ := hr
  rcases causal_known_table hstore hknown with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem acceptedBlockAt_cases {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) :
    (r = anchor ∧ b = anchorBlock.message) ∨
      (r = child ∧ b = childBlock.message) := by
  obtain ⟨store, hstore, hr, hblock⟩ := h
  rcases causal_known_table hstore hr with h | h
  · left; exact ⟨h.1, hblock.symm.trans h.2⟩
  · right; exact ⟨h.1, hblock.symm.trans h.2⟩

theorem child_parentEdge : E.ParentEdge child anchor := by
  exact Or.inr ⟨0, 1, childBlock,
    block_mem_schedule_iff.mpr ⟨rfl, rfl⟩, rfl, rfl⟩

theorem child_descends_anchor : E.RootDescends child anchor :=
  .step child_parentEdge (.refl anchor)

theorem acceptedRoot_descends_anchor {r : Root}
    (hr : E.AcceptedRoot cfg ext r) : E.RootDescends r anchor := by
  rcases acceptedRoot_cases hr with rfl | rfl
  · exact .refl anchor
  · exact child_descends_anchor

/-- There are no included attestations in the two-block run. -/
def included (_carrier : Root) (_a : Attestation Root) : Prop := False

def includedAttestations : Execution.CausalCarrierAttestationRelation
    cfg ext E ext.is_valid_indexed_attestation where
  Included := included
  evidence := by
    intro carrier a h
    exact False.elim h

def C (r : Root) (e : Epoch) : Checkpoint Root :=
  { epoch := e
    root := if r = child ∧ 0 < e then child else anchor }

def formed (r : Root) (c : Checkpoint Root) : Prop :=
  r = anchor ∧ c = anchorCheckpoint

theorem formed_anchor : formed anchor anchorCheckpoint := ⟨rfl, rfl⟩

def ffgState : CausalCarrierFFGState cfg ext E anchorCheckpoint where
  attestationValidity := ext.is_valid_indexed_attestation
  includedAttestations := includedAttestations
  formed := formed
  C := C
  GJ := fun _ => anchorCheckpoint
  GU := fun _ => anchorCheckpoint
  GF := fun _ => anchorCheckpoint
  GUF := fun _ => anchorCheckpoint
  checkpoint_epoch := by intro r e; rfl
  formed_carrier_accepted := by
    intro r c h
    rcases h with ⟨rfl, rfl⟩
    exact anchor_accepted
  formed_evidence := by
    intro r c h
    rcases h with ⟨rfl, rfl⟩
    exact
      { certified := ⟨IncludedCertifiedJustified.anchor⟩
        on_chain := .refl anchor
        causal := Or.inl rfl }
  gj_mem := by
    intro r hr
    exact ⟨anchor, acceptedRoot_descends_anchor hr, formed_anchor⟩
  gu_mem := by
    intro r hr
    exact ⟨anchor, acceptedRoot_descends_anchor hr, formed_anchor⟩
  gf_mem := by
    intro r hr
    exact ⟨anchor, acceptedRoot_descends_anchor hr, formed_anchor⟩
  guf_mem := by
    intro r hr
    exact ⟨anchor, acceptedRoot_descends_anchor hr, formed_anchor⟩
  gj_anchor_or_before := by
    intro r b haccepted
    exact Or.inl rfl
  gj_max := by
    intro r b c haccepted hformed hepoch
    obtain ⟨carrier, hdesc, ⟨rfl, rfl⟩⟩ := hformed
    rfl
  gu_max := by
    intro r c hr hformed
    obtain ⟨carrier, hdesc, ⟨rfl, rfl⟩⟩ := hformed
    rfl
  au_epoch_le_block := by
    intro r b c haccepted hformed
    obtain ⟨carrier, hdesc, ⟨rfl, rfl⟩⟩ := hformed
    exact Nat.zero_le _
  gf_evidence := by intro r hr; exact Or.inl rfl
  guf_evidence := by intro r hr; exact Or.inl rfl
  gf_epoch_le_gj := by intro r hr; rfl
  guf_epoch_le_gu := by intro r hr; rfl


theorem checkpointOfKnown {store : Store Root}
    (hstore : E.CausalStore cfg ext store) (r : Root)
    (hr : r ∈ store.block_roots) (e : Epoch) :
    C r e = get_checkpoint_for_block cfg store r e := by
  have hanchor := causal_anchor_message hstore
  rcases causal_known_table hstore hr with hroot | hroot
  · rcases hroot with ⟨rfl, hroot⟩
    apply checkpoint_eq_of_epoch_root_eq <;>
      simp [C, get_checkpoint_for_block, get_checkpoint_block,
        compute_start_slot_at_epoch, get_ancestor, get_ancestor_aux,
        cfg, anchorBlock, hanchor, (by decide : anchor ≠ child)]
  · rcases hroot with ⟨rfl, hchild⟩
    cases e with
    | zero =>
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [C, get_checkpoint_for_block, get_checkpoint_block,
            compute_start_slot_at_epoch, get_ancestor, get_ancestor_aux,
            cfg, anchorBlock, childBlock, hanchor, hchild]
    | succ e =>
        have hstop : ¬ 1 > (e + 1) * 2 := by
          have htwo : 2 ≤ (e + 1) * 2 := by
            change 1 * 2 ≤ (e + 1) * 2
            exact Nat.mul_le_mul_right 2 (by simp)
          exact Nat.not_lt_of_ge ((by decide : 1 ≤ 2).trans htwo)
        apply checkpoint_eq_of_epoch_root_eq <;>
          simp [C, get_checkpoint_for_block, get_checkpoint_block,
            compute_start_slot_at_epoch, get_ancestor, get_ancestor_aux,
            cfg, hchild, childBlock, hstop]

theorem au_cases {r : Root} {c : Checkpoint Root}
    (hAU : ffgState.AU cfg ext r c) : c = anchorCheckpoint := by
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  exact hformed.2

theorem auCheckpointOfKnown {store : Store Root}
    (hstore : E.CausalStore cfg ext store) (r : Root)
    (hr : r ∈ store.block_roots) (c : Checkpoint Root)
    (hAU : ffgState.AU cfg ext r c) :
    c = get_checkpoint_for_block cfg store r c.epoch := by
  have hc := au_cases hAU
  subst c
  rcases causal_known_table hstore hr with h | h
  · rcases h with ⟨rfl, hmessage⟩
    simpa [anchorCheckpoint] using checkpointOfKnown hstore anchor hr 0
  · rcases h with ⟨rfl, hmessage⟩
    simpa [anchorCheckpoint] using checkpointOfKnown hstore child hr 0

theorem acceptedTransition_case
    (t : E.AcceptedBlockTransition cfg ext) :
    t.signedBlock = childBlock ∧
      t.postStore.block_states child = state 1 := by
  have heventMem : Event.block t.signedBlock ∈
      E.schedule t.atPrefix.node (t.atPrefix.previousSecond + 1) := by
    obtain ⟨hlt, hevent⟩ := List.getElem?_eq_some_iff.mp t.event_at
    have hmem := List.getElem_mem hlt
    rw [hevent] at hmem
    exact hmem
  obtain ⟨hprev, hblock⟩ := block_mem_schedule_iff.mp heventMem
  have hprev' : t.atPrefix.previousSecond = 0 := by omega
  have hcountLe : t.atPrefix.processedCount ≤ 2 := by
    simpa [E, schedule, hprev'] using t.atPrefix.count_le
  have hevent := t.event_at
  simp only [E, schedule, hprev'] at hevent
  have hcount : t.atPrefix.processedCount = 0 := by
    interval_cases hp : t.atPrefix.processedCount <;> simp_all
  have hpostPrefix :
      t.successorPrefix.store cfg ext = childPostPrefix.store cfg ext := by
    simp only [Execution.AcceptedBlockTransition.successorPrefix,
      Execution.ScheduledEventPrefix.successor,
      Execution.ScheduledEventPrefix.store, childPostPrefix,
      childPrefix, hprev', hcount]
    rw [store_symmetric t.atPrefix.node 0 0]
    rfl
  have hpostStore : t.postStore = childPostPrefix.store cfg ext := by
    rw [← t.successorPrefix_store]
    exact hpostPrefix
  refine ⟨hblock, ?_⟩
  rw [hpostStore]
  rfl

theorem genesis_known_eq_anchor {r : Root}
    (hr : r ∈ E.genesis_store.block_roots) : r = anchor := by
  simpa [E, get_forkchoice_store, anchorBlock] using hr

def ffgCoherence : FFGSelectorsAndCheckpointReadsMatchBeaconStates
    cfg ext ffgState where
  genesis_gj := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_gf := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_gu := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_guf := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  genesis_unrealized_justification := by
    intro r hr
    have hr' := genesis_known_eq_anchor hr
    subst r
    rfl
  transition_gj := by
    intro t
    have h := acceptedTransition_case t
    rw [h.1]
    change (t.postStore.block_states child).current_justified_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl
  transition_gf := by
    intro t
    have h := acceptedTransition_case t
    rw [h.1]
    change (t.postStore.block_states child).finalized_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl
  transition_gu := by
    intro t
    have h := acceptedTransition_case t
    rw [h.1]
    change (pjf (t.postStore.block_states child)).current_justified_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl
  transition_guf := by
    intro t
    have h := acceptedTransition_case t
    rw [h.1]
    change (pjf (t.postStore.block_states child)).finalized_checkpoint =
      anchorCheckpoint
    rw [h.2]
    rfl
  checkpoint_of_known := by
    intro store hstore r hr e
    exact checkpointOfKnown hstore r hr e
  au_checkpoint_of_known := by
    intro store hstore r hr c hAU
    exact auCheckpointOfKnown hstore r hr c hAU

def semantics : CausalPrefixFFGInterpretation cfg ext E where
  anchor := anchorCheckpoint
  state := ffgState
  coherence := ffgCoherence


def checkpointProjection : EpochCheckpointClosure anchorCheckpoint
    (E.AcceptedRoot cfg ext) C where
  checkpoint_root_accepted := by
    intro r e hr hanchor
    rcases acceptedRoot_cases hr with rfl | rfl
    · simpa [C, anchor, child] using anchor_accepted
    · cases e with
      | zero => simpa [C, anchor, child] using anchor_accepted
      | succ e => simpa [C, anchor, child] using child_accepted
  checkpoint_comp := by
    intro r sourceEpoch targetEpoch hr hanchor hle
    rcases acceptedRoot_cases hr with rfl | rfl
    · simp [C, anchor, child]
    · cases targetEpoch with
      | zero =>
          have : sourceEpoch = 0 := Nat.eq_zero_of_le_zero hle
          subst sourceEpoch
          simp [C, anchor, child]
      | succ targetEpoch =>
          cases sourceEpoch with
          | zero => simp [C, anchor, child]
          | succ sourceEpoch => simp [C, anchor, child]

theorem paperA32 : ffgState.PaperA32Inclusion cfg ext := by
  constructor
  intro b bb e hb hbe hcanonical hsupport w hw m hHm hboundary
  have hmlt := time_lt_four hHm
  rw [slot_at_eq] at hboundary
  change (e + 2) * 2 ≤ m at hboundary
  have hfour : 4 ≤ (e + 2) * 2 := by
    change 2 * 2 ≤ (e + 2) * 2
    exact Nat.mul_le_mul_right 2 (by simp)
  have hbad : 4 ≤ m := hfour.trans hboundary
  exact False.elim ((Nat.not_le_of_gt hmlt) hbad)

theorem noIncludedLink {carrier : Root}
    {source target : Checkpoint Root}
    (L : IncludedSupermajorityLink cfg E included carrier source target) :
    False := by
  have hsigners : L.signers.Nonempty := by
    by_contra hnone
    have hempty : L.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * E.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using L.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by decide) (E.total_active_pos cfg))
  obtain ⟨i, hi⟩ := hsigners
  obtain ⟨a, ⟨containing, hdesc, hincluded⟩, hiatt,
    hsource, htarget⟩ := L.signer_attestation i hi
  exact hincluded

def exactLinkValidity : ffgState.ExactLinkValidity where
  carrier_accepted := by
    intro carrier source target L hcontributing
    exact False.elim (noIncludedLink L)
  endpoints_on_carrier := by
    intro carrier source target L hcontributing
    exact False.elim (noIncludedLink L)

theorem finalizationDelay : E.RealizedFinalizationDelay cfg ext semantics := by
  intro t
  change (t.postStore.block_states t.signedBlock.root).finalized_checkpoint =
      anchorCheckpoint ∨
    (t.postStore.block_states t.signedBlock.root).finalized_checkpoint.epoch + 2 ≤
      compute_epoch_at_slot cfg t.signedBlock.message.slot
  left
  have h := acceptedTransition_case t
  rw [h.1]
  change (t.postStore.block_states child).finalized_checkpoint =
    anchorCheckpoint
  rw [h.2]
  rfl


/-! ## Literal selected-helper provisos -/

private theorem bounded_no_currentTargetAcceptedEdge_under_selector :
    ∀ (v : Fin 2) (n : Fin 3) (a c : Root),
      getLatestSelectorGuard cfg
        (E.fcrStoreAtCall cfg ext v.val n.val)
        (E.getLatestConfirmedTraceAt cfg ext v.val n.val).afterObserved →
      (a, c) ∈
        (findLatestSelectedTrace cfg ext
          (E.fcrStoreAtCall cfg ext v.val n.val)
          (E.getLatestConfirmedTraceAt cfg ext v.val n.val).afterObserved).2.2 →
      get_block_epoch cfg (E.fcrStoreAtCall cfg ext v.val n.val).store a <
        get_block_epoch cfg (E.fcrStoreAtCall cfg ext v.val n.val).store c →
      False := by
  simp only [getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide

private theorem bounded_no_selectedPreviousResult_under_selector :
    ∀ (v : Fin 2) (n : Fin 3) (result : Root),
      getLatestSelectorGuard cfg
        (E.fcrStoreAtCall cfg ext v.val n.val)
        (E.getLatestConfirmedTraceAt cfg ext v.val n.val).afterObserved →
      find_latest_confirmed_descendant cfg ext
        (E.fcrStoreAtCall cfg ext v.val n.val)
        (E.getLatestConfirmedTraceAt cfg ext v.val n.val).afterObserved = result →
      result ≠
        (E.getLatestConfirmedTraceAt cfg ext v.val n.val).afterObserved →
      get_block_epoch cfg (E.fcrStoreAtCall cfg ext v.val n.val).store result ≠
        get_current_store_epoch cfg
          (E.fcrStoreAtCall cfg ext v.val n.val).store →
      is_start_slot_at_epoch cfg
        (get_current_slot cfg (E.fcrStoreAtCall cfg ext v.val n.val).store)
          ≠ true → False := by
  simp only [getLatestSelectorGuard]
  set_option maxRecDepth 50000 in decide


theorem selectedHelperProvisos
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hselector : getLatestSelectorGuard cfg
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved) :
    FCRPredictionSupportAt cfg ext E v (n + 1)
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved := by
  have hnlt := time_lt_four hHn1
  have hnlt' : n < 3 := by
    exact Nat.lt_of_succ_lt_succ (by
      simpa [Nat.succ_eq_add_one] using hnlt)
  have hvlt : v < 2 := by
    rcases honest_eq_zero_or_one hv with rfl | rfl <;> decide
  let vf : Fin 2 := ⟨v, hvlt⟩
  let nf : Fin 3 := ⟨n, hnlt'⟩
  refine
    { current_target := ?_
      selected_previous_result_no_conflict := ?_ }
  · intro a c hedge
    rcases hedge with ⟨hmem, hlt⟩
    exact False.elim (bounded_no_currentTargetAcceptedEdge_under_selector
      vf nf a c hselector hmem hlt)
  · intro result hout hstrict hprevious hnotStart
    exact False.elim
      (bounded_no_selectedPreviousResult_under_selector
        vf nf result hselector hout hstrict hprevious hnotStart)

def completedCalls : E.CompletedFCRCallPremises cfg ext where
  synchrony := paperSafetySynchrony
  static_validators := staticValidatorSet
  byzantine_bound := byzantineBound
  phase0_source := phase0SourceCoherence
  phase0_boundary_source := phase0BoundarySourceCoherence
  balance_floor := balanceFloor
  delivery_lookahead := voteDeliveryLookahead

def acceptedBundle : E.NextSlotSafetyPremises cfg ext where
  semantics := semantics
  trajectory := trajectory
  completed_calls := completedCalls
  epoch_ends_fit := epochEndsFit
  anchor_eq := by
    simpa only [semantics] using anchorEquality.symm
  anchor_boundary := by
    simpa only [semantics] using anchorBoundary
  finalization_delay := finalizationDelay
  slots_per_epoch_gt_one := by decide
  paper_a32 := paperA32
  checkpoint_projection := checkpointProjection
  exact_link_validity := exactLinkValidity


/-- The same FFG interpretation satisfies the interpretation-fidelity record.
The run includes no vote, so body membership and validity hold vacuously. -/
theorem ffg_interpretation_fidelity :
    FFGInterpretationFidelity cfg ext E acceptedBundle.semantics where
  included_fidelity := by
    intro carrier a h
    exact False.elim h
  attestation_validity := rfl
  gf_epoch_le_guf := by
    intro r hr
    rfl

/-- One accepted finite run with a completed epoch, every live field, and an
actual strict change in the stored confirmed root. -/
theorem joint_witness :
    Nonempty (E.NextSlotSafetyPremises cfg ext) ∧
    LiveMonotonicityPremises cfg ext E 0 1 2 ∧
    0 ∈ E.honest ∧
    1 < 2 ∧
    E.WithinHorizon cfg 2 ∧
    E.slot_at cfg 1 < compute_start_slot_at_epoch cfg 1 ∧
    compute_start_slot_at_epoch cfg 1 ≤ E.slot_at cfg 2 ∧
    E.confirmed cfg ext 0 1 ≠ E.confirmed cfg ext 0 2 := by
  refine ⟨⟨acceptedBundle⟩, livePremises, by decide, by decide,
    within_two, by decide, by decide, ?_⟩
  rw [confirmed_at_one, confirmed_at_two]
  decide

/-- The public live theorem applies to the same strict advancing interval. -/
theorem joint_monotonicity :
    is_ancestor (E.store cfg ext 0 2)
      (get_node_for_root (E.confirmed cfg ext 0 2))
      (get_node_for_root (E.confirmed cfg ext 0 1)) = true ∧
    E.confirmed cfg ext 0 1 ≠ E.confirmed cfg ext 0 2 := by
  obtain ⟨haccepted, hlive, hhonest, hstrict, hH,
    hbefore, hafter, hadvance⟩ := joint_witness
  exact ⟨live_confirmed_root_monotonicity cfg ext E haccepted
    0 hhonest 1 2 (Nat.le_of_lt hstrict) hH hlive, hadvance⟩


end LiveMonotonicityWitness
end FastConfirmation.Spec

end
