module
public import FastConfirmation.Spec.Proof.CompleteEvidence

@[expose] public section

/-!
# Concrete complete-evidence examples

These are small model stores, not a reconstruction of the unavailable Python
fixtures. Eight validators have equal balances. Their slot committees rotate
once per eight-slot epoch. The query is at slot two, after all votes from slots
zero and one. Root zero is the anchor and root one is its child.
-/

namespace FastConfirmation.Spec.CompleteEvidenceWitness

set_option maxRecDepth 10000

def cfg : Config where
  slots_per_epoch := 8
  slots_per_epoch_pos := by decide
  slot_duration_ms := 1000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 3333
  min_seed_lookahead := 1

def anchor : Checkpoint Nat := ⟨0, 0⟩

def validator : Validator := ⟨100, false, 0, 100⟩

def state : BeaconState Nat where
  genesis_time := 0
  slot := 0
  validators := List.replicate 8 validator
  current_justified_checkpoint := anchor
  finalized_checkpoint := anchor

def ext : Externals Nat where
  get_beacon_committee := fun _ s _ => [s % 8]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st s => { st with slot := s }
  state_transition := fun st b => some { st with slot := b.message.slot }
  process_justification_and_finalization := id
  is_valid_indexed_attestation := fun _ _ => true

def store : Store Nat where
  time := 2
  genesis_time := 0
  justified_checkpoint := anchor
  finalized_checkpoint := anchor
  unrealized_justified_checkpoint := anchor
  unrealized_finalized_checkpoint := anchor
  proposer_boost_root := 0
  equivocating_indices := ∅
  block_roots := [0, 1]
  blocks := fun r => if r = 1 then ⟨1, 0⟩ else ⟨0, 9⟩
  block_states := fun _ => state
  block_timeliness := fun _ => some true
  checkpoint_state_keys := {anchor}
  checkpoint_states := fun _ => state
  latest_messages := fun i =>
    if i = 0 then some ⟨0, 0⟩ else if i = 1 then some ⟨0, 1⟩ else none
  unrealized_justifications := fun _ => anchor

def fcr : FastConfirmationStore Nat := get_fast_confirmation_store store

/-- The before-head query has already received the preceding slot's vote. -/
theorem before_head_confirms_nonanchor :
    Strong.get_latest_confirmed cfg ext fcr = 1 ∧
    Weak.get_latest_confirmed cfg ext fcr = 1 ∧
    (1 : Nat) ≠ store.finalized_checkpoint.root := by
  decide

theorem before_head_is_certified :
    (get_head cfg store).root = 1 ∧
    Weak.get_certified_head cfg ext store state = 1 ∧
    Weak.has_head_broadcast_certificate cfg ext store state = true := by
  decide

/-- The after-head query adds the slot-two proposal before its attestation.
The earlier votes and every balance source remain unchanged. -/
def afterHeadStore : Store Nat :=
  { store with
    block_roots := [0, 1, 2]
    blocks := fun r => if r = 2 then ⟨2, 1⟩ else store.blocks r }

def afterHeadFcr : FastConfirmationStore Nat := get_fast_confirmation_store afterHeadStore

/-- Complete prior-slot votes cannot certify a new current-slot proposal.
The selected carrier is its parent, so carrier equality is false. -/
theorem after_head_carrier_differs :
    (get_head cfg afterHeadStore).root = 2 ∧
    Weak.get_certified_head cfg ext afterHeadStore state = 1 ∧
    Weak.get_certified_head cfg ext afterHeadStore state ≠
      (get_head cfg afterHeadStore).root := by
  decide

/-- The false carrier equality does not make the two output roots differ. -/
theorem after_head_confirms_nonanchor :
    Strong.get_latest_confirmed cfg ext afterHeadFcr = 1 ∧
    Weak.get_latest_confirmed cfg ext afterHeadFcr = 1 ∧
    (1 : Nat) ≠ afterHeadStore.finalized_checkpoint.root := by
  decide

theorem prior_slot_committees_present :
    (∀ i ∈ get_slot_committee cfg ext store 0,
      store.latest_messages i = some ⟨0, 0⟩) ∧
    (∀ i ∈ get_slot_committee cfg ext store 1,
      store.latest_messages i = some ⟨0, 1⟩) := by
  decide

theorem after_head_prior_slot_committees_present :
    (∀ i ∈ get_slot_committee cfg ext afterHeadStore 0,
      afterHeadStore.latest_messages i = some ⟨0, 0⟩) ∧
    (∀ i ∈ get_slot_committee cfg ext afterHeadStore 1,
      afterHeadStore.latest_messages i = some ⟨0, 1⟩) := by
  decide

/-- Nonempty evidence contract, with all prior-slot committee votes present. -/
theorem complete_evidence : CompleteEvidence cfg ext fcr where
  epoch_size := Or.inl rfl
  threshold := rfl
  after_genesis := by decide
  no_equivocations := rfl
  prior_votes := by
    intro s hs i hi
    have hs' : s = 0 ∨ s = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hs)
    rcases hs' with rfl | rfl
    · exact ⟨⟨0, 0⟩, prior_slot_committees_present.1 i hi, by decide⟩
    · exact ⟨⟨0, 1⟩, prior_slot_committees_present.2 i hi, by decide⟩
  fresh := by
    intro i lm _
    have hc : Weak.recorded_cutoff_epoch cfg fcr.store = 0 := rfl
    simp [Weak.is_duty_fresh_message, hc]
  recorded_provenance := by
    intro i lm hm
    by_cases h0 : i = 0
    · subst i
      have he : (⟨0, 0⟩ : LatestMessage Nat) = lm := by simpa [fcr,
        get_fast_confirmation_store, store] using hm
      subst lm
      exact ⟨0, by decide, by decide, rfl, by decide⟩
    · by_cases h1 : i = 1
      · subst i
        have he : (⟨0, 1⟩ : LatestMessage Nat) = lm := by simpa [fcr,
          get_fast_confirmation_store, store] using hm
        subst lm
        exact ⟨1, by decide, by decide, rfl, by decide⟩
      · simp [fcr, get_fast_confirmation_store, store,
          h0, h1] at hm
  balance_sources := ⟨rfl, rfl, rfl, rfl⟩
  equal_balances := by
    refine ⟨100, by decide, ?_⟩
    intro v hv
    change v ∈ List.replicate 8 validator at hv
    have he := (List.mem_replicate.mp hv).2
    subst v
    rfl
  carrier_support := by decide
  witness_support := by decide
  realized_target_carrier := by intro _; rfl
  bank_epoch_newer := by decide
  bank_alignment := by
    intro h
    change false = true at h
    cases h

/-- The evidence contract also admits the documented after-head call order. -/
theorem after_head_complete_evidence : CompleteEvidence cfg ext afterHeadFcr where
  epoch_size := Or.inl rfl
  threshold := rfl
  after_genesis := by decide
  no_equivocations := rfl
  prior_votes := by
    intro s hs i hi
    have hs' : s = 0 ∨ s = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hs)
    rcases hs' with rfl | rfl
    · exact ⟨⟨0, 0⟩, after_head_prior_slot_committees_present.1 i hi, by decide⟩
    · exact ⟨⟨0, 1⟩, after_head_prior_slot_committees_present.2 i hi, by decide⟩
  fresh := by
    intro i lm _
    have hc : Weak.recorded_cutoff_epoch cfg afterHeadFcr.store = 0 := rfl
    simp [Weak.is_duty_fresh_message, hc]
  recorded_provenance := by
    intro i lm hm
    by_cases h0 : i = 0
    · subst i
      have he : (⟨0, 0⟩ : LatestMessage Nat) = lm := by simpa [afterHeadFcr,
        get_fast_confirmation_store, afterHeadStore, store] using hm
      subst lm
      exact ⟨0, by decide, by decide, rfl, by decide⟩
    · by_cases h1 : i = 1
      · subst i
        have he : (⟨0, 1⟩ : LatestMessage Nat) = lm := by simpa [afterHeadFcr,
          get_fast_confirmation_store, afterHeadStore, store] using hm
        subst lm
        exact ⟨1, by decide, by decide, rfl, by decide⟩
      · simp [afterHeadFcr, get_fast_confirmation_store, afterHeadStore, store,
          h0, h1] at hm
  balance_sources := ⟨rfl, rfl, rfl, rfl⟩
  equal_balances := complete_evidence.equal_balances
  carrier_support := by decide
  witness_support := by decide
  realized_target_carrier := by intro _; rfl
  bank_epoch_newer := by decide
  bank_alignment := by
    intro h
    change false = true at h
    cases h

/-- An explicit non-anchor confirmation under the evidence contract. -/
theorem nonvacuity : ∃ f : FastConfirmationStore Nat,
    CompleteEvidence cfg ext f ∧
    Strong.get_latest_confirmed cfg ext f = 1 ∧
    Weak.get_latest_confirmed cfg ext f = 1 ∧
    (1 : Nat) ≠ f.store.finalized_checkpoint.root :=
  ⟨fcr, complete_evidence, before_head_confirms_nonanchor⟩

/-- STOP certificate for the unconditional carrier-equals-head proposal. -/
theorem certified_head_equality_false :
    ¬ (∀ f : FastConfirmationStore Nat, CompleteEvidence cfg ext f →
      Weak.get_certified_head cfg ext f.store (get_current_balance_source f) =
        (get_head cfg f.store).root) := by
  intro h
  exact after_head_carrier_differs.2.2 (h afterHeadFcr after_head_complete_evidence)

end FastConfirmation.Spec.CompleteEvidenceWitness

end
