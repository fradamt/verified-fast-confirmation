module
public import FastConfirmationProofs.FFG.Concrete.JustificationSoundness

@[expose] public section

/-! Proves that the concrete attestation transition equals a form without
`Finset.sort`: the sorted participation fold is a pointwise update, and the
structural indexed check is a finite-set test. Kernel evaluation cannot reduce
`Finset.sort`; the equal forms here let finite witnesses evaluate concrete
runs. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-- The participation write as a pointwise update. -/
def pointwiseUpdate (flags : List ℕ) (indices : Finset ValidatorIndex)
    (participation : List ℕ) : List ℕ :=
  (List.range participation.length).map fun i =>
    if i ∈ indices then flags.foldl add_flag (participation.getD i 0) else participation.getD i 0

theorem map_range_getD (participation : List ℕ) :
    (List.range participation.length).map (fun i => participation.getD i 0) = participation := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem participationUpdate_eq_map (flags : List ℕ) :
    ∀ (indices : List ValidatorIndex), indices.Nodup → ∀ (participation : List ℕ),
      participationUpdate flags indices participation =
        (List.range participation.length).map fun i =>
          if i ∈ indices then flags.foldl add_flag (participation.getD i 0)
          else participation.getD i 0
  | [], _, participation => by
    simp only [participationUpdate, List.foldl_nil, List.not_mem_nil, if_false]
    exact (map_range_getD participation).symm
  | j :: indices, hnodup, participation => by
    have hj : j ∉ indices := (List.nodup_cons.mp hnodup).1
    have hrest := participationUpdate_eq_map flags indices (List.nodup_cons.mp hnodup).2
    simp only [participationUpdate, List.foldl_cons] at hrest ⊢
    rw [hrest, List.length_set]
    apply List.map_congr_left
    intro i hi
    have hi' : i < participation.length := List.mem_range.mp hi
    by_cases hij : i = j
    · subst hij
      simp only [hj, if_false, List.mem_cons, true_or, if_true, List.getD_eq_getElem?_getD,
        List.getElem?_set_self hi', Option.getD_some]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hij), List.mem_cons,
        hij, false_or]

theorem foldl_sort_eq_pointwiseUpdate (flags : List ℕ) (indices : Finset ValidatorIndex)
    (participation : List ℕ) :
    (indices.sort (· ≤ ·)).foldl
      (fun values i => values.set i (flags.foldl add_flag (values.getD i 0)))
      participation = pointwiseUpdate flags indices participation := by
  change participationUpdate flags _ participation = _
  rw [participationUpdate_eq_map flags _ (Finset.sort_nodup _ _)]
  unfold pointwiseUpdate
  apply List.map_congr_left
  intro i _
  simp only [Finset.mem_sort]

/-- The structural indexed check of `process_attestation` as a finite-set test. -/
theorem is_valid_indexed_attestation_get_indexed (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) (state : FFGBeaconState Root)
    (vote : FFGWireAttestation Root) :
    is_valid_indexed_attestation preset state (get_indexed_attestation schedule vote) =
      decide (0 < (get_attesting_indices schedule vote).card ∧
        (get_attesting_indices schedule vote).card ≤
          preset.max_validators_per_committee * preset.max_committees_per_slot ∧
        ∀ i ∈ get_attesting_indices schedule vote, i < state.validators.length) := by
  have hpair : ((get_attesting_indices schedule vote).sort (· ≤ ·)).Pairwise (· < ·) :=
    ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp
      fun h => Nat.lt_of_le_of_ne h.1 h.2
  unfold is_valid_indexed_attestation get_indexed_attestation
  simp only [hpair, decide_true, Bool.and_true, Finset.length_sort]
  by_cases h0 : 0 < (get_attesting_indices schedule vote).card
  · have hne : ((get_attesting_indices schedule vote).sort (· ≤ ·)).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
      exact ⟨i, (Finset.mem_sort _).mpr hi⟩
    simp only [hne, h0, Bool.not_false, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp [List.all_eq_true, Finset.mem_sort]
  · have he : (get_attesting_indices schedule vote) = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    simp [he]

/-- `process_attestation` with the sorted fold and indexed check replaced by
their equal pointwise forms. -/
def process_attestation_pointwise (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) [BEq Root]
    (state : FFGBeaconState Root) (vote : FFGWireAttestation Root)
    (parentSlot : Slot) : Checked (FFGBeaconState Root) := do
  let data := vote.data
  let current := compute_epoch_at_slot cfg state.slot
  guard (data.target.epoch == current || data.target.epoch == get_previous_epoch cfg state) .target
  guard (data.target.epoch == compute_epoch_at_slot cfg data.slot) .target
  guard (data.slot + preset.min_attestation_inclusion_delay ≤ state.slot) .inclusion
  guard (data.index < 2) .payloadIndex
  guard (vote.committee_bits.length == preset.max_committees_per_slot) .committee
  let count ← (match schedule.count data.target.epoch with
    | some n => (pure n : Checked ℕ)
    | none => throw .committee : Checked ℕ)
  let mut offset := 0
  for committeeIndex in get_committee_indices vote.committee_bits do
    guard (committeeIndex < count) .committee
    let committee ← (match schedule.committee data.slot committeeIndex with
      | some members => (pure members : Checked (List ValidatorIndex))
      | none => throw .committee : Checked (List ValidatorIndex))
    guard (committee.length ≤ preset.max_validators_per_committee) .committee
    guard (offset + committee.length ≤ vote.aggregation_bits.length) .bitfield
    guard ((List.range committee.length).any fun i =>
      vote.aggregation_bits.getD (offset + i) false) .bitfield
    offset := offset + committee.length
  guard (vote.aggregation_bits.length == offset) .bitfield
  let flags ← (get_attestation_participation_flag_indices cfg preset state data
    (state.slot - data.slot) parentSlot : Checked (List ℕ))
  guard (decide (0 < (get_attesting_indices schedule vote).card ∧
    (get_attesting_indices schedule vote).card ≤
      preset.max_validators_per_committee * preset.max_committees_per_slot ∧
    ∀ i ∈ get_attesting_indices schedule vote, i < state.validators.length)) .indexed
  let indices := get_attesting_indices schedule vote
  let participation := if data.target.epoch == current then
    state.current_epoch_participation else state.previous_epoch_participation
  guard (participation.length == state.validators.length) .state
  let updated := pointwiseUpdate flags indices participation
  if data.target.epoch == current then
    return { state with current_epoch_participation := updated }
  else
    return { state with previous_epoch_participation := updated }

theorem process_attestation_eq_pointwise [BEq Root] (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) (state : FFGBeaconState Root)
    (vote : FFGWireAttestation Root) (parentSlot : Slot) :
    process_attestation cfg preset schedule state vote parentSlot =
      process_attestation_pointwise cfg preset schedule state vote parentSlot := by
  unfold process_attestation process_attestation_pointwise
  simp only [is_valid_indexed_attestation_get_indexed, foldl_sort_eq_pointwiseUpdate]
  rfl

/-- `process_operations` over the pointwise attestation form. -/
def process_operations_pointwise (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) [BEq Root]
    (state : FFGBeaconState Root) (block : FFGWireBlock Root)
    (parentSlot : Slot) : Checked (FFGBeaconState Root) := do
  guard (block.deposit_count == 0) .operations
  guard (block.proposer_slashing_count ≤ preset.max_proposer_slashings &&
    block.attester_slashing_count ≤ preset.max_attester_slashings &&
    block.attestations.length ≤ preset.max_attestations &&
    block.voluntary_exit_count ≤ preset.max_voluntary_exits &&
    block.bls_to_execution_change_count ≤ preset.max_bls_to_execution_changes &&
    block.payload_attestation_count ≤ preset.max_payload_attestations) .operations
  block.attestations.foldlM (init := state) fun state vote =>
    process_attestation_pointwise cfg preset schedule state vote parentSlot

/-- `process_block` over the pointwise attestation form. -/
def process_block_pointwise (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) [BEq Root]
    (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    Checked (FFGBeaconState Root) := do
  let parentSlot := state.latest_block_header.slot
  let state ← process_parent_execution_payload preset state block
  let state ← process_block_header state block
  let state := process_execution_payload_bid state block
  process_operations_pointwise cfg preset schedule state block parentSlot

/-- `state_transition` over the pointwise attestation form. -/
def state_transition_pointwise (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) (oracle : BlockValidityOracle Root)
    [BEq Root] (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    Checked (FFGBeaconState Root) := do
  guard (state.slot ≤ UINT64_MAX && block.slot ≤ UINT64_MAX) .slot
  guard (state.justification_bits.length == 4 &&
    state.previous_epoch_participation.length == state.validators.length &&
    state.current_epoch_participation.length == state.validators.length &&
    state.block_roots.length == preset.slots_per_historical_root &&
    state.execution_payload_availability.length == preset.slots_per_historical_root) .state
  let atSlot ← process_slots cfg preset state block.slot
  let result ← process_block_pointwise cfg preset schedule atSlot block
  guard (oracle.accepts atSlot block result) .oracle
  return result

theorem state_transition_eq_pointwise [BEq Root] (cfg : Config) (preset : FFGPreset)
    (schedule : FixedCommitteeSchedule) (oracle : BlockValidityOracle Root)
    (state : FFGBeaconState Root) (block : FFGWireBlock Root) :
    state_transition cfg preset schedule oracle state block =
      state_transition_pointwise cfg preset schedule oracle state block := by
  unfold state_transition state_transition_pointwise process_block process_block_pointwise
    process_operations process_operations_pointwise
  simp only [process_attestation_eq_pointwise]

/-- `attestationVotes` over the pointwise attestation form. -/
def attestationVotes_pointwise [BEq Root] (S : FFGSetup Root) (block : FFGWireBlock Root)
    (parentSlot : Slot) : FFGBeaconState Root → List (FFGWireAttestation Root) →
    List (IncludedVote Root)
  | _, [] => []
  | state, vote :: votes =>
    match process_attestation_pointwise S.cfg S.preset S.schedule state vote parentSlot with
    | .ok next => ⟨block, vote, state, parentSlot⟩ ::
        attestationVotes_pointwise S block parentSlot next votes
    | .error _ => []

theorem attestationVotes_eq_pointwise [BEq Root] (S : FFGSetup Root)
    (block : FFGWireBlock Root) (parentSlot : Slot) :
    ∀ (state : FFGBeaconState Root) (votes : List (FFGWireAttestation Root)),
      attestationVotes S block parentSlot state votes =
        attestationVotes_pointwise S block parentSlot state votes
  | _, [] => rfl
  | state, vote :: votes => by
    rw [attestationVotes, attestationVotes_pointwise, process_attestation_eq_pointwise]
    cases process_attestation_pointwise S.cfg S.preset S.schedule state vote parentSlot with
    | ok next => simp only [attestationVotes_eq_pointwise S block parentSlot next votes]
    | error _ => rfl

/-- `blockVotes` over the pointwise attestation form. -/
def blockVotes_pointwise [BEq Root] (S : FFGSetup Root) (state : FFGBeaconState Root)
    (block : FFGWireBlock Root) : List (IncludedVote Root) :=
  match process_slots S.cfg S.preset state block.slot with
  | .error _ => []
  | .ok atSlot =>
    match process_parent_execution_payload S.preset atSlot block >>=
        fun state => process_block_header state block with
    | .error _ => []
    | .ok headed =>
      attestationVotes_pointwise S block atSlot.latest_block_header.slot
        (process_execution_payload_bid headed block) block.attestations

theorem blockVotes_eq_pointwise [BEq Root] (S : FFGSetup Root) (state : FFGBeaconState Root)
    (block : FFGWireBlock Root) :
    blockVotes S state block = blockVotes_pointwise S state block := by
  unfold blockVotes blockVotes_pointwise
  cases process_slots S.cfg S.preset state block.slot with
  | error _ => rfl
  | ok atSlot =>
    dsimp only
    cases (process_parent_execution_payload S.preset atSlot block >>=
        fun state => process_block_header state block) with
    | error _ => rfl
    | ok headed => exact attestationVotes_eq_pointwise S _ _ _ _

end FastConfirmation.Spec.ConcreteFFG

end
