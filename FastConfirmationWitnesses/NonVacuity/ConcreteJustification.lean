module
public import FastConfirmationProofs.FFG.Concrete.PointwiseAttestation

@[expose] public section

/-! Gives a finite concrete FFG run from genesis in which the end of epoch 2
justifies the epoch-1 checkpoint. The run extracts the actual supermajority
certificate of three distinct signers, and it includes a wrong-target vote
that `process_attestation` accepts but that does not count. -/

namespace FastConfirmation.Spec.ConcreteJustificationWitness
open FastConfirmation.Spec FastConfirmation.Spec.ConcreteFFG

/-- Two slots per epoch and increments of 100 Gwei. -/
def cfg : Config := {
  slots_per_epoch := 2
  slots_per_epoch_pos := by decide
  slot_duration_ms := 12000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 2500
  min_seed_lookahead := 1 }

/-- A four-slot ring, one committee per slot, and four attestations per block. -/
def preset : FFGPreset := {
  slots_per_historical_root := 4
  max_committees_per_slot := 1
  max_validators_per_committee := 4
  max_attestations := 4
  max_proposer_slashings := 0
  max_attester_slashings := 0
  max_voluntary_exits := 0
  max_bls_to_execution_changes := 0
  max_payload_attestations := 0
  min_attestation_inclusion_delay := 1
  ring_pos := by decide
  min_delay_pos := by decide }

/-- An active, unslashed validator with one increment of effective balance. -/
def validator : Validator := ⟨100, false, 0, 1000⟩

/-- Four fixed validators over epochs 0 to 10. -/
def scope : FixedFFGScope := {
  validators := [validator, validator, validator, validator]
  first_epoch := 0
  last_epoch := 10
  epoch_order := by decide
  activity_fixed := by decide }

/-- The first slot of each epoch has one committee of all four validators. -/
def schedule : FixedCommitteeSchedule := {
  committees := (List.range 11).map fun e => (2 * e, 0, [0, 1, 2, 3])
  counts := (List.range 11).map fun e => (e, 1) }

/-- The oracle accepts every candidate. It supplies no FFG state. -/
def oracle : BlockValidityOracle ℕ := ⟨fun _ _ _ => true⟩

def setup : FFGSetup ℕ := {
  cfg := cfg
  preset := preset
  scope := scope
  schedule := schedule
  oracle := oracle
  zeroRoot := 0
  genesisRoot := 1
  genesisTime := 0 }

theorem setup_admissible : setup.Admissible where
  ring_covers_two_epochs := by decide
  scope_from_genesis := rfl
  balance_floor := by decide

/-- The block at slot 2, the first slot of epoch 1. -/
def block1 : FFGWireBlock ℕ := {
  slot := 2, parent_root := 1, proposer_index := 0, root := 11,
  parent_block_hash := 5, block_hash := 0, parent_requests_empty := true,
  parent_requests_match := true, attestations := [] }

/-- Validators 0, 1 and 2 vote for the epoch-1 checkpoint from the stub. -/
def goodVote : FFGWireAttestation ℕ := {
  aggregation_bits := [true, true, true, false]
  committee_bits := [true]
  data := ⟨2, 0, 11, ⟨0, 0⟩, ⟨1, 11⟩⟩
  signature := 0 }

/-- Validator 3 names a wrong target root with the correct source. -/
def wrongVote : FFGWireAttestation ℕ := {
  aggregation_bits := [false, false, false, true]
  committee_bits := [true]
  data := ⟨2, 0, 11, ⟨0, 0⟩, ⟨1, 99⟩⟩
  signature := 0 }

/-- The block at slot 3 includes both votes. -/
def block2 : FFGWireBlock ℕ := {
  slot := 3, parent_root := 11, proposer_index := 1, root := 12,
  parent_block_hash := 5, block_hash := 0, parent_requests_empty := true,
  parent_requests_match := true, attestations := [goodVote, wrongVote] }

/-- The successful value of a checked call, or a default. -/
def okValue {α : Type} [Inhabited α] : Checked α → α
  | .ok a => a
  | .error _ => default

/-- A Boolean success test that kernel evaluation can reduce. -/
def isOkCheck {α : Type} : Checked α → Bool
  | .ok _ => true
  | .error _ => false

theorem eq_ok_of_isOkCheck {α : Type} [Inhabited α] {x : Checked α}
    (h : isOkCheck x = true) : x = .ok (okValue x) := by
  cases x with
  | ok a => rfl
  | error e => simp [isOkCheck] at h

def state1 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle setup.genesis block1)

def state2 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle state1 block2)

def state3 : FFGBeaconState ℕ :=
  okValue (process_slots cfg preset state2 6)

theorem transition1 :
    state_transition cfg preset schedule oracle setup.genesis block1 = .ok state1 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem transition2 : state_transition cfg preset schedule oracle state1 block2 = .ok state2 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem slots3 : process_slots cfg preset state2 6 = .ok state3 :=
  eq_ok_of_isOkCheck (by decide +kernel)

/-- The recorded body votes of the run. -/
def votes : List (IncludedVote ℕ) :=
  [] ++ blockVotes setup setup.genesis block1 ++ blockVotes setup state1 block2

/-- The run is a concrete reachable trace. -/
theorem run_reachable : Reachable setup ([] ++ [block1] ++ [block2]) votes state3 :=
  .slots (.block block2 (.block block1 .genesis transition1) transition2) slots3

theorem state3_in_horizon :
    compute_epoch_at_slot setup.cfg state3.slot ≤ setup.scope.last_epoch := by
  decide +kernel

/-- The end of epoch 2 justifies the epoch-1 checkpoint. -/
theorem state3_justified : state3.current_justified_checkpoint = ⟨1, 11⟩ := by
  decide +kernel

theorem votes_eq_pointwise :
    votes = [] ++ blockVotes_pointwise setup setup.genesis block1 ++
      blockVotes_pointwise setup state1 block2 := by
  simp only [votes, blockVotes_eq_pointwise]

/-- **Certificate extraction on a concrete run.** The epoch-1 checkpoint has
a supermajority link from a justified source. Its signers are at least three
distinct validators of total weight at least two thirds of 400 Gwei. Each has
a target-included vote in the body of the slot-3 block. -/
theorem concrete_certificate_extraction :
    ∃ (source : Checkpoint ℕ) (link : SupermajorityLink setup votes source ⟨1, 11⟩),
      Justified setup votes source ∧ 3 ≤ link.signers.card ∧
      2 * setup.scope.activeBalance ≤ 3 * setup.scope.weight link.signers ∧
      ∀ i ∈ link.signers, ∃ r ∈ votes, r.block = block2 ∧ TargetIncluded setup votes r ∧
        i ∈ r.attesters setup ∧ r.vote.data.target = ⟨1, 11⟩ := by
  have hJ := (justification_soundness setup_admissible run_reachable state3_in_horizon).1
  rw [state3_justified] at hJ
  rcases justified_certificate setup_admissible run_reachable hJ with hstub | hcert
  · exact absurd hstub (by decide)
  · obtain ⟨source, link, hsource, -, -, hsuper, hvotes⟩ := hcert
    refine ⟨source, link, hsource, ?_, hsuper, ?_⟩
    · have hweight : setup.scope.weight link.signers = 100 * link.signers.card := by
        unfold FixedFFGScope.weight
        rw [Finset.sum_congr rfl (g := fun _ => 100), Finset.sum_const, smul_eq_mul, mul_comm]
        intro i hi
        obtain ⟨hlt, -⟩ := link.signer_active i hi
        have : i < 4 := hlt
        interval_cases i <;> rfl
      have hactive : setup.scope.activeBalance = 400 := by decide
      rw [hweight, hactive] at hsuper
      beacon_omega
    · intro i hi
      obtain ⟨r, hr, hb, hv, hti, hri, -, ht⟩ := hvotes i hi
      refine ⟨r, hr, ?_, hti, hri, ht⟩
      simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with hb | hb
      · rw [hb] at hv
        simp [block1] at hv
      · exact hb

/-- **Wrong-target inclusion.** The run records the wrong-target vote as an
accepted body vote, but it is not target-included. -/
theorem wrong_target_vote_not_counted :
    ∃ r ∈ votes, r.vote.data = wrongVote.data ∧ ¬ TargetIncluded setup votes r := by
  have hmem : ∃ r ∈ blockVotes_pointwise setup state1 block2,
      r.vote.data = wrongVote.data ∧
      (match get_block_root cfg preset r.pre 1 with
        | .ok root => root == 11
        | .error _ => false) = true := by
    decide +kernel
  obtain ⟨r, hr, hdata, hread⟩ := hmem
  have hr' : r ∈ votes := by
    rw [votes_eq_pointwise]
    exact List.mem_append_right _ hr
  refine ⟨r, hr', hdata, ?_⟩
  have hroot : get_block_root setup.cfg setup.preset r.pre r.vote.data.target.epoch = .ok 11 := by
    rw [hdata]
    change get_block_root cfg preset r.pre 1 = .ok 11
    revert hread
    cases get_block_root cfg preset r.pre 1 with
    | ok root => intro h; rw [beq_iff_eq.mp h]
    | error e => intro h; simp at h
  exact not_targetIncluded_of_wrong_target run_reachable hr' hroot (by rw [hdata]; decide)

end FastConfirmation.Spec.ConcreteJustificationWitness

end
