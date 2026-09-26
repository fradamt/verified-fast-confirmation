module
public import FastConfirmationWitnesses.NonVacuity.ConcreteJustification
public import FastConfirmationProofs.FFG.Concrete.FinalizedPrefix

@[expose] public section

/-! Gives a finite concrete FFG run from genesis with length-two finality, the
pattern of the pinned pyspec `two-step-finality` run. Epoch-2 votes are
included in epoch 3 and justify epoch 2 from the stub. Epoch-3 votes keep the
stub source and are included in epoch 4. At the end of epoch 4 the
previous-epoch test justifies epoch 3 from the stub, the current-epoch test
gives the link 2 -> 4, and Python rule 3 finalizes epoch 2. No link 2 -> 3
exists. -/

namespace FastConfirmation.Spec.ConcreteFinalityWitness
open FastConfirmation.Spec FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec.ConcreteJustificationWitness

/-- A full-committee vote of the committee at `slot`. -/
def fullVote (slot : Slot) (head : ℕ) (source target : Checkpoint ℕ) :
    FFGWireAttestation ℕ := {
  aggregation_bits := [true, true, true, true]
  committee_bits := [true]
  data := ⟨slot, 0, head, source, target⟩
  signature := 0 }

/-- Epoch-2 votes from the stub, included in epoch 3. -/
def vote2 : FFGWireAttestation ℕ := fullVote 4 14 ⟨0, 0⟩ ⟨2, 14⟩

/-- Epoch-3 votes from the stub, included in epoch 4. -/
def vote3 : FFGWireAttestation ℕ := fullVote 6 16 ⟨0, 0⟩ ⟨3, 16⟩

/-- Epoch-4 votes from the epoch-2 checkpoint. -/
def vote4 : FFGWireAttestation ℕ := fullVote 8 18 ⟨2, 14⟩ ⟨4, 18⟩

/-- A block with the fixed payload fields of the fixture. -/
def mkBlock (slot : Slot) (parent : ℕ) (proposer : ValidatorIndex) (root : ℕ)
    (attestations : List (FFGWireAttestation ℕ)) : FFGWireBlock ℕ := {
  slot := slot, parent_root := parent, proposer_index := proposer, root := root,
  parent_block_hash := 5, block_hash := 0, parent_requests_empty := true,
  parent_requests_match := true, attestations := attestations }

def block4 : FFGWireBlock ℕ := mkBlock 4 1 0 14 []
def block6 : FFGWireBlock ℕ := mkBlock 6 14 1 16 [vote2]
def block8 : FFGWireBlock ℕ := mkBlock 8 16 2 18 [vote3]
def block9 : FFGWireBlock ℕ := mkBlock 9 18 3 19 [vote4]

def state4 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle setup.genesis block4)

def state6 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle state4 block6)

def state8 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle state6 block8)

def state9 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle state8 block9)

def state10 : FFGBeaconState ℕ :=
  okValue (process_slots cfg preset state9 10)

theorem transition4 :
    state_transition cfg preset schedule oracle setup.genesis block4 = .ok state4 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem transition6 : state_transition cfg preset schedule oracle state4 block6 = .ok state6 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem transition8 : state_transition cfg preset schedule oracle state6 block8 = .ok state8 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem transition9 : state_transition cfg preset schedule oracle state8 block9 = .ok state9 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem slots10 : process_slots cfg preset state9 10 = .ok state10 :=
  eq_ok_of_isOkCheck (by decide +kernel)

/-- The accepted blocks of the run. -/
def blocks : List (FFGWireBlock ℕ) := [] ++ [block4] ++ [block6] ++ [block8] ++ [block9]

/-- The recorded body votes of the run. -/
def votes : List (IncludedVote ℕ) :=
  [] ++ blockVotes setup setup.genesis block4 ++ blockVotes setup state4 block6 ++
    blockVotes setup state6 block8 ++ blockVotes setup state8 block9

/-- The run is a concrete reachable trace. -/
theorem run_reachable : Reachable setup blocks votes state10 :=
  .slots (.block block9 (.block block8 (.block block6 (.block block4 .genesis transition4)
    transition6) transition8) transition9) slots10

theorem state10_in_horizon :
    compute_epoch_at_slot setup.cfg state10.slot ≤ setup.scope.last_epoch := by
  decide +kernel

/-- The end of epoch 4 finalizes the epoch-2 checkpoint. -/
theorem state10_finalized : state10.finalized_checkpoint = ⟨2, 14⟩ := by
  decide +kernel

/-- The end of epoch 4 justifies the epoch-4 checkpoint. -/
theorem state10_justified : state10.current_justified_checkpoint = ⟨4, 18⟩ := by
  decide +kernel

/-- The source and target of every body vote of the run. -/
theorem body_vote_data : ∀ b ∈ blocks, ∀ v ∈ b.attestations,
    (v.data.source = ⟨0, 0⟩ ∧ v.data.target = ⟨2, 14⟩ ∧ b.slot = 6) ∨
    (v.data.source = ⟨0, 0⟩ ∧ v.data.target = ⟨3, 16⟩ ∧ b.slot = 8) ∨
    (v.data.source = ⟨2, 14⟩ ∧ v.data.target = ⟨4, 18⟩ ∧ b.slot = 9) := by
  decide

theorem includedVote_data {r : IncludedVote ℕ} (hr : r ∈ votes) :
    (r.vote.data.source = ⟨0, 0⟩ ∧ r.vote.data.target = ⟨2, 14⟩ ∧ r.block.slot = 6) ∨
    (r.vote.data.source = ⟨0, 0⟩ ∧ r.vote.data.target = ⟨3, 16⟩ ∧ r.block.slot = 8) ∨
    (r.vote.data.source = ⟨2, 14⟩ ∧ r.vote.data.target = ⟨4, 18⟩ ∧ r.block.slot = 9) := by
  obtain ⟨hb, hv, -⟩ := includedVote_provenance run_reachable r hr
  exact body_vote_data r.block hb r.vote hv

/-- **The finality is length two.** No supermajority link goes from the
epoch-2 checkpoint to an epoch-3 checkpoint: every epoch-3 vote has the stub
source. -/
theorem no_adjacent_link {t : Checkpoint ℕ} (ht : t.epoch = 3)
    (L : SupermajorityLink setup votes ⟨2, 14⟩ t) : False := by
  obtain ⟨i, hi⟩ := L.signers_nonempty setup_admissible
  obtain ⟨r, hr, -, hrs, hrt⟩ := L.signer_vote i hi
  rcases includedVote_data hr.1 with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨-, ht', -⟩
  · rw [hrs] at hs; exact absurd hs (by decide)
  · rw [hrs] at hs; exact absurd hs (by decide)
  · rw [hrt] at ht'; rw [ht'] at ht; exact absurd ht (by decide)

/-- **Length-two certificate extraction.** The finalized epoch-2 checkpoint
has a finalizing link to the epoch-4 chain checkpoint, and the epoch-3 chain
checkpoint between them is justified. The link has at least three distinct
signers of weight at least two thirds of 400 Gwei, and each signer has a
target-included vote in the body of the slot-9 block. -/
theorem k2_certificate_extraction :
    ∃ (target : Checkpoint ℕ) (link : SupermajorityLink setup votes ⟨2, 14⟩ target),
      FinalizationLink setup blocks votes ⟨2, 14⟩ target ∧ target = ⟨4, 18⟩ ∧
      Justified setup votes ⟨3, 16⟩ ∧ 3 ≤ link.signers.card ∧
      2 * setup.scope.activeBalance ≤ 3 * setup.scope.weight link.signers ∧
      ∀ i ∈ link.signers, ∃ r ∈ votes, TargetIncluded setup votes r ∧ i ∈ r.attesters setup ∧
        r.block.slot = 9 ∧ r.vote.data.source = ⟨2, 14⟩ ∧ r.vote.data.target = ⟨4, 18⟩ := by
  rcases finalization_soundness setup_admissible run_reachable state10_in_horizon with
    hstub | ⟨target, hl, -⟩
  · rw [state10_finalized] at hstub
    exact absurd hstub (by decide)
  rw [state10_finalized] at hl
  obtain ⟨L⟩ := hl.link
  have htarget : target.epoch = 4 := by
    rcases hl.target_epoch with h | h
    · exact (no_adjacent_link h L).elim
    · exact h
  have htarget' : target = ⟨4, 18⟩ := by
    rw [hl.target_on_chain, htarget]
    rfl
  have hmid : Justified setup votes ⟨3, 16⟩ := hl.middle_justified htarget
  refine ⟨target, L, hl, htarget', hmid, ?_, L.supermajority, ?_⟩
  · have hweight : setup.scope.weight L.signers = 100 * L.signers.card := by
      unfold FixedFFGScope.weight
      rw [Finset.sum_congr rfl (g := fun _ => 100), Finset.sum_const, smul_eq_mul, mul_comm]
      intro i hi
      obtain ⟨hlt, -⟩ := L.signer_active i hi
      have : i < 4 := hlt
      interval_cases i <;> rfl
    have hactive : setup.scope.activeBalance = 400 := by decide
    have hsuper := L.supermajority
    rw [hweight, hactive] at hsuper
    beacon_omega
  · intro i hi
    obtain ⟨r, hr, hri, hrs, hrt⟩ := L.signer_vote i hi
    rw [htarget'] at hrt
    refine ⟨r, hr.1, hr, hri, ?_, hrs, hrt⟩
    rcases includedVote_data hr.1 with ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hs⟩
    · rw [hrt] at ht; exact absurd ht (by decide)
    · rw [hrt] at ht; exact absurd ht (by decide)
    · exact hs

/-! ### One more epoch: adjacent finality by rule 4 -/

/-- Epoch-5 votes from the epoch-4 checkpoint. -/
def vote5 : FFGWireAttestation ℕ := fullVote 10 20 ⟨4, 18⟩ ⟨5, 20⟩

def block10 : FFGWireBlock ℕ := mkBlock 10 19 0 20 []
def block11 : FFGWireBlock ℕ := mkBlock 11 20 1 21 [vote5]

def state10' : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle state9 block10)

def state11 : FFGBeaconState ℕ :=
  okValue (state_transition_pointwise cfg preset schedule oracle state10' block11)

def state12 : FFGBeaconState ℕ :=
  okValue (process_slots cfg preset state11 12)

theorem transition10 :
    state_transition cfg preset schedule oracle state9 block10 = .ok state10' := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem transition11 :
    state_transition cfg preset schedule oracle state10' block11 = .ok state11 := by
  rw [state_transition_eq_pointwise]
  exact eq_ok_of_isOkCheck (by decide +kernel)

theorem slots12 : process_slots cfg preset state11 12 = .ok state12 :=
  eq_ok_of_isOkCheck (by decide +kernel)

def blocks' : List (FFGWireBlock ℕ) := blocks ++ [block10] ++ [block11]

def votes' : List (IncludedVote ℕ) :=
  votes ++ blockVotes setup state9 block10 ++ blockVotes setup state10' block11

theorem run_reachable' : Reachable setup blocks' votes' state12 :=
  .slots (.block block11 (.block block10 (.block block9 (.block block8 (.block block6
    (.block block4 .genesis transition4) transition6) transition8) transition9) transition10)
    transition11) slots12

theorem state12_in_horizon :
    compute_epoch_at_slot setup.cfg state12.slot ≤ setup.scope.last_epoch := by
  decide +kernel

/-- The end of epoch 5 finalizes the epoch-4 checkpoint by rule 4. Rule 1
also passes for the epoch-2 checkpoint, and the later rule 4 wins. -/
theorem state12_finalized : state12.finalized_checkpoint = ⟨4, 18⟩ := by
  decide +kernel

/-- **Adjacent certificate extraction.** The finalized epoch-4 checkpoint has
a finalizing link to the epoch-5 chain checkpoint. -/
theorem adjacent_certificate_extraction :
    FinalizationLink setup blocks' votes' ⟨4, 18⟩ ⟨5, 20⟩ := by
  rcases finalization_soundness setup_admissible run_reachable' state12_in_horizon with
    hstub | ⟨target, hl, hlt⟩
  · rw [state12_finalized] at hstub
    exact absurd hstub (by decide)
  rw [state12_finalized] at hl
  have hE : compute_epoch_at_slot setup.cfg state12.slot = 6 := by decide +kernel
  rw [hE] at hlt
  have htarget : target.epoch = 5 := by
    rcases hl.target_epoch with h | h
    · exact h
    · change target.epoch = 4 + 2 at h
      beacon_omega
  have htarget' : target = ⟨5, 20⟩ := by
    rw [hl.target_on_chain, htarget]
    rfl
  rw [← htarget']
  exact hl

end FastConfirmation.Spec.ConcreteFinalityWitness

end
