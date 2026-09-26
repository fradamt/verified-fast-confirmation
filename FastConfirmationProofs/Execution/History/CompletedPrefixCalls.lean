module
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionCallInduction

public import FastConfirmationStatements.Premises.FCRCallPremises
@[expose] public section

/-!
# Completed-prefix supplier for historical A3.2 call interfaces

An `Execution.fcr` write-back call reads `E.store v (n+1)`, which is exactly
the full scheduled prefix for second `n+1`.  This module uses that concrete
prefix to construct the accounting evidence and accepted current-target gate
producer consumed by `AcceptedHistoricalA32CallInterfaces`.

The adapter does not use `SelectedMarginAssumptions`, a justification
interface, transition history, canonicity, or safety. Prediction support is derived later by the joint call and endpoint-slot
induction; it is absent from the call interface. A one-slot operational delivery
law covers the finite-prefix boundary case: a vote created in the last
verified slot is scheduled just after the exclusive public cutoff.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

/-! ## The completed scheduled prefix -/

/-- The full event prefix whose store is the ordinary execution boundary at
second `n+1`. -/
def completedScheduledEventPrefix (v : ValidatorIndex) (n : ℕ) :
    E.ScheduledEventPrefix :=
  { node := v
    previousSecond := n
    processedCount := (E.schedule v (n + 1)).length
    count_le := le_rfl }

/-- Replaying the completed prefix is definitionally the execution store at
the end of that second. -/
theorem completedScheduledEventPrefix_store
    (v : ValidatorIndex) (n : ℕ) :
    (E.completedScheduledEventPrefix v n).store cfg ext =
      E.store cfg ext v (n + 1) := by
  simp [Execution.completedScheduledEventPrefix,
    ScheduledEventPrefix.store, Execution.store]

/-- All prefix accounting evidence at an execution boundary is mechanical:
operational facts come from exact replay, while committee readback in the read
window follows from external coherence for the completed execution store. -/
theorem completedScheduledEventPrefix_accountingEvidence
    (hT : E.ScheduledExecutionPremises cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest)
    (n : ℕ) (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext v (n + 1)) (n + 1) := by
  let p := E.completedScheduledEventPrefix v n
  have hpstore : p.store cfg ext = E.store cfg ext v (n + 1) := by
    simpa only [p] using E.completedScheduledEventPrefix_store cfg ext v n
  have hp : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1) :=
    { operational := p.operationalEvidence cfg ext E hT hv hHn1
      committees := by
        intro slot hslotA hslotC
        rw [hpstore] at hslotC ⊢
        rw [E.store_current_slot cfg ext v (n + 1)] at hslotC
        exact hT.externals_coherence.committee_read_eq cfg ext hv hHn1
          ⟨hslotA, hslotC⟩
      anchor_le_current := by
        obtain ⟨ast, ablk, hgeq, _⟩ := hT.genesis
        rw [hpstore, E.store_current_slot cfg ext v (n + 1)]
        exact E.anchor_state_slot_le_slot_at cfg hT.whole_seconds ⟨ast, ablk, hgeq⟩ (n + 1) }
  rw [hpstore] at hp
  simpa only [p, Execution.completedScheduledEventPrefix] using hp

/-! ## Mechanical gate fields at the completed boundary -/

/-- The pulled-up head state reads the static execution registry. -/
theorem completedPrefix_pulledUpHead_validators
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    (get_pulled_up_head_state cfg ext
      (E.store cfg ext v n)).validators = E.registry := by
  have hhead := E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hv n hHn
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hT.genesis_structure
    exact ⟨ast, ablk, hgeq⟩
  have hregistry :=
    (E.registryConstant cfg ext hT.externals_coherence hgen v hv n hHn).1
      (get_head cfg (E.store cfg ext v n)).root hhead
  have htargetH : E.SlotWithinHorizon cfg
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext v n))) := by
    have hle : compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext v n)) ≤
        E.slot_at cfg n := by
      simp only [compute_start_slot_at_epoch, get_current_store_epoch,
        E.store_current_slot cfg ext v n, compute_epoch_at_slot]
      exact Nat.div_mul_le_self _ _
    constructor
    · exact hle.trans hHn.2.1
    · simpa only [compute_start_slot_at_epoch, get_current_store_epoch,
        E.store_current_slot cfg ext v n, compute_epoch_at_slot,
        Nat.mul_div_cancel _ cfg.slots_per_epoch_pos] using hHn.2.2
  simp only [get_pulled_up_head_state]
  split_ifs
  · apply hT.externals_coherence.registry_static_in_horizon
    right
    refine ⟨_, _, ?_, htargetH, rfl⟩
    exact ⟨_, E.honest_store_prefix cfg ext v hv n hHn,
      Or.inl ⟨_, hhead, rfl⟩⟩
  · exact hregistry

/-- Pulling the head up makes its state epoch exactly the execution store's
current epoch.  In the no-pull branch this follows from the head-state slot
bound and the negated pull guard. -/
theorem completedPrefix_pulledUpHead_epoch
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    get_current_epoch cfg (get_pulled_up_head_state cfg ext
        (E.store cfg ext v n)) =
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  let store := E.store cfg ext v n
  let head := (get_head cfg store).root
  have hhead : head ∈ store.block_roots := by
    simpa only [store, head] using
      E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT hanchor
        hboundary hv n hHn
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hstateSlots := E.stateSlotsLE cfg ext hT.whole_seconds
    hT.externals_coherence ⟨ast, ablk, hgen⟩ v n
  have hheadSlot : (store.block_states head).slot ≤
      get_current_slot cfg store := by
    have h := hstateSlots.1 head (by simpa only [store] using hhead)
    simpa only [store, E.store_current_slot] using h
  simp only [get_pulled_up_head_state]
  change get_current_epoch cfg (if get_current_epoch cfg (store.block_states head) <
      get_current_store_epoch cfg store then
        ext.process_slots (store.block_states head)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg store))
      else store.block_states head) =
        get_current_store_epoch cfg store
  by_cases hpull : get_current_epoch cfg (store.block_states head) <
      get_current_store_epoch cfg store
  · rw [if_pos hpull]
    have hslotLt : (store.block_states head).slot <
        compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg store) := by
      have hnext : compute_epoch_at_slot cfg
            (store.block_states head).slot + 1 ≤
          get_current_store_epoch cfg store := by
        simpa only [get_current_epoch, compute_epoch_at_slot] using
          Nat.succ_le_of_lt hpull
      have hlt := Nat.lt_mul_div_succ
        (store.block_states head).slot cfg.slots_per_epoch_pos
      calc
        (store.block_states head).slot < cfg.slots_per_epoch *
            ((store.block_states head).slot / cfg.slots_per_epoch + 1) := hlt
        _ ≤ cfg.slots_per_epoch * get_current_store_epoch cfg store :=
          Nat.mul_le_mul_left cfg.slots_per_epoch hnext
        _ = compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg store) := by
          simp only [compute_start_slot_at_epoch, Nat.mul_comm]
    change (ext.process_slots (store.block_states head)
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg store))).slot /
          cfg.slots_per_epoch = get_current_store_epoch cfg store
    rw [hT.externals_coherence.process_slots_slot _ _ hslotLt]
    simp only [compute_start_slot_at_epoch]
    exact Nat.mul_div_cancel _ cfg.slots_per_epoch_pos
  · rw [if_neg hpull]
    apply Nat.le_antisymm
    · simpa only [get_current_epoch, get_current_store_epoch,
        compute_epoch_at_slot] using Nat.div_le_div_right hheadSlot
    · exact Nat.le_of_not_gt hpull

/-- The trusted anchor state's epoch belongs to the verified segment. -/
theorem completedPrefix_anchor_epoch_within
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E) :
    get_current_epoch cfg E.anchor_state < E.verification_horizon := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hanchorSlot := E.anchor_state_slot_le cfg hT.whole_seconds
    ⟨ast, ablk, hgen⟩
  exact lt_of_le_of_lt
    (by simpa only [get_current_epoch, compute_epoch_at_slot] using
      Nat.div_le_div_right hanchorSlot)
    hsv.genesis_within_horizon.2.2

/-- The pulled-up head balance source has the ground-truth total active
balance.  Registry equality and the two in-horizon state epochs are enough;
no selected-domain or justification interface is involved. -/
theorem completedPrefix_pulledUpHead_totalActive
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    get_total_active_balance cfg (get_pulled_up_head_state cfg ext
      (E.store cfg ext v n)) = E.total_active cfg := by
  let state := get_pulled_up_head_state cfg ext (E.store cfg ext v n)
  have hval : state.validators = E.registry := by
    simpa only [state] using E.completedPrefix_pulledUpHead_validators
      cfg ext B hT hanchor hboundary hv hHn
  have hstateEpoch : get_current_epoch cfg state < E.verification_horizon := by
    rw [E.completedPrefix_pulledUpHead_epoch cfg ext B hT hanchor
      hboundary hv hHn]
    simpa only [get_current_store_epoch, E.store_current_slot,
      compute_epoch_at_slot] using hHn.2.2
  have hanchorEpoch := E.completedPrefix_anchor_epoch_within
    cfg ext hT hsv
  change get_total_active_balance cfg state =
    get_total_active_balance cfg E.anchor_state
  apply get_total_active_balance_congr cfg
  · simpa only [Execution.registry] using hval
  · intro i
    rw [hval]
    simpa only [Execution.registry] using
      hsv.activity_constant i (get_current_epoch cfg state)
        (get_current_epoch cfg E.anchor_state) hstateEpoch hanchorEpoch

/-! ## Horizon reduction -/

/-- A query inside the finite execution segment has a representable current
epoch end under the Phase0 preset invariant. No next-epoch execution time is
needed. -/
theorem currentTargetEpochEnd_within_of_epochEndsFitUint64
    (hfit : EpochEndsFitUint64 cfg)
    {v : ValidatorIndex} {q : Nat}
    (hqH : E.WithinHorizon cfg q) :
    E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v q)) := by
  let s := E.slot_at cfg q
  let k := cfg.slots_per_epoch
  obtain ⟨a, ha⟩ := hfit
  have hsLe : s ≤ UINT64_MAX := hqH.2.1
  have hsLt : s < UINT64_MAX + 1 := Nat.lt_succ_iff.mpr hsLe
  have hsLtMul : s < a * k := by
    calc
      s < UINT64_MAX + 1 := hsLt
      _ = cfg.slots_per_epoch * a := ha
      _ = a * k := by simp only [k, Nat.mul_comm]
  have hdivLt : s / k < a := by
    apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
    simpa only [k, Nat.mul_comm] using hsLtMul
  have hmulLe : (s / k + 1) * k ≤ a * k :=
    Nat.mul_le_mul_right k (Nat.succ_le_of_lt hdivLt)
  have hendLt : s / k * k + (k - 1) < (s / k + 1) * k := by
    have hk : 0 < k := cfg.slots_per_epoch_pos
    simp only [Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left (Nat.sub_lt hk (by omega)) _
  have hendLe : s / k * k + (k - 1) ≤ UINT64_MAX := by
    apply Nat.le_of_lt_succ
    have hlt : s / k * k + (k - 1) < UINT64_MAX + 1 := by
      apply hendLt.trans_le
      calc
        (s / k + 1) * k ≤ a * k := hmulLe
        _ = cfg.slots_per_epoch * a := by simp only [k, Nat.mul_comm]
        _ = UINT64_MAX + 1 := ha.symm
    simpa only [Nat.succ_eq_add_one] using hlt
  constructor
  · simpa only [currentTargetEpochEnd, currentTargetEpochStart,
      compute_start_slot_at_epoch, get_current_store_epoch,
      E.store_current_slot cfg ext v q, s, k, Nat.mul_comm] using hendLe
  · have hepochEnd : compute_epoch_at_slot cfg
        (currentTargetEpochEnd cfg (E.store cfg ext v q)) =
      compute_epoch_at_slot cfg (E.slot_at cfg q) := by
      simp only [currentTargetEpochEnd, currentTargetEpochStart,
        compute_start_slot_at_epoch, get_current_store_epoch,
        E.store_current_slot cfg ext v q, compute_epoch_at_slot]
      apply Nat.div_eq_of_lt_le
      · exact Nat.le_add_right _ _
      · have hk : 0 < cfg.slots_per_epoch :=
          cfg.slots_per_epoch_pos
        simp only [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left (Nat.sub_lt hk (by omega)) _
    rw [hepochEnd]
    exact hqH.2.2


/-! ## Irreducible call-supply assumptions -/

/-- At one actual boundary call, the completed scheduled prefix supplies the
accepted current-target gate producer.  The producer remains conditional on
the executable Boolean and its matching whole-slot target-support proviso;
neither is assumed by this theorem. -/
noncomputable def completedPrefix_acceptedTargetGateProducerAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (_hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.AcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n) := by
  intro hgate hsupport hguard
  let p := E.completedScheduledEventPrefix v n
  have hpstore : p.store cfg ext = E.store cfg ext v (n + 1) := by
    simpa only [p] using E.completedScheduledEventPrefix_store cfg ext v n
  have hevidenceBoundary :=
    E.completedScheduledEventPrefix_accountingEvidence cfg ext hT
      v hv n hHn1
  have hevidence : E.CurrentTargetPrefixAccountingEvidence cfg ext
      (p.store cfg ext) (p.previousSecond + 1) := by
    rw [hpstore]
    change E.CurrentTargetPrefixAccountingEvidence cfg ext
      (E.store cfg ext v (n + 1)) (n + 1)
    exact hevidenceBoundary
  let state := get_pulled_up_head_state cfg ext
    (E.store cfg ext v (n + 1))
  have hstate : state = get_pulled_up_head_state cfg ext
      (p.store cfg ext) := by
    rw [hpstore]
  have hval : state.validators = E.registry := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_validators cfg ext B hT
        hanchor hboundary hv hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state] using
      E.completedPrefix_pulledUpHead_totalActive cfg ext B hT
        hC.static_validators hanchor hboundary hv hHn1
  have hgateBoundary : will_current_target_be_justified cfg ext
      (E.store cfg ext v (n + 1)) = true := by
    simpa only [E.fcrStep_store] using hgate
  have hsupportBoundary : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v (n + 1))) (n + 1) := by
    simpa only [E.fcrStep_store] using hsupport
  have hendH := E.currentTargetEpochEnd_within_of_epochEndsFitUint64
    cfg ext hfit (v := v) (q := n + 1) hHn1
  have hanchorH := E.completedPrefix_anchor_epoch_within cfg ext hT
    hC.static_validators
  have hendHP : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (p.store cfg ext)) := by
    rw [hpstore]
    exact hendH
  have hgateP : will_current_target_be_justified cfg ext
      (p.store cfg ext) = true := by
    rw [hpstore]
    exact hgateBoundary
  have hsupportP : HonestVotesSupportTarget cfg E
      (get_current_target cfg (p.store cfg ext))
      (p.previousSecond + 1) := by
    rw [hpstore]
    change HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v (n + 1))) (n + 1)
    exact hsupportBoundary
  have hrealized :=
    E.scheduledEventPrefix_acceptedTargetA32GateRealization_withLookahead
    cfg ext B hT hC.synchrony.delivery_lookahead hC.static_validators
      hC.byzantine_bound
      hC.phase0_source hC.phase0_boundary_source hanchor hboundary p hv hHn1
      hevidence hstate hval htab hendHP hanchorH (by have := hC.balance_floor; omega)
      hgateP hsupportP
      (by rw [hpstore]; simpa only [E.fcrStep_store] using hguard)
  rw [hpstore] at hrealized
  simpa only [E.fcrStep_store] using hrealized

/-- The completed-prefix primitive bundle discharges the complete call
interface required by the historical write-back induction. -/
noncomputable def
    acceptedHistoricalA32CallInterfaces_of_completedPrefixes
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    E.AcceptedHistoricalA32CallInterfaces cfg ext B := by
  intro v hv n hcall hHn1
  exact {
    target_gate_producer :=
      E.completedPrefix_acceptedTargetGateProducerAt cfg ext B hT hC hfit
        hanchor hboundary hv hcall hHn1
  }

end Execution

end FastConfirmation.Spec

end
