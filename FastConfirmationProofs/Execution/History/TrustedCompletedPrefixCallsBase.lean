module
public import FastConfirmationProofs.Execution.History.CompletedPrefixCalls
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionCallInduction
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetGateGeometry

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem trusted_completedPrefix_pulledUpHead_validators
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    (get_pulled_up_head_state cfg ext
      (E.store cfg ext v n)).validators = E.registry := by
  have hhead := E.trusted_headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hv n hHn
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hT.genesis_structure
    exact ⟨ast, ablk, hgeq⟩
  have hregistry :=
    (E.registryConstant cfg ext hT.externals_coherence hgen v n).1
      (get_head cfg (E.store cfg ext v n)).root hhead
  simp only [get_pulled_up_head_state]
  split_ifs
  · rw [hT.externals_coherence.process_slots_registry]
    exact hregistry
  · exact hregistry

/-- Pulling the head up makes its state epoch exactly the execution store's
current epoch.  In the no-pull branch this follows from the head-state slot
bound and the negated pull guard. -/
theorem trusted_completedPrefix_pulledUpHead_epoch
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
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
      E.trusted_headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT hanchor
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
theorem trusted_completedPrefix_anchor_epoch_within
    (hT : E.ScheduledPrefixPremises cfg ext)
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
theorem trusted_completedPrefix_pulledUpHead_totalActive
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsv : StaticValidatorSet cfg E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n) :
    get_total_active_balance cfg (get_pulled_up_head_state cfg ext
      (E.store cfg ext v n)) = E.total_active cfg := by
  let state := get_pulled_up_head_state cfg ext (E.store cfg ext v n)
  have hval : state.validators = E.registry := by
    simpa only [state] using E.trusted_completedPrefix_pulledUpHead_validators
      cfg ext B hT hanchor hboundary hv hHn
  have hstateEpoch : get_current_epoch cfg state < E.verification_horizon := by
    rw [E.trusted_completedPrefix_pulledUpHead_epoch cfg ext B hT hanchor
      hboundary hv hHn]
    simpa only [get_current_store_epoch, E.store_current_slot,
      compute_epoch_at_slot] using hHn.2.2
  have hanchorEpoch := E.trusted_completedPrefix_anchor_epoch_within
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

noncomputable def trusted_completedPrefix_acceptedTargetGateProducerAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (_hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      B.anchor B.state (n + 1) (E.fcrStoreAtCall cfg ext v n) := by
  intro hgate hsupport
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
      E.trusted_completedPrefix_pulledUpHead_validators cfg ext B hT
        hanchor hboundary hv hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state] using
      E.trusted_completedPrefix_pulledUpHead_totalActive cfg ext B hT
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
    E.trusted_scheduledEventPrefix_acceptedTargetA32GateRealization_withLookahead
    cfg ext B hT hC.delivery_lookahead hC.static_validators
      hC.byzantine_bound
      hC.phase0_source hC.phase0_boundary_source hanchor hboundary p hv hHn1
      hevidence hstate hval htab hendHP hanchorH hC.balance_floor
      hgateP hsupportP
  rw [hpstore] at hrealized
  simpa only [E.fcrStep_store] using hrealized

theorem trusted_selectedMarginAssumptions_of_completedPrefixes
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    SelectedMarginAssumptions cfg ext E :=
  { genesis := hT.genesis_structure
    wellFormed := hT.wellFormed
    whole_seconds := hT.whole_seconds
    honest_behavior := hT.honest_behavior
    synchrony := hC.synchrony
    externals_coherence := hT.externals_coherence
    static_validators := hC.static_validators
    byzantine_bound := hC.byzantine_bound
    domain := hdomain }

/-- The completed-prefix primitive bundle discharges the complete call
interface required by the historical write-back induction. -/
noncomputable def
    trusted_acceptedHistoricalA32CallInterfaces_of_completedPrefixes
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    E.TrustedAcceptedHistoricalA32CallInterfaces cfg ext B := by
  intro v hv n hcall hHn1
  exact {
    target_gate_producer :=
      E.trusted_completedPrefix_acceptedTargetGateProducerAt cfg ext B hT hC hfit
        hanchor hboundary hv hcall hHn1
  }

/-- End-to-end historical current-lineage invariant after replacing the
abstract call interface by completed-prefix protocol assumptions. -/
theorem trusted_acceptedHistoricalA32CurrentLineage_invariant_of_completedPrefixes
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    ∀ v ∈ E.honest, ∀ n : ℕ, E.WithinHorizon cfg n →
      E.TrustedAcceptedHistoricalA32CurrentLineageAt cfg ext B v n := by
  exact E.trusted_acceptedHistoricalA32CurrentLineage_invariant cfg ext B hT
    (E.trusted_selectedMarginAssumptions_of_completedPrefixes cfg ext B hT hC hdomain
      hanchor hboundary)
    hC.phase0_source hC.phase0_boundary_source hanchor hboundary
      (E.trusted_acceptedHistoricalA32CallInterfaces_of_completedPrefixes
        cfg ext B hT hC hfit hanchor hboundary)

/-- Headline current-epoch lineage using the completed-prefix supplier. -/
theorem trusted_acceptedHistoricalA32CurrentLineage_of_completedPrefixes
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hHn : E.WithinHorizon cfg n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n)) :
    ∃ e : Epoch, Nonempty (E.TrustedAcceptedHistoricalA32LineageCoreAt
      cfg ext B (E.confirmed cfg ext v n) e
      (E.TrustedLazyCertAt cfg ext B n) (E.TrustedLazySupportAt cfg ext B v n)) :=
  (E.trusted_acceptedHistoricalA32CurrentLineage_invariant_of_completedPrefixes
    cfg ext B hT hC hfit hdomain hanchor hboundary v hv n hHn).current_lineage hcurrent

end Execution
end FastConfirmation.Spec
end
