module
public import FastConfirmationProofs.FFG.SourceHistory.CandidateHistoryRecurrence
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

structure TrustedAcceptedUJCacheInstallationAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (v : ValidatorIndex) (upper : ℕ) (field : Checkpoint Root) where
  originSecond : ℕ
  origin_le : originSecond ≤ upper
  field_eq : field =
    (E.store cfg ext v originSecond).unrealized_justified_checkpoint
  initialization_or_rotation :
    originSecond = 0 ∨
      is_start_slot_at_epoch cfg
        (get_current_slot cfg (E.store cfg ext v originSecond) + 1) = true
  /-- Every noninitial origin is the first second after a scheduled slot
      advance. This retains the source time needed by deadline-cutoff relay. -/
  origin_call : originSecond = 0 ∨
    ∃ pred, originSecond = pred + 1 ∧
      E.IsScheduledFCRCallAt cfg ext v pred
  accepted_origin : TrustedAcceptedGlobalUnrealizedJustifiedOrigin B.state
    (E.store cfg ext v originSecond)
    (E.store cfg ext v originSecond).unrealized_justified_checkpoint

/-- A cached UJ installation is observed at or before the attestation
deadline of its source slot. Initialization uses second zero; every later
installation follows an exact scheduled slot advance. -/
theorem TrustedAcceptedUJCacheInstallationAt.origin_before_deadline
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {upper : ℕ} {field : Checkpoint Root}
    (h : E.TrustedAcceptedUJCacheInstallationAt cfg ext B v upper field)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time) :
    h.originSecond ≤
      E.slot_start cfg (E.slot_at cfg h.originSecond) +
        get_attestation_due_ms cfg / 1000 := by
  rcases h.origin_call with hzero | ⟨pred, heq, hcall⟩
  · rw [hzero]
    exact Nat.zero_le _
  · rw [heq]
    have hstartLe :
        E.slot_start cfg (E.slot_at cfg (pred + 1)) ≤ pred + 1 :=
      E.slot_start_le_of_slot_at cfg hdiv hgenTime rfl
    have hslotStart :
        E.slot_at cfg (E.slot_start cfg (E.slot_at cfg (pred + 1))) =
          E.slot_at cfg (pred + 1) :=
      E.slot_at_slot_start cfg hdiv
        (E.slot_at_mono cfg (Nat.zero_le (pred + 1))) hgenTime
    have hadvance : E.slot_at cfg pred < E.slot_at cfg (pred + 1) := by
      unfold Execution.IsScheduledFCRCallAt at hcall
      rw [E.store_current_slot cfg ext v (pred + 1),
        E.store_current_slot cfg ext v pred] at hcall
      exact hcall
    have hstartGe : pred + 1 ≤
        E.slot_start cfg (E.slot_at cfg (pred + 1)) := by
      by_contra hnot
      have hstartPred : E.slot_start cfg (E.slot_at cfg (pred + 1)) ≤ pred := by
        omega
      have hmono := E.slot_at_mono cfg hstartPred
      rw [hslotStart] at hmono
      exact (Nat.not_lt_of_ge hmono) hadvance
    omega

/-- Exact previous-greatest field recurrence, stated independently of any
checkpoint realization or history bundle. -/
private theorem fcr_previousGreatest_succ_exact
    (v : ValidatorIndex) (n : ℕ)
    (hcall : E.IsScheduledFCRCallAt cfg ext v n) :
    (E.fcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else
        (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  have hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n) := hcall
  simp only [Execution.fcr]
  rw [if_pos hadv]
  change FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
    (update_fast_confirmation_variables cfg
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- The previous-greatest cache always names an exact earlier UJ field and
retains the accepted global origin at the installation store. -/
theorem trusted_previousGreatest_acceptedInstallation
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (v : ValidatorIndex) :
    ∀ n : ℕ, Nonempty (E.TrustedAcceptedUJCacheInstallationAt cfg ext B v n
      (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint) := by
  intro n
  induction n with
  | zero =>
      have horigin :=
        (B.causalStoreGlobalProjection hgen hanchor
          (E.store_causal cfg ext v 0)).storeGlobal.unrealized_justified
      refine ⟨{
        originSecond := 0
        origin_le := Nat.le_refl 0
        field_eq := ?_
        initialization_or_rotation := Or.inl rfl
        origin_call := Or.inl rfl
        accepted_origin := horigin
      }⟩
      obtain ⟨ast, ablk, hgenEq, _hslot⟩ := hgen
      change E.genesis_store.finalized_checkpoint =
        E.genesis_store.unrealized_justified_checkpoint
      rw [hgenEq]
      simp only [get_forkchoice_store]
  | succ n ih =>
      obtain ⟨ih⟩ := ih
      by_cases hcall : E.IsScheduledFCRCallAt cfg ext v n
      · rw [E.fcr_previousGreatest_succ_exact cfg ext v n hcall]
        by_cases hrotate : is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) = true
        · rw [if_pos hrotate]
          exact ⟨{
            originSecond := n + 1
            origin_le := Nat.le_refl _
            field_eq := rfl
            initialization_or_rotation := Or.inr hrotate
            origin_call := Or.inr ⟨n, rfl, hcall⟩
            accepted_origin :=
              (B.causalStoreGlobalProjection hgen hanchor
                (E.store_causal cfg ext v (n + 1))).storeGlobal
                  |>.unrealized_justified
          }⟩
        · rw [if_neg hrotate]
          exact ⟨{
            originSecond := ih.originSecond
            origin_le := ih.origin_le.trans (Nat.le_succ n)
            field_eq := ih.field_eq
            initialization_or_rotation := ih.initialization_or_rotation
            origin_call := ih.origin_call
            accepted_origin := ih.accepted_origin
          }⟩
      · have hfield :
            (E.fcr cfg ext v (n + 1)
              ).previous_epoch_greatest_unrealized_checkpoint =
            (E.fcr cfg ext v n
              ).previous_epoch_greatest_unrealized_checkpoint := by
          have hadv : ¬ get_current_slot cfg
              (E.store cfg ext v (n + 1)) >
              get_current_slot cfg (E.store cfg ext v n) := hcall
          simp only [Execution.fcr, if_neg hadv]
        exact ⟨{
          originSecond := ih.originSecond
          origin_le := ih.origin_le.trans (Nat.le_succ n)
          field_eq := hfield.trans ih.field_eq
          initialization_or_rotation := ih.initialization_or_rotation
          origin_call := ih.origin_call
          accepted_origin := ih.accepted_origin
        }⟩

/-- `compute_slots_since_epoch_start` is the slot modulo the positive epoch
length. -/
private theorem slotsSinceEpochStart_eq_mod (s : Slot) :
    compute_slots_since_epoch_start cfg s = s % cfg.slots_per_epoch := by
  have h := Nat.div_add_mod s cfg.slots_per_epoch
  simp only [compute_slots_since_epoch_start, compute_start_slot_at_epoch,
    compute_epoch_at_slot]
  rw [Nat.mul_comm (s / cfg.slots_per_epoch) cfg.slots_per_epoch]
  omega

/-- A non-degenerate epoch cannot start at two consecutive slots. -/
private theorem next_not_epochStart_of_epochStart
    (hspe : 1 < cfg.slots_per_epoch) {s : Slot}
    (hstart : is_start_slot_at_epoch cfg s = true) :
    is_start_slot_at_epoch cfg (s + 1) ≠ true := by
  intro hnext
  simp only [is_start_slot_at_epoch, decide_eq_true_eq,
    slotsSinceEpochStart_eq_mod] at hstart hnext
  have hsmod : s % cfg.slots_per_epoch = 0 := hstart
  have hnmod : (s + 1) % cfg.slots_per_epoch = 0 := hnext
  have hsdvd : cfg.slots_per_epoch ∣ s := Nat.dvd_of_mod_eq_zero hsmod
  have hndvd : cfg.slots_per_epoch ∣ s + 1 := Nat.dvd_of_mod_eq_zero hnmod
  have honedvd : cfg.slots_per_epoch ∣ 1 :=
    (Nat.dvd_add_right hsdvd).mp hndvd
  have hone := Nat.le_of_dvd Nat.one_pos honedvd
  omega

/-- At a non-degenerate epoch start, the speculative query's observed field
is exactly the carried previous-greatest field. -/
private theorem fcrStep_observed_eq_previousGreatest_of_start
    (hspe : 1 < cfg.slots_per_epoch)
    (v : ValidatorIndex) (n : ℕ)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true) :
    (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint =
      (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  have hnext := next_not_epochStart_of_epochStart cfg hspe hstart
  rw [Execution.fcrStoreAtCall]
  simp only [update_fast_confirmation_variables]
  rw [if_neg hnext, if_pos hstart]

/-- Installation provenance attached to the observed-reset arm of an exact
actual query.  In particular, the source second is `k ≤ n`, the cached
checkpoint is exactly `(store v k).unrealized_justified_checkpoint`, the
initialization/rotation tag is retained, and that UJ field has the accepted
global origin `anchor` or `GU(tip)` at the same store. -/
theorem ObservedResetCandidateInputAt.trusted_acceptedInstallation
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} {n : ℕ}
    {trace : LatestConfirmedCallTrace cfg ext (E.fcrStoreAtCall cfg ext v n)}
    (h : ObservedResetCandidateInputAt cfg ext
      (E.fcrStoreAtCall cfg ext v n) trace) :
    Nonempty (E.TrustedAcceptedUJCacheInstallationAt cfg ext B v n
      (E.fcrStoreAtCall cfg ext v n
        ).current_epoch_observed_justified_checkpoint) := by
  have hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true := by
    simpa only [E.fcrStep_store] using h.epoch_start
  have hfield := E.fcrStep_observed_eq_previousGreatest_of_start
    cfg ext hspe v n hstart
  obtain ⟨hhistory⟩ := E.trusted_previousGreatest_acceptedInstallation
    cfg ext B hgen hanchor v n
  exact ⟨{
    originSecond := hhistory.originSecond
    origin_le := hhistory.origin_le
    field_eq := hfield.trans hhistory.field_eq
    initialization_or_rotation := hhistory.initialization_or_rotation
    origin_call := hhistory.origin_call
    accepted_origin := hhistory.accepted_origin
  }⟩

end Execution
end FastConfirmation.Spec
end
