import FastConfirmation.Spec.Proof.AcceptedCandidateHistoryRecurrence
import FastConfirmation.Spec.Proof.AcceptedResetAdoption

/-!
# Accepted active-observed restart adoption

The observed checkpoint used by an active epoch-start restart is copied from
an earlier store-global unrealized-justified field.  The accepted cache
installation theorem retains that field's exact origin: it is either the
trusted anchor or `GU` of an accepted carrier known at the installation
store.

At the actual epoch-boundary call, ordinary block relay makes that carrier
known at every honest endpoint.  Since the carrier predates the boundary, the
handler-derived accepted justified-maximality invariant has already pulled
its `GU` epoch into the endpoint's realized justified maximum.  Thus the
restart's epoch-only adoption law is a theorem of the executable trajectory;
it is not an additional reset assumption.

No checkpoint ancestry, source lock, fork-choice head, filter result, or
`SafeFrom` conclusion is used here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Boundary adoption, scoped to an actually compatible observed restart.

The conclusion is deliberately only an epoch inequality.  It does not order
checkpoint roots and does not itself imply the all-future observed source
lock. -/
def ActualFCRGuardedObservedAdoption
    (v : ValidatorIndex) (n : ℕ) : Prop :=
  ObservedRestartCompatible cfg (E.fcrStep cfg ext v n) →
    ∀ w ∈ E.honest, E.WithinHorizon cfg (n + 1) →
      (E.fcrStep cfg ext v n
        ).current_epoch_observed_justified_checkpoint.epoch ≤
        (E.store cfg ext w (n + 1)).justified_checkpoint.epoch

/-- The active observed-reset branch's boundary adoption follows from its
accepted cache installation, the actual epoch-boundary clock, ordinary block
relay, and the handler-derived old-`GU` maximum.

The `ObservedRestartCompatible` argument in the conclusion is intentionally
unused: the stronger branch-indexed `ObservedResetCandidateInputAt` premise
already contains the exact active restart facts. -/
theorem ObservedResetCandidateInputAt.actualFCRGuardedObservedAdoption
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (h : ObservedResetCandidateInputAt cfg ext
      (E.fcrStep cfg ext v n) trace) :
    E.ActualFCRGuardedObservedAdoption cfg ext v n := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  obtain ⟨hi⟩ :=
    FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.acceptedInstallation
      (E := E) cfg ext B hgenShort hanchor hspe h
  have horiginLeBoundary : hi.originSecond ≤ n + 1 :=
    hi.origin_le.trans (Nat.le_succ n)
  have horiginH : E.WithinHorizon cfg hi.originSecond :=
    E.withinHorizon_mono cfg horiginLeBoundary hHn1
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    have hslotAdvanceRaw := hcall
    unfold IsFCRCallAt at hslotAdvanceRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hslotAdvanceRaw
    exact hslotAdvanceRaw
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.fcrStep_store, E.store_current_slot] using h.epoch_start
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hrelayGate : E.slot_at cfg hi.originSecond + 1 ≤
      E.slot_at cfg (n + 1 + 1) := by
    calc
      E.slot_at cfg hi.originSecond + 1 ≤ E.slot_at cfg n + 1 :=
        Nat.add_le_add_right (E.slot_at_mono cfg hi.origin_le) 1
      _ ≤ E.slot_at cfg (n + 1) := Nat.succ_le_iff.mpr hslotAdvance
      _ ≤ E.slot_at cfg (n + 1 + 1) :=
        E.slot_at_mono cfg (Nat.le_succ _)
  unfold ActualFCRGuardedObservedAdoption
  intro _hrestart w hw hHn1'
  rcases hi.accepted_origin with hanchorField | ⟨tip, htip, hguField⟩
  · have hcAnchor :
        (E.fcrStep cfg ext v n
          ).current_epoch_observed_justified_checkpoint = B.anchor :=
      hi.field_eq.trans hanchorField
    rw [hcAnchor]
    exact E.anchor_epoch_le_acceptedGlobalJustified
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w (n + 1))
  · have htipEndpoint : tip ∈
        (E.store cfg ext w (n + 1)).block_roots :=
      hsync.block_relay v hv hi.originSecond tip horiginH htip.known
        w hw (n + 1) hHn1' hrelayGate
    have htipBlockAgree :
        (E.store cfg ext v hi.originSecond).blocks tip =
          (E.store cfg ext w (n + 1)).blocks tip :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext v hi.originSecond)
        (E.blockProvenance cfg ext w (n + 1)) htip.known htipEndpoint
    have htipSlotOrigin :
        ((E.store cfg ext v hi.originSecond).blocks tip).slot ≤
          E.slot_at cfg hi.originSecond := by
      simpa only [E.store_current_slot] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds
          hgenShort v hi.originSecond tip htip.known
    have htipSlotLtBoundary :
        ((E.store cfg ext w (n + 1)).blocks tip).slot <
          E.slot_at cfg (n + 1) := by
      rw [← htipBlockAgree]
      exact (htipSlotOrigin.trans (E.slot_at_mono cfg hi.origin_le)).trans_lt
        hslotAdvance
    have htipOld : get_block_epoch cfg (E.store cfg ext w (n + 1)) tip <
        get_current_store_epoch cfg (E.store cfg ext w (n + 1)) := by
      have htipSlotLtStart := htipSlotLtBoundary
      rw [hslotBoundary] at htipSlotLtStart
      simp only [get_block_epoch, get_current_store_epoch,
        E.store_current_slot, compute_epoch_at_slot]
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch] using htipSlotLtStart
    have hendpoint : E.CausalStore cfg ext
        (E.store cfg ext w (n + 1)) :=
      E.store_causal cfg ext w (n + 1)
    have htipAccepted : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
        (E.store cfg ext w (n + 1)) tip :=
      Execution.AcceptedCarrierIn.of_causal_known hendpoint htipEndpoint
    have hmax := hendpoint.acceptedFFGJustifiedMaximality
      B hT.whole_seconds hgenShort hanchor
    have hcGU :
        (E.fcrStep cfg ext v n
          ).current_epoch_observed_justified_checkpoint = B.state.GU tip :=
      hi.field_eq.trans hguField
    rw [hcGU]
    exact hmax.oldGU tip htipAccepted htipOld

end Execution

end FastConfirmation.Spec
