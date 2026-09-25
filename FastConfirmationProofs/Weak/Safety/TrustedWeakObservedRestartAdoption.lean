module
public import FastConfirmationProofs.Weak.Safety.WeakObservedRestartAdoption
public import FastConfirmationProofs.Weak.Certificates.TrustedWeakBankedJustification
public import FastConfirmationProofs.FFG.SourceHistory.TrustedFFGJustifiedMaximality
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {trusted : Store Root → Prop}

theorem trusted_bankedCheckpoint_epoch_le_honestJustified
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : E.slot_at cfg h.second ≤ E.slot_at cfg m)
    (hstart : is_start_slot_at_epoch cfg (E.slot_at cfg m) = true) :
    fcr_store.current_epoch_observed_justified_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgeq, hslotEq, _hparentNe⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgeq, hslotEq⟩
  -- The certified supplier reaches the endpoint by certificate dissemination.
  have hsupplierW : h.supplier ∈ (E.store cfg ext w m).block_roots :=
    (Weak.trusted_bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
      hanchor hboundary hsync  hA.genesis hcomm h hw hmH hgate).1
  -- The banked checkpoint *is* that supplier's own `GU`.
  have hGU : fcr_store.current_epoch_observed_justified_checkpoint =
      B.state.GU h.supplier := by
    rw [h.banked_eq]
    exact E.trusted_accepted_unrealized_justification_eq
      B.coherence.toTrustedFFGSelectorsMatchBeaconStates obs h.second h.supplier_known
  -- The supplier predates the boundary, at the endpoint's own store.
  have hblocksAgree : (E.store cfg ext obs h.second).blocks h.supplier =
      (E.store cfg ext w m).blocks h.supplier :=
    hT.wellFormed.blocks_agree (E.blockProvenance cfg ext obs h.second)
      (E.blockProvenance cfg ext w m) h.supplier_known hsupplierW
  have hsupplierSlotLt :
      ((E.store cfg ext w m).blocks h.supplier).slot < E.slot_at cfg m := by
    have hlt := Weak.BankedJustificationCertificate.supplier_slot_lt cfg ext h
    simp only [get_block_slot, hblocksAgree] at hlt
    exact hlt.trans_le hgate
  have hcurrentEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      compute_epoch_at_slot cfg (E.slot_at cfg m) := by
    simp only [get_current_store_epoch, E.store_current_slot]
  have hstartZero : compute_slots_since_epoch_start cfg (E.slot_at cfg m) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundary : E.slot_at cfg m =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg m)) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hold : get_block_epoch cfg (E.store cfg ext w m) h.supplier <
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    rw [hcurrentEpoch]
    rw [hslotBoundary] at hsupplierSlotLt
    simp only [get_block_epoch, compute_epoch_at_slot]
    exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2 hsupplierSlotLt
  -- The endpoint's own realized justified maximum has already absorbed it.
  have hendpoint : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hmax := hendpoint.trustedAcceptedFFGJustifiedMaximality
    B hT.whole_seconds hgenShort hanchor
  have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
      (E.store cfg ext w m) h.supplier :=
    Execution.AcceptedCarrierIn.of_causal_known hendpoint hsupplierW
  rw [hGU]
  exact hmax.oldGU h.supplier hcarrier hold

/-! ## The call-indexed form -/


theorem ObservedResetCandidateInputAt.trusted_guardedObservedAdoption
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ}
    {trace : Weak.LatestConfirmedCallTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hcert : Weak.BankedJustificationCertificate cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n)) :
    Weak.GuardedObservedAdoption cfg ext E obs n := by
  intro w hw hHn1
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.weakFcrStep_store, E.store_current_slot] using hinput.epoch_start
  exact Weak.trusted_bankedCheckpoint_epoch_le_honestJustified cfg ext hA B hT hanchor
    hboundary hsync  hcomm hcert hw hHn1
    (E.slot_at_mono cfg hcert.second_le) hstart

end Weak
end FastConfirmation.Spec
end
