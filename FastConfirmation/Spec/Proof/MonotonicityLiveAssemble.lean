module
public import FastConfirmation.Spec.Proof.MonotonicityLiveRestart

@[expose] public section

/-!
# Assembly of live monotonicity certificates

The lemmas here join historical one-block confirmations to their later
boundary checks.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- A consecutive parent in the same epoch makes the confirmation window
start at the block itself. -/
theorem live_consecutive_parent_window_start
    (store : Store Root) (b : Root) (e : Epoch)
    (hepoch : get_block_epoch cfg store b = e)
    (hstart : compute_start_slot_at_epoch cfg e < (store.blocks b).slot)
    (hconsecutive :
      (store.blocks (store.blocks b).parent_root).slot + 1 =
        (store.blocks b).slot) :
    (if get_block_epoch cfg store b >
        get_block_epoch cfg store (store.blocks b).parent_root then
      compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
     else (store.blocks b).slot) = (store.blocks b).slot := by
  have hpStart : compute_start_slot_at_epoch cfg e ≤
      (store.blocks (store.blocks b).parent_root).slot := by
    rw [← hconsecutive] at hstart
    exact Nat.lt_succ_iff.mp hstart
  have hpEpochLo : e ≤
      get_block_epoch cfg store (store.blocks b).parent_root := by
    apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
    simpa only [get_block_epoch, compute_epoch_at_slot,
      compute_start_slot_at_epoch] using hpStart
  have hpEpochHi :
      get_block_epoch cfg store (store.blocks b).parent_root ≤ e := by
    have hparentLe : (store.blocks (store.blocks b).parent_root).slot ≤
        (store.blocks b).slot :=
      (Nat.le_succ _).trans hconsecutive.le
    have hdiv :
        (store.blocks (store.blocks b).parent_root).slot / cfg.slots_per_epoch ≤
          (store.blocks b).slot / cfg.slots_per_epoch :=
      Nat.div_le_div_right hparentLe
    have hbe : (store.blocks b).slot / cfg.slots_per_epoch = e := hepoch
    rw [hbe] at hdiv
    simpa only [get_block_epoch, compute_epoch_at_slot] using hdiv
  have hpEpoch := Nat.le_antisymm hpEpochHi hpEpochLo
  simp [hepoch, hpEpoch]

namespace Execution

variable (E : Execution Root)

/-- Every proper partial window inside the accepted current epoch has an
estimator value divisible by one hundred. The first slot's exact committee
weight determines the estimator's per-slot rate. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_epoch_partial_estimate_divisible
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (store : Store Root) (e : Epoch)
    (hcurrent : get_current_store_epoch cfg store = e)
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hstartH : E.SlotWithinHorizon cfg (compute_start_slot_at_epoch cfg e))
    (hendH : E.SlotWithinHorizon cfg
      (compute_start_slot_at_epoch cfg (e + 1) - 1))
    (s t : Slot) (hs : compute_start_slot_at_epoch cfg e < s)
    (hst : s ≤ t)
    (ht : t ≤ compute_start_slot_at_epoch cfg (e + 1) - 1) :
    100 ∣ estimate_committee_weight_between_slots cfg
      (E.total_active cfg) s t := by
  let A := compute_start_slot_at_epoch cfg e
  let Z := compute_start_slot_at_epoch cfg (e + 1) - 1
  have hnext : compute_start_slot_at_epoch cfg (e + 1) =
      A + cfg.slots_per_epoch := by
    simp [A, compute_start_slot_at_epoch, Nat.add_mul]
  have hZeq : Z = A + (cfg.slots_per_epoch - 1) := by
    dsimp only [Z]
    rw [hnext]
    exact Nat.add_sub_assoc (Nat.succ_le_of_lt cfg.slots_per_epoch_pos) A
  have hZlt : Z < compute_start_slot_at_epoch cfg (e + 1) := by
    rw [hZeq, hnext]
    exact Nat.add_lt_add_left
      (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
  have hA1Z : A + 1 ≤ Z := by
    rw [hZeq]
    exact Nat.add_le_add_left
      (Nat.le_sub_one_of_lt h.slots_per_epoch_gt_one) A
  have hA1H : E.SlotWithinHorizon cfg (A + 1) :=
    E.slotWithinHorizon_mono cfg hA1Z hendH
  have hEpoch : ∀ x : Slot,
      A ≤ x → x < compute_start_slot_at_epoch cfg (e + 1) →
      compute_epoch_at_slot cfg x = e := by
    intro x hlo hhi
    have hge : e ≤ compute_epoch_at_slot cfg x := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [A, compute_start_slot_at_epoch, compute_epoch_at_slot] using hlo
    have hlt : compute_epoch_at_slot cfg x < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hhi
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hge
  have hAeq : currentTargetEpochStart cfg store = A := by
    simp [currentTargetEpochStart, A, hcurrent]
  have hEndEq : currentTargetEpochEnd cfg store = Z := by
    simp [currentTargetEpochEnd, hAeq, hZeq]
  have hAhi : A < compute_start_slot_at_epoch cfg (e + 1) :=
    ((Nat.lt_succ_self A).trans_le hA1Z).trans_le hZlt.le
  have hA1hi : A + 1 < compute_start_slot_at_epoch cfg (e + 1) :=
    hA1Z.trans_lt hZlt
  have hFirstCov : is_full_validator_set_covered cfg A A = false := by
    apply no_full_coverage_of_short_range cfg A A
    simpa only [hZeq] using hA1Z
  have hRestCov : is_full_validator_set_covered cfg (A + 1) Z = false :=
    no_full_coverage_inside_epoch_after_start cfg e (A + 1) Z
      (Nat.lt_succ_self A) hZlt
  have hFirst := h.current_epoch_partial_window_exact cfg ext E store A
    hcurrentH (by rw [hAeq]; exact hstartH)
    (by rw [hEndEq]; exact hendH)
    hstartH hA1H
    (by rw [hAeq]) (by rw [hEndEq]; exact hA1Z)
    (by rw [hAeq, hEndEq]
        exact (hEpoch A (Nat.le_refl A) hAhi).trans
          (hEpoch Z ((Nat.le_succ A).trans hA1Z) hZlt).symm)
    (by rw [hAeq]; exact hFirstCov)
    (by rw [hEndEq]; exact hRestCov)
    (by rw [hAeq])
    (by rw [hEndEq]
        exact (hEpoch (A + 1) (Nat.le_succ A) hA1hi).trans
          (hEpoch Z ((Nat.le_succ A).trans hA1Z) hZlt).symm)
  have hFirstExact :
      estimate_committee_weight_between_slots cfg (E.total_active cfg) A A =
        E.weight (E.committee A) := by
    simpa [hAeq, Execution.span_committee] using hFirst.1.symm
  have hsHi : s < compute_start_slot_at_epoch cfg (e + 1) :=
    (hst.trans ht).trans_lt hZlt
  have htHi : t < compute_start_slot_at_epoch cfg (e + 1) :=
    ht.trans_lt hZlt
  exact E.hundred_dvd_same_epoch_estimate_of_one_slot_exact cfg
    h.completed_calls.byzantine_bound (E.total_active cfg) A s t
    hFirstCov hFirstExact hst
    (no_full_coverage_inside_epoch_after_start cfg e s t hs htHi)
    ((hEpoch s hs.le hsHi).trans (hEpoch t (hs.le.trans hst) htHi).symm)

/-- A confirmed live block and its parent keep consecutive slots in every
later store. Thus neither store charges an empty-slot support discount. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_confirmed_parent_window_later
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q T : ℕ}
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hqm : q + 1 ≤ m) (hqT : q + 1 ≤ T)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true)
    (hs0 : E.slot_at cfg 0 <
      get_block_slot (E.store cfg ext w (q + 1)) b)
    (hsm : get_block_slot (E.store cfg ext w (q + 1)) b <
      E.slot_at cfg m) :
    let old := E.store cfg ext w (q + 1)
    let later := E.store cfg ext w T
    (old.blocks (old.blocks b).parent_root).slot + 1 = (old.blocks b).slot ∧
    (later.blocks b).slot = (old.blocks b).slot ∧
    (later.blocks (later.blocks b).parent_root).slot + 1 =
      (later.blocks b).slot ∧
    (∀ source : BeaconState Root,
      get_support_discount cfg ext old source b = 0 ∧
      get_support_discount cfg ext later source b = 0) := by
  dsimp only
  let old := E.store cfg ext w (q + 1)
  let later := E.store cfg ext w T
  obtain ⟨r, br, hbr, hslot, _, hparent⟩ :=
    h.live_one_confirmed_parent cfg ext E live hw hHq1 hqm
      hb hp hconf hs0 hsm
  have hrOld : r ∈ old.block_roots := by
    rw [← hparent]
    exact hp
  have hrLater : r ∈ later.block_roots :=
    (E.store_storeLE cfg ext w hqT).1 hrOld
  have hbLater : b ∈ later.block_roots :=
    (E.store_storeLE cfg ext w hqT).1 hb
  have hbAgree : old.blocks b = later.blocks b :=
    h.trajectory.wellFormed.blocks_agree
      (E.blockProvenance cfg ext w (q + 1))
      (E.blockProvenance cfg ext w T) hb hbLater
  have hrAgree : old.blocks r = later.blocks r :=
    h.trajectory.wellFormed.blocks_agree
      (E.blockProvenance cfg ext w (q + 1))
      (E.blockProvenance cfg ext w T) hrOld hrLater
  have hrBlock := E.blockAt_of_store_known cfg ext hrOld
  have hrEq := E.blockAt_unique h.trajectory.wellFormed hbr hrBlock
  have hconsecutive : (old.blocks (old.blocks b).parent_root).slot + 1 =
      (old.blocks b).slot := by
    dsimp only [old]
    rw [hparent]
    rw [hrEq] at hslot
    simpa only [get_block_slot] using hslot
  have hlater : (later.blocks (later.blocks b).parent_root).slot + 1 =
      (later.blocks b).slot := by
    rw [← hbAgree, hparent, ← hrAgree]
    simpa only [old, hparent] using hconsecutive
  refine ⟨hconsecutive, congrArg BeaconBlock.slot hbAgree.symm, hlater, ?_⟩
  intro source
  exact ⟨live_support_discount_zero_of_consecutive_slots cfg ext old source b
      hconsecutive,
    live_support_discount_zero_of_consecutive_slots cfg ext later source b hlater⟩

/-- A historical current-source certificate fixes the start of both the
historical and boundary confirmation windows at the same block slot. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_confirmed_window_start_later
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q T : ℕ}
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hqm : q + 1 ≤ m) (hqT : q + 1 ≤ T)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true)
    (hs0 : E.slot_at cfg 0 <
      get_block_slot (E.store cfg ext w (q + 1)) b)
    (hsm : get_block_slot (E.store cfg ext w (q + 1)) b <
      E.slot_at cfg m)
    (e : Epoch)
    (hepoch : get_block_epoch cfg (E.store cfg ext w (q + 1)) b = e)
    (hstart : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w (q + 1)).blocks b).slot) :
    let old := E.store cfg ext w (q + 1)
    let later := E.store cfg ext w T
    (if get_block_epoch cfg old b >
        get_block_epoch cfg old (old.blocks b).parent_root then
      compute_start_slot_at_epoch cfg (get_block_epoch cfg old b)
     else (old.blocks b).slot) = (old.blocks b).slot ∧
    (if get_block_epoch cfg later b >
        get_block_epoch cfg later (later.blocks b).parent_root then
      compute_start_slot_at_epoch cfg (get_block_epoch cfg later b)
     else (later.blocks b).slot) = (old.blocks b).slot := by
  dsimp only
  obtain ⟨hold, hslot, hlater, _⟩ :=
    h.live_confirmed_parent_window_later cfg ext E live hw
      hHq1 hqm hqT hb hp hconf hs0 hsm
  have hepochLater : get_block_epoch cfg (E.store cfg ext w T) b = e := by
    simpa only [get_block_epoch, compute_epoch_at_slot, get_block_slot]
      using (congrArg (fun s : Slot => compute_epoch_at_slot cfg s) hslot).trans hepoch
  have hstartLater : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w T).blocks b).slot := by
    rw [hslot]
    exact hstart
  refine ⟨live_consecutive_parent_window_start cfg _ _ e hepoch
    hstart hold, ?_⟩
  rw [live_consecutive_parent_window_start cfg _ _ e hepochLater
    hstartLater hlater, hslot]

/-- The old current source and boundary previous source use the same keyed
checkpoint and have the accepted static registry and total. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_historical_boundary_sources
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    {q T : ℕ} (hqT : q < T)
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hHT1 : E.WithinHorizon cfg (T + 1))
    (hT : E.slot_at cfg T < compute_start_slot_at_epoch cfg (e + 1))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (T + 1))) = true)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hbSlot : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w (q + 1)).blocks b).slot)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    let oldSource := get_current_balance_source (E.fcrStep cfg ext w q)
    let newSource := get_previous_balance_source (E.fcrStep cfg ext w T)
    oldSource.validators = E.registry ∧
      newSource.validators = E.registry ∧
      get_current_epoch cfg oldSource < E.verification_horizon ∧
      get_current_epoch cfg newSource < E.verification_horizon ∧
      get_total_active_balance cfg oldSource = E.total_active cfg ∧
      get_total_active_balance cfg newSource = E.total_active cfg := by
  let cp := (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint
  have hsource : (E.fcrStep cfg ext w T).previous_epoch_observed_justified_checkpoint =
      cp := h.live_boundary_source_checkpoint_eq cfg ext E w e hqT hT
        hstart hb hbSlot
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext w (q + 1))
      ((E.store cfg ext w (q + 1)).checkpoint_states cp) b = true := by
    simpa only [cp, E.fcrStep_store, get_current_balance_source] using hconf
  have hgeometry := h.live_confirmed_source_geometry_later cfg ext E
    hw ((Nat.succ_le_of_lt hqT).trans (Nat.le_succ T))
    hHq1 hHT1 cp b hconf'
  simpa only [get_current_balance_source, get_previous_balance_source,
    E.fcrStep_store, hsource, cp] using hgeometry

/-- The estimator for a historically certified post-start block grows by
exactly the remaining suffix of the completed epoch. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_historical_boundary_estimate_growth
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    {q T : ℕ} (hqT : q < T)
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hHT1 : E.WithinHorizon cfg (T + 1))
    (hT : E.slot_at cfg T < compute_start_slot_at_epoch cfg (e + 1))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (T + 1))) = true)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hbSlot : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w (q + 1)).blocks b).slot)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    let old := E.store cfg ext w (q + 1)
    let oldSource := get_current_balance_source (E.fcrStep cfg ext w q)
    let newSource := get_previous_balance_source (E.fcrStep cfg ext w T)
    let a := (old.blocks b).slot
    let u := E.slot_at cfg (q + 1)
    let z := compute_start_slot_at_epoch cfg (e + 1) - 1
    estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg newSource) a z =
      estimate_committee_weight_between_slots cfg
        (get_total_active_balance cfg oldSource) a (u - 1) +
      estimate_committee_weight_between_slots cfg (E.total_active cfg) u z := by
  dsimp only
  let a := ((E.store cfg ext w (q + 1)).blocks b).slot
  let u := E.slot_at cfg (q + 1)
  let z := compute_start_slot_at_epoch cfg (e + 1) - 1
  obtain ⟨_, _, _, _, hOldTotal, hNewTotal⟩ :=
    h.live_historical_boundary_sources cfg ext E hw e hqT hHq1 hHT1
      hT hstart hb hbSlot hconf
  have hBefore : a < u := h.live_one_confirmed_slot_before_call
    cfg ext E hw hHq1 hb hp hconf
  have huZ : u ≤ z := by
    exact (E.slot_at_mono cfg (Nat.succ_le_of_lt hqT)).trans
      (Nat.le_sub_one_of_lt hT)
  have hzU : z < compute_start_slot_at_epoch cfg (e + 1) :=
    Nat.sub_lt (by
      simp only [compute_start_slot_at_epoch]
      exact Nat.mul_pos (Nat.succ_pos e) cfg.slots_per_epoch_pos) (by omega)
  have huPrev : u - 1 + 1 = u :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hBefore))
  have haPrev : a ≤ u - 1 := Nat.le_sub_one_of_lt hBefore
  have hgrowth := estimate_growth_inside_epoch_after_start cfg
    (E.total_active cfg) e a (u - 1) z hbSlot haPrev
    (by rw [huPrev]; exact huZ) hzU
  simpa only [hOldTotal, hNewTotal,
    huPrev] using hgrowth

/-- Both pieces of the historical block's boundary window are quantized in
hundreds of Gwei. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_historical_boundary_estimate_divisors
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    {q T : ℕ} (hqT : q < T)
    (hHq1 : E.WithinHorizon cfg (q + 1))
    (hHT1 : E.WithinHorizon cfg (T + 1))
    (hT : E.slot_at cfg T < compute_start_slot_at_epoch cfg (e + 1))
    (hboundary : E.slot_at cfg (T + 1) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (T + 1))) = true)
    {b : Root} (hb : b ∈ (E.store cfg ext w (q + 1)).block_roots)
    (hp : ((E.store cfg ext w (q + 1)).blocks b).parent_root ∈
      (E.store cfg ext w (q + 1)).block_roots)
    (hbSlot : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w (q + 1)).blocks b).slot)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    let old := E.store cfg ext w (q + 1)
    let oldSource := get_current_balance_source (E.fcrStep cfg ext w q)
    let a := (old.blocks b).slot
    let u := E.slot_at cfg (q + 1)
    let z := compute_start_slot_at_epoch cfg (e + 1) - 1
    (100 ∣ estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg oldSource) a (u - 1)) ∧
    (100 ∣ estimate_committee_weight_between_slots cfg
      (E.total_active cfg) u z) := by
  dsimp only
  let old := E.store cfg ext w (q + 1)
  let a := (old.blocks b).slot
  let u := E.slot_at cfg (q + 1)
  let z := compute_start_slot_at_epoch cfg (e + 1) - 1
  have hBefore : a < u := h.live_one_confirmed_slot_before_call
    cfg ext E hw hHq1 hb hp hconf
  have hUleT : u ≤ E.slot_at cfg T :=
    E.slot_at_mono cfg (Nat.succ_le_of_lt hqT)
  have huZ : u ≤ z := hUleT.trans (Nat.le_sub_one_of_lt hT)
  have huU : u < compute_start_slot_at_epoch cfg (e + 1) :=
    hUleT.trans_lt hT
  have hEpochU : compute_epoch_at_slot cfg u = e := by
    have hlo : e ≤ compute_epoch_at_slot cfg u := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using
        (hbSlot.le.trans hBefore.le)
    have hhi : compute_epoch_at_slot cfg u < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using huU
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
  have hCurrent : get_current_store_epoch cfg old = e := by
    rw [get_current_store_epoch, E.store_current_slot]
    exact hEpochU
  have hCurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg old) := by
    rw [E.store_current_slot]
    exact E.slotWithinHorizon_of_le cfg (Nat.le_refl u) hHq1
  have hStartH : E.SlotWithinHorizon cfg (compute_start_slot_at_epoch cfg e) :=
    E.slotWithinHorizon_mono cfg (hbSlot.le.trans hBefore.le)
      (by exact E.slotWithinHorizon_of_le cfg (Nat.le_refl u) hHq1)
  have hEndH : E.SlotWithinHorizon cfg z := by
    apply E.slotWithinHorizon_of_le cfg _ hHT1
    rw [hboundary]
    exact Nat.sub_le _ _
  have hOldTotal := (h.live_historical_boundary_sources cfg ext E
    hw e hqT hHq1 hHT1 hT hstart hb hbSlot hconf).2.2.2.2.1
  have hOldWindow := h.live_epoch_partial_estimate_divisible cfg ext E
    old e hCurrent hCurrentH hStartH hEndH a (u - 1)
    hbSlot (Nat.le_sub_one_of_lt hBefore)
    (Nat.sub_le u 1 |>.trans huZ)
  have hSuffix := h.live_epoch_partial_estimate_divisible cfg ext E
    old e hCurrent hCurrentH hStartH hEndH u z
    (hbSlot.trans hBefore) huZ (Nat.le_refl z)
  simpa only [hOldTotal] using And.intro hOldWindow hSuffix

end Execution

end FastConfirmation.Spec

end
