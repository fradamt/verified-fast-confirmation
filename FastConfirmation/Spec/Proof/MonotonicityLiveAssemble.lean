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

omit [LinearOrder Root] [Inhabited Root] in
/-- Every member of a parent-linked chain starts strictly after its
terminal parent. -/
theorem live_chain_member_slot_gt_terminal {store : Store Root}
    (hwf : ParentSlotLt store)
    {L : List Root}
    (hchain : List.IsChain (fun a c => (store.blocks c).parent_root = a) L)
    (hmem : ∀ x ∈ L, x ∈ store.block_roots)
    {terminal : Root} (hterminal : terminal ∈ store.block_roots)
    (hhead : ∀ x, L.head? = some x → (store.blocks x).parent_root = terminal)
    {x : Root} (hx : x ∈ L) :
    (store.blocks terminal).slot < (store.blocks x).slot := by
  induction hchain generalizing terminal with
  | nil => simp at hx
  | singleton a =>
      have hpar : (store.blocks a).parent_root = terminal := hhead a rfl
      have hlt := hwf a (hmem a (by simp)) (by rw [hpar]; exact hterminal)
      rw [hpar] at hlt
      simp only [List.mem_singleton] at hx
      subst x
      exact hlt
  | @cons_cons a d rest hpar _ ih =>
      have hamem : a ∈ store.block_roots := hmem a (by simp)
      have hparA : (store.blocks a).parent_root = terminal := hhead a rfl
      have ha : (store.blocks terminal).slot < (store.blocks a).slot := by
        have h := hwf a hamem (by rw [hparA]; exact hterminal)
        rwa [hparA] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha
      · have hmem' : ∀ y ∈ d :: rest, y ∈ store.block_roots :=
          fun y hy => hmem y (List.mem_cons_of_mem _ hy)
        have hhead' : ∀ y, (d :: rest).head? = some y →
            (store.blocks y).parent_root = a := by
          intro y hy
          rw [List.head?_cons, Option.some_inj] at hy
          subst y
          exact hpar
        exact ha.trans (ih hmem' hamem hhead' hx')

/-- Each strict descendant in an executable ancestor list has a slot later
than the list's terminal block. -/
theorem live_ancestor_roots_member_slot_gt_terminal {store : Store Root}
    (hwf : ParentSlotLt store)
    {top terminal x : Root}
    (hwalk : WalkKnown store (store.blocks terminal).slot top)
    (hterminal : terminal ∈ store.block_roots)
    (hx : x ∈ get_ancestor_roots store top terminal) :
    (store.blocks terminal).slot < (store.blocks x).slot := by
  exact live_chain_member_slot_gt_terminal
    hwf (get_ancestor_roots_isChain hwf hwalk)
    (fun y hy => get_ancestor_roots_mem hwf hwalk hy)
    hterminal (fun y hy => get_ancestor_roots_head? hwf hwalk hy) hx

namespace Execution

variable (E : Execution Root)

/-- A known block later than the execution's initial slot is not the
genesis-store anchor and therefore has a known parent. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_parent_known_after_initial
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (w : ValidatorIndex) (t : ℕ) {b : Root}
    (hb : b ∈ (E.store cfg ext w t).block_roots)
    (hs0 : E.slot_at cfg 0 < ((E.store cfg ext w t).blocks b).slot) :
    ((E.store cfg ext w t).blocks b).parent_root ∈
      (E.store cfg ext w t).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hstateSlot, _⟩ :=
    h.trajectory.genesis_structure
  rcases E.store_nonAnchorParentKnown cfg ext hgenEq w t b hb with heq | hp
  · subst b
    have hslot0 : E.slot_at cfg 0 = ablk.message.slot := by
      have hc := E.store_current_slot cfg ext 0 0
      change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hc
      rw [hgenEq, get_current_slot_get_forkchoice_store cfg
        h.trajectory.whole_seconds] at hc
      exact hc.symm.trans hstateSlot
    have hanchor := E.store_anchor_block cfg ext
      h.trajectory.wellFormed hgenEq w t hb
    rw [hanchor, ← hslot0] at hs0
    exact False.elim ((Nat.lt_irrefl _) hs0)
  · exact hp

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

/-- The future suffix is both exact and quantized when it begins after the
first slot of the accepted epoch. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_epoch_suffix_quantized_exact
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (store : Store Root) (e : Epoch)
    (hcurrent : get_current_store_epoch cfg store = e)
    (hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hstartH : E.SlotWithinHorizon cfg (compute_start_slot_at_epoch cfg e))
    (hendH : E.SlotWithinHorizon cfg
      (compute_start_slot_at_epoch cfg (e + 1) - 1))
    (u : Slot) (huLo : compute_start_slot_at_epoch cfg e < u)
    (huHi : u ≤ compute_start_slot_at_epoch cfg (e + 1) - 1) :
    let z := compute_start_slot_at_epoch cfg (e + 1) - 1
    E.weight (E.span_committee u z) =
        estimate_committee_weight_between_slots cfg (E.total_active cfg) u z ∧
    100 ∣ estimate_committee_weight_between_slots cfg (E.total_active cfg) u z := by
  exact ⟨h.live_epoch_suffix_estimate_exact cfg ext E store e
      hcurrent hcurrentH hstartH hendH u huLo huHi,
    h.live_epoch_partial_estimate_divisible cfg ext E store e
      hcurrent hcurrentH hstartH hendH u _ huLo huHi (Nat.le_refl _)⟩

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

set_option maxRecDepth 2048 in
/-- A historical current-source certificate for a post-start cached-chain
block survives the next boundary's previous-source check. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_historical_block_reconfirmed
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    {q T : ℕ} (hqT : q < T) (hTm : T + 1 ≤ m)
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
    (hbEpoch : get_block_epoch cfg (E.store cfg ext w (q + 1)) b = e)
    (hbSlot : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w (q + 1)).blocks b).slot)
    (hs0 : E.slot_at cfg 0 <
      ((E.store cfg ext w (q + 1)).blocks b).slot)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
      (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    is_one_confirmed cfg ext (E.store cfg ext w (T + 1))
      (get_previous_balance_source (E.fcrStep cfg ext w T)) b = true := by
  let old := E.store cfg ext w (q + 1)
  let later := E.store cfg ext w (T + 1)
  let oldSource := get_current_balance_source (E.fcrStep cfg ext w q)
  let newSource := get_previous_balance_source (E.fcrStep cfg ext w T)
  let a := (old.blocks b).slot
  let u := E.slot_at cfg (q + 1)
  let z := compute_start_slot_at_epoch cfg (e + 1) - 1
  let added := estimate_committee_weight_between_slots cfg (E.total_active cfg) u z
  let HS := (E.span_committee u z).filter fun i => i ∈ E.honest
  have hqLater : q + 1 ≤ T + 1 :=
    (Nat.succ_le_of_lt hqT).trans (Nat.le_succ T)
  have hqm : q + 1 ≤ m := hqLater.trans hTm
  have hBefore : a < u := h.live_one_confirmed_slot_before_call
    cfg ext E hw hHq1 hb hp hconf
  have huZ : u ≤ z :=
    (E.slot_at_mono cfg (Nat.succ_le_of_lt hqT)).trans
      (Nat.le_sub_one_of_lt hT)
  have hUhi : u < compute_start_slot_at_epoch cfg (e + 1) :=
    (E.slot_at_mono cfg (Nat.succ_le_of_lt hqT)).trans_lt hT
  have hsm : a < E.slot_at cfg m :=
    hBefore.trans_le (E.slot_at_mono cfg hqm)
  have hCurrent : get_current_store_epoch cfg old = e := by
    have hlo : e ≤ compute_epoch_at_slot cfg u := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using
        (hbSlot.le.trans hBefore.le)
    have hhi : compute_epoch_at_slot cfg u < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hUhi
    rw [get_current_store_epoch, E.store_current_slot]
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
  have hCurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg old) := by
    rw [E.store_current_slot]
    exact E.slotWithinHorizon_of_le cfg (Nat.le_refl u) hHq1
  have hStartH : E.SlotWithinHorizon cfg (compute_start_slot_at_epoch cfg e) :=
    E.slotWithinHorizon_mono cfg (hbSlot.le.trans hBefore.le)
      (E.slotWithinHorizon_of_le cfg (Nat.le_refl u) hHq1)
  have hEndH : E.SlotWithinHorizon cfg z := by
    apply E.slotWithinHorizon_of_le cfg _ hHT1
    rw [hboundary]
    exact Nat.sub_le _ _
  have hAinH : E.SlotWithinHorizon cfg a :=
    E.slotWithinHorizon_mono cfg hBefore.le
      (E.slotWithinHorizon_of_le cfg (Nat.le_refl u) hHq1)
  have hOldEndH : E.SlotWithinHorizon cfg (u - 1) :=
    E.slotWithinHorizon_mono cfg (Nat.sub_le u 1)
      (E.slotWithinHorizon_of_le cfg (Nat.le_refl u) hHq1)
  obtain ⟨hvalOld, hvalNew, hOldH, hNewH, htabOld, htabNew⟩ :=
    h.live_historical_boundary_sources cfg ext E hw e hqT hHq1 hHT1
      hT hstart hb hbSlot hconf
  obtain ⟨hParentOld, hslotLater, hParentLater, hDiscount⟩ :=
    h.live_confirmed_parent_window_later cfg ext E live hw
      hHq1 hqm hqLater hb hp hconf hs0 hsm
  obtain ⟨hStartOld, hStartLater⟩ :=
    h.live_confirmed_window_start_later cfg ext E live hw
      hHq1 hqm hqLater hb hp hconf hs0 hsm
      e hbEpoch hbSlot
  have hsupport : ∀ j ∈ E.honest, ∀ t kt att,
      a ≤ t → t < E.slot_at cfg (T + 1) →
      E.vote j t = some (kt, att) →
        b ∈ (E.store cfg ext j kt).block_roots ∧
        is_ancestor (E.store cfg ext j kt)
          (get_node_for_root att.data.beacon_block_root)
          (get_node_for_root b) = true := by
    have hLive := h.live_one_confirmed_supports_live_votes cfg ext E
      live hw hHq1 hqm hb hp hconf hs0.le hsm
    intro j hj t kt att hat ht hVote
    exact hLive j hj t kt att hat
      (ht.trans_le (E.slot_at_mono cfg hTm)) hVote
  have hOldConf : is_one_confirmed cfg ext old oldSource b = true := by
    simpa only [old, oldSource, E.fcrStep_store] using hconf
  have hGrowth := h.live_historical_boundary_estimate_growth cfg ext E
    hw e hqT hHq1 hHT1 hT hstart hb hp hbSlot hconf
  have hEstimate : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg newSource) a
      (get_current_slot cfg later - 1) =
        estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg oldSource) a
          (get_current_slot cfg old - 1) + added := by
    simpa only [old, later, oldSource, newSource, added,
      E.store_current_slot, hboundary] using hGrowth
  obtain ⟨hOldDiv, hAddedDiv⟩ :=
    h.live_historical_boundary_estimate_divisors cfg ext E
      hw e hqT hHq1 hHT1 hT hboundary hstart hb hp hbSlot hconf
  have hSuffix := h.live_epoch_suffix_quantized_exact cfg ext E
    old e hCurrent hCurrentH hStartH hEndH u
    (hbSlot.trans hBefore) huZ
  have hHonestSpan := h.live_boundary_added_honest_span cfg ext E
    hHT1 hboundary u a (hbSlot.le.trans hBefore.le) huZ hBefore.le
  have hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      ∃ t : Slot, E.SlotWithinHorizon cfg t ∧
        a ≤ t ∧ get_current_slot cfg (E.store cfg ext w (q + 1)) ≤ t ∧
        t < E.slot_at cfg (T + 1) ∧
        t < compute_start_slot_at_epoch cfg (e + 1) ∧
        i ∈ E.committee t ∧ E.slot_start cfg (t + 1) ≤ T + 1 := by
    intro i hi
    obtain ⟨hih, t, htH, hat, hut, htB, htU, hit, hdel⟩ := hHonestSpan.1 i hi
    exact ⟨hih, t, htH, hat, by rw [E.store_current_slot]; exact hut,
      htB, htU, hit, hdel⟩
  have hHonest : 3 * added ≤ 4 * E.weight HS := by
    simpa only [added, hSuffix.1] using hHonestSpan.2
  have hWindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg newSource)
      ((later.blocks (later.blocks b).parent_root).slot + 1)
      (get_current_slot cfg later - 1) ≤
        estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg oldSource)
          ((old.blocks (old.blocks b).parent_root).slot + 1)
          (get_current_slot cfg old - 1) + added := by
    rw [hParentOld, hParentLater, hslotLater]
    exact hEstimate.le
  have hOldDiscount := (hDiscount oldSource).1
  have hNewDiscount := (hDiscount newSource).2
  have hsa : a ≤ ((E.store cfg ext w (q + 1)).blocks b).slot := Nat.le_refl _
  have hOldEndHActual : E.SlotWithinHorizon cfg
      (get_current_slot cfg old - 1) := by
    simpa only [old, E.store_current_slot] using hOldEndH
  have hNewEndHActual : E.SlotWithinHorizon cfg
      (get_current_slot cfg later - 1) := by
    simpa only [later, E.store_current_slot, hboundary] using hEndH
  have hOldDivActual : 100 ∣ estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg oldSource) a
      (get_current_slot cfg old - 1) := by
    simpa only [old, a, oldSource, E.store_current_slot] using hOldDiv
  exact h.live_boundary_reconfirm_of_window cfg ext E
    (w := w) (n := q + 1) (m := T + 1) (e := e) (b := b) (s := a)
    hw hqLater
    hHq1 hHT1 hCurrent hboundary hb hbEpoch hAinH hs0.le
    hsupport oldSource newSource hvalOld hvalNew hOldH hNewH
    htabOld htabNew hOldConf hOldDiscount hNewDiscount a added
    hsa hAinH hOldEndHActual hNewEndHActual
    (by simpa only [E.store_current_slot, hboundary] using
      (Nat.sub_le u 1).trans huZ)
    hStartOld hStartLater hEstimate hOldDivActual hAddedDiv hWindow
    HS hHS hHonest

/-- Historical certificates at the last store of an epoch reconfirm every
strict descendant of the timely checkpoint on the cached chain. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_chain_certificates
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (T : ℕ) (hTm : T + 1 ≤ m)
    (hHT1 : E.WithinHorizon cfg (T + 1))
    (hT : E.slot_at cfg T < compute_start_slot_at_epoch cfg (e + 1))
    (hboundary : E.slot_at cfg (T + 1) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (T + 1))) = true)
    (cp : Root) (hcp : cp ∈ (E.store cfg ext w (T + 1)).block_roots)
    (hcpSlot : ((E.store cfg ext w (T + 1)).blocks cp).slot =
      compute_start_slot_at_epoch cfg e)
    (htip : E.confirmed cfg ext w T ∈
      (E.store cfg ext w T).block_roots)
    (hHistory : ∀ b ∈ (E.store cfg ext w T).block_roots,
      is_ancestor (E.store cfg ext w T)
        (get_node_for_root (E.confirmed cfg ext w T))
        (get_node_for_root b) = true →
      compute_start_slot_at_epoch cfg e <
        ((E.store cfg ext w T).blocks b).slot →
      ∃ q, q < T ∧
        b ∈ (E.store cfg ext w (q + 1)).block_roots ∧
        is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
          (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    ∀ b ∈ get_ancestor_roots (E.store cfg ext w (T + 1))
      (E.confirmed cfg ext w T) cp,
      is_one_confirmed cfg ext (E.store cfg ext w (T + 1))
        (get_previous_balance_source (E.fcrStep cfg ext w T)) b = true := by
  let old := E.store cfg ext w T
  let later := E.store cfg ext w (T + 1)
  let tip := E.confirmed cfg ext w T
  obtain ⟨ast, ablk, hgenEq, hstateSlot, hparent⟩ :=
    h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot := ⟨ast, ablk, hgenEq, hstateSlot⟩
  have hwf : ParentSlotLt later :=
    E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence
      ⟨ast, ablk, hgenEq, hstateSlot, hparent⟩
      h.trajectory.wellFormed.anchor_parent_unscheduled w (T + 1)
  have hwalk : ∀ t ∈ later.block_roots, ∀ r ∈ later.block_roots,
      WalkKnown later (later.blocks t).slot r :=
    E.store_walkKnownK cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence
      ⟨ast, ablk, hgenEq, hstateSlot, hparent⟩ w (T + 1)
  have htipLater : tip ∈ later.block_roots :=
    (E.store_storeLE cfg ext w (Nat.le_succ T)).1 htip
  have hinitialStart : E.slot_at cfg 0 ≤
      compute_start_slot_at_epoch cfg e := by
    rw [h.live_initial_slot_eq_epoch_start cfg ext E]
    exact Nat.mul_le_mul_right cfg.slots_per_epoch he0
  intro b hbList
  have hbLater : b ∈ later.block_roots :=
    get_ancestor_roots_mem hwf (hwalk cp hcp tip htipLater) hbList
  have hancLater : is_ancestor later
      (get_node_for_root tip) (get_node_for_root b) = true :=
    ancestorRoots_member_below_head hwf hwalk htipLater hcp hbList
  obtain ⟨hbOld, hancOld⟩ :=
    h.live_ancestor_reflect_earlier cfg ext E (Nat.le_succ T)
      htip hbLater hancLater
  have hbSlotLater : compute_start_slot_at_epoch cfg e <
      (later.blocks b).slot := by
    rw [← hcpSlot]
    exact live_ancestor_roots_member_slot_gt_terminal
      hwf (hwalk cp hcp tip htipLater) hcp hbList
  have hbAgree : old.blocks b = later.blocks b :=
    h.trajectory.wellFormed.blocks_agree
      (E.blockProvenance cfg ext w T)
      (E.blockProvenance cfg ext w (T + 1)) hbOld hbLater
  have hbSlotOld : compute_start_slot_at_epoch cfg e <
      (old.blocks b).slot := by rw [hbAgree]; exact hbSlotLater
  obtain ⟨q, hqT, hbQ, hconf⟩ := hHistory b hbOld hancOld hbSlotOld
  have hHq1 : E.WithinHorizon cfg (q + 1) :=
    E.withinHorizon_mono cfg
      ((Nat.succ_le_of_lt hqT).trans (Nat.le_succ T)) hHT1
  have hbQAgree : (E.store cfg ext w (q + 1)).blocks b = old.blocks b :=
    h.trajectory.wellFormed.blocks_agree
      (E.blockProvenance cfg ext w (q + 1))
      (E.blockProvenance cfg ext w T) hbQ hbOld
  have hbSlotQ : compute_start_slot_at_epoch cfg e <
      ((E.store cfg ext w (q + 1)).blocks b).slot := by
    rw [hbQAgree]
    exact hbSlotOld
  have hs0 : E.slot_at cfg 0 <
      ((E.store cfg ext w (q + 1)).blocks b).slot :=
    hinitialStart.trans_lt hbSlotQ
  have hpQ := h.live_parent_known_after_initial cfg ext E
    w (q + 1) hbQ hs0
  have hbBeforeT : (old.blocks b).slot ≤ E.slot_at cfg T := by
    rw [← E.store_current_slot cfg ext w T]
    exact E.store_blocks_slot_le_current cfg ext
      h.trajectory.whole_seconds hgen w T b hbOld
  have hbEpochQ : get_block_epoch cfg (E.store cfg ext w (q + 1)) b = e := by
    have hUpper : ((E.store cfg ext w (q + 1)).blocks b).slot <
        compute_start_slot_at_epoch cfg (e + 1) := by
      rw [hbQAgree]
      exact hbBeforeT.trans_lt hT
    have hlo : e ≤ get_block_epoch cfg (E.store cfg ext w (q + 1)) b := by
      apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
      simpa only [get_block_epoch, compute_epoch_at_slot,
        compute_start_slot_at_epoch] using hbSlotQ.le
    have hhi : get_block_epoch cfg (E.store cfg ext w (q + 1)) b < e + 1 := by
      apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
      simpa only [get_block_epoch, compute_epoch_at_slot,
        compute_start_slot_at_epoch] using hUpper
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
  exact h.live_historical_block_reconfirmed cfg ext E live hw e
    hqT hTm hHq1 hHT1 hT hboundary hstart
    hbQ hpQ hbEpochQ hbSlotQ hs0 hconf

/-- The historical boundary certificates discharge the executable
confirmed-chain safety check when the cached root is above the checkpoint. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_chain_safe
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (T : ℕ) (hTm : T + 1 ≤ m)
    (hHT1 : E.WithinHorizon cfg (T + 1))
    (hT : E.slot_at cfg T < compute_start_slot_at_epoch cfg (e + 1))
    (hboundary : E.slot_at cfg (T + 1) =
      compute_start_slot_at_epoch cfg (e + 1))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (T + 1))) = true)
    (cp : Checkpoint Root)
    (hcpEpoch : cp.epoch = e)
    (hobs : (E.fcrStep cfg ext w T).current_epoch_observed_justified_checkpoint = cp)
    (hcp : cp.root ∈ (E.store cfg ext w (T + 1)).block_roots)
    (hcpSlot : ((E.store cfg ext w (T + 1)).blocks cp.root).slot =
      compute_start_slot_at_epoch cfg e)
    (htip : E.confirmed cfg ext w T ∈
      (E.store cfg ext w T).block_roots)
    (hcpAnc : is_ancestor (E.store cfg ext w (T + 1))
      (get_node_for_root (E.confirmed cfg ext w T))
      (get_node_for_root cp.root) = true)
    (hHistory : ∀ b ∈ (E.store cfg ext w T).block_roots,
      is_ancestor (E.store cfg ext w T)
        (get_node_for_root (E.confirmed cfg ext w T))
        (get_node_for_root b) = true →
      compute_start_slot_at_epoch cfg e <
        ((E.store cfg ext w T).blocks b).slot →
      ∃ q, q < T ∧
        b ∈ (E.store cfg ext w (q + 1)).block_roots ∧
        is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
          (get_current_balance_source (E.fcrStep cfg ext w q)) b = true) :
    is_confirmed_chain_safe cfg ext (E.fcrStep cfg ext w T)
      (E.confirmed cfg ext w T) = true := by
  let later := E.store cfg ext w (T + 1)
  let tip := E.confirmed cfg ext w T
  have hcpForTip : cp = get_checkpoint_for_block cfg later tip cp.epoch := by
    have hroot : (get_ancestor later (get_node_for_root tip)
        (later.blocks cp.root).slot).root = cp.root := by
      simpa only [get_node_for_root, is_ancestor_pending,
        decide_eq_true_eq] using hcpAnc
    apply checkpoint_eq_of_epoch_root_eq (a := cp)
      (b := get_checkpoint_for_block cfg later tip cp.epoch) rfl
    rw [hcpSlot] at hroot
    simpa only [get_checkpoint_for_block, get_checkpoint_block,
      hcpEpoch, get_node_for_root] using hroot.symm
  have hcurrent : get_current_store_epoch cfg later = e + 1 := by
    rw [get_current_store_epoch, E.store_current_slot, hboundary]
    simp [compute_epoch_at_slot, compute_start_slot_at_epoch,
      cfg.slots_per_epoch_pos]
  have hsafe := is_confirmed_chain_safe_of_checkpoint_certificates
    cfg ext (E.fcrStep cfg ext w T) tip
    (by simpa only [E.fcrStep_store, E.fcrStep_confirmed_root, hobs]
      using hcpForTip)
    (by rw [hobs, E.fcrStep_store, hcpEpoch, hcurrent])
    (by
      intro b hb
      have hcert := h.live_boundary_chain_certificates cfg ext E live
        hw e he0 T hTm hHT1 hT hboundary hstart cp.root hcp hcpSlot
        htip hHistory b
      have hb' : b ∈ get_ancestor_roots later tip cp.root := by
        simpa only [E.fcrStep_store, E.fcrStep_confirmed_root, hobs]
          using hb
      simpa only [E.fcrStep_store] using hcert hb')
  exact hsafe

/-- The timely checkpoint is the actual observed cache at the boundary, is
known, occupies the preceding epoch start, and lies on the boundary head. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_checkpoint_geometry
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hlastAfterZero : E.slot_at cfg 0 <
      compute_start_slot_at_epoch cfg (e + 1) - 1)
    (hHm : E.WithinHorizon cfg m)
    {w : ValidatorIndex} (hw : w ∈ E.honest) :
    let B := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
    let q := B - 1
    ∃ c : Checkpoint Root, c.epoch = e ∧
      (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint = c ∧
      c.root ∈ (E.store cfg ext w B).block_roots ∧
      get_block_slot (E.store cfg ext w B) c.root =
        compute_start_slot_at_epoch cfg e ∧
      is_ancestor (E.store cfg ext w B)
        (get_head cfg (E.store cfg ext w B)) (get_node_for_root c.root) = true := by
  let S := compute_start_slot_at_epoch cfg (e + 1)
  let B := E.slot_start cfg S
  let q := B - 1
  dsimp only
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have hfrom : E.slot_at cfg 0 < S :=
    lt_of_lt_of_le hlastAfterZero (Nat.sub_le _ _)
  have hBpos : 0 < B :=
    (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).1 hfrom
  have hq : q + 1 = B := Nat.sub_add_cancel (Nat.succ_le_of_lt hBpos)
  have hBslot : E.slot_at cfg B = S :=
    E.slot_at_slot_start cfg h.trajectory.whole_seconds hfrom.le hgenTime
  have hBleM : B ≤ m := by
    apply Nat.le_of_not_gt
    intro htooLate
    have hslotLt : E.slot_at cfg m < S :=
      (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).2 htooLate
    exact (Nat.not_lt_of_ge heDone) hslotLt
  have hHB : E.WithinHorizon cfg B := E.withinHorizon_mono cfg hBleM hHm
  obtain ⟨c, hcEpoch, ⟨r, b, hblock, hbe, hroot⟩, hstores⟩ :=
    live.ffg_timely_justification e he0 heDone
  have hgate := h.live_ffg_actual_boundary_inputs cfg ext E live
    he0 heDone hlastAfterZero hw
  dsimp only at hgate
  have hhead : (E.store cfg ext w B).unrealized_justifications
      (get_head cfg (E.store cfg ext w B)).root = c := by
    exact (hstores w hw).2.2.1
  have hobs : (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint = c := by
    have hgate' := hgate.1
    rw [hq] at hgate'
    exact hgate'.trans hhead
  have hknown : c.root ∈ (E.store cfg ext w B).block_roots := by
    have hk := h.live_observed_root_known cfg ext E w q
    rw [hq, hobs] at hk
    exact hk
  have hrootEpoch : get_block_epoch cfg (E.store cfg ext w B) c.root = e := by
    rw [hroot]
    exact (h.live_known_block_epoch cfg ext E hblock
      (by rwa [hroot] at hknown)).trans hbe
  have hcheckpoint : get_checkpoint_for_block cfg (E.store cfg ext w B)
      (get_head cfg (E.store cfg ext w B)).root e = ⟨e, c.root⟩ := by
    have hcp : get_checkpoint_for_block cfg (E.store cfg ext w B)
        (get_head cfg (E.store cfg ext w B)).root e = c := by
      simpa only [B, S] using (hstores w hw).2.1
    have hcStruct : c = ⟨e, c.root⟩ := by
      cases c with
      | mk ce cr => cases hcEpoch; rfl
    exact hcp.trans hcStruct
  have hheadKnown : (get_head cfg (E.store cfg ext w B)).root ∈
      (E.store cfg ext w B).block_roots :=
    E.headRootKnown_of_acceptedGlobalTrajectory cfg ext
      h.semantics h.trajectory h.anchor_eq h.anchor_boundary hw B hHB
  have hwalk : WalkKnown (E.store cfg ext w B)
      (compute_start_slot_at_epoch cfg e)
      (get_head cfg (E.store cfg ext w B)).root :=
    E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext
      h.trajectory h.anchor_eq h.anchor_boundary w B
      (by rw [h.live_anchor_checkpoint_epoch cfg ext E]; exact he0)
      hheadKnown
  have hwf : ParentSlotLt (E.store cfg ext w B) :=
    E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      h.trajectory.wellFormed.anchor_parent_unscheduled w B
  have hcpSlot : get_block_slot (E.store cfg ext w B) c.root =
      compute_start_slot_at_epoch cfg e :=
    live_epoch_checkpoint_root_slot cfg _ e _ hwf hwalk hcheckpoint hrootEpoch
  have hcpHead : is_ancestor (E.store cfg ext w B)
      (get_head cfg (E.store cfg ext w B)) (get_node_for_root c.root) = true :=
    live_epoch_checkpoint_root_on_head cfg _ e _ hwf hwalk hcheckpoint hrootEpoch
  exact ⟨c, hcEpoch, hobs, hknown, hcpSlot, hcpHead⟩

/-- The initial and later epoch history lemmas expose one uniform witness at
the last store before any completed boundary. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_history
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (e : Epoch)
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    {m : ℕ} (hHm : E.WithinHorizon cfg m)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m) :
    let T := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1)) - 1
    ∀ b ∈ (E.store cfg ext w T).block_roots,
      is_ancestor (E.store cfg ext w T)
        (get_node_for_root (E.confirmed cfg ext w T))
        (get_node_for_root b) = true →
      compute_start_slot_at_epoch cfg e <
        ((E.store cfg ext w T).blocks b).slot →
      ∃ q, q < T ∧
        b ∈ (E.store cfg ext w (q + 1)).block_roots ∧
        is_one_confirmed cfg ext (E.fcrStep cfg ext w q).store
          (get_current_balance_source (E.fcrStep cfg ext w q)) b = true := by
  dsimp only
  rcases Nat.eq_or_lt_of_le he0 with heq | hlt
  · subst e
    intro b hb hbAnc hbSlot
    obtain ⟨q, hqT, _, hbQ, hconf⟩ :=
      h.live_initial_historical_chain_before_boundary cfg ext E
        hw hHm heDone b hb hbAnc hbSlot
    exact ⟨q, hqT, hbQ, hconf⟩
  · have hstartAfterZero : E.slot_at cfg 0 <
        compute_start_slot_at_epoch cfg e := by
      rw [h.live_initial_slot_eq_epoch_start cfg ext E]
      simpa only [compute_start_slot_at_epoch] using
        (Nat.mul_lt_mul_of_pos_right hlt cfg.slots_per_epoch_pos)
    have hhist := h.live_historical_chain_before_boundary cfg ext E
      hw e he0 hstartAfterZero hHm heDone
    intro b hb hbAnc hbSlot
    obtain ⟨q, _, hqT, _, hbQ, hconf⟩ := hhist b hb hbAnc hbSlot
    exact ⟨q, hqT, hbQ, hconf⟩

/-- At an actual timely boundary, a cached root strictly above the observed
checkpoint passes the finalized-phase confirmed-chain safety guard. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_actual_boundary_chain_safe
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    (e : Epoch)
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hlastAfterZero : E.slot_at cfg 0 <
      compute_start_slot_at_epoch cfg (e + 1) - 1)
    (hHm : E.WithinHorizon cfg m)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (hAhead : compute_start_slot_at_epoch cfg e <
      get_block_slot (E.store cfg ext w
        (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))))
        (E.confirmed cfg ext w
          (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1)) - 1))) :
    let B := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
    let T := B - 1
    is_confirmed_chain_safe cfg ext (E.fcrStep cfg ext w T)
      (E.confirmed cfg ext w T) = true := by
  let S := compute_start_slot_at_epoch cfg (e + 1)
  let B := E.slot_start cfg S
  let T := B - 1
  dsimp only
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have hfrom : E.slot_at cfg 0 < S :=
    lt_of_lt_of_le hlastAfterZero (Nat.sub_le _ _)
  have hBpos : 0 < B :=
    (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).1 hfrom
  have hTsucc : T + 1 = B :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hBpos)
  have hBslot : E.slot_at cfg B = S :=
    E.slot_at_slot_start cfg h.trajectory.whole_seconds hfrom.le hgenTime
  have hTslot : E.slot_at cfg T < S := by
    exact (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).2
      (by simpa only [T, B] using (Nat.sub_lt hBpos (by omega)))
  have hBm : B ≤ m := by
    apply Nat.le_of_not_gt
    intro htooLate
    have hslotLt : E.slot_at cfg m < S :=
      (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).2 htooLate
    exact (Nat.not_lt_of_ge heDone) hslotLt
  have hHB : E.WithinHorizon cfg B := E.withinHorizon_mono cfg hBm hHm
  have hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (T + 1))) = true := by
    rw [hTsucc]
    exact h.live_boundary_is_start cfg ext E w (e + 1) hfrom.le
  obtain ⟨cp, hcpEpoch, hobs, hcpKnown, hcpSlot, hcpHead⟩ :=
    h.live_boundary_checkpoint_geometry cfg ext E live
      he0 heDone hlastAfterZero hHm hw
  have htip : E.confirmed cfg ext w T ∈
      (E.store cfg ext w T).block_roots :=
    E.confirmed_known_of_acceptedGlobalTrajectory cfg ext
      h.semantics h.trajectory h.anchor_eq h.anchor_boundary hw T
      (E.withinHorizon_mono cfg (Nat.sub_le B 1) hHB)
  have hheadKnown : (get_head cfg (E.store cfg ext w B)).root ∈
      (E.store cfg ext w B).block_roots :=
    E.headRootKnown_of_acceptedGlobalTrajectory cfg ext
      h.semantics h.trajectory h.anchor_eq h.anchor_boundary hw B hHB
  have hwf : ParentSlotLt (E.store cfg ext w B) :=
    E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      h.trajectory.wellFormed.anchor_parent_unscheduled w B
  have hwalkK := E.store_walkKnownK cfg ext h.trajectory.wellFormed
    h.trajectory.externals_coherence h.trajectory.genesis_structure w B
  have hheadTip : is_ancestor (E.store cfg ext w B)
      (get_head cfg (E.store cfg ext w B))
      (get_node_for_root (E.confirmed cfg ext w T)) = true :=
    h.confirmed_head_nextSlot cfg ext E hw hw
      (by rw [← hTsucc]; exact Nat.le_succ T)
      (by rw [hBslot]; exact Nat.succ_le_of_lt hTslot)
      hHB
  have hcpHeadPending : is_ancestor (E.store cfg ext w B)
      (get_node_for_root (get_head cfg (E.store cfg ext w B)).root)
      (get_node_for_root cp.root) = true := by
    rw [← is_ancestor_node_root]
    exact hcpHead
  have hheadTipPending : is_ancestor (E.store cfg ext w B)
      (get_node_for_root (get_head cfg (E.store cfg ext w B)).root)
      (get_node_for_root (E.confirmed cfg ext w T)) = true := by
    rw [← is_ancestor_node_root]
    exact hheadTip
  have hcpAnc : is_ancestor (E.store cfg ext w B)
      (get_node_for_root (E.confirmed cfg ext w T))
      (get_node_for_root cp.root) = true := by
    have hcpLe : ((E.store cfg ext w B).blocks cp.root).slot ≤
        ((E.store cfg ext w B).blocks (E.confirmed cfg ext w T)).slot := by
      calc
        ((E.store cfg ext w B).blocks cp.root).slot =
            compute_start_slot_at_epoch cfg e := hcpSlot
        _ ≤ ((E.store cfg ext w B).blocks (E.confirmed cfg ext w T)).slot :=
          hAhead.le
    exact ancestor_comparable_of_common hwf hcpLe
      (hwalkK cp.root hcpKnown _ hheadKnown)
      hcpHeadPending hheadTipPending
  have hHistory := h.live_boundary_history cfg ext E hw e he0 hHm heDone
  have hresult := h.live_boundary_chain_safe cfg ext E live hw e he0 T
    (by rw [hTsucc]; exact hBm) (by rw [hTsucc]; exact hHB)
    hTslot (by rw [hTsucc]; exact hBslot) hstart cp hcpEpoch
    (by simpa only [T, hTsucc] using hobs)
    (by simpa only [T, hTsucc] using hcpKnown)
    (by simpa only [T, hTsucc] using hcpSlot)
    htip (by simpa only [T, hTsucc] using hcpAnc)
    (by simpa only [T, B, S] using hHistory)
  exact hresult

end Execution

end FastConfirmation.Spec

end
