module
public import FastConfirmation.Spec.Proof.MonotonicityLiveConfirmation
public import FastConfirmation.Spec.Proof.MonotonicityTrace
public import FastConfirmation.Spec.Proof.AcceptedSelectedStrictEdgeFilterSupply

@[expose] public section

/-!
# An observed epoch checkpoint catches a stale cache

At an epoch-start call, an observed checkpoint at or beyond the cached root
prevents a slot rollback even if the finalized-revert phase runs. This is an
executable calculation; the live timing field supplies the checkpoint and
head agreement at the appropriate calls.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The epoch-start chain check reduces to one-confirmation of each strict
descendant of the observed checkpoint. This is the executable interface for
the historical reconfirmation invariant. -/
theorem is_confirmed_chain_safe_of_checkpoint_certificates
    (query : FastConfirmationStore Root) (c : Root)
    (hcheckpoint : query.current_epoch_observed_justified_checkpoint =
      get_checkpoint_for_block cfg query.store c
        query.current_epoch_observed_justified_checkpoint.epoch)
    (hepoch : query.current_epoch_observed_justified_checkpoint.epoch + 1 ≥
      get_current_store_epoch cfg query.store)
    (hcert : ∀ b ∈ get_ancestor_roots query.store c
        query.current_epoch_observed_justified_checkpoint.root,
      is_one_confirmed cfg ext query.store
        (get_previous_balance_source query) b = true) :
    is_confirmed_chain_safe cfg ext query c = true := by
  have hall : (get_ancestor_roots query.store c
      query.current_epoch_observed_justified_checkpoint.root).all
      (fun b => is_one_confirmed cfg ext query.store
        (get_previous_balance_source query) b) = true := by
    exact List.all_eq_true.mpr hcert
  simp only [is_confirmed_chain_safe]
  rw [if_neg (by intro hne; exact hne hcheckpoint)]
  rw [if_pos hepoch]
  exact hall

/-- A cached root equal to the observed checkpoint has an empty strict
descendant chain, so the epoch-start chain check is automatic. -/
theorem is_confirmed_chain_safe_at_observed_checkpoint
    (query : FastConfirmationStore Root)
    (hcheckpoint : query.current_epoch_observed_justified_checkpoint =
      get_checkpoint_for_block cfg query.store
        query.current_epoch_observed_justified_checkpoint.root
        query.current_epoch_observed_justified_checkpoint.epoch)
    (hepoch : query.current_epoch_observed_justified_checkpoint.epoch + 1 ≥
      get_current_store_epoch cfg query.store) :
    is_confirmed_chain_safe cfg ext query
      query.current_epoch_observed_justified_checkpoint.root = true := by
  apply is_confirmed_chain_safe_of_checkpoint_certificates cfg ext query _
    hcheckpoint hepoch
  intro b hb
  have hnil := get_ancestor_roots_stop (store := query.store)
    (block_root := query.current_epoch_observed_justified_checkpoint.root)
    (terminal_root := query.current_epoch_observed_justified_checkpoint.root) (le_refl _)
  rw [hnil] at hb
  cases hb

/-- An epoch checkpoint whose root is an actual block of that epoch is the
start-slot block on the head's ancestor walk. The pending target accepts
either Gloas payload status of the head walk. -/
theorem live_epoch_checkpoint_root_on_head
    (store : Store Root) (e : Epoch) (r : Root)
    (hwf : ParentSlotLt store)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e)
      (get_head cfg store).root)
    (hcheckpoint : get_checkpoint_for_block cfg store
      (get_head cfg store).root e = ⟨e, r⟩)
    (hepoch : get_block_epoch cfg store r = e) :
    is_ancestor store (get_head cfg store) (get_node_for_root r) = true := by
  have hroot : (get_ancestor store
      (get_node_for_root (get_head cfg store).root)
      (compute_start_slot_at_epoch cfg e)).root = r := by
    exact congrArg Checkpoint.root hcheckpoint
  have hslotLe : (store.blocks r).slot ≤ compute_start_slot_at_epoch cfg e := by
    rw [← hroot]
    exact (get_ancestor_spec hwf hwalk).2
  have hstartLe : compute_start_slot_at_epoch cfg e ≤ (store.blocks r).slot := by
    simp only [get_block_epoch, compute_epoch_at_slot] at hepoch
    simp only [compute_start_slot_at_epoch]
    rw [← hepoch]
    exact Nat.div_mul_le_self (store.blocks r).slot cfg.slots_per_epoch
  have hslot : (store.blocks r).slot = compute_start_slot_at_epoch cfg e :=
    Nat.le_antisymm hslotLe hstartLe
  simp only [get_node_for_root, is_ancestor_pending, hslot]
  rw [get_ancestor_root_eq_status store
    (compute_start_slot_at_epoch cfg e) (get_head cfg store).root
    (get_head cfg store).payload_status .pending]
  exact decide_eq_true hroot

/-- The block named by an epoch checkpoint on a known head walk is exactly
the epoch's start-slot block when it belongs to that epoch. -/
theorem live_epoch_checkpoint_root_slot
    (store : Store Root) (e : Epoch) (r : Root)
    (hwf : ParentSlotLt store)
    (hwalk : WalkKnown store (compute_start_slot_at_epoch cfg e)
      (get_head cfg store).root)
    (hcheckpoint : get_checkpoint_for_block cfg store
      (get_head cfg store).root e = ⟨e, r⟩)
    (hepoch : get_block_epoch cfg store r = e) :
    get_block_slot store r = compute_start_slot_at_epoch cfg e := by
  have hroot : (get_ancestor store
      (get_node_for_root (get_head cfg store).root)
      (compute_start_slot_at_epoch cfg e)).root = r :=
    congrArg Checkpoint.root hcheckpoint
  have hslotLe : (store.blocks r).slot ≤ compute_start_slot_at_epoch cfg e := by
    rw [← hroot]
    exact (get_ancestor_spec hwf hwalk).2
  have hstartLe : compute_start_slot_at_epoch cfg e ≤ (store.blocks r).slot := by
    simp only [get_block_epoch, compute_epoch_at_slot] at hepoch
    simp only [compute_start_slot_at_epoch]
    rw [← hepoch]
    exact Nat.div_mul_le_self (store.blocks r).slot cfg.slots_per_epoch
  exact Nat.le_antisymm hslotLe hstartLe

/-- The slot computed as an epoch boundary satisfies the FCR start test. -/
theorem live_epoch_start_is_start (e : Epoch) :
    is_start_slot_at_epoch cfg (compute_start_slot_at_epoch cfg e) = true := by
  simp [is_start_slot_at_epoch, compute_slots_since_epoch_start,
    compute_start_slot_at_epoch, compute_epoch_at_slot,
    cfg.slots_per_epoch_pos]

/-- The slot immediately after an epoch start is not another start when an
epoch has more than one slot. -/
theorem live_epoch_start_succ_not_start
    (hgt : 1 < cfg.slots_per_epoch) (e : Epoch) :
    is_start_slot_at_epoch cfg
      (compute_start_slot_at_epoch cfg e + 1) = false := by
  have hdiv : (e * cfg.slots_per_epoch + 1) / cfg.slots_per_epoch = e := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · simp only [Nat.add_mul, one_mul]
      omega
  simp [is_start_slot_at_epoch, compute_slots_since_epoch_start,
    compute_start_slot_at_epoch, compute_epoch_at_slot, hdiv]

omit [LinearOrder Root] [Inhabited Root] in
/-- A strict block-epoch order implies the same block-slot order. -/
theorem live_block_slot_lt_of_epoch_lt
    (store : Store Root) (a b : Root)
    (h : get_block_epoch cfg store a < get_block_epoch cfg store b) :
    get_block_slot store a < get_block_slot store b := by
  by_contra hnot
  have hslots : get_block_slot store b ≤ get_block_slot store a :=
    Nat.le_of_not_gt hnot
  have hepoch : get_block_epoch cfg store b ≤ get_block_epoch cfg store a := by
    simpa only [get_block_epoch, compute_epoch_at_slot, get_block_slot] using
      Nat.div_le_div_right hslots
  exact (Nat.not_lt_of_ge hepoch) h

/-- If the observed epoch checkpoint reaches the cached root, either the
finalized phase already has enough slot progress or the observed restart
restores it. -/
theorem getLatestAfterObserved_slot_ge_cached_of_observed_catches_up
    (query : FastConfirmationStore Root)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = true)
    (hepoch : get_block_epoch cfg query.store
      query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store)
    (hhead : query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (get_head cfg query.store).root)
    (hcatch : get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store
        query.current_epoch_observed_justified_checkpoint.root) :
    get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store
        (getLatestAfterObserved cfg ext query) := by
  by_cases hphase : get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store (getLatestAfterFinalized cfg ext query)
  · exact hphase.trans
      (getLatestAfterObserved_slot_ge_afterFinalized cfg ext query)
  · have hlt : get_block_slot query.store
        (getLatestAfterFinalized cfg ext query) <
        get_block_slot query.store
          query.current_epoch_observed_justified_checkpoint.root :=
      (Nat.lt_of_not_ge hphase).trans_le hcatch
    have hguard : getLatestObservedRestartGuard cfg query
        (getLatestAfterFinalized cfg ext query) = true := by
      simp [getLatestObservedRestartGuard, hstart, ← hhead, hepoch, hlt]
    simp [getLatestAfterObserved, hguard, hcatch]

/-- At a timely epoch boundary, a finalized revert is repaired exactly to
the observed checkpoint, including the first boundary where finalized and
observed may coincide. -/
theorem getLatestAfterObserved_eq_checkpoint_of_revert
    (query : FastConfirmationStore Root)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = true)
    (hepoch : get_block_epoch cfg query.store
      query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store)
    (hhead : query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (get_head cfg query.store).root)
    (hrevert : getLatestFinalizedRevertGuard cfg ext query)
    (hfinalized : get_block_slot query.store
        query.store.finalized_checkpoint.root <
        get_block_slot query.store
          query.current_epoch_observed_justified_checkpoint.root ∨
      query.store.finalized_checkpoint.root =
        query.current_epoch_observed_justified_checkpoint.root) :
    getLatestAfterObserved cfg ext query =
      query.current_epoch_observed_justified_checkpoint.root := by
  classical
  have hfirst : getLatestAfterFinalized cfg ext query =
      query.store.finalized_checkpoint.root := by
    simp only [getLatestAfterFinalized]
    split_ifs with hg
    · rfl
    · exact False.elim (hg (by simpa only [getLatestFinalizedRevertGuard] using hrevert))
  rcases hfinalized with hlt | heq
  · have hguard : getLatestObservedRestartGuard cfg query
        (getLatestAfterFinalized cfg ext query) = true := by
      simp only [getLatestObservedRestartGuard, hstart, Bool.true_and,
        hfirst]
      rw [← hhead]
      simp [hepoch, hlt]
    simp [getLatestAfterObserved, hguard]
  · simp [getLatestAfterObserved, hfirst, heq]

/-- The descendant selector preserves the catch-up result on a known walk. -/
theorem getLatestTraceResult_slot_ge_cached_of_observed_catches_up
    (query : FastConfirmationStore Root)
    (hwf : ∀ r ∈ query.store.block_roots,
      (query.store.blocks r).parent_root ∈ query.store.block_roots →
        (query.store.blocks (query.store.blocks r).parent_root).slot <
          (query.store.blocks r).slot)
    (hwalk : ∀ t ∈ query.store.block_roots, ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r)
    (hheadKnown : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinputKnown : getLatestAfterObserved cfg ext query ∈ query.store.block_roots)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = true)
    (hepoch : get_block_epoch cfg query.store
      query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store)
    (hhead : query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (get_head cfg query.store).root)
    (hcatch : get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store
        query.current_epoch_observed_justified_checkpoint.root) :
    get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store (getLatestTraceResult cfg ext query) := by
  exact (getLatestAfterObserved_slot_ge_cached_of_observed_catches_up
    cfg ext query hstart hepoch hhead hcatch).trans
    (getLatestTraceResult_slot_ge_afterObserved cfg ext query
      hwf hwalk hheadKnown hinputKnown)

/-- The only remaining local source of rollback is a finalized revert while
the cached block is ahead of the timely observed checkpoint. -/
theorem getLatestTraceResult_slot_ge_cached_of_catch_or_no_revert
    (query : FastConfirmationStore Root)
    (hwf : ∀ r ∈ query.store.block_roots,
      (query.store.blocks r).parent_root ∈ query.store.block_roots →
        (query.store.blocks (query.store.blocks r).parent_root).slot <
          (query.store.blocks r).slot)
    (hwalk : ∀ t ∈ query.store.block_roots, ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r)
    (hheadKnown : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinputKnown : getLatestAfterObserved cfg ext query ∈ query.store.block_roots)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = true)
    (hepoch : get_block_epoch cfg query.store
      query.current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg query.store)
    (hhead : query.current_epoch_observed_justified_checkpoint =
      query.store.unrealized_justifications
        (get_head cfg query.store).root)
    (hchoice :
      get_block_slot query.store query.confirmed_root ≤
        get_block_slot query.store
          query.current_epoch_observed_justified_checkpoint.root ∨
      ¬ getLatestFinalizedRevertGuard cfg ext query) :
    get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store (getLatestTraceResult cfg ext query) := by
  rcases hchoice with hcatch | hnoRevert
  · exact getLatestTraceResult_slot_ge_cached_of_observed_catches_up
      cfg ext query hwf hwalk hheadKnown hinputKnown
      hstart hepoch hhead hcatch
  · exact getLatestTraceResult_slot_ge_confirmed_of_no_finalized_revert
      cfg ext query hwf hwalk hheadKnown hinputKnown hnoRevert

namespace Execution

variable (E : Execution Root)

/-- At the first execution second of an epoch boundary, the actual FCR
store satisfies the start-slot test. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_is_start
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (v : ValidatorIndex) (e : Epoch)
    (hfrom : E.slot_at cfg 0 ≤ compute_start_slot_at_epoch cfg e) :
    is_start_slot_at_epoch cfg
      (get_current_slot cfg
        (E.store cfg ext v
          (E.slot_start cfg (compute_start_slot_at_epoch cfg e)))) = true := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  rw [E.store_current_slot,
    E.slot_at_slot_start cfg h.trajectory.whole_seconds hfrom hgenTime]
  exact live_epoch_start_is_start cfg e

/-- A slot strictly after the execution's initial slot has a genuine first
second and a preceding second at which the FCR call runs. The second before
the following slot begins remains in this slot. -/
theorem adjacent_slot_start_call_geometry
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (v : ValidatorIndex) {s : Slot}
    (hs0 : E.slot_at cfg 0 < s) :
    let L := E.slot_start cfg s
    let B := E.slot_start cfg (s + 1)
    (L - 1) + 1 = L ∧
      (B - 1) + 1 = B ∧
      L ≤ B - 1 ∧
      E.slot_at cfg L = s ∧
      E.slot_at cfg (B - 1) = s ∧
      E.IsFCRCallAt cfg ext v (L - 1) := by
  let L := E.slot_start cfg s
  let B := E.slot_start cfg (s + 1)
  have hLpos : 0 < L :=
    (E.slot_at_lt_iff cfg hdiv hgenTime).1 hs0
  have hLslot : E.slot_at cfg L = s :=
    E.slot_at_slot_start cfg hdiv hs0.le hgenTime
  have hLB : L < B :=
    (E.slot_at_lt_iff cfg hdiv hgenTime).1 (by
      rw [hLslot]
      exact Nat.lt_succ_self s)
  have hBpos : 0 < B := (Nat.zero_le L).trans_lt hLB
  have hLq : L ≤ B - 1 := by omega
  have hQlt : E.slot_at cfg (B - 1) < s + 1 :=
    (E.slot_at_lt_iff cfg hdiv hgenTime).2 (by omega)
  have hQge : s ≤ E.slot_at cfg (B - 1) := by
    rw [← hLslot]
    exact E.slot_at_mono cfg hLq
  have hQslot : E.slot_at cfg (B - 1) = s :=
    Nat.le_antisymm (Nat.lt_succ_iff.mp hQlt) hQge
  have hbefore : E.slot_at cfg (L - 1) < s :=
    (E.slot_at_lt_iff cfg hdiv hgenTime).2 (by omega)
  have hcall : E.IsFCRCallAt cfg ext v (L - 1) := by
    change get_current_slot cfg (E.store cfg ext v ((L - 1) + 1)) >
      get_current_slot cfg (E.store cfg ext v (L - 1))
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLpos),
      E.store_current_slot, E.store_current_slot, hLslot]
    exact hbefore
  exact ⟨Nat.sub_add_cancel (Nat.succ_le_of_lt hLpos),
    Nat.sub_add_cancel (Nat.succ_le_of_lt hBpos),
    hLq, hLslot, hQslot, hcall⟩

/-- Every first second of a slot strictly after the execution start runs
the FCR update. -/
theorem slot_start_is_fcr_call
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (v : ValidatorIndex) {s : Slot}
    (hs0 : E.slot_at cfg 0 < s) :
    E.IsFCRCallAt cfg ext v (E.slot_start cfg s - 1) := by
  let B := E.slot_start cfg s
  have hBpos : 0 < B :=
    (E.slot_at_lt_iff cfg hdiv hgenTime).1 hs0
  have hBslot : E.slot_at cfg B = s :=
    E.slot_at_slot_start cfg hdiv hs0.le hgenTime
  have hbefore : E.slot_at cfg (B - 1) < s :=
    (E.slot_at_lt_iff cfg hdiv hgenTime).2 (by omega)
  change get_current_slot cfg (E.store cfg ext v ((B - 1) + 1)) >
    get_current_slot cfg (E.store cfg ext v (B - 1))
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hBpos),
    E.store_current_slot, E.store_current_slot, hBslot]
  exact hbefore

/-- The two epoch-boundary input caches remain fixed between two seconds in
the same slot. The read-only store snapshot may still change. -/
theorem fcr_boundary_inputs_constant_in_slot
    (v : ValidatorIndex) {a b : ℕ} (hab : a ≤ b)
    (hslot : E.slot_at cfg a = E.slot_at cfg b) :
    (E.fcr cfg ext v a).previous_epoch_greatest_unrealized_checkpoint =
        (E.fcr cfg ext v b).previous_epoch_greatest_unrealized_checkpoint ∧
      (E.fcr cfg ext v a).current_slot_head =
        (E.fcr cfg ext v b).current_slot_head := by
  induction b with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      exact ⟨rfl, rfl⟩
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact ⟨rfl, rfl⟩
      have hab' : a ≤ b := by omega
      have hslotB : E.slot_at cfg b = E.slot_at cfg (b + 1) := by
        apply Nat.le_antisymm (E.slot_at_mono cfg (Nat.le_succ b))
        calc
          E.slot_at cfg (b + 1) = E.slot_at cfg a := hslot.symm
          _ ≤ E.slot_at cfg b := E.slot_at_mono cfg hab'
      have hslotA : E.slot_at cfg a = E.slot_at cfg b :=
        hslot.trans hslotB.symm
      obtain ⟨hgreatest, hhead⟩ := ih hab' hslotA
      have hno : ¬ get_current_slot cfg (E.store cfg ext v (b + 1)) >
          get_current_slot cfg (E.store cfg ext v b) := by
        rw [E.store_current_slot cfg ext v (b + 1),
          E.store_current_slot cfg ext v b, hslotB]
        simp
      simp only [Execution.fcr, if_neg hno]
      exact ⟨hgreatest, hhead⟩

/-- On a nondegenerate epoch boundary, the observed checkpoint is the
previously cached greatest unrealized checkpoint. -/
theorem fcrStep_observed_of_previousGreatest
    (v : ValidatorIndex) (n : ℕ)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true)
    (hnextNot : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) = false) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
      (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  rw [E.fcrStep_observed_boundary cfg ext v n hstart]
  simp [hnextNot]

/-- An actual FCR call saves the head it sees for the next slot's
previous-head test. -/
theorem fcr_currentSlotHead_succ_of_call
    (v : ValidatorIndex) (n : ℕ)
    (hcall : E.IsFCRCallAt cfg ext v n) :
    (E.fcr cfg ext v (n + 1)).current_slot_head =
      (get_head cfg (E.store cfg ext v (n + 1))).root := by
  simp only [Execution.fcr]
  have hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n) := hcall
  rw [if_pos hadv]
  simp only [on_fast_confirmation, update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- At a last-slot FCR call, the greatest-unrealized cache stores exactly
that call's unrealized justified checkpoint. -/
theorem fcr_previousGreatest_succ_of_last_call
    (v : ValidatorIndex) (n : ℕ)
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hlast : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) = true) :
    (E.fcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint := by
  simp only [Execution.fcr]
  have hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n) := hcall
  rw [if_pos hadv]
  simp only [on_fast_confirmation, update_fast_confirmation_variables]
  rw [if_pos hlast]
  split_ifs <;> rfl

/-- The last-slot call's two cached inputs survive until the next epoch
boundary. The explicit clock facts identify the two FCR calls. -/
theorem fcrStep_boundary_caches_of_last_call
    (v : ValidatorIndex) {lastCall q : ℕ}
    (hcall : E.IsFCRCallAt cfg ext v lastCall)
    (hle : lastCall + 1 ≤ q)
    (hsameSlot : E.slot_at cfg (lastCall + 1) = E.slot_at cfg q)
    (hlast : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (lastCall + 1)) + 1) = true)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (q + 1))) = true)
    (hnextNot : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (q + 1)) + 1) = false) :
    (E.fcrStep cfg ext v q).current_epoch_observed_justified_checkpoint =
        (E.store cfg ext v (lastCall + 1)).unrealized_justified_checkpoint ∧
      (E.fcrStep cfg ext v q).previous_slot_head =
        (get_head cfg (E.store cfg ext v (lastCall + 1))).root := by
  obtain ⟨hgreatest, hhead⟩ :=
    E.fcr_boundary_inputs_constant_in_slot cfg ext v hle hsameSlot
  constructor
  · rw [E.fcrStep_observed_of_previousGreatest cfg ext v q hstart hnextNot,
      ← hgreatest]
    exact E.fcr_previousGreatest_succ_of_last_call cfg ext v lastCall hcall hlast
  · rw [E.fcrStep_previousSlotHead_eq_currentSlotHead cfg ext v q,
      ← hhead]
    exact E.fcr_currentSlotHead_succ_of_call cfg ext v lastCall hcall

/-- The fifth live field supplies the head-agreement and previous-head
voting-source tests at the boundary once the ordinary FCR cache rotation is
identified with the last-slot store. -/
theorem live_ffg_boundary_gate_inputs
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {q : ℕ}
    (hq : q + 1 = E.slot_start cfg
      (compute_start_slot_at_epoch cfg (e + 1)))
    (hobserved : (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext w
        (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1) - 1))).unrealized_justified_checkpoint)
    (hprevious : (E.fcrStep cfg ext w q).previous_slot_head =
      (get_head cfg (E.store cfg ext w
        (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1) - 1)))).root) :
    (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext w (q + 1)).unrealized_justifications
        (get_head cfg (E.store cfg ext w (q + 1))).root ∧
    (get_voting_source cfg (E.store cfg ext w (q + 1))
      (E.fcrStep cfg ext w q).previous_slot_head).epoch + 2 ≥ e + 1 := by
  obtain ⟨c, _, _, hstores⟩ := live.ffg_timely_justification e he0 heDone
  obtain ⟨hlast, _, hnext, hsource⟩ := hstores w hw
  rw [hq]
  constructor
  · exact hobserved.trans (hlast.trans hnext.symm)
  · rw [hprevious]
    exact hsource

/-- For a completed epoch whose last slot begins after execution start, the
fifth live field reaches the actual next-boundary FCR query. Its observed
checkpoint agrees with the head's unrealized justification and its cached
previous head has a recent voting source. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_ffg_actual_boundary_inputs
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hlastAfterZero : E.slot_at cfg 0 <
      compute_start_slot_at_epoch cfg (e + 1) - 1)
    {w : ValidatorIndex} (hw : w ∈ E.honest) :
    let B := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
    let q := B - 1
    (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext w (q + 1)).unrealized_justifications
        (get_head cfg (E.store cfg ext w (q + 1))).root ∧
    (get_voting_source cfg (E.store cfg ext w (q + 1))
      (E.fcrStep cfg ext w q).previous_slot_head).epoch + 2 ≥ e + 1 := by
  let s := compute_start_slot_at_epoch cfg (e + 1) - 1
  let L := E.slot_start cfg s
  let B := E.slot_start cfg (s + 1)
  let q := B - 1
  have hnextPos : 0 < compute_start_slot_at_epoch cfg (e + 1) := by
    simp only [compute_start_slot_at_epoch]
    exact Nat.mul_pos (Nat.succ_pos e) cfg.slots_per_epoch_pos
  have hsSucc : s + 1 = compute_start_slot_at_epoch cfg (e + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hnextPos)
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have hgeom := E.adjacent_slot_start_call_geometry cfg ext
    h.trajectory.whole_seconds hgenTime w hlastAfterZero
  change (L - 1) + 1 = L ∧ (B - 1) + 1 = B ∧
    L ≤ B - 1 ∧ E.slot_at cfg L = s ∧
    E.slot_at cfg (B - 1) = s ∧
    E.IsFCRCallAt cfg ext w (L - 1) at hgeom
  obtain ⟨hLidx, hBidx, hLq, hLslot, hQslot, hcall⟩ := hgeom
  have hBslot : E.slot_at cfg B = s + 1 :=
    E.slot_at_slot_start cfg h.trajectory.whole_seconds
      (Nat.le_succ_of_le hlastAfterZero.le) hgenTime
  have hlast : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w ((L - 1) + 1)) + 1) = true := by
    rw [hLidx, E.store_current_slot, hLslot, hsSucc]
    exact live_epoch_start_is_start cfg (e + 1)
  have hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (q + 1))) = true := by
    rw [show q + 1 = B from hBidx, E.store_current_slot, hBslot, hsSucc]
    exact live_epoch_start_is_start cfg (e + 1)
  have hnextNot : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (q + 1)) + 1) = false := by
    rw [show q + 1 = B from hBidx, E.store_current_slot, hBslot, hsSucc]
    exact live_epoch_start_succ_not_start cfg h.slots_per_epoch_gt_one (e + 1)
  obtain ⟨hcacheObserved, hcacheHead⟩ :=
    E.fcrStep_boundary_caches_of_last_call cfg ext w
      hcall (by rw [hLidx]; exact hLq)
      (by rw [hLidx]; exact hLslot.trans hQslot.symm)
      hlast hstart hnextNot
  have hq : q + 1 = E.slot_start cfg
      (compute_start_slot_at_epoch cfg (e + 1)) := by
    rw [hBidx]
    exact congrArg (E.slot_start cfg) hsSucc
  have hlastIndex : (L - 1) + 1 = E.slot_start cfg
      (compute_start_slot_at_epoch cfg (e + 1) - 1) := by
    simpa only [L, s] using hLidx
  have hcacheObserved' :
      (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext w
        (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1) - 1))).unrealized_justified_checkpoint := by
    simpa only [hlastIndex] using hcacheObserved
  have hcacheHead' :
      (E.fcrStep cfg ext w q).previous_slot_head =
      (get_head cfg (E.store cfg ext w
        (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1) - 1)))).root := by
    simpa only [hlastIndex] using hcacheHead
  have hgate := E.live_ffg_boundary_gate_inputs cfg ext live
    he0 heDone hw hq hcacheObserved' hcacheHead'
  simpa only [B, q, hsSucc] using hgate

/-- The exact observed FCR cache root is known in the query store. This
holds regardless of whether the observed restart branch is taken. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_observed_root_known
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (v : ValidatorIndex) (q : ℕ) :
    (E.fcrStep cfg ext v q).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext v (q + 1)).block_roots := by
  have hrealized :=
    E.fcrStep_observed_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary v q
  simpa only [E.fcrStep_store] using hrealized.root_known

/-- A known execution block has the same epoch in its accepted carrier and
in the actual query store's block map. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_known_block_epoch
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} {q : ℕ} {r : Root} {b : BeaconBlock Root}
    (hblock : E.BlockAt r b)
    (hknown : r ∈ (E.store cfg ext v q).block_roots) :
    get_block_epoch cfg (E.store cfg ext v q) r =
      compute_epoch_at_slot cfg b.slot := by
  have hblock' := E.blockAt_of_store_known cfg ext hknown
  have heq := E.blockAt_unique h.trajectory.wellFormed hblock hblock'
  simpa only [get_block_epoch] using
    congrArg (fun x : BeaconBlock Root => compute_epoch_at_slot cfg x.slot) heq.symm

/-- At a completed next-epoch boundary, the observed checkpoint's block
epoch is exactly the previous epoch. This closes the executable restart
guard's epoch test from the fifth live field. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_ffg_observed_epoch_at_boundary
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hlastAfterZero : E.slot_at cfg 0 <
      compute_start_slot_at_epoch cfg (e + 1) - 1)
    {w : ValidatorIndex} (hw : w ∈ E.honest) :
    let B := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
    let q := B - 1
    get_block_epoch cfg (E.store cfg ext w (q + 1))
      (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint.root + 1 =
    get_current_store_epoch cfg (E.store cfg ext w (q + 1)) := by
  let B := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
  let q := B - 1
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have hfrom : E.slot_at cfg 0 < compute_start_slot_at_epoch cfg (e + 1) :=
    lt_of_lt_of_le hlastAfterZero (Nat.sub_le _ _)
  have hBpos : 0 < B :=
    (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).1 hfrom
  have hBidx : q + 1 = B :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hBpos)
  obtain ⟨c, _, ⟨r, b, hblock, hbe, hroot⟩, hstores⟩ :=
    live.ffg_timely_justification e he0 heDone
  have hAU : (E.store cfg ext w B).unrealized_justifications
      (get_head cfg (E.store cfg ext w B)).root = c := by
    simpa only [B] using (hstores w hw).2.2.1
  have hgate := h.live_ffg_actual_boundary_inputs cfg ext E live
    he0 heDone hlastAfterZero hw
  have hobs : (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint = c := by
    have hhead := hgate.1
    rw [hBidx] at hhead
    exact hhead.trans hAU
  have hknown : c.root ∈ (E.store cfg ext w B).block_roots := by
    have hk := h.live_observed_root_known cfg ext E w q
    rw [hBidx, hobs] at hk
    exact hk
  have hrootEpoch : get_block_epoch cfg (E.store cfg ext w B) c.root = e := by
    rw [hroot]
    exact (h.live_known_block_epoch cfg ext E hblock (by rwa [hroot] at hknown)).trans hbe
  have hBslot : E.slot_at cfg B = compute_start_slot_at_epoch cfg (e + 1) :=
    E.slot_at_slot_start cfg h.trajectory.whole_seconds hfrom.le hgenTime
  have hcurrent : get_current_store_epoch cfg (E.store cfg ext w B) = e + 1 := by
    rw [get_current_store_epoch, E.store_current_slot, hBslot]
    simp [compute_epoch_at_slot, compute_start_slot_at_epoch,
      cfg.slots_per_epoch_pos]
  dsimp only
  rw [hBidx, hobs, hrootEpoch, hcurrent]

/-- At an accepted epoch-start call, a timely observed checkpoint at or
beyond the old cache prevents a slot rollback in the stored output. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.confirmed_slot_ge_of_observed_catches_up
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hcall : E.IsFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true)
    (hepoch : get_block_epoch cfg (E.store cfg ext v (n + 1))
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root + 1 =
        get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (hhead : (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext v (n + 1)).unrealized_justifications
        (get_head cfg (E.store cfg ext v (n + 1))).root)
    (hcatch : get_block_slot (E.store cfg ext v (n + 1))
      (E.confirmed cfg ext v n) ≤
      get_block_slot (E.store cfg ext v (n + 1))
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) :
    get_block_slot (E.store cfg ext v (n + 1))
      (E.confirmed cfg ext v n) ≤
    get_block_slot (E.store cfg ext v (n + 1))
      (E.confirmed cfg ext v (n + 1)) := by
  let query := E.fcrStep cfg ext v n
  have hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots :=
    E.confirmed_known_of_acceptedGlobalTrajectory cfg ext
      h.semantics h.trajectory h.anchor_eq h.anchor_boundary hv n
      (E.withinHorizon_mono cfg (Nat.le_succ n) hHn1)
  have hinputKnown : getLatestAfterObserved cfg ext query ∈
      query.store.block_roots := by
    simpa only [query, Execution.getLatestConfirmedTraceAt,
      getLatestConfirmedTrace, getLatestAfterObserved] using
      E.getLatestConfirmedTraceAt_input_known cfg ext
        h.semantics h.trajectory h.anchor_eq h.anchor_boundary hknownN
  have hheadKnown : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    rw [show query.store = E.store cfg ext v (n + 1) from E.fcrStep_store cfg ext v n]
    exact E.headRootKnown_of_acceptedGlobalTrajectory cfg ext
      h.semantics h.trajectory h.anchor_eq h.anchor_boundary hv (n + 1) hHn1
  have hwf : ParentSlotLt query.store := by
    rw [show query.store = E.store cfg ext v (n + 1) from E.fcrStep_store cfg ext v n]
    exact E.store_parentSlotLt cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      (h.trajectory.wellFormed.anchor_parent_unscheduled) v (n + 1)
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r := by
    rw [show query.store = E.store cfg ext v (n + 1) from E.fcrStep_store cfg ext v n]
    exact E.store_walkKnownK cfg ext h.trajectory.wellFormed
      h.trajectory.externals_coherence h.trajectory.genesis_structure
      v (n + 1)
  have hlocal := getLatestTraceResult_slot_ge_cached_of_observed_catches_up
    cfg ext query hwf hwalk hheadKnown hinputKnown
    (by rw [E.fcrStep_store]; exact hstart)
    (by rw [E.fcrStep_store]; exact hepoch)
    (by rw [E.fcrStep_store]; exact hhead)
    (by rw [E.fcrStep_store, E.fcrStep_confirmed_root]; exact hcatch)
  rw [E.confirmed_succ_of_advance cfg ext v n hcall,
    ← getLatestTraceResult_eq_getLatestConfirmed]
  simpa only [query, E.fcrStep_store, E.fcrStep_confirmed_root] using hlocal

/-- A cached root from before the completed epoch cannot roll back at the
next epoch-start call. The fifth field makes the observed checkpoint newer,
and the actual restart catches any finalized-phase reset. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_stale_boundary_slot_monotone
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer : ValidatorIndex} {n m : ℕ}
    (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {e : Epoch}
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (heDone : compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hlastAfterZero : E.slot_at cfg 0 <
      compute_start_slot_at_epoch cfg (e + 1) - 1)
    {w : ValidatorIndex} (hw : w ∈ E.honest) :
    let B := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
    let q := B - 1
    get_block_epoch cfg (E.store cfg ext w B) (E.confirmed cfg ext w q) < e →
    get_block_slot (E.store cfg ext w B) (E.confirmed cfg ext w q) ≤
      get_block_slot (E.store cfg ext w B) (E.confirmed cfg ext w B) := by
  let S := compute_start_slot_at_epoch cfg (e + 1)
  let B := E.slot_start cfg S
  let q := B - 1
  dsimp only
  intro hstale
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have hfrom : E.slot_at cfg 0 < S :=
    lt_of_lt_of_le hlastAfterZero (Nat.sub_le _ _)
  have hBpos : 0 < B :=
    (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).1 hfrom
  have hq : q + 1 = B :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hBpos)
  have hBslot : E.slot_at cfg B = S :=
    E.slot_at_slot_start cfg h.trajectory.whole_seconds hfrom.le hgenTime
  have hBleM : B ≤ m := by
    apply Nat.le_of_not_gt
    intro htooLate
    have hslotLt : E.slot_at cfg m < S :=
      (E.slot_at_lt_iff cfg h.trajectory.whole_seconds hgenTime).2 htooLate
    exact (Nat.not_lt_of_ge heDone) hslotLt
  have hHB : E.WithinHorizon cfg B := E.withinHorizon_mono cfg hBleM hHm
  have hcall : E.IsFCRCallAt cfg ext w q :=
    E.slot_start_is_fcr_call cfg ext h.trajectory.whole_seconds
      hgenTime w hfrom
  have hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext w (q + 1))) = true := by
    rw [hq, E.store_current_slot, hBslot]
    exact live_epoch_start_is_start cfg (e + 1)
  have hgate := h.live_ffg_actual_boundary_inputs cfg ext E live
    he0 heDone hlastAfterZero hw
  dsimp only at hgate
  have hhead : (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext w (q + 1)).unrealized_justifications
        (get_head cfg (E.store cfg ext w (q + 1))).root := hgate.1
  have hepoch := h.live_ffg_observed_epoch_at_boundary cfg ext E live
    he0 heDone hlastAfterZero hw
  dsimp only at hepoch
  have hcurrent : get_current_store_epoch cfg (E.store cfg ext w B) = e + 1 := by
    rw [get_current_store_epoch, E.store_current_slot, hBslot]
    simp [S, compute_epoch_at_slot, compute_start_slot_at_epoch,
      cfg.slots_per_epoch_pos]
  have hobsEpoch : get_block_epoch cfg (E.store cfg ext w B)
      (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint.root = e := by
    rw [hq, hcurrent] at hepoch
    exact Nat.add_right_cancel hepoch
  have hcatch : get_block_slot (E.store cfg ext w (q + 1))
      (E.confirmed cfg ext w q) ≤
      get_block_slot (E.store cfg ext w (q + 1))
        (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint.root := by
    rw [hq]
    exact (live_block_slot_lt_of_epoch_lt cfg (E.store cfg ext w B)
      (E.confirmed cfg ext w q)
      (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint.root
      (by rw [hobsEpoch]; exact hstale)).le
  have hresult := h.confirmed_slot_ge_of_observed_catches_up cfg ext E hw
    hcall (by simpa only [hq] using hHB) hstart hepoch hhead hcatch
  simpa only [hq] using hresult

/-- The trusted anchor checkpoint has the epoch of the execution's first
slot. This also covers checkpoint-sync starts after genesis. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_anchor_checkpoint_epoch
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext) :
    h.semantics.anchor.epoch =
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hanchor : h.semantics.anchor.epoch = get_current_epoch cfg ast := by
    have heq := congrArg Checkpoint.epoch h.anchor_eq
    rw [hgenEq] at heq
    simpa only [get_forkchoice_store] using heq
  rw [hanchor]
  have hstate := h.anchor_epoch_eq_initial cfg ext E
  simpa only [Execution.anchor_state, hgenEq, get_forkchoice_store,
    Function.update_self] using hstate

/-- Repaired L3 age bound. At the first boundary the finalized root may be
the previous epoch's start block, so the bound is non-strict. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_finalized_slot_le_previous_start
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (w : ValidatorIndex) (t : ℕ) (e : Epoch)
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (hcurrent : get_current_store_epoch cfg (E.store cfg ext w t) = e + 1) :
    get_block_slot (E.store cfg ext w t)
      (E.store cfg ext w t).finalized_checkpoint.root ≤
        compute_start_slot_at_epoch cfg e := by
  let st := E.store cfg ext w t
  have hboundary := Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
    cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary w t
  have hslot : get_block_slot st st.finalized_checkpoint.root ≤
      compute_start_slot_at_epoch cfg st.finalized_checkpoint.epoch :=
    hboundary.finalized_root_slot_le_boundary
  have hlag := (E.acceptedFinalizationLagAt cfg ext h.semantics
    h.trajectory h.anchor_eq h.finalization_delay w t).realized
  have hepoch : st.finalized_checkpoint.epoch ≤ e := by
    rcases hlag with hanchor | hdelay
    · rw [hanchor]
      exact (h.live_anchor_checkpoint_epoch cfg ext E).trans_le he0
    · rw [hcurrent] at hdelay
      dsimp only [st] at hdelay ⊢
      have hstep : (E.store cfg ext w t).finalized_checkpoint.epoch + 1 ≤
          (E.store cfg ext w t).finalized_checkpoint.epoch + 2 :=
        Nat.add_le_add_left (by omega : 1 ≤ 2) _
      exact Nat.add_le_add_iff_right.mp (hstep.trans hdelay)
  exact hslot.trans (Nat.mul_le_mul_right cfg.slots_per_epoch hepoch)

/-- At a live epoch boundary, a finalized reset is either below the observed
checkpoint's start slot or has exactly that checkpoint root. The second case
is the first-boundary anchor equality witnessed in m8. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_finalized_below_or_eq_checkpoint
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (t : ℕ)
    (hHt : E.WithinHorizon cfg t) (e : Epoch) (cp : Root)
    (he0 : compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e)
    (hcurrent : get_current_store_epoch cfg (E.store cfg ext w t) = e + 1)
    (hcpSlot : get_block_slot (E.store cfg ext w t) cp =
      compute_start_slot_at_epoch cfg e)
    (hcpHead : is_ancestor (E.store cfg ext w t)
      (get_head cfg (E.store cfg ext w t)) (get_node_for_root cp) = true) :
    get_block_slot (E.store cfg ext w t)
      (E.store cfg ext w t).finalized_checkpoint.root <
        get_block_slot (E.store cfg ext w t) cp ∨
      (E.store cfg ext w t).finalized_checkpoint.root = cp := by
  let st := E.store cfg ext w t
  have hle := h.live_finalized_slot_le_previous_start cfg ext E w t e
    he0 hcurrent
  rw [← hcpSlot] at hle
  by_cases hlt : get_block_slot st st.finalized_checkpoint.root <
      get_block_slot st cp
  · exact Or.inl hlt
  right
  have hslotEq : (st.blocks st.finalized_checkpoint.root).slot =
      (st.blocks cp).slot := Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
  have hlag := (E.acceptedFinalizationLagAt cfg ext h.semantics
    h.trajectory h.anchor_eq h.finalization_delay w t).realized
  rcases hlag with hanchor | hdelay
  · have hanchorHead : is_ancestor st (get_head cfg st)
        (get_node_for_root h.semantics.anchor.root) = true := by
      exact (E.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory cfg ext
        h.semantics h.trajectory h.anchor_eq h.anchor_boundary)
        w hw t (Nat.zero_le _) hHt
    rw [hanchor] at hslotEq ⊢
    simp only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq] at hanchorHead hcpHead
    rw [hslotEq] at hanchorHead
    exact hanchorHead.symm.trans hcpHead
  · have hfinEpoch : st.finalized_checkpoint.epoch < e := by
      dsimp only [st] at hdelay ⊢
      rw [hcurrent] at hdelay
      have hsucc : (E.store cfg ext w t).finalized_checkpoint.epoch + 1 ≤ e :=
        Nat.le_of_succ_le_succ hdelay
      exact (Nat.lt_succ_self _).trans_le hsucc
    have hboundary := Execution.ExactPrefixAcceptedFFGSemantics.finalizedBoundaryRealizationAt
      cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary w t
    have hstrict : get_block_slot st st.finalized_checkpoint.root <
        compute_start_slot_at_epoch cfg e :=
      hboundary.finalized_root_slot_le_boundary.trans_lt
        (Nat.mul_lt_mul_of_pos_right hfinEpoch cfg.slots_per_epoch_pos)
    have hslotEq' : get_block_slot st st.finalized_checkpoint.root =
        compute_start_slot_at_epoch cfg e := by
      rw [show get_block_slot st st.finalized_checkpoint.root =
        get_block_slot st cp from hslotEq, hcpSlot]
    rw [hslotEq'] at hstrict
    exact False.elim (Nat.lt_irrefl _ hstrict)

/-- The fifth live field supplies the checkpoint used by the repaired L3
branch split at the actual next-epoch FCR call. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_boundary_finalized_below_or_eq_observed
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
    get_block_slot (E.store cfg ext w B)
      (E.store cfg ext w B).finalized_checkpoint.root <
      get_block_slot (E.store cfg ext w B)
        (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint.root ∨
    (E.store cfg ext w B).finalized_checkpoint.root =
      (E.fcrStep cfg ext w q).current_epoch_observed_justified_checkpoint.root := by
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
  have hcurrent : get_current_store_epoch cfg (E.store cfg ext w B) = e + 1 := by
    rw [get_current_store_epoch, E.store_current_slot, hBslot]
    simp [S, compute_epoch_at_slot, compute_start_slot_at_epoch,
      cfg.slots_per_epoch_pos]
  have hresult := h.live_finalized_below_or_eq_checkpoint cfg ext E
    w hw B hHB e c.root he0 hcurrent hcpSlot hcpHead
  simpa only [B, S, q, hobs] using hresult

end Execution

end FastConfirmation.Spec

end
