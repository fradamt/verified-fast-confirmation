module
public import FastConfirmation.Spec.Proof.MonotonicityLiveConfirmation
public import FastConfirmation.Spec.Proof.MonotonicityTrace

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

namespace Execution

variable (E : Execution Root)

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

end Execution

end FastConfirmation.Spec

end
