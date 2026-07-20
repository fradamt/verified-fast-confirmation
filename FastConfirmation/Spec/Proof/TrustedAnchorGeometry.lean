import FastConfirmation.Spec.Proof.CheckpointGeometry
import FastConfirmation.Spec.Proof.FFGGlobalCheckpointTrajectory

/-!
# Safety-free trusted-anchor geometry

These facts turn the checkpoint-sync boundary condition and ordinary store
growth into checkpoint and walk geometry.  They deliberately carry no safety,
canonicality, filter, source-availability, tip-placement, takeover, or
honest-head conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- A boundary-aligned trusted checkpoint is its own block checkpoint.  The
alignment may occur at any epoch: no `GENESIS_SLOT` specialization is used. -/
theorem trustedAnchor_checkpointForBlock
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    get_checkpoint_for_block cfg E.genesis_store anchor.root
        (get_block_epoch cfg E.genesis_store anchor.root) = anchor := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, _hanchorParent⟩ := hA.genesis
  have hroot : anchor.root = ablk.root := by
    have h := congrArg Checkpoint.root hanchor
    rw [hgenEq] at h
    simpa only [get_forkchoice_store] using h
  have hepoch : get_block_epoch cfg E.genesis_store anchor.root =
      anchor.epoch := by
    rw [hgenEq, hroot]
    have h := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at h
    simp only [get_block_epoch, get_forkchoice_store,
      Function.update_self, get_current_epoch, hanchorSlot] at h ⊢
    exact h.symm
  have hstartLe : compute_start_slot_at_epoch cfg anchor.epoch ≤
      (E.genesis_store.blocks anchor.root).slot := by
    rw [← hepoch]
    exact start_slot_at_block_epoch_le cfg E.genesis_store anchor.root
  have hslotEq : (E.genesis_store.blocks anchor.root).slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    exact Nat.le_antisymm hboundary hstartLe
  apply checkpoint_eq_of_epoch_root_eq
  · simpa only [get_checkpoint_for_block] using hepoch
  · simp only [get_checkpoint_for_block, get_checkpoint_block]
    rw [hepoch, ← hslotEq, get_ancestor_stop (Nat.le_refl _)]

/-- Boundary alignment identifies the trusted anchor block slot with the start
of the anchor's declared epoch, at an arbitrary checkpoint-sync boundary. -/
theorem trustedAnchor_slot_eq_start
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    (E.genesis_store.blocks anchor.root).slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, _hanchorParent⟩ := hA.genesis
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hepoch : get_block_epoch cfg E.genesis_store anchor.root =
      anchor.epoch := by
    rw [hgenEq, hroot]
    have h := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at h
    simp only [get_block_epoch, get_forkchoice_store,
      Function.update_self, get_current_epoch, hanchorSlot] at h ⊢
    exact h.symm
  apply Nat.le_antisymm hboundary
  rw [← hepoch]
  exact start_slot_at_block_epoch_le cfg E.genesis_store anchor.root

/-- The trusted anchor supplies a known walk down to every later epoch
boundary in every concrete execution store. -/
theorem trustedAnchor_boundaryWalkAtEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) {e : Epoch}
    (hae : anchor.epoch ≤ e)
    {r : Root} (hr : r ∈ (E.store cfg ext v n).block_roots) :
    WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg e) r := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hanchor0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorN : anchor.root ∈
      (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchor0
  have hwalkAnchor : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks anchor.root).slot r :=
    E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
        v n anchor.root hanchorN r hr
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hroot]
    exact E.store_anchor_block cfg ext hA.wellFormed hgenEq v n
      (hroot ▸ hanchorN)
  have hslot0 := E.trustedAnchor_slot_eq_start cfg ext hA
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgenEq, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  apply hwalkAnchor.mono
  rw [hanchorBlock, hanchorStart]
  simpa only [compute_start_slot_at_epoch] using
    Nat.mul_le_mul_right cfg.slots_per_epoch hae

/-- Every known concrete block lies in the trusted anchor epoch or later. -/
theorem trustedAnchor_epoch_le_blockEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) {b : Root}
    (hb : b ∈ (E.store cfg ext v n).block_roots) :
    anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext v n) b := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hslot0 := E.trustedAnchor_slot_eq_start cfg ext hA
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgenEq, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  have hminimum : ablk.message.slot ≤
      ((E.store cfg ext v n).blocks b).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgenEq hanchorSlot hanchorParent v n b hb
  simp only [get_block_epoch, compute_epoch_at_slot]
  apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
  change compute_start_slot_at_epoch cfg anchor.epoch ≤
    ((E.store cfg ext v n).blocks b).slot
  rw [← hanchorStart]
  exact hminimum

/-- The trusted anchor epoch is no later than the clock epoch of every
concrete execution store. -/
theorem trustedAnchor_epoch_le_currentEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) (n : ℕ) :
    anchor.epoch ≤ get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hroot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hanchor0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hroot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorN : anchor.root ∈
      (E.store cfg ext v n).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchor0
  have hanchorBlock :
      (E.store cfg ext v n).blocks anchor.root = ablk.message := by
    rw [hroot]
    exact E.store_anchor_block cfg ext hA.wellFormed hgenEq v n
      (hroot ▸ hanchorN)
  have hslot0 := E.trustedAnchor_slot_eq_start cfg ext hA
    hanchor hboundary
  have hanchorStart : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hgenEq, hroot] at hslot0
    simpa only [get_forkchoice_store, Function.update_self] using hslot0
  have hslotUpper : ((E.store cfg ext v n).blocks anchor.root).slot ≤
      get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hanchorSlot⟩ v n anchor.root hanchorN
  simp only [get_current_store_epoch, compute_epoch_at_slot]
  apply (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).2
  change compute_start_slot_at_epoch cfg anchor.epoch ≤
    get_current_slot cfg (E.store cfg ext v n)
  rw [← hanchorStart, ← hanchorBlock]
  exact hslotUpper

/-- The checkpoint of a known block is stable under growth of one execution
store trajectory.  This is block-map provenance plus the ordinary walk
domain, not a cross-store ancestry assumption. -/
theorem checkpointForBlock_storeLE
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {n m : ℕ} (hnm : n ≤ m)
    {b : Root} (hb : b ∈ (E.store cfg ext v n).block_roots)
    {e : Epoch}
    (hwalkBoundary : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg e) b) :
    get_checkpoint_for_block cfg (E.store cfg ext v n) b e =
      get_checkpoint_for_block cfg (E.store cfg ext v m) b e := by
  have hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext v m).block_roots :=
    (E.store_storeLE cfg ext v hnm).1
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x =
        (E.store cfg ext v m).blocks x :=
    fun x hx => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v m) hx (hsub hx)
  have hroot : get_checkpoint_block cfg (E.store cfg ext v n) b e =
      get_checkpoint_block cfg (E.store cfg ext v m) b e := by
    simp only [get_checkpoint_block]
    rw [get_ancestor_congr hagree hb hwalkBoundary]
  exact congrArg (Checkpoint.mk e) hroot

end Execution

end FastConfirmation.Spec
