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

end Execution

end FastConfirmation.Spec

end
