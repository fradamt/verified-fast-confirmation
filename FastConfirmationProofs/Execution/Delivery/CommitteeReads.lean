module
public import FastConfirmationProofs.Execution.Delivery.Registry

@[expose] public section

/-!
# Committee reads in the read window

An honest committee read in the read window is the execution committee. The
two premise fields are `BeaconExternalsPremises.committee_seed_agreement`,
which makes honest reads in the window agree, and
`BeaconExternalsPremises.committees_agree`, which makes the execution committee
one of these reads. This file also gives the window bounds that the FCR
ranges use: each range starts at or after the start of the anchor epoch and
ends at or before the current slot.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- The first slot of the anchor epoch, the lower end of the committee read
window. -/
def anchorEpochStart : Slot :=
  compute_start_slot_at_epoch cfg (compute_epoch_at_slot cfg E.anchor_state.slot)

variable {E}

omit [LinearOrder Root] [Inhabited Root] in
/-- The read window in the two bounds used by the proofs. -/
theorem committeeReadWindow_iff {n : ℕ} {s : Slot} :
    CommitteeReadWindow cfg E n s ↔
      E.anchorEpochStart cfg ≤ s ∧ s ≤ E.slot_at cfg n :=
  Iff.rfl

omit [LinearOrder Root] [Inhabited Root] in
/-- A slot at or after the anchor slot is at or after the anchor epoch start. -/
theorem anchorEpochStart_le_of_anchor_le {x : Slot}
    (h : E.anchor_state.slot ≤ x) : E.anchorEpochStart cfg ≤ x :=
  (Nat.div_mul_le_self _ _).trans h

omit [LinearOrder Root] [Inhabited Root] in
/-- The epoch start of a slot at or after the anchor slot is at or after the
anchor epoch start. -/
theorem anchorEpochStart_le_epochStart {x : Slot}
    (h : E.anchor_state.slot ≤ x) :
    E.anchorEpochStart cfg ≤
      compute_start_slot_at_epoch cfg (compute_epoch_at_slot cfg x) := by
  simp only [anchorEpochStart, compute_start_slot_at_epoch, compute_epoch_at_slot]
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

/-- The anchor slot is at most the wall-clock slot of every relative second. -/
theorem anchor_state_slot_le_slot_at (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) (n : ℕ) :
    E.anchor_state.slot ≤ E.slot_at cfg n :=
  le_trans (E.anchor_state_slot_le cfg hdiv hgen) (E.slot_at_mono cfg (Nat.zero_le n))

end Execution

/-- An honest committee read in the read window is the execution committee. -/
theorem BeaconExternalsPremises.committee_read_eq {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hnH : E.WithinHorizon cfg n) {s : Slot}
    (hs : CommitteeReadWindow cfg E n s) :
    get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s := by
  obtain ⟨w, hw, m, hmH, hsm, hread⟩ := hec.committees_agree v hv n s hnH hs
  rw [hec.committee_seed_agreement v hv w hw n m s hnH hmH hs hsm, hread]

/-- Honest committee reads over a range in the read window are the execution
committees. -/
theorem BeaconExternalsPremises.committee_reads_Icc {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest)
    {n : ℕ} (hnH : E.WithinHorizon cfg n) {sa es : Slot}
    (hsaA : E.anchorEpochStart cfg ≤ sa) (hesN : es ≤ E.slot_at cfg n) :
    (Finset.Icc sa es).biUnion
        (fun s => get_slot_committee cfg ext (E.store cfg ext v n) s) =
      (Finset.Icc sa es).biUnion E.committee := by
  apply Finset.biUnion_congr rfl
  intro s hs
  exact hec.committee_read_eq cfg ext hv hnH
    ⟨hsaA.trans (Finset.mem_Icc.mp hs).1, (Finset.mem_Icc.mp hs).2.trans hesN⟩

end FastConfirmation.Spec

end
