module
public import FastConfirmationProofs.FFG.SelectedSource.SelectedTraceFFGRealization
public import FastConfirmationProofs.FFG.Certificates.CurrentTargetCertificateRealization
public import FastConfirmationProofs.Checkpoints.PaperCheckpointInclusionSupportRealization
public import FastConfirmationProofs.Checkpoints.GlobalResetCheckpointRealization
public import FastConfirmationProofs.Execution.History.HistoricalCurrentTargetTrajectory
public import FastConfirmationProofs.Execution.Delivery.VoteDeadlineOrigin

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Assumption 3.2 at actual calls

Connects selected checkpoints to included attestations and canonical chain evidence.

This module contains `currentTarget_eq_selectedCheckpoint_of_currentEpochAncestor`, `canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch`, `selectedEarlyA32Carrier_of_currentTarget_eq_anchor` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)



/-- For a current-epoch selected result, the post-query selected induction
window covers the whole next epoch.  Strict epoch separation supplies the
lower and upper timing inequalities, and block relay supplies the knownness
conjunct which `SelectedCanonicalBeforeEndpointAt` intentionally omits. -/
theorem canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (hcallAt : ∃ n : ℕ, q = n + 1 ∧
      E.IsScheduledFCRCallAt cfg ext v n)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hknownLater : ∀ w' ∈ E.honest, ∀ m',
      E.slot_start cfg (E.slot_at cfg q) ≤ m' → E.WithinHorizon cfg m' →
      selected ∈ (E.store cfg ext w' m').block_roots)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m) :
    E.CanonicalThroughoutEpoch cfg ext selected (e + 1) := by
  intro w' hw' m' hm'H hm'Epoch
  have hqEpoch : compute_epoch_at_slot cfg (E.slot_at cfg q) = e := by
    calc
      compute_epoch_at_slot cfg (E.slot_at cfg q) =
          get_current_store_epoch cfg (E.store cfg ext v q) := by
        simp only [get_current_store_epoch, E.store_current_slot cfg ext v q]
      _ = e := heCurrent.symm
  have hslotLower : E.slot_at cfg q < E.slot_at cfg m' := by
    by_contra hnot
    have hle : E.slot_at cfg m' ≤ E.slot_at cfg q := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m') ≤
      compute_epoch_at_slot cfg (E.slot_at cfg q) at hepochLe
    rw [hm'Epoch, hqEpoch] at hepochLe
    exact (Nat.not_succ_le_self e) (by
      simpa only [Nat.succ_eq_add_one] using hepochLe)
  have hindexLower : E.slot_start cfg (E.slot_at cfg q) ≤ m' :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotLower.le
  have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext w m]
  have hslotUpper : E.slot_at cfg m' < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg m' := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m) ≤
      compute_epoch_at_slot cfg (E.slot_at cfg m') at hepochLe
    rw [hmEpoch, hm'Epoch] at hepochLe
    have hbad : Nat.succ (e + 1) ≤ e + 1 := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        hlate.trans hepochLe
    exact (Nat.not_succ_le_self (e + 1)) hbad
  have hknown := hknownLater w' hw' m' hindexLower hm'H
  exact ⟨hknown, hcanonical w' hw' m' hindexLower hslotUpper hm'H⟩






end Execution

end FastConfirmation.Spec

end
