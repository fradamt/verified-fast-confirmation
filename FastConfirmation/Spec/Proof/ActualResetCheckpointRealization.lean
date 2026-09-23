module
public import FastConfirmation.Spec.Proof.FCRCallContracts
public import FastConfirmation.Spec.Proof.TrustedAnchorGeometry
public import FastConfirmation.Spec.Proof.ModelFacts

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Concrete realization of the two actual FCR reset checkpoints

The finalized reset is reconstructed from the executable global-checkpoint
ledger.  The observed reset is reconstructed from the exact
`update_fast_confirmation_variables` rotation, with a ghost invariant for the
two checkpoint fields retained by `Execution.fcr`.

Only root knownness and a conditional certificate for the root's current-epoch
checkpoint are exported.  No FCR ancestry, safety, historical conclusion, or
`JustificationInterface` premise enters this construction.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact FCR field rotation -/

/-- Exact source selected for the carried greatest-unrealized field. -/
theorem update_fcv_previous_greatest_exact
    (fcrStore : FastConfirmationStore Root) :
    FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
        (update_fast_confirmation_variables cfg fcrStore) =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store + 1) then
        fcrStore.store.unrealized_justified_checkpoint
      else fcrStore.previous_epoch_greatest_unrealized_checkpoint := by
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- Exact source selected for the observed checkpoint, including the ordered
write through the possibly just-updated greatest-unrealized field. -/
theorem update_fcv_observed_exact
    (fcrStore : FastConfirmationStore Root) :
    (update_fast_confirmation_variables cfg fcrStore).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store) then
        if is_start_slot_at_epoch cfg
            (get_current_slot cfg fcrStore.store + 1) then
          fcrStore.store.unrealized_justified_checkpoint
        else fcrStore.previous_epoch_greatest_unrealized_checkpoint
      else fcrStore.current_epoch_observed_justified_checkpoint := by
  simp only [update_fast_confirmation_variables]
  split_ifs <;> rfl

namespace Execution

variable (E : Execution Root)

/-! ## Store-local checkpoint realization -/

/-- Internal evidence retained while a reset checkpoint is carried through
the FCR trajectory.  The boundary inequality is the concrete geometry needed
to identify `c` with the checkpoint of `c.root` when that root is in the
store's current epoch. -/
structure ResetCheckpointRealizedAt
    (anchor : Checkpoint Root) (store : Store Root)
    (c : Checkpoint Root) : Prop where
  root_known : c.root ∈ store.block_roots
  root_slot_le_boundary :
    (store.blocks c.root).slot ≤ compute_start_slot_at_epoch cfg c.epoch
  epoch_le_current : c.epoch ≤ get_current_store_epoch cfg store
  certified : Nonempty (CertifiedJustified cfg E anchor c)


/-- Realization is stable under growth along one node's execution-store
trajectory. -/
theorem ResetCheckpointRealizedAt.mono
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor c : Checkpoint Root} {v : ValidatorIndex} {n m : ℕ}
    (hnm : n ≤ m)
    (h : E.ResetCheckpointRealizedAt cfg anchor
      (E.store cfg ext v n) c) :
    E.ResetCheckpointRealizedAt cfg anchor (E.store cfg ext v m) c := by
  have hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext v m).block_roots :=
    (E.store_storeLE cfg ext v hnm).1
  have hknownM : c.root ∈ (E.store cfg ext v m).block_roots :=
    hsub h.root_known
  have hagree : (E.store cfg ext v n).blocks c.root =
      (E.store cfg ext v m).blocks c.root :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v m) h.root_known hknownM
  have hcurrentMono :
      get_current_store_epoch cfg (E.store cfg ext v n) ≤
        get_current_store_epoch cfg (E.store cfg ext v m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (E.slot_at_mono cfg hnm)
  exact {
    root_known := hknownM
    root_slot_le_boundary := by
      rw [← hagree]
      exact h.root_slot_le_boundary
    epoch_le_current := h.epoch_le_current.trans hcurrentMono
    certified := h.certified
  }





/-! ## Global field realizations -/



/-! ## The retained FCR checkpoint history -/

/-- Ghost evidence for the two FCR fields from which an observed checkpoint
can be sourced at the next query. -/
structure ResetCheckpointHistoryAt
    (anchor : Checkpoint Root) (v : ValidatorIndex) (n : ℕ) : Prop where
  observed : E.ResetCheckpointRealizedAt cfg anchor
    (E.store cfg ext v n)
    (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint
  previous_greatest : E.ResetCheckpointRealizedAt cfg anchor
    (E.store cfg ext v n)
    (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint

/-- At a real slot advance, the retained greatest-unrealized field is either
the current store's UJ checkpoint or the previous retained value. -/
theorem fcr_previous_greatest_succ_of_advance
    (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.fcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else
        (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  simp only [Execution.fcr]
  rw [if_pos hadv]
  change FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
    (update_fast_confirmation_variables cfg
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  exact update_fcv_previous_greatest_exact cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- At a real slot advance, the observed field follows the exact ordered
two-stage rotation. -/
theorem fcr_observed_succ_of_advance
    (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.fcr cfg ext v (n + 1)).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1))) then
        if is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
          (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
        else
          (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint
      else
        (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint := by
  simp only [Execution.fcr]
  rw [if_pos hadv]
  change FastConfirmationStore.current_epoch_observed_justified_checkpoint
    (update_fast_confirmation_variables cfg
      { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  exact update_fcv_observed_exact cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }

/-- The actual query's observed checkpoint follows the same exact rotation,
whether or not that speculative query is a real slot call. -/
theorem fcrStep_observed_exact (v : ValidatorIndex) (n : ℕ) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1))) then
        if is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
          (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
        else
          (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint
      else
        (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint := by
  rw [Execution.fcrStep]
  exact update_fcv_observed_exact cfg
    { E.fcr cfg ext v n with store := E.store cfg ext v (n + 1) }



/-! ## Public reset producer -/


end Execution

end FastConfirmation.Spec

end
